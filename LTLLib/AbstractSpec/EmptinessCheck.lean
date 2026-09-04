/-
  Abstract contract any concrete emptiness-check algorithm must satisfy.

  Key definitions:
  - `EmptinessResult`: Outcome of a check (empty, or a witnessing stem/loop)
  - `AcceptingCycle`: Lasso witness of non-emptiness over a graph
  - `Reachable`/`FiniteReach`: Canonical reachability and its finiteness hypothesis
  - `EmptinessChecker`: Sound and complete emptiness-check contract

  Key theorems:
  - `Reachable.toChain`: a `Reachable` proof unrolled into its explicit witnessing chain
  - `FiniteReach.exists_lt_sample_eq`: the pigeonhole step shared by the pumping lemmas

  Sections:
  - Accepting cycle definition
  - Finite-reachability hypothesis
  - Algorithm-agnostic emptiness-check contract
-/
import Std
import Mathlib.Data.Set.Card
import LTLLib.AbstractSpec.Lasso
import LTLLib.AbstractSpec.GraphPaths

namespace LTLLib

/-- Result of a graph emptiness check: does the graph reachable from
`initialStates` via `succs` contain a cycle through an `isAccepting`
state? -/
inductive EmptinessResult (State : Type u) where
  -- No accepting cycle found: the automaton's language is empty.
  | empty (exploredStates : Nat)
  -- An accepting cycle was found: the automaton's language is non-empty.
  -- `stem`: path from an initial state to the accepting state (inclusive).
  -- `loop`: cycle from the accepting state back to itself (inclusive on both ends).
  | nonEmpty (stem : List State) (loop : List State)
deriving Repr, Inhabited

/-! ## Accepting cycle definition -/

/-- An accepting cycle: a stem from an initial state to an accepting state, plus a cycle from that
    state back to itself. This is the standard "lasso" witness for Büchi automaton non-emptiness
    (cf. CVWY §2, Schwoon & Esparza §2). -/
structure AcceptingCycle {State}
    (initialStates : List State) (succs : State → Array State)
    (isAccepting : State → Bool) where
  stem : List State
  cycle : List State
  stem_nonempty : stem.length ≥ 1
  cycle_nonempty : cycle.length ≥ 1
  stem_head_initial : stem.head (List.ne_nil_of_length_pos (by omega)) ∈ initialStates
  stem_chain : ∀ (i : Nat), (hi : i + 1 < stem.length) →
    stem[i + 1] ∈ succs (stem[i])
  overlap : stem.getLast (List.ne_nil_of_length_pos (by omega)) =
            cycle.head (List.ne_nil_of_length_pos (by omega))
  cycle_chain : ∀ (i : Nat), (hi : i + 1 < cycle.length) →
    cycle[i + 1] ∈ succs (cycle[i])
  cycle_back : cycle.head (List.ne_nil_of_length_pos (by omega)) ∈
    succs (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
  cycle_head_accepting : isAccepting (cycle.head (List.ne_nil_of_length_pos (by omega))) = true

/-- An `AcceptingCycle` over any graph is exactly a `ValidLasso` for any `OASpec` whose
`trans`/`initial`/`acceptSet` agree with that graph's `succs`/`initialStates`/`isAccepting`. -/
def AcceptingCycle.toValidLassoOf {State : Type u} {α : Type v}
    {succs : State → Array State} {initialStates : List State}
    {isAccepting : State → Bool} {A : OASpec State α 1}
    (htrans : ∀ {s t : State}, t ∈ succs s ↔ A.trans s t)
    (hinit : ∀ {s : State}, s ∈ initialStates ↔ A.initial s)
    (hacc : ∀ {s : State}, isAccepting s = true ↔ A.acceptSet ⟨0, by omega⟩ s)
    (ac : AcceptingCycle initialStates succs isAccepting) :
    ValidLasso A ac.stem ac.cycle where
  stem_nonempty := ac.stem_nonempty
  cycle_nonempty := ac.cycle_nonempty
  stem_initial := hinit.mp ac.stem_head_initial
  stem_chain := fun i hi => htrans.mp (ac.stem_chain i hi)
  overlap := ac.overlap
  cycle_chain := fun i hi => htrans.mp (ac.cycle_chain i hi)
  cycle_back := htrans.mp ac.cycle_back
  cycle_accepting := hacc.mp ac.cycle_head_accepting

/-! ## Finite-reachability hypothesis -/

/-- Canonical reachability: every `i ∈ initialStates` is reachable
(reflexively), and reachability is closed under one `succs`-step. -/
inductive Reachable {State : Type u} (initialStates : List State)
    (succs : State → Array State) : State → Prop where
  | base {i : State} (hi : i ∈ initialStates) : Reachable initialStates succs i
  | step {s t : State} (hs : Reachable initialStates succs s) (ht : t ∈ succs s) :
      Reachable initialStates succs t

/-- A `Reachable` proof unrolled into its explicit witnessing chain from some initial state. -/
theorem Reachable.toChain {State : Type u} {initialStates : List State} {succs : State → Array State}
    {s : State} (h : Reachable initialStates succs s) :
    ∃ l : List State, ∃ hne : l ≠ [], l.head hne ∈ initialStates ∧ l.getLast hne = s ∧
      ∀ i, (hi : i + 1 < l.length) → l[i + 1] ∈ succs (l[i]) := by
  induction h with
  | @base i hi => exact ⟨[i], by simp, by simpa using hi, by simp, by simp⟩
  | @step s t _ ht ih =>
    obtain ⟨l, hne, hhead, hlast, hchain⟩ := ih
    refine ⟨l ++ [t], by simp, ?_, by simp, chain_append_singleton l t hchain hne (by rw [hlast]; exact ht)⟩
    rw [head_append_singleton_eq l t hne]
    exact hhead

/-- Every state along a run from an initial state is reachable. -/
theorem Reachable.of_run {State : Type u} {initialStates : List State} {succs : State → Array State}
    {σ : Nat → State} (hinit : σ 0 ∈ initialStates) (htrans : ∀ n, σ (n + 1) ∈ succs (σ n)) (n : Nat) :
    Reachable initialStates succs (σ n) := by
  induction n with
  | zero => exact .base hinit
  | succ n ih => exact .step ih (htrans n)

/-- Bare existence certificate: the canonically-reachable set is finite.
    No witness must be provided. -/
def FiniteReach {State : Type u} (initialStates : List State)
    (succs : State → Array State) : Prop :=
  {s | Reachable initialStates succs s}.Finite

/-- Pigeonhole on an infinite sampling of a run: only finitely many states are reachable, so two distinct
sample points carry the same state. The step every pumping lemma opens with, `f` need not be injective. -/
theorem FiniteReach.exists_lt_sample_eq {State : Type u} {initialStates : List State}
    {succs : State → Array State} (fr : FiniteReach initialStates succs) {σ : Nat → State}
    (hmem : ∀ n, Reachable initialStates succs (σ n)) (f : Nat → Nat) :
    ∃ i j, i < j ∧ σ (f i) = σ (f j) := by
  obtain ⟨i, -, j, -, hne, heq⟩ := Set.Infinite.exists_ne_map_eq_of_mapsTo
    (s := (Set.univ : Set Nat)) (t := {s | Reachable initialStates succs s})
    (f := fun k => σ (f k)) Set.infinite_univ (fun k _ => hmem _) fr
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact ⟨i, j, h, heq⟩
  · exact ⟨j, i, h, heq.symm⟩

/-! ## Algorithm-agnostic emptiness-check contract -/

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-- Contract any emptiness-check algorithm must satisfy. -/
structure EmptinessChecker (State : Type u) [BEq State] [Hashable State]
    [LawfulBEq State] where
  -- Runs the algorithm on a graph and reports whether an accepting cycle exists.
  check : (succs : State → Array State) → (initialStates : List State) →
    FiniteReach initialStates succs → (isAccepting : State → Bool) →
    EmptinessResult State
  -- Soundness of `.nonEmpty`: a returned `stem`/`loop` is a genuine `AcceptingCycle` witness.
  nonEmpty_valid : ∀ {succs : State → Array State} {initialStates : List State}
      {fr : FiniteReach initialStates succs} {isAccepting : State → Bool}
      {stem loop : List State},
    check succs initialStates fr isAccepting = .nonEmpty stem loop →
    ∃ ac : AcceptingCycle initialStates succs isAccepting,
      ac.stem = stem ∧ ac.cycle = loop.tail
  -- Completeness of `.empty`: no `AcceptingCycle` exists.
  empty_no_cycle : ∀ {succs : State → Array State} {initialStates : List State}
      {fr : FiniteReach initialStates succs} {isAccepting : State → Bool} {n : Nat},
    check succs initialStates fr isAccepting = .empty n →
    ¬∃ _ac : AcceptingCycle initialStates succs isAccepting, True

end LTLLib
