module

/-
  Generic graph-search infrastructure: the verdict an emptiness check reports, canonical reachability and
  its finiteness certificate, the termination measure built on it, and the fused expansion the searches walk.

  Defines:
  - `EmptinessResult`: the outcome of a check, empty or a witnessing stem and loop, with `map` renaming its states
  - `Reachable`, `FiniteReach`: canonical reachability and the bare certificate that only finitely much of it exists
  - `reachCount`: termination measure counting the reachable states satisfying a property
  - `ExpandCoherent`, `derivedExpand`, `filterExpand`: the fused `(succs, edgeMarks)` callback and its laws
  - `totalizeSucc`: a successor function with a self-loop put at every terminal state

  Proves:
  - `Reachable.toChain`: a `Reachable` proof unrolled into its explicit witnessing chain
  - `Reachable.mono_init`: reachability from a list is reachability from any list containing its members
  - `Reachable.exists_pathTo`: a reachable state is reached by a path through reachable states only
  - `FiniteReach.exists_lt_sample_eq`: the pigeonhole step shared by the pumping lemmas
  - `reachCount_le`, `reachCount_lt`: the measure is monotone, and strictly so once a reachable state leaves
  - `finiteReach_totalizeSucc`: totalizing the successors preserves finite reachability

  Sections:
  - Emptiness-check verdict
  - Finite-reachability hypothesis
  - Totalized successors
-/
public import Std
public import Lasso.Data.FinitePred
public import Lasso.Data.List
public import Lasso.AbstractSpec.GraphPaths

public section

namespace Lasso

/-! ## Emptiness-check verdict -/

/-- Result of a graph emptiness check: does the graph reachable from `initialStates` via `succs` contain
an accepting cycle? -/
inductive EmptinessResult (State : Type u) where
  -- No accepting cycle found: the automaton's language is empty.
  | empty (exploredStates : Nat)
  -- An accepting cycle was found: the automaton's language is non-empty.
  -- `stem`: path from an initial state to the state `q` the cycle closes at (inclusive).
  -- `loop`: `q :: cycle`, where `cycle` starts at `q` and its last state steps back to `q`, the
  --   checkers' contracts equating their witness's `cycle` with `loop.tail`. The run is `stem`, then
  --   `loop.tail` repeated, the two sharing `q`.
  | nonEmpty (stem : List State) (loop : List State)
deriving Repr, Inhabited

/-- Rename the states of a result, leaving the verdict alone. -/
@[expose] def EmptinessResult.map {P : Type u} {Q : Type v} (f : P → Q) :
    EmptinessResult P → EmptinessResult Q
  | .empty n => .empty n
  | .nonEmpty stem loop => .nonEmpty (stem.map f) (loop.map f)

/-- `map` does not invent a verdict: an `.empty` image comes from an `.empty`, with the same count. -/
theorem EmptinessResult.map_eq_empty {P : Type u} {Q : Type v} {f : P → Q}
    {r : EmptinessResult P} {n : Nat} (h : r.map f = .empty n) : r = .empty n := by
  cases r with
  | empty m => simpa [EmptinessResult.map] using h
  | nonEmpty stem loop => simp [EmptinessResult.map] at h

/-- The other direction: a `.nonEmpty` image comes from a `.nonEmpty`, whose witness is the preimage. -/
theorem EmptinessResult.map_eq_nonEmpty {P : Type u} {Q : Type v} {f : P → Q}
    {r : EmptinessResult P} {stem loop : List Q} (h : r.map f = .nonEmpty stem loop) :
    ∃ stem' loop', r = .nonEmpty stem' loop' := by
  cases r with
  | empty n => simp [EmptinessResult.map] at h
  | nonEmpty stem' loop' => exact ⟨stem', loop', rfl⟩

/-! ## Finite-reachability hypothesis -/

/-- Canonical reachability: every `i ∈ initialStates` is reachable
(reflexively), and reachability is closed under one `succs`-step. -/
inductive Reachable {State : Type u} (initialStates : List State)
    (succs : State → Array State) : State → Prop where
  | base {i : State} (hi : i ∈ initialStates) : Reachable initialStates succs i
  | step {s t : State} (hs : Reachable initialStates succs s) (ht : t ∈ succs s) :
      Reachable initialStates succs t

/-- Reachability from a list is reachability from any list containing its members. -/
theorem Reachable.mono_init {State : Type u} {l l' : List State} {succs : State → Array State} {s : State}
    (hmem : ∀ x, x ∈ l → x ∈ l') (h : Reachable l succs s) : Reachable l' succs s := by
  induction h with
  | base hi => exact .base (hmem _ hi)
  | step _ ht ih => exact .step ih ht

/-- A reachable state is an initial state or the end of a path from one whose intermediates are all reachable. -/
theorem Reachable.exists_pathTo {State : Type u} {l : List State} {succs : State → Array State} {s : State}
    (h : Reachable l succs s) : ∃ s0 ∈ l, s0 = s ∨ PathTo succs (fun x => ¬ Reachable l succs x) s0 s := by
  induction h with
  | @base i hi => exact ⟨i, hi, Or.inl rfl⟩
  | @step s t hs ht ih =>
    obtain ⟨s0, hs0, h⟩ := ih
    refine ⟨s0, hs0, Or.inr ?_⟩
    rcases h with rfl | hp
    · exact .direct ht
    · exact hp.snoc (fun hn => hn hs) ht

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

/-- `expand` is the fused form of the two callbacks it stands for: one call yields a state's successors and the marks
of each, so a search pays the caller's per-source cost once per pushed frame instead of once per outgoing edge. -/
@[expose] def ExpandCoherent {State : Type u} (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) : Prop :=
  ∀ s, ((expand s).1, (expand s).2.1) = (succs s, (succs s).map (edgeMarks s))

/-- Filter a fused expansion by a predicate on the target, keeping the successors, their marks and their option bits
in step. The option-bit array is either empty or parallel to the successors, and filtering it by its own pass rather
than by one three-way `zip` is what preserves that, since `Array.zip` truncates to the shorter operand. -/
@[expose] def filterExpand {State : Type u} (e : Array State × Array (Std.HashSet Nat) × Array Nat)
    (p : State → Bool) : Array State × Array (Std.HashSet Nat) × Array Nat :=
  let z := (e.1.zip e.2.1).filter fun x => p x.1
  (z.map Prod.fst, z.map Prod.snd,
    if e.2.2.isEmpty then #[] else ((e.1.zip e.2.2).filter fun x => p x.1).map Prod.snd)

/-- Zipping an array against its own image and filtering on the source is filtering then re-pairing. -/
theorem zip_filter_map {State : Type u} {β : Type v} (ss : Array State) (f : State → β)
    (p : State → Bool) :
    ((ss.zip (ss.map f)).filter fun x => p x.1) = (ss.filter p).map (fun a => (a, f a)) := by
  have hlist : ∀ (l : List State),
      (l.zip (l.map f)).filter (fun x => p x.1) = (l.filter p).map (fun a => (a, f a)) := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => by_cases h : p a <;> simp [List.zip_cons_cons, h, ih]
  apply Array.ext'
  simp only [Array.toList_filter, Array.toList_zip, Array.toList_map, hlist]

/-- Filtering a fused expansion agrees with filtering the successors and re-deriving their marks, on the two
projections `ExpandCoherent` is stated over. -/
theorem filterExpand_fst_snd {State : Type u}
    {e : Array State × Array (Std.HashSet Nat) × Array Nat}
    {ss : Array State} {f : State → Std.HashSet Nat} (p : State → Bool)
    (h : (e.1, e.2.1) = (ss, ss.map f)) :
    ((filterExpand e p).1, (filterExpand e p).2.1) = (ss.filter p, (ss.filter p).map f) := by
  have h1 : e.1 = ss := congrArg Prod.fst h
  have h2 : e.2.1 = ss.map f := congrArg Prod.snd h
  simp only [filterExpand, h1, h2, zip_filter_map, Array.map_map, Function.comp_def]
  simp

/-- The fused expansion derived pointwise from the two callbacks: coherent by definition, but it does the per-source
work once per edge, so it is only for callers whose `succs`/`edgeMarks` are cheap. -/
@[expose] def derivedExpand {State : Type u} (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (optBits : Option (State → State → Nat) := none) :
    State → Array State × Array (Std.HashSet Nat) × Array Nat :=
  -- `none` means "this caller has no options", and then the third array is empty rather than a run of
  -- zeros: no allocation on the routes that never run the option scan.
  fun s =>
    let ss := succs s
    (ss, ss.map (edgeMarks s), match optBits with | none => #[] | some f => ss.map (f s))

/-- A pointwise-derived expansion is coherent, with `derivedExpand`'s own `optBits` default carried over. -/
theorem derivedExpand_coherent {State : Type u} (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (optBits : Option (State → State → Nat) := none) :
    ExpandCoherent succs edgeMarks (derivedExpand succs edgeMarks optBits) := fun _ => rfl

/-- The fused successors are the plain ones. -/
theorem ExpandCoherent.fst {State : Type u} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat}
    {expand : State → Array State × Array (Std.HashSet Nat) × Array Nat}
    (h : ExpandCoherent succs edgeMarks expand)
    (s : State) : (expand s).1 = succs s := congrArg Prod.fst (h s)

/-- The fused marks are the pointwise ones. -/
theorem ExpandCoherent.snd {State : Type u} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat}
    {expand : State → Array State × Array (Std.HashSet Nat) × Array Nat}
    (h : ExpandCoherent succs edgeMarks expand)
    (s : State) : (expand s).2.1 = (succs s).map (edgeMarks s) := congrArg Prod.snd (h s)

/-- Reading one cached mark back: entry `i` of a coherent frame's cache is that edge's `edgeMarks`. -/
theorem ExpandCoherent.getElem {State : Type u} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat}
    {expand : State → Array State × Array (Std.HashSet Nat) × Array Nat}
    (h : ExpandCoherent succs edgeMarks expand)
    (s : State) {i : Nat} (hi : i < (succs s).size) :
    (expand s).2.1[i]! = edgeMarks s (succs s)[i] := by
  rw [h.snd s, getElem!_pos _ i (by simpa using hi), Array.getElem_map]

/-- Bare existence certificate: only finitely many states are canonically reachable (some list contains all of
    them). No witness must be provided. -/
@[expose] def FiniteReach {State : Type u} (initialStates : List State)
    (succs : State → Array State) : Prop :=
  FinitePred (Reachable initialStates succs)

/-- A list containing every state makes any graph over them finite-reach. -/
theorem FiniteReach.of_forall_mem {State : Type u} {initialStates : List State} {succs : State → Array State}
    (l : List State) (h : ∀ s, s ∈ l) : FiniteReach initialStates succs :=
  FinitePred.of_forall_mem l h

/-- Pigeonhole on an infinite sampling of a run: only finitely many states are reachable, so two distinct
sample points carry the same state. The step every pumping lemma opens with, `f` need not be injective. -/
theorem FiniteReach.exists_lt_sample_eq {State : Type u} {initialStates : List State}
    {succs : State → Array State} (fr : FiniteReach initialStates succs) {σ : Nat → State}
    (hmem : ∀ n, Reachable initialStates succs (σ n)) (f : Nat → Nat) :
    ∃ i j, i < j ∧ σ (f i) = σ (f j) :=
  FinitePred.exists_lt_eq fr (σ := fun k => σ (f k)) fun k => hmem (f k)

/-- Termination measure: the reachable states satisfying `q`, counted along a fixed list covering the reachable
states (a state may count more than once, only monotonicity matters). `0` without `FiniteReach`, like the
cardinality of an infinite set. -/
@[expose] noncomputable def reachCount {State : Type u} (initialStates : List State) (succs : State → Array State)
    (q : State → Prop) : Nat :=
  open Classical in
  if h : FiniteReach initialStates succs then
    (Classical.choose h).countP fun s => decide (Reachable initialStates succs s ∧ q s)
  else 0

section ReachCount

variable {State : Type u} {initialStates : List State} {succs : State → Array State}

open Classical in
/-- Weakening the property (on reachable states) cannot decrease the count. -/
theorem reachCount_le {q q' : State → Prop} (h : ∀ s, Reachable initialStates succs s → q s → q' s) :
    reachCount initialStates succs q ≤ reachCount initialStates succs q' := by
  by_cases fr : FiniteReach initialStates succs
  · simp only [reachCount, dite_eq_left fr]
    exact List.countP_mono_left fun s _ hs => by
      simp only [decide_eq_true_eq] at hs ⊢
      exact ⟨hs.1, h s hs.1 hs.2⟩
  · simp only [reachCount, dite_eq_right fr, Nat.le_refl]

open Classical in
/-- Weakening the property strictly increases the count once some reachable state gains it. -/
theorem reachCount_lt (fr : FiniteReach initialStates succs) {q q' : State → Prop}
    (h : ∀ s, Reachable initialStates succs s → q s → q' s) {x : State}
    (hx : Reachable initialStates succs x) (hq : ¬ q x) (hq' : q' x) :
    reachCount initialStates succs q < reachCount initialStates succs q' := by
  simp only [reachCount, dite_eq_left fr]
  refine Lasso.List.countP_lt_countP (fun s _ hs => ?_) (Classical.choose_spec fr x hx) ?_ ?_
  · simp only [decide_eq_true_eq] at hs ⊢
    exact ⟨hs.1, h s hs.1 hs.2⟩
  · simp [hq]
  · simp [hx, hq']

/-- Properties agreeing on the reachable states have the same count. -/
theorem reachCount_congr {q q' : State → Prop} (h : ∀ s, Reachable initialStates succs s → (q s ↔ q' s)) :
    reachCount initialStates succs q = reachCount initialStates succs q' :=
  Nat.le_antisymm (reachCount_le fun s hs hq => (h s hs).mp hq) (reachCount_le fun s hs hq => (h s hs).mpr hq)

end ReachCount

/-! ## Totalized successors -/

/-- Wraps a successor function so a terminal state gets a self-loop instead, giving every state
a total transition relation, as required by Büchi semantics over infinite words. -/
@[expose] def totalizeSucc {State : Type u} (succs : State → Array State) : State → Array State :=
  fun s =>
    let ss := succs s
    if ss.isEmpty then #[s] else ss

/-- A state reachable through the totalized successors was already reachable through the original ones. -/
theorem reachable_totalizeSucc_imp {State : Type u} (initialStates : List State)
    (succs : State → Array State) :
    ∀ {s : State}, Reachable initialStates (totalizeSucc succs) s →
      Reachable initialStates succs s := by
  intro s hs
  induction hs with
  | base hi => exact .base hi
  | step _ hmem ih =>
    rename_i s t
    dsimp only [totalizeSucc] at hmem
    split at hmem
    · exact (Array.mem_singleton.mp hmem) ▸ ih
    · exact .step ih hmem

/-- Totalizing adds no reachable state, so the caller's finiteness certificate carries over. -/
theorem finiteReach_totalizeSucc {State : Type u} (initialStates : List State)
    (succs : State → Array State) (fr : FiniteReach initialStates succs) :
    FiniteReach initialStates (totalizeSucc succs) :=
  fr.subset (fun _ hs => reachable_totalizeSucc_imp initialStates succs hs)

end Lasso
