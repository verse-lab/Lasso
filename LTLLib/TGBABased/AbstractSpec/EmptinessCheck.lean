module

/-
  Transition-marked analogue of `AbstractSpec/EmptinessCheck.lean`'s algorithm-agnostic emptiness contract. Acceptance
  is a set of marks per transition (`edgeMarks`) plus their count (`numMarks`), instead of a single state predicate.

  Defines:
  - `TAcceptingCycle`: a lasso witness whose cycle carries every mark
  - `TEmptinessChecker`: the contract a transition-based emptiness check satisfies

  Sections:
  - Accepting cycle witness
  - Checker contract
-/
public import LTLLib.AbstractSpec.EmptinessCheck

public section

namespace LTLLib

/-! ## Accepting cycle witness -/

/-- A lasso witness for a TGBA: a stem into a cycle where every mark `m < numMarks` is carried by some cycle edge. -/
structure TAcceptingCycle
    (initialStates : List State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat) where
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
  -- Every mark is carried by some cycle edge, `(i + 1) % cycle.length` covering the wraparound edge `cycle_back`.
  cycle_covers_marks : ∀ m, m < numMarks → ∃ (i : Nat) (hi : i < cycle.length),
    m ∈ edgeMarks (cycle[i]) (cycle[(i + 1) % cycle.length]'(Nat.mod_lt _ (by omega)))

/-- Transport along an edge-marks function with the same membership, e.g. a cached one. -/
@[expose] def TAcceptingCycle.congr_edgeMarks {State : Type u} {initialStates : List State}
    {succs : State → Array State} {em em' : State → State → Std.HashSet Nat} {numMarks : Nat}
    (h : ∀ s t m, m ∈ em s t ↔ m ∈ em' s t)
    (ac : TAcceptingCycle initialStates succs em numMarks) :
    TAcceptingCycle initialStates succs em' numMarks :=
  { ac with
    cycle_covers_marks := by
      intro m hm
      obtain ⟨i, hi, hmem⟩ := ac.cycle_covers_marks m hm
      exact ⟨i, hi, (h _ _ m).mp hmem⟩ }

/-- Weaken to the first `n` marks, each carried by `em` wherever `em'` carries it. -/
@[expose] def TAcceptingCycle.restrictMarks {State : Type u} {initialStates : List State}
    {succs : State → Array State} {em em' : State → State → Std.HashSet Nat} {n n' : Nat}
    (hn : n ≤ n') (h : ∀ s t m, m < n → m ∈ em' s t → m ∈ em s t)
    (ac : TAcceptingCycle initialStates succs em' n') :
    TAcceptingCycle initialStates succs em n :=
  { ac with
    cycle_covers_marks := by
      intro m hm
      obtain ⟨i, hi, hmem⟩ := ac.cycle_covers_marks m (by omega)
      exact ⟨i, hi, h _ _ m hm hmem⟩ }

/-! ## Checker contract -/

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-- Contract any transition-based emptiness-check algorithm must satisfy. The two proof fields assume the reachable set
is finite and every mark index stays below `numMarks`, neither of which `check` itself is given. -/
structure TEmptinessChecker (State : Type u) [BEq State] [Hashable State]
    [LawfulBEq State] where
  -- `expand` is the fused `(succs, edgeMarks)` the search actually walks with: one call per state gives its
  -- successors and their marks, so a caller whose per-source cost is high pays it once per state rather
  -- than once per edge. `ExpandCoherent` says it agrees with the two callbacks the spec is stated in terms
  -- of; the proof fields assume it. See `GenericDFS.DFSStep.succMarks`.
  check : (succs : State → Array State) → (initialStates : List State) →
    (edgeMarks : State → State → Std.HashSet Nat) →
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) → (numMarks : Nat) →
    EmptinessResult State
  -- Soundness of `.nonEmpty`: a returned `stem`/`loop` is a `TAcceptingCycle` witness.
  nonEmpty_valid : ∀ {succs : State → Array State} {initialStates : List State}
      {edgeMarks : State → State → Std.HashSet Nat}
      {expand : State → Array State × Array (Std.HashSet Nat) × Array Nat} {numMarks : Nat}
      {stem loop : List State},
    FiniteReach initialStates succs →
    ExpandCoherent succs edgeMarks expand →
    (∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks) →
    check succs initialStates edgeMarks expand numMarks = .nonEmpty stem loop →
    ∃ ac : TAcceptingCycle initialStates succs edgeMarks numMarks,
      ac.stem = stem ∧ ac.cycle = loop.tail
  -- Completeness of `.empty`: no `TAcceptingCycle` exists.
  empty_no_cycle : ∀ {succs : State → Array State} {initialStates : List State}
      {edgeMarks : State → State → Std.HashSet Nat}
      {expand : State → Array State × Array (Std.HashSet Nat) × Array Nat} {numMarks : Nat} {n : Nat},
    FiniteReach initialStates succs →
    ExpandCoherent succs edgeMarks expand →
    (∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks) →
    check succs initialStates edgeMarks expand numMarks = .empty n →
    ¬∃ _ac : TAcceptingCycle initialStates succs edgeMarks numMarks, True

end LTLLib
