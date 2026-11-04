module

/-
  Deciding `TAcceptingCycle` on a concrete stem and cycle. Every field of `TAcceptingCycle` is a decidable statement
  about two lists, so a reported witness can be checked rather than trusted, and an emptiness checker that validates
  before reporting is sound whatever its search does.

  Defines:
  - `chainOK`: consecutive elements are real edges
  - `validLasso`: all nine `TAcceptingCycle` fields at once

  Proves:
  - `chainOK_spec`: the indexed reading of `chainOK`
  - `TAcceptingCycle.ofValid`: a passing check is a `TAcceptingCycle`
  - `validLasso_of_TAcceptingCycle`: the converse, every `TAcceptingCycle` passes the check

  Sections:
  - Chains
  - The validator
  - Soundness of the validator
  - Completeness of the validator
-/
public import LTLLib.AbstractSpec.EmptinessCheck

public section

namespace LTLLib

variable {State : Type u} [BEq State] [LawfulBEq State]

/-! ## Chains -/

/-- Every consecutive pair is a real edge. -/
def chainOK (succs : State → Array State) : List State → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (succs a).contains b && chainOK succs (b :: rest)

theorem chainOK_spec {succs : State → Array State} :
    ∀ {l : List State}, chainOK succs l = true →
      ∀ i, (hi : i + 1 < l.length) → l[i + 1] ∈ succs l[i] := by
  intro l
  induction l with
  | nil => intro _ i hi; simp at hi
  | cons a rest ih =>
    cases rest with
    | nil => intro _ i hi; simp at hi
    | cons b rest' =>
      intro h i hi
      rw [chainOK, Bool.and_eq_true] at h
      cases i with
      | zero => simpa using Array.contains_iff_mem.mp h.1
      | succ j =>
        have := ih h.2 j (by simp only [List.length_cons] at hi ⊢; omega)
        simpa using this

/-! ## The validator -/

/-- The marks carried by the cycle read cyclically, so `(i + 1) % length` covers the closing edge. -/
def cycleCarries [Hashable State] (edgeMarks : State → State → Std.HashSet Nat)
    (cycle : List State) (m : Nat) : Bool :=
  (List.range cycle.length).any fun i =>
    match cycle[i]?, cycle[(i + 1) % cycle.length]? with
    | some a, some b => (edgeMarks a b).contains m
    | _, _ => false

/-- All nine `TAcceptingCycle` fields, decided. -/
@[expose] def validLasso [Hashable State] [Inhabited State] (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat)
    (initialStates : List State) (stem cycle : List State) : Bool :=
  !stem.isEmpty && !cycle.isEmpty &&
  initialStates.contains (stem.head?.getD default) &&
  (stem.getLast?.getD default == cycle.head?.getD default) &&
  (succs (cycle.getLast?.getD default)).contains (cycle.head?.getD default) &&
  chainOK succs stem && chainOK succs cycle &&
  (List.range numMarks).all (cycleCarries edgeMarks cycle)

/-! ## Soundness of the validator -/

omit [LawfulBEq State] in
/-- The eight checks, unpacked. -/
private theorem validLasso_parts [Hashable State] [Inhabited State] {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} {initialStates : List State}
    {stem cycle : List State}
    (h : validLasso succs edgeMarks numMarks initialStates stem cycle = true) :
    stem ≠ [] ∧ cycle ≠ [] ∧
    initialStates.contains (stem.head?.getD default) = true ∧
    (stem.getLast?.getD default == cycle.head?.getD default) = true ∧
    (succs (cycle.getLast?.getD default)).contains (cycle.head?.getD default) = true ∧
    chainOK succs stem = true ∧ chainOK succs cycle = true ∧
    (List.range numMarks).all (cycleCarries edgeMarks cycle) = true := by
  unfold validLasso at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨by simpa using h1, by simpa using h2, h3, h4, h5, h6, h7, h8⟩

/-- A witness that passes the check really is a `TAcceptingCycle`. -/
def TAcceptingCycle.ofValid [Hashable State] [Inhabited State] {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} {initialStates : List State}
    {stem cycle : List State}
    (h : validLasso succs edgeMarks numMarks initialStates stem cycle = true) :
    TAcceptingCycle initialStates succs edgeMarks numMarks where
  stem := stem
  cycle := cycle
  stem_nonempty := List.length_pos_iff.mpr (validLasso_parts h).1
  cycle_nonempty := List.length_pos_iff.mpr (validLasso_parts h).2.1
  stem_head_initial := by
    have hne := (validLasso_parts h).1
    have hc := (validLasso_parts h).2.2.1
    rw [List.head?_eq_some_head hne] at hc
    simpa using List.contains_iff_mem.mp hc
  stem_chain := chainOK_spec (validLasso_parts h).2.2.2.2.2.1
  overlap := by
    have hsne := (validLasso_parts h).1
    have hcne := (validLasso_parts h).2.1
    have hc := (validLasso_parts h).2.2.2.1
    rw [List.getLast?_eq_some_getLast hsne, List.head?_eq_some_head hcne] at hc
    simpa using beq_iff_eq.mp hc
  cycle_chain := chainOK_spec (validLasso_parts h).2.2.2.2.2.2.1
  cycle_back := by
    have hcne := (validLasso_parts h).2.1
    have hc := (validLasso_parts h).2.2.2.2.1
    rw [List.getLast?_eq_some_getLast hcne, List.head?_eq_some_head hcne] at hc
    simpa using Array.contains_iff_mem.mp hc
  cycle_covers_marks := by
    intro m hm
    have hcarry := (List.all_eq_true.mp (validLasso_parts h).2.2.2.2.2.2.2) m (List.mem_range.mpr hm)
    unfold cycleCarries at hcarry
    obtain ⟨i, hi, hedge⟩ := List.any_eq_true.mp hcarry
    have hilt : i < cycle.length := List.mem_range.mp hi
    have hmod : (i + 1) % cycle.length < cycle.length := Nat.mod_lt _ (by omega)
    rw [List.getElem?_eq_getElem hilt, List.getElem?_eq_getElem hmod] at hedge
    exact ⟨i, hilt, Std.HashSet.mem_iff_contains.mpr hedge⟩

@[simp] theorem TAcceptingCycle.ofValid_stem [Hashable State] [Inhabited State]
    {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat}
    {initialStates stem cycle : List State}
    (h : validLasso succs edgeMarks numMarks initialStates stem cycle = true) :
    (TAcceptingCycle.ofValid h).stem = stem := by rfl

@[simp] theorem TAcceptingCycle.ofValid_cycle [Hashable State] [Inhabited State]
    {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat}
    {initialStates stem cycle : List State}
    (h : validLasso succs edgeMarks numMarks initialStates stem cycle = true) :
    (TAcceptingCycle.ofValid h).cycle = cycle := by rfl

/-! ## Completeness of the validator -/

theorem chainOK_of_chain {succs : State → Array State} :
    ∀ {l : List State}, (∀ i, (hi : i + 1 < l.length) → l[i + 1] ∈ succs l[i]) → chainOK succs l = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a rest ih =>
    cases rest with
    | nil => intro _; rfl
    | cons b rest' =>
      intro h
      rw [chainOK, Bool.and_eq_true]
      exact ⟨Array.contains_iff_mem.mpr (by simpa using h 0 (by simp)),
        ih fun i hi => h (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)⟩

/-- A genuine accepting cycle passes the check. -/
theorem validLasso_of_TAcceptingCycle [Hashable State] [Inhabited State] {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} {initialStates : List State}
    (ac : TAcceptingCycle initialStates succs edgeMarks numMarks) :
    validLasso succs edgeMarks numMarks initialStates ac.stem ac.cycle = true := by
  have hsne : ac.stem ≠ [] := List.ne_nil_of_length_pos (by have := ac.stem_nonempty; omega)
  have hcne : ac.cycle ≠ [] := List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)
  unfold validLasso
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨by simpa using hsne, by simpa using hcne⟩, ?_⟩, ?_⟩, ?_⟩, chainOK_of_chain ac.stem_chain⟩,
    chainOK_of_chain ac.cycle_chain⟩, ?_⟩
  · rw [List.head?_eq_some_head hsne]
    exact List.contains_iff_mem.mpr ac.stem_head_initial
  · rw [List.getLast?_eq_some_getLast hsne, List.head?_eq_some_head hcne]
    exact beq_iff_eq.mpr ac.overlap
  · rw [List.getLast?_eq_some_getLast hcne, List.head?_eq_some_head hcne]
    exact Array.contains_iff_mem.mpr ac.cycle_back
  · refine List.all_eq_true.mpr fun m hm => ?_
    obtain ⟨i, hi, hmem⟩ := ac.cycle_covers_marks m (List.mem_range.mp hm)
    unfold cycleCarries
    refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
    have hmod : (i + 1) % ac.cycle.length < ac.cycle.length := Nat.mod_lt _ (by omega)
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hmod]
    exact Std.HashSet.mem_iff_contains.mp hmem

end LTLLib
