/-
  GBA to TGBA conversion, pushing each state's acceptance-set membership and propositional label onto its outgoing
  transitions, states and initial states unchanged. `toTGBA` refines `OASpec.toTOASpec` onto `TGBA.Edge`s, every edge
  `⟨q, gba.tgbaTransitionOf q q'⟩` projecting to the state pair `(q, q')`.

  Defines:
  - `GBA.tgbaTransitionOf`: the transition for the edge `q → q'`, carrying `q`'s label and marks
  - `GBA.toTGBA`: the converted TGBA

  Proves:
  - `GBA.toTGBA_toSpec_accepts`: `gba.toTGBA` accepts exactly the ω-words `gba` accepts
  - `GBA.toTGBA_wellFormed`, `GBA.toTGBA_marks_lt`: well-formedness is preserved and marks stay below `numAcceptSets`

  Sections:
  - Computational conversion
  - Successor characterization
  - Label and acceptance-mark characterization
  - Correctness
-/

import LTLLib.GBA
import LTLLib.TGBA
import LTLLib.TGBABased.AbstractSpec.Acceptance

namespace LTLLib

namespace GBA

variable [BEq α] [Hashable α]

/-! ## Computational conversion -/

/-- The transition `toTGBA` emits for the edge `q → q'`, carrying `q`'s own label and acceptance marks. -/
def tgbaTransitionOf (gba : GBA α) (q q' : Nat) : TGBA.Transition α :=
  let (pos, neg) := gba.labeling[q]?.getD
    (Std.HashSet.emptyWithCapacity 0, Std.HashSet.emptyWithCapacity 0)
  { target := q', positiveProps := pos, negativeProps := neg, acceptMarks := gba.acceptMarksOf q }

/-- Push each state's label and acceptance marks onto its outgoing transitions. -/
def toTGBA (gba : GBA α) : TGBA α where
  states := gba.states
  initialStates := gba.initialStates
  successors := gba.successors.map fun q qsuccs => qsuccs.map (gba.tgbaTransitionOf q)
  numAcceptSets := gba.acceptSets.size

/-! ## Successor characterization -/

theorem toTGBA_getSuccessors (gba : GBA α) (q : Nat) :
    gba.toTGBA.getSuccessors q = (gba.getSuccessors q).map (gba.tgbaTransitionOf q) := by
  simp only [TGBA.getSuccessors, toTGBA, GBA.getSuccessors, Std.HashMap.getElem?_map]
  cases gba.successors[q]? with
  | none => simp
  | some arr => simp

theorem toTGBA_isInitial (gba : GBA α) (q : Nat) : gba.toTGBA.isInitial q = gba.isInitial q := by
  simp [TGBA.isInitial, toTGBA, GBA.isInitial]

/-! ## Label and acceptance-mark characterization -/

private theorem hashSet_foldl_cond_insert_contains
    (l : List Nat) (p : Nat → Bool) (init : Std.HashSet Nat) (q : Nat) :
    (l.foldl (fun acc x => if p x then acc.insert x else acc) init).contains q =
      (init.contains q || l.any (fun x => p x && (x == q))) := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.any_cons]
    split
    · next hp => rw [ih]; simp only [Std.HashSet.contains_insert, hp, Bool.true_and]; ac_rfl
    · next hp => rw [ih]; simp only [Bool.not_eq_true] at hp; simp [hp]

private theorem acceptMarksOf_lt (gba : GBA α) (q m : Nat) (hm : (gba.acceptMarksOf q).contains m) :
    m < gba.acceptSets.size := by
  unfold acceptMarksOf at hm
  rw [hashSet_foldl_cond_insert_contains] at hm
  simp only [Std.HashSet.contains_emptyWithCapacity, Bool.false_or, List.any_eq_true,
    List.mem_range, Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨x, hx, -, rfl⟩ := hm
  exact hx

/-- `toTGBA` preserves well-formedness. -/
theorem toTGBA_wellFormed (gba : GBA α) (hwf : gba.WellFormed) : gba.toTGBA.WellFormed := by
  refine ⟨fun q hq => ?_, fun q t hq ht => ?_, fun q t hq ht m hm => ?_⟩
  · exact hwf.initial_mem q ((toTGBA_isInitial gba q) ▸ hq)
  · rw [toTGBA_getSuccessors] at ht
    obtain ⟨q', hq', rfl⟩ := Array.mem_map.mp ht
    exact hwf.succ_mem q q' hq hq'
  · rw [toTGBA_getSuccessors] at ht
    obtain ⟨q', hq', rfl⟩ := Array.mem_map.mp ht
    exact acceptMarksOf_lt gba q m (Std.HashSet.mem_iff_contains.mp hm)

/-- `toTGBA`'s marks are below `numAcceptSets` at every state, not only inside `states`. -/
theorem toTGBA_marks_lt (gba : GBA α) (q : Nat) (t : TGBA.Transition α)
    (ht : t ∈ gba.toTGBA.getSuccessors q) (m : Nat) (hm : m ∈ t.acceptMarks) :
    m < gba.toTGBA.numAcceptSets := by
  rw [toTGBA_getSuccessors] at ht
  obtain ⟨q', -, rfl⟩ := Array.mem_map.mp ht
  exact acceptMarksOf_lt gba q m (Std.HashSet.mem_iff_contains.mp hm)

private theorem acceptMarksOf_contains (gba : GBA α) (q i : Nat) (hi : i < gba.acceptSets.size) :
    (gba.acceptMarksOf q).contains i = gba.isAccepting i q := by
  unfold acceptMarksOf
  rw [hashSet_foldl_cond_insert_contains]
  simp only [Std.HashSet.contains_emptyWithCapacity, Bool.false_or]
  by_cases hacc : gba.isAccepting i q = true
  · simp only [hacc]
    exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, by simp [hacc]⟩
  · simp only [Bool.not_eq_true] at hacc
    simp only [hacc]
    apply List.any_eq_false.mpr
    rintro x - hcon
    simp only [Bool.and_eq_true, beq_iff_eq] at hcon
    obtain ⟨hxacc, rfl⟩ := hcon
    simp_all

theorem tgbaTransitionOf_labelCompat (gba : GBA α) (q q' : Nat) (v : α → Prop) :
    ((∀ a, (gba.tgbaTransitionOf q q').positiveProps.contains a → v a) ∧
      (∀ a, (gba.tgbaTransitionOf q q').negativeProps.contains a → ¬ v a)) ↔
    gba.toSpec.labelCompat q v := by
  simp only [tgbaTransitionOf, GBA.toSpec]
  cases h : gba.labeling[q]? with
  | none => simp
  | some p => simp

theorem tgbaTransitionOf_acceptMark (gba : GBA α) (q q' : Nat) (i : Fin gba.numAcceptSets) :
    (gba.tgbaTransitionOf q q').acceptMarks.contains i.val ↔ gba.toSpec.acceptSet i q := by
  simp only [tgbaTransitionOf, GBA.toSpec]
  rw [acceptMarksOf_contains gba q i.val i.isLt]

/-! ## Correctness -/

/-- `gba.toTGBA.toSpec` refines `gba.toSpec.toTOASpec` along the target-projection `e ↦ (e.1, e.2.target)`. -/
theorem toTGBA_toSpec_toTOASpec_accepts (gba : GBA α) (ξ : OmegaWord α) :
    gba.toTGBA.toSpec.accepts ξ ↔ gba.toSpec.toTOASpec.accepts ξ := by
  constructor
  · rintro ⟨σ, hrun, hcompat, hacc⟩
    refine ⟨fun n => ((σ n).1, (σ n).2.target), ⟨?_, fun n => ?_⟩, fun n => ?_, fun i n => ?_⟩
    · have hinit : gba.toTGBA.isInitial (σ 0).1 := hrun.1
      rwa [toTGBA_isInitial] at hinit
    · have hvalid : (σ n).2 ∈ gba.toTGBA.getSuccessors (σ n).1 := (hrun.2 n).1
      have hdsteq : (σ n).2.target = (σ (n + 1)).1 := (hrun.2 n).2
      rw [toTGBA_getSuccessors, Array.mem_map] at hvalid
      obtain ⟨q0, hq0, heq⟩ := hvalid
      have htarget : (σ n).2.target = q0 := by simp [← heq, tgbaTransitionOf]
      have hmem : (σ n).2.target ∈ gba.getSuccessors (σ n).1 := by rw [htarget]; exact hq0
      exact ⟨hmem, hdsteq⟩
    · have hcomp : (∀ a, (σ n).2.positiveProps.contains a → ξ n a) ∧
          (∀ a, (σ n).2.negativeProps.contains a → ¬ ξ n a) := hcompat n
      have hvalid : (σ n).2 ∈ gba.toTGBA.getSuccessors (σ n).1 := (hrun.2 n).1
      rw [toTGBA_getSuccessors, Array.mem_map] at hvalid
      obtain ⟨q0, -, heq⟩ := hvalid
      rw [← heq] at hcomp
      exact (tgbaTransitionOf_labelCompat gba (σ n).1 q0 (ξ n)).mp hcomp
    · obtain ⟨j, hj⟩ := hacc i n
      have hmark : (σ (n + j)).2.acceptMarks.contains i.val := hj
      have hvalid : (σ (n + j)).2 ∈ gba.toTGBA.getSuccessors (σ (n + j)).1 := (hrun.2 (n + j)).1
      rw [toTGBA_getSuccessors, Array.mem_map] at hvalid
      obtain ⟨q0, -, heq⟩ := hvalid
      rw [← heq] at hmark
      exact ⟨j, (tgbaTransitionOf_acceptMark gba (σ (n + j)).1 q0 i).mp hmark⟩
  · rintro ⟨σ, hrun, hcompat, hacc⟩
    refine ⟨fun n => ⟨(σ n).1, gba.tgbaTransitionOf (σ n).1 (σ n).2⟩,
      ⟨?_, fun n => ⟨?_, ?_⟩⟩, fun n => ?_, fun i n => ?_⟩
    · have hinit : gba.isInitial (σ 0).1 := hrun.1
      have hinit' : gba.toTGBA.isInitial (σ 0).1 := by rw [toTGBA_isInitial]; exact hinit
      exact hinit'
    · have hvalid : (σ n).2 ∈ gba.getSuccessors (σ n).1 := (hrun.2 n).1
      have hvalid' : gba.tgbaTransitionOf (σ n).1 (σ n).2 ∈ gba.toTGBA.getSuccessors (σ n).1 := by
        rw [toTGBA_getSuccessors]; exact Array.mem_map_of_mem hvalid
      exact hvalid'
    · have hdsteq : (σ n).2 = (σ (n + 1)).1 := (hrun.2 n).2
      show (gba.tgbaTransitionOf (σ n).1 (σ n).2).target = (σ (n + 1)).1
      exact hdsteq
    · have hcomp : gba.toSpec.labelCompat (σ n).1 (ξ n) := hcompat n
      exact (tgbaTransitionOf_labelCompat gba (σ n).1 (σ n).2 (ξ n)).mpr hcomp
    · obtain ⟨j, hj⟩ := hacc i n
      have hacc' : gba.toSpec.acceptSet i (σ (n + j)).1 := hj
      exact ⟨j, (tgbaTransitionOf_acceptMark gba (σ (n + j)).1 (σ (n + j)).2 i).mpr hacc'⟩

/-- `gba.toTGBA` accepts exactly the ω-words `gba` accepts. -/
theorem toTGBA_toSpec_accepts (gba : GBA α) (ξ : OmegaWord α) :
    gba.toTGBA.toSpec.accepts ξ ↔ gba.toSpec.accepts ξ :=
  (toTGBA_toSpec_toTOASpec_accepts gba ξ).trans (OASpec.toTOASpec_accepts gba.toSpec ξ)
