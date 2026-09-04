/-
  End-to-end satisfiability: LTL formula φ → is φ satisfiable? Chains
  `createGraph → constructGBA → GBA.toTGBA → dijkstraCheck`, landing directly in a `Nat` state space with no
  degeneralization product.

  Defines:
  - `tgbaPipeline`: the decision procedure itself
  - `tgbaPipeline_eq`: unfolds it once `createGraph` is known to succeed
  - `tgbaPipeline_nonEmpty_sat`:  a `.nonEmpty` result yields a concrete `ξ` satisfying `φ`
  - `tgbaPipeline_empty_unsat`:   an `.empty` result certifies `φ` unsatisfiable

  Sections:
  - The pipeline
  - Checker obligations
  - Satisfiability
  - Unsatisfiability
-/
import LTLLib.LTL.Semantics
import LTLLib.LTLtoGBA.Bridge
import LTLLib.LTLtoGBA.Completeness
import LTLLib.LTLtoGBA.Correctness
import LTLLib.LTLtoGBA.ExpandTermination
import LTLLib.TGBA
import LTLLib.TGBABased.LTLtoTGBA.GBAToTGBA
import LTLLib.TGBABased.SCC.DijkstraSCC

namespace LTLLib

variable {α : Type u} {S : Type v} [FSet (NNF α) S]
  [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α]

/-! ## The pipeline -/

/-- Decide `φ`'s satisfiability. The `none` branch is defensive dead code, `createGraph_term` guarantees success. -/
def tgbaPipeline (φ : NNF α) : EmptinessResult Nat :=
  match createGraph (S := S) φ with
  | some st =>
    let tgba := (constructGBA φ st).toTGBA
    dijkstraCheck tgba.succStates tgba.initialStates.toList tgba.cachedEdgeMarks tgba.numAcceptSets
  | none => .empty 0

omit [LawfulBEq α] [LawfulHashable α] [DecidableEq α] in
theorem tgbaPipeline_eq (φ : NNF α) {st : ExpandState α S} (hcg : createGraph φ = some st) :
    tgbaPipeline (S := S) φ =
      dijkstraCheck (constructGBA φ st).toTGBA.succStates
        (constructGBA φ st).toTGBA.initialStates.toList
        (constructGBA φ st).toTGBA.cachedEdgeMarks
        (constructGBA φ st).toTGBA.numAcceptSets := by
  unfold tgbaPipeline
  split
  next st' hcg' =>
    obtain rfl : st' = st := Option.some.inj (hcg'.symm.trans hcg)
    rfl
  next hcg' => exact absurd (hcg'.symm.trans hcg) (by simp)

/-! ## Checker obligations

The pipeline runs on `cachedEdgeMarks`, everything downstream is stated over `edgeMarks`, and
`cachedEdgeMarks_contains_iff` is what moves between them.
-/

omit [LawfulBEq α] [LawfulHashable α] [DecidableEq α] in
private theorem cached_iff_edgeMarks (tgba : TGBA α) (q q' m : Nat) :
    m ∈ tgba.cachedEdgeMarks q q' ↔ m ∈ tgba.edgeMarks q q' := by
  simp only [Std.HashSet.mem_iff_contains]
  exact tgba.cachedEdgeMarks_contains_iff q q' m

omit [LawfulBEq α] [LawfulHashable α] [DecidableEq α] in
private theorem cached_marksBound (gba : GBA α) (q q' m : Nat)
    (hm : m ∈ gba.toTGBA.cachedEdgeMarks q q') : m < gba.toTGBA.numAcceptSets :=
  TGBA.edgeMarks_lt _ (GBA.toTGBA_marks_lt gba) q q' m ((cached_iff_edgeMarks _ q q' m).mp hm)

/-! ## Satisfiability -/

/-- `.nonEmpty` case: `tgbaPipeline` reports a genuine `ξ` satisfying `φ`. -/
theorem tgbaPipeline_nonEmpty_sat (φ : NNF α) {stem loop : List Nat}
    (h : tgbaPipeline (S := S) φ = .nonEmpty stem loop) :
    ∃ ξ : OmegaWord α, NNF.satisfies ξ φ := by
  obtain ⟨st, hcg, _⟩ := createGraph_term (S := S) φ
  rw [tgbaPipeline_eq φ hcg] at h
  have htwf := GBA.toTGBA_wellFormed (constructGBA φ st) (constructGBA_wellFormed hcg)
  obtain ⟨ac0, -, -⟩ := dijkstraCheck_nonEmpty_valid (constructGBA φ st).toTGBA.numAcceptSets
    (constructGBA φ st).toTGBA.succStates (constructGBA φ st).toTGBA.cachedEdgeMarks
    (constructGBA φ st).toTGBA.initialStates.toList (cached_marksBound _)
    ((constructGBA φ st).toTGBA.finiteReach htwf) h
  set ac := ac0.congr_edgeMarks (fun s t m => cached_iff_edgeMarks _ s t m) with hac
  refine ⟨fun n => canonicalLabel (constructGBA φ st).labeling (ac.toTValidLasso.run n).1,
    (constructGBA_correct hcg _).mp ((GBA.toTGBA_toSpec_accepts _ _).mp
      (ac.toTValidLasso.accepts_of_validLasso (fun n => ?_)))⟩
  -- every run edge is a `tgbaTransitionOf` of its own source, so its label constraint is that source's
  have hv : (ac.toTValidLasso.run n).2 ∈
      (constructGBA φ st).toTGBA.getSuccessors (ac.toTValidLasso.run n).1 :=
    ac.toTValidLasso.run_valid n
  rw [GBA.toTGBA_getSuccessors] at hv
  obtain ⟨q', -, hedge⟩ := Array.mem_map.mp hv
  have hmem := (buildStates_mem_iff (ac.toTValidLasso.run n).1).mp (ac.run_states_mem htwf n).1
  rw [Std.HashMap.contains_eq_isSome_getElem?] at hmem
  obtain ⟨node, hnode⟩ := Option.isSome_iff_exists.mp hmem
  have key := (GBA.tgbaTransitionOf_labelCompat (constructGBA φ st) (ac.toTValidLasso.run n).1 q'
    (canonicalLabel (constructGBA φ st).labeling (ac.toTValidLasso.run n).1)).mpr
    (constructGBA_canonicalLabel_compat φ hcg hnode)
  rw [hedge] at key
  exact key

/-! ## Unsatisfiability -/

/-- `.empty` case: `tgbaPipeline` certifies `φ` unsatisfiable. A satisfying `ξ` would give the TGBA an accepting run. -/
theorem tgbaPipeline_empty_unsat (φ : NNF α) {n : Nat} (h : tgbaPipeline (S := S) φ = .empty n) :
    ∀ ξ : OmegaWord α, ¬ NNF.satisfies ξ φ := by
  intro ξ hξ
  obtain ⟨st, hcg, _⟩ := createGraph_term (S := S) φ
  rw [tgbaPipeline_eq φ hcg] at h
  set gba := constructGBA φ st with hgba
  have htwf := GBA.toTGBA_wellFormed gba (constructGBA_wellFormed hcg)
  obtain ⟨σ, hrun, -, hacc⟩ := (GBA.toTGBA_toSpec_accepts gba ξ).mpr ((constructGBA_correct hcg ξ).mpr hξ)
  obtain ⟨ac, -⟩ := TGBA.exists_TAcceptingCycle_of_acceptingRun gba.toTGBA htwf hrun hacc
  exact dijkstraCheck_empty_no_cycle gba.toTGBA.numAcceptSets gba.toTGBA.succStates
    gba.toTGBA.cachedEdgeMarks gba.toTGBA.initialStates.toList (cached_marksBound gba)
    (gba.toTGBA.finiteReach htwf) h
    ⟨ac.congr_edgeMarks (fun s t m => (cached_iff_edgeMarks gba.toTGBA s t m).symm), trivial⟩

end LTLLib
