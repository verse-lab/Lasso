/-
  End-to-end satisfiability of an LTL formula. Translates with `ltl3ba` (`LTLtoTGBA/Pipeline.lean`) and runs
  `dijkstraCheck` on the automaton's consistent part, with no degeneralization and no product. The check reads only the
  graph, so the transitions no valuation takes are dropped first (`TGBA.consistentPart`), after which every accepting
  cycle is read by some word.

  Defines:
  - `tgbaPipeline`: the decision procedure

  Proves:
  - `tgbaPipeline_nonEmpty_sat`: a `.nonEmpty` result yields a concrete `ξ` satisfying `φ`
  - `tgbaPipeline_empty_unsat`: an `.empty` result certifies `φ` unsatisfiable

  Sections:
  - The pipeline
  - Checker obligations
  - Satisfiability
  - Unsatisfiability
-/
import LTLLib.LTL.Semantics
import LTLLib.TGBA
import LTLLib.TGBABased.LTLtoTGBA.Pipeline
import LTLLib.TGBABased.SCC.DijkstraSCC

namespace LTLLib

variable {α : Type u} [BEq α] [Hashable α]

/-! ## The pipeline -/

/-- Decide `φ`'s satisfiability. The `none` branch is unreachable by `ltl3ba_isSome`. -/
def tgbaPipeline (φ : NNF α) : EmptinessResult Nat :=
  match ltl3ba φ with
  | some tgba =>
    let c := tgba.consistentPart
    dijkstraCheck c.succStates c.initialStates.toList c.cachedEdgeMarks c.numAcceptSets
  | none => .empty 0

theorem tgbaPipeline_eq (φ : NNF α) {tgba : TGBA α} (htg : ltl3ba φ = some tgba) :
    tgbaPipeline φ =
      dijkstraCheck tgba.consistentPart.succStates tgba.consistentPart.initialStates.toList
        tgba.consistentPart.cachedEdgeMarks tgba.consistentPart.numAcceptSets := by
  unfold tgbaPipeline
  split
  next tgba' htg' =>
    obtain rfl : tgba' = tgba := Option.some.inj (htg'.symm.trans htg)
    rfl
  next htg' => exact absurd (htg'.symm.trans htg) (by simp)

/-! ## Checker obligations -/

private theorem cached_iff_edgeMarks (tgba : TGBA α) (q q' m : Nat) :
    m ∈ tgba.cachedEdgeMarks q q' ↔ m ∈ tgba.edgeMarks q q' := by
  simp only [Std.HashSet.mem_iff_contains]
  exact tgba.cachedEdgeMarks_contains_iff q q' m

variable [LawfulBEq α] [LawfulHashable α]

private theorem cached_marksBound (φ : NNF α) {tgba : TGBA α} (htg : ltl3ba φ = some tgba) (q q' m : Nat)
    (hm : m ∈ tgba.consistentPart.cachedEdgeMarks q q') : m < tgba.consistentPart.numAcceptSets :=
  TGBA.edgeMarks_lt _ (fun q t ht => by
      rw [TGBA.getSuccessors_consistentPart] at ht
      exact ltl3ba_marks_lt φ htg q t (Array.mem_filter.mp ht).1)
    q q' m ((cached_iff_edgeMarks _ q q' m).mp hm)

variable [DecidableEq α]

/-! ## Satisfiability -/

/-- A `.nonEmpty` result yields a `ξ` satisfying `φ`. -/
theorem tgbaPipeline_nonEmpty_sat (φ : NNF α) {stem loop : List Nat} (h : tgbaPipeline φ = .nonEmpty stem loop) :
    ∃ ξ : OmegaWord α, NNF.satisfies ξ φ := by
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome φ)
  rw [tgbaPipeline_eq φ htg] at h
  have hwf := TGBA.consistentPart_wellFormed (ltl3ba_wellFormed φ htg)
  obtain ⟨ac, -, -⟩ := dijkstraCheck_nonEmpty_valid tgba.consistentPart.numAcceptSets
    tgba.consistentPart.succStates tgba.consistentPart.cachedEdgeMarks tgba.consistentPart.initialStates.toList
    (cached_marksBound φ htg) (tgba.consistentPart.finiteReach hwf) h
  obtain ⟨ξ, hacc⟩ := tgba.accepts_of_consistentPart_cycle
    (ac.congr_edgeMarks fun s t m => cached_iff_edgeMarks _ s t m)
  exact ⟨ξ, (ltl3ba_accepts φ htg ξ).mp hacc⟩

/-! ## Unsatisfiability -/

/-- An `.empty` result certifies `φ` unsatisfiable. -/
theorem tgbaPipeline_empty_unsat (φ : NNF α) {n : Nat} (h : tgbaPipeline φ = .empty n) :
    ∀ ξ : OmegaWord α, ¬ NNF.satisfies ξ φ := by
  intro ξ hξ
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome φ)
  rw [tgbaPipeline_eq φ htg] at h
  have hwf := TGBA.consistentPart_wellFormed (ltl3ba_wellFormed φ htg)
  obtain ⟨σ, hrun, -, hacc⟩ := (tgba.consistentPart_accepts ξ).mpr ((ltl3ba_accepts φ htg ξ).mpr hξ)
  obtain ⟨ac, -⟩ := TGBA.exists_TAcceptingCycle_of_acceptingRun _ hwf hrun hacc
  exact dijkstraCheck_empty_no_cycle tgba.consistentPart.numAcceptSets tgba.consistentPart.succStates
    tgba.consistentPart.cachedEdgeMarks tgba.consistentPart.initialStates.toList (cached_marksBound φ htg)
    (tgba.consistentPart.finiteReach hwf) h
    ⟨ac.congr_edgeMarks (fun s t m => (cached_iff_edgeMarks _ s t m).symm), trivial⟩

end LTLLib
