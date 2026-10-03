module

/-
  End-to-end pipeline for satisfiability:
  LTL formula φ → satisfiability decision.
-/
public import LTLLib.LTLtoGBA.Correctness
public import LTLLib.DegeneralBridge
public import LTLLib.LTLtoGBA.ExpandTermination
public import LTLLib.NestedDFS.NestedDFSTermination
meta import LTLLib.Tactic.Set

public section

namespace LTLLib

variable {α : Type u} {S : Type v} [FSet (NNF α) S]
  [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]

/-- Chain `createGraph → constructGBA → GBA.degeneralize → nestedDFSWF` -/
@[expose] def fullPipeline (φ : NNF α) : EmptinessResult BAState :=
  match hcg : createGraph (S := S) φ with
  | some st =>
    let gba := constructGBA φ st
    let ba := gba.degeneralize
    let hbawf := degeneralize_wellFormed_any gba (constructGBA_wellFormed hcg)
    nestedDFSWF ba.getSuccessors ba.initialStates.toList (ba.finiteReach hbawf) ba.isAccepting
  | none => .empty 0

omit [LawfulBEq α] [LawfulHashable α] in
/-- `fullPipeline` restated with the `createGraph` result exposed as `st`. -/
theorem fullPipeline_eq (φ : NNF α) {st : ExpandState α S} (hcg : createGraph φ = some st) :
    fullPipeline (S := S) φ =
      nestedDFSWF (constructGBA φ st).degeneralize.getSuccessors
        (constructGBA φ st).degeneralize.initialStates.toList
        ((constructGBA φ st).degeneralize.finiteReach
          (degeneralize_wellFormed_any (constructGBA φ st) (constructGBA_wellFormed hcg)))
        (constructGBA φ st).degeneralize.isAccepting := by
  unfold fullPipeline
  split
  next st' hcg' =>
    obtain rfl : st' = st := Option.some.inj (hcg'.symm.trans hcg)
    rfl
  next hcg' => exact absurd (hcg'.symm.trans hcg) (by simp)

/-- `.nonEmpty` case: `fullPipeline` reports a genuine `ξ` satisfying `φ`. -/
theorem fullPipeline_nonEmpty_sat (φ : NNF α) {stem loop : List BAState}
    (h : fullPipeline (S := S) φ = .nonEmpty stem loop) :
    ∃ ξ : OmegaWord α, NNF.satisfies ξ φ := by
  obtain ⟨st, hcg, _⟩ := createGraph_term (S := S) φ
  rw [fullPipeline_eq φ hcg] at h
  set gba := constructGBA φ st with hgba
  set ba := gba.degeneralize with hba
  have hwf := constructGBA_wellFormed hcg
  have hbawf := degeneralize_wellFormed_any gba hwf
  obtain ⟨ac, _, _⟩ := nestedDFSWF_nonEmpty_valid ba.getSuccessors
    (ba.finiteReach hbawf) ba.isAccepting stem loop h
  set ξ : OmegaWord α := fun n => canonicalLabel ba.labeling (ac.toValidLasso.run n).gbaState
    with hξ
  have hcompat : ∀ n, ba.toSpec.labelCompat (ac.toValidLasso.run n) (ξ n) := by
    intro n
    have hm := ac.run_states_mem hbawf n
    have h1 := degeneralize_states_gbaState_mem_any gba (ac.toValidLasso.run n) hm
    have h2 : st.nodes.contains (ac.toValidLasso.run n).gbaState = true := by
      have h1' := h1
      simp only [hgba, constructGBA] at h1'
      exact (buildStates_mem_iff (ac.toValidLasso.run n).gbaState).mp h1'
    rw [Std.HashMap.contains_eq_isSome_getElem?] at h2
    obtain ⟨node, hnode⟩ := Option.isSome_iff_exists.mp h2
    exact degeneralize_canonicalLabel_compat gba (ac.toValidLasso.run n)
      (constructGBA_canonicalLabel_compat φ hcg hnode)
  exact ⟨ξ, (constructGBA_correct hcg ξ).mp
    ((degeneralize_accepts_any gba hwf ξ).mp
      (ac.toValidLasso.accepts_of_validLasso hcompat))⟩

/-- `.empty` case: `fullPipeline` correctly certifies `φ`'s unsatisfiability. -/
theorem fullPipeline_empty_unsat (φ : NNF α) {n : Nat}
    (h : fullPipeline (S := S) φ = .empty n) :
    ∀ ξ : OmegaWord α, ¬ NNF.satisfies ξ φ := by
  intro ξ hξ
  obtain ⟨st, hcg, _⟩ := createGraph_term (S := S) φ
  rw [fullPipeline_eq φ hcg] at h
  set gba := constructGBA φ st with hgba
  set ba := gba.degeneralize with hba
  have hwf := constructGBA_wellFormed hcg
  have hbawf := degeneralize_wellFormed_any gba hwf
  have hgba_acc : gba.toSpec.accepts ξ := (constructGBA_correct hcg ξ).mpr hξ
  have hba_acc : ba.toSpec.accepts ξ := (degeneralize_accepts_any gba hwf ξ).mpr hgba_acc
  obtain ⟨σ, hrun, _, hacc⟩ := hba_acc
  have hcyc : ∃ _ac : AcceptingCycle ba.initialStates.toList ba.getSuccessors ba.isAccepting, True :=
    -- Need pumping lemma to bridge "some `ξ` satisfies `φ`" (word level) to "an `AcceptingCycle` exists" (graph level)
    exists_acceptingCycle_of_run (ba.finiteReach hbawf)
      (Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hrun.1))
      hrun.2
      (fun N => by
        obtain ⟨j, hj⟩ := hacc ⟨0, Nat.one_pos⟩ N
        exact ⟨N + j, by omega, hj⟩)
  exact nestedDFSWF_empty_no_cycle ba.getSuccessors (ba.finiteReach hbawf)
    ba.isAccepting n h hcyc

end LTLLib
