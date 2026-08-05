/-
  End-to-end pipeline: LTL formula φ → satisfiability decision.

  Track B, item 4 (`ProofPlan.md`): chains `createGraph → constructGBA →
  GBA.degeneralize → nestedDFSWF` into a single total function, and proves
  its correctness. Assembles items 1-3 (`GBA.WellFormed`/`BA.WellFormed`/
  `FiniteReach`, the `AcceptingCycle` → `ValidLasso` wiring, and
  `canonicalLabel` compatibility) plus the pumping lemma
  (`exists_acceptingCycle_of_run`, `NestedDFS/NestedDFSTermination.lean`) into a
  genuinely usable decision procedure — no new mathematical content beyond
  the wiring itself.

  Corresponds to CAVA's `CAVA_Abstract.thy`'s `abs_model_check`, minus the
  `inter_spec`/system-intersection stage (this project checks `φ`'s own
  realizability directly, not model checking against a system) — closer to
  `create_name_gba_correct` combined with a `find_ce_spec`-shaped oracle.
-/
import LTLLib.LTLtoGBA.GraphComplete
import LTLLib.DegeneralBridge
import LTLLib.LTLtoGBA.ExpandTermination
import LTLLib.NestedDFS.NestedDFSTermination
import LTLLib.OutputVerifyBA

namespace LTLLib

variable {α : Type u} {S : Type v} [FSet (NNF α) S]
  [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α]

/-- Chain `createGraph → constructGBA → GBA.degeneralize → nestedDFSWF` into
a single total decision procedure for `φ`'s satisfiability. `createGraph`'s
`none` branch is defensive dead code — `createGraph_term` guarantees success
for every `φ`; a genuine `Option` pattern match still needs *some* value
there, matching the "junk value on unreachable input" pattern already used
throughout Phase 2's termination work. -/
def fullPipeline (φ : NNF α) : EmptinessResult BAState :=
  match hcg : createGraph (S := S) φ with
  | some st =>
    let gba := constructGBA φ st
    let ba := gba.degeneralize
    let hbawf := degeneralize_wellFormed_any gba (constructGBA_wellFormed hcg)
    nestedDFSWF ba.getSuccessors (ba.finiteReach hbawf) ba.isAccepting ba.initialStates.toList
  | none => .empty 0

omit [LawfulBEq α] [LawfulHashable α] [DecidableEq α] in
/-- Unfolding lemma: `fullPipeline` at a known `createGraph` result. -/
theorem fullPipeline_eq (φ : NNF α) {st : ExpandState α S} (hcg : createGraph φ = some st) :
    fullPipeline (S := S) φ =
      nestedDFSWF (constructGBA φ st).degeneralize.getSuccessors
        ((constructGBA φ st).degeneralize.finiteReach
          (degeneralize_wellFormed_any (constructGBA φ st) (constructGBA_wellFormed hcg)))
        (constructGBA φ st).degeneralize.isAccepting
        (constructGBA φ st).degeneralize.initialStates.toList := by
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
  obtain ⟨ac, _, _⟩ := nestedDFSWF_nonEmpty_valid ba.getSuccessors (ba.finiteReach hbawf)
    ba.isAccepting ba.initialStates.toList stem loop
    (BA.initialStates_subset_finiteReach ba hbawf) h
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
  exact ⟨ξ, (constructGBA_correct_weak hcg ξ).mp
    ((degeneralize_accepts_any gba hwf ξ).mp
      (ac.toValidLasso.accepts_of_validLasso hcompat))⟩

/-- `.empty` case: `fullPipeline` correctly certifies `φ`'s unsatisfiability.
Needs the pumping lemma (`exists_acceptingCycle_of_run`) to bridge from
"some `ξ` satisfies `φ`" (word-level) down to "an `AcceptingCycle` exists"
(graph-level) for the contradiction — the CAVA-`accepted_lasso` step. -/
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
  have hgba_acc : gba.toSpec.accepts ξ := (constructGBA_correct_weak hcg ξ).mpr hξ
  have hba_acc : ba.toSpec.accepts ξ := (degeneralize_accepts_any gba hwf ξ).mpr hgba_acc
  obtain ⟨σ, hrun, _, hacc⟩ := hba_acc
  have hcyc : ∃ _ac : AcceptingCycle ba.initialStates.toList ba.getSuccessors ba.isAccepting, True :=
    exists_acceptingCycle_of_run (ba.finiteReach hbawf)
      (BA.initialStates_subset_finiteReach ba hbawf)
      (Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hrun.1))
      hrun.2
      (fun N => by
        obtain ⟨j, hj⟩ := hacc ⟨0, Nat.one_pos⟩ N
        exact ⟨N + j, by omega, hj⟩)
  exact nestedDFSWF_empty_no_cycle ba.getSuccessors (ba.finiteReach hbawf) ba.isAccepting
    ba.initialStates.toList n (BA.initialStates_subset_finiteReach ba hbawf) h hcyc

end LTLLib
