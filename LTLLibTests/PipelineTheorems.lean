module

/-
  Proof-level tests, checked at elaboration time: the correctness theorems are usable on concrete inputs, and the
  checked declarations depend only on explicitly allowed axioms.
  - `dijkstraTChecker.check` is definitionally `dijkstraCheck`.
  - Both top-level theorem pairs apply to a concrete system given only its `FiniteReach`.
  - `exists_TAcceptingCycle_of_run` still produces a non-empty cycle at `numMarks = 0`, where the marks hypothesis is vacuous.

  Sections:
  - The checker instance
  - Applying the top-level theorems
  - The zero-marks corner of the pumping lemma
  - Axioms
-/
import LTLLib.DijkstraCheck
import LTLLib.ModelCheck
import LTLLib.Satisfiability
-- This proof test reuses the private traffic-light fixture.
import all LTLLibTests.ModelCheckCounterExample
import LTLLibTests.GuardAxioms

namespace LTLLib.Tests.PipelineTheorems

open LTLLib LTLLib.Tests LTLLib.Tests.ModelCheckCounterExample

/-! ## The checker instance -/

example {State : Type u} [BEq State] [Hashable State] [LawfulBEq State] [LawfulHashable State]
    [Inhabited State] (succs : State → Array State) (init : List State)
    (em : State → State → Std.HashSet Nat) (nm : Nat) :
    (dijkstraTChecker (State := State)).check succs init em (derivedExpand succs em) nm =
      dijkstraCheck succs init em (derivedExpand succs em) nm := rfl

/-! ## Applying the top-level theorems -/

/-- Model checking the traffic light yields a verified answer either way, given only `lightFR`. -/
theorem light_checked :
    (∀ τ : Nat → Light, Sys.IsRun lightSucc lightInit τ →
      Formula.directSatisfies (fun i a => a ∈ lightLabel (τ i)) ψ) ∨
    (∃ τ : Nat → Light, Sys.IsRun lightSucc lightInit τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ lightLabel (τ i)) ψ) := by
  cases h : modelCheckTGBA ψ lightInit (LSys.unlabelled lightSucc) lightLabel with
  | empty n =>
    refine Or.inl (fun τ hτ => ?_)
    simpa only [LSys.valuation_ofRun] using
      modelCheckTGBA_empty_unsat ψ lightInit (LSys.unlabelled lightSucc) lightLabel
        (LSys.finiteReach_unlabelled lightFR) _ h (LSys.ofRun τ) (LSys.toSpec_isRun_ofRun hτ)
  | nonEmpty stem loop =>
    obtain ⟨ρ, hρ, hviolates⟩ :=
      modelCheckTGBA_nonEmpty_sat ψ lightInit (LSys.unlabelled lightSucc) lightLabel
        (LSys.finiteReach_unlabelled lightFR) _ h
    refine Or.inr ⟨fun n => (ρ n).1, LSys.isRun_of_toSpec_unlabelled hρ, ?_⟩
    simpa only [LSys.valuation_unlabelled hρ] using hviolates

/-- Satisfiability of any formula yields a verified answer either way, with nothing to supply. -/
theorem pipeline_checked (φ : NNF String) :
    (∀ ξ : OmegaWord String, ¬ NNF.satisfies ξ φ) ∨ (∃ ξ : OmegaWord String, NNF.satisfies ξ φ) := by
  cases h : tgbaPipeline φ with
  | empty n => exact Or.inl (tgbaPipeline_empty_unsat φ h)
  | nonEmpty stem loop => exact Or.inr (tgbaPipeline_nonEmpty_sat φ h)

/-! ## The zero-marks corner of the pumping lemma -/

/-- At `numMarks = 0` the lemma still produces a non-empty cycle from an infinite run alone. -/
example {State : Type u} {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat}
    {initialStates : List State} (fr : FiniteReach initialStates succs) {σ : Nat → State}
    (hinit : σ 0 ∈ initialStates) (htrans : ∀ n, σ (n + 1) ∈ succs (σ n)) :
    ∃ _ac : TAcceptingCycle initialStates succs edgeMarks 0, True :=
  exists_TAcceptingCycle_of_run fr hinit htrans (fun _ h => absurd h (by omega))

/-! ## Axioms -/

#guard_axioms
  modelCheckTGBA_empty_unsat, modelCheckTGBA_nonEmpty_sat,
  modelCheckNDFS_empty_unsat, modelCheckNDFS_nonEmpty_sat,
  modelCheckDijkstra_empty_unsat, modelCheckDijkstra_nonEmpty_sat,
  modelCheckFairDirect_empty_unsat, modelCheckFairDirect_nonEmpty_sat,
  modelCheckFairFNFCross_empty_unsat, modelCheckFairFNFCross_nonEmpty_sat,
  modelCheckFairFNFPrune_empty_unsat, modelCheckFairFNFPrune_nonEmpty_sat,
  modelCheckFair_empty_unsat, modelCheckFair_nonEmpty_sat,
  tgbaPipeline_empty_unsat, tgbaPipeline_nonEmpty_sat,
  dijkstraTChecker, exists_TAcceptingCycle_of_run, light_checked, pipeline_checked
  ⊆ [propext, Classical.choice, Quot.sound]

end LTLLib.Tests.PipelineTheorems
