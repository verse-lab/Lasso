/-
  Proof-level tests, checked at elaboration time: the correctness theorems are usable on concrete inputs, and nothing in
  the pipeline leaks an axiom.
  - `dijkstraTChecker.check` is definitionally `dijkstraCheck`.
  - Both top-level theorem pairs apply to a concrete system given only its `FiniteReach`.
  - `exists_TAcceptingCycle_of_run` still produces a non-empty cycle at `numMarks = 0`, where the marks hypothesis is vacuous.

  Sections:
  - The checker instance
  - Applying the top-level theorems
  - The zero-marks corner of the pumping lemma
  - Axioms
-/
import LTLLib.TGBABased.DijkstraCheck
import LTLLib.TGBABased.ModelCheck
import LTLLib.TGBABased.Satisfiability
import LTLLib.TGBABased.Tests.ModelCheckCounterExample

namespace LTLLib.Tests.PipelineTheorems

open LTLLib LTLLib.Tests LTLLib.Tests.ModelCheckCounterExample

/-! ## The checker instance -/

example {State : Type u} [BEq State] [Hashable State] [LawfulBEq State] [LawfulHashable State]
    [Inhabited State] (succs : State → Array State) (init : List State) (fr : FiniteReach init succs)
    (em : State → State → Std.HashSet Nat) (nm : Nat) :
    (dijkstraTChecker (State := State)).check succs init fr em nm = dijkstraCheck succs init em nm := rfl

/-! ## Applying the top-level theorems -/

/-- Model checking the traffic light yields a verified answer either way, given only `lightFR`. -/
theorem light_checked :
    (∀ τ : Nat → Light, (Sys.toSpec lightSucc lightInit lightLabel).isRun τ →
      Formula.directSatisfies (fun i a => a ∈ lightLabel (τ i)) ψ) ∨
    (∃ τ : Nat → Light, (Sys.toSpec lightSucc lightInit lightLabel).isRun τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ lightLabel (τ i)) ψ) := by
  cases h : modelCheckTGBA ψ lightInit lightSucc lightLabel lightFR with
  | empty n => exact Or.inl (modelCheckTGBA_empty_unsat ψ lightInit lightSucc lightLabel lightFR _ h)
  | nonEmpty stem loop =>
    exact Or.inr (modelCheckTGBA_nonEmpty_sat ψ lightInit lightSucc lightLabel lightFR _ h)

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

#print axioms modelCheckTGBA_empty_unsat
#print axioms modelCheckTGBA_nonEmpty_sat
#print axioms modelCheckNDFS_empty_unsat
#print axioms modelCheckNDFS_nonEmpty_sat
#print axioms modelCheckDijkstra_empty_unsat
#print axioms modelCheckDijkstra_nonEmpty_sat
#print axioms modelCheckFairDirect_empty_unsat
#print axioms modelCheckFairDirect_nonEmpty_sat
#print axioms modelCheckFairFNFCross_empty_unsat
#print axioms modelCheckFairFNFCross_nonEmpty_sat
#print axioms modelCheckFairFNFPrune_empty_unsat
#print axioms modelCheckFairFNFPrune_nonEmpty_sat
#print axioms modelCheckFair_empty_unsat
#print axioms modelCheckFair_nonEmpty_sat
#print axioms tgbaPipeline_empty_unsat
#print axioms tgbaPipeline_nonEmpty_sat
#print axioms dijkstraTChecker
#print axioms exists_TAcceptingCycle_of_run
#print axioms light_checked

end LTLLib.Tests.PipelineTheorems
