/-
  Re-hoisting the kept conjuncts through the rewrite pass. `simplify` is a single-pass normal form for its rules, so one
  `simplify`, `splitConj`, `hoistFairness` sequence finds everything those rules expose, with no repeated rounds.

  Defines:
  - `rehoist`: `hoistFairness` after a `simplify`/`splitConj` pre-pass on the kept conjuncts

  Proves:
  - `rehoist_correct`: the conjuncts hold exactly when the newly hoisted normal forms and the kept conjuncts do

  Sections:
  - Re-hoisting
  - Correctness
-/
import LTLLib.LTL.Semantics
import LTLLib.TGBABased.Fairness.FairRouter
import LTLLib.TGBABased.LTLtoTGBA.Preprocess.Simplify

namespace LTLLib

variable {α : Type u} [BEq α] [DecidableEq α]

/-! ## Re-hoisting -/

/-- Simplify every kept conjunct, re-split at `∧`, and hoist again, catching a fairness conjunct the first hoist missed
because it was still nested under a rewritable shape. -/
def rehoist (cs : List (NNF α)) : List (List (NNF.FairDisjunct α)) × List (NNF α) :=
  hoistFairness (cs.flatMap fun c => (simplify c).splitConj)

/-! ## Correctness -/

/-- The conjuncts hold exactly when every newly hoisted normal form and every newly kept conjunct does. -/
theorem rehoist_correct [LawfulBEq α] (ξ : OmegaWord α) (cs : List (NNF α)) :
    (∀ c ∈ cs, c.satisfies ξ) ↔
      ((∀ ds ∈ (rehoist cs).1, ∃ d ∈ ds, NNF.FairDisjunct.holds ξ d) ∧ ∀ c ∈ (rehoist cs).2, c.satisfies ξ) := by
  unfold rehoist
  rw [← hoistFairness_correct]
  simp only [List.mem_flatMap]
  constructor
  · rintro h c ⟨c0, hc0, hc⟩
    exact (NNF.satisfies_splitConj ξ _).mp ((simplify_correct c0 ξ).mpr (h c0 hc0)) c hc
  · intro h c0 hc0
    exact (simplify_correct c0 ξ).mp ((NNF.satisfies_splitConj ξ _).mpr fun c hc => h c ⟨c0, hc0, hc⟩)

end LTLLib
