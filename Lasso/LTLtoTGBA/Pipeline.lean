module

/-
  The end-to-end LTL to TGBA translator, and a `Formula α` wrapper that translates the negation of its argument,
  following the model-checking convention.

  Defines:
  - `ltl3ba`: `NNF α → Option (TGBA α)`, formula rewriting (`simplify`), VWAA (`ConcreteVWAA.build`),
    TGBA (`buildTGBA`), a posteriori simplification (`simplifyTGBA`)
  - `ltl3baFormula`: `Formula α → Option (TGBA α)`, the automaton of the negated formula

  Proves:
  - `ltl3ba_accepts`: `ltl3ba φ` accepts exactly the models of `φ`
  - `ltl3baFormula_accepts`: `ltl3baFormula φ` accepts exactly the words violating `φ`
  - `ltl3ba_isSome`, `ltl3ba_wellFormed`, `ltl3ba_marks_lt`: the translation always succeeds, with a well-formed TGBA
    whose marks all index an acceptance set

  Sections:
  - Pipeline
  - Correctness
-/
public import Lasso.LTL.Syntax
public import Lasso.LTL.Semantics
public import Lasso.TGBA
public import Lasso.LTLtoTGBA.VWAA
public import Lasso.LTLtoTGBA.TGBAConstruct
public import Lasso.LTLtoTGBA.TGBAConstructCorrect
public import Lasso.LTLtoTGBA.TGBASimplify
public import Lasso.LTLtoTGBA.Preprocess.Simplify

public section

namespace Lasso

variable {α : Type u} [BEq α] [Hashable α]

/-! ## Pipeline -/

/-- Translate an NNF formula to a `TGBA α` accepting exactly its models, rewriting the formula first (as LTL3BA does
while parsing) and simplifying the TGBA last. -/
@[expose] def ltl3ba (φ : NNF α) : Option (TGBA α) :=
  (buildTGBA (ConcreteVWAA.build (simplify φ))).map simplifyTGBA

/-- Translate the negation of a surface `Formula α` to a `TGBA α`. -/
def ltl3baFormula (φ : Formula α) : Option (TGBA α) := ltl3ba (φ.toNNF false)

/-! ## Correctness -/

variable [LawfulBEq α] [LawfulHashable α]

/-- `ltl3ba` always returns a TGBA. -/
theorem ltl3ba_isSome (φ : NNF α) : (ltl3ba φ).isSome := by
  unfold ltl3ba
  cases h : buildTGBA (ConcreteVWAA.build (simplify φ)) with
  | none => exact absurd h (buildTGBA_ne_none (simplify φ))
  | some t => simp

/-- `ltl3ba`'s TGBA is well-formed. -/
theorem ltl3ba_wellFormed (φ : NNF α) {t : TGBA α} (h : ltl3ba φ = some t) : t.WellFormed := by
  obtain ⟨t0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
  exact simplifyTGBA_wellFormed t0 (buildTGBA_wellFormed _ t0 h0)

/-- Every transition of `ltl3ba`'s TGBA, at any state, has its marks below `numAcceptSets`. -/
theorem ltl3ba_marks_lt (φ : NNF α) {t : TGBA α} (h : ltl3ba φ = some t) :
    ∀ q tr, tr ∈ t.getSuccessors q → ∀ m ∈ tr.acceptMarks, m < t.numAcceptSets := by
  obtain ⟨t0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
  exact simplifyTGBA_marks_lt t0 (buildTGBA_wellFormed _ t0 h0) (buildTGBA_marks_lt _ t0 h0)

/-- `ltl3ba φ` accepts exactly the models of `φ`. -/
theorem ltl3ba_accepts [DecidableEq α] (φ : NNF α) {t : TGBA α} (h : ltl3ba φ = some t) (ξ : OmegaWord α) :
    t.toSpec.accepts ξ ↔ φ.satisfies ξ := by
  obtain ⟨t0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (simplifyTGBA_correct t0 (buildTGBA_wellFormed _ t0 h0) ξ).symm.trans
    ((buildTGBA_build_accepts_iff (simplify φ) h0 ξ).trans (simplify_correct φ ξ))

/-- `ltl3baFormula φ` accepts exactly the words violating `φ`. -/
theorem ltl3baFormula_accepts [DecidableEq α] (φ : Formula α) {t : TGBA α} (h : ltl3baFormula φ = some t)
    (ξ : OmegaWord α) : t.toSpec.accepts ξ ↔ ¬ φ.satisfies ξ := by
  rw [ltl3ba_accepts _ h ξ, ← Formula.toNNF_correct_neg, Formula.directSatisfies_eq_satisfies]

end Lasso
