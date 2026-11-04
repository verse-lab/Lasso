module

/-
  The end-to-end differential test: does `ltl3ba φ` accept exactly the lassos `Lasso.evalNNF` says satisfy
  `φ`, for `φ` and for `¬φ`, plus well-formedness of the exported `TGBA`.

  Sections:
  - Cases
  - Well-formedness
  - Membership
-/
import Lasso.LTLtoTGBA.Pipeline
import LassoTests.LTLtoTGBA.Eval
import LassoTests.LTLtoTGBA.Gen
import LassoTests.LTLtoTGBA.TGBAOnLasso
import LassoTests.TestUtil
meta import Lasso.LTLtoTGBA.Pipeline
meta import LassoTests.LTLtoTGBA.Eval
meta import LassoTests.LTLtoTGBA.Gen
meta import LassoTests.LTLtoTGBA.TGBAOnLasso
meta import LassoTests.TestUtil

namespace Lasso.LTLtoTGBA.Tests.PipelineTests

open Lasso Lasso.Tests Lasso.LTLtoTGBA.Tests

/-! ## Cases -/

private def genCases (seed trials : Nat) : List (NNF String × Lasso String) :=
  go trials (mkStdGen seed)
where go : Nat → StdGen → List (NNF String × Lasso String)
  | 0, _ => []
  | n + 1, g =>
    let (φ, g1) := genFormula props 6 g
    let (l, g2) := genLasso props 5 4 g1
    (φ, l) :: go n g2

private def cases : List (NNF String × Lasso String) := genCases 161803 300

/-! ## Well-formedness -/

private def formulas : List (NNF String) := cases.map (·.1)

private def wellFormedCheck (φ : NNF String) : Bool :=
  match ltl3ba φ with
  | none => false
  | some tgba =>
    tgba.initialStates.toList.all tgba.states.contains &&
    tgba.states.toList.all fun q => (tgba.getSuccessors q).all fun t =>
      tgba.states.contains t.target && t.acceptMarks.toList.all (· < tgba.numAcceptSets)

/-! ## Membership -/

private def membershipAgrees (φ : NNF String) (l : Lasso String) : Bool :=
  match ltl3ba φ with
  | none => false
  | some tgba => l.holdsNNF φ == lassoAcceptsTGBA l tgba

def report : IO Unit :=
  verdict "ltl3ba against Lasso.evalNNF" do
    let a ← check "every translation succeeds" (formulas.all fun φ => (ltl3ba φ).isSome)
    let b ← check "every translation is well-formed" (formulas.all wellFormedCheck)
    let c ← check "TGBA membership agrees with the evaluator" (cases.all fun (φ, l) => membershipAgrees φ l)
    let d ← check "TGBA membership agrees with the evaluator on the negation"
      (cases.all fun (φ, l) => membershipAgrees φ.neg l)
    return [a, b, c, d]

#eval report

end Lasso.LTLtoTGBA.Tests.PipelineTests
