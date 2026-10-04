module

/-
  Differential tests of `ConcreteVWAA.build` against `Lasso.evalNNF`, checking the id bookkeeping (`SubformulaTable`,
  mask targets, the renumbering to reachable states) rather than `NNF.rtrans` itself.

  Sections:
  - Table round trip
  - One-step expansion by id
-/
import LTLLibTests.TGBABased.LTLtoTGBA.Eval
import LTLLibTests.TGBABased.LTLtoTGBA.Gen
import LTLLib.TGBABased.LTLtoTGBA.VWAA
import LTLLibTests.TGBABased.TestUtil
meta import LTLLibTests.TGBABased.LTLtoTGBA.Eval
meta import LTLLibTests.TGBABased.LTLtoTGBA.Gen
meta import LTLLib.TGBABased.LTLtoTGBA.VWAA
meta import LTLLibTests.TGBABased.TestUtil

namespace LTLLib.LTLtoTGBA.Tests.ConcreteVWAATests

open LTLLib LTLLib.Tests LTLLib.LTLtoTGBA.Tests

private def genFormulas (seed trials fuel : Nat) : List (NNF String) :=
  go trials (mkStdGen seed)
where go : Nat → StdGen → List (NNF String)
  | 0, _ => []
  | n + 1, g => let (φ, g') := genFormula props fuel g; φ :: go n g'

private def formulas : List (NNF String) := genFormulas 271828 200 8

/-! ## Table round trip -/

private def roundTrips (φ : NNF String) : Bool :=
  let t := SubformulaTable.build φ
  t.formulaOf (t.idOf φ) == φ

/-! ## One-step expansion by id -/

private def genCases (seed trials : Nat) : List (NNF String × Lasso String × Nat) :=
  go trials (mkStdGen seed)
where go : Nat → StdGen → List (NNF String × Lasso String × Nat)
  | 0, _ => []
  | n + 1, g =>
    let (φ, g1) := genFormula props 8 g
    let (l, g2) := genLasso props 6 5 g1
    let (i, g3) := randNat g2 0 (l.size - 1)
    (φ, l, i) :: go n g3

private def cases : List (NNF String × Lasso String × Nat) := genCases 141421 400

private def idExpansionHolds (l : Lasso String) (cv : ConcreteVWAA String) (i : Nat) : Bool :=
  (cv.trans.getD cv.initial []).any fun (g, t) =>
    DNF.eval g (l.wordAt i) && (maskMembers t).all fun tid => (l.evalNNF (cv.table.formulaOf tid)).getD (l.next i) false

def report : IO Unit :=
  verdict "ConcreteVWAA.build against Lasso.evalNNF" do
    let a ← check "every formula round-trips through its subformula table" (formulas.all roundTrips)
    let b ← check "initial is a valid id into the table"
      (formulas.all fun φ => (SubformulaTable.build φ).idOf φ < (SubformulaTable.build φ).formulas.size)
    let c ← check "the id-indexed one-step expansion agrees with the evaluator at every position"
      (cases.all fun (φ, l, i) => (l.evalNNF φ).getD i false == idExpansionHolds l (ConcreteVWAA.build φ) i)
    return [a, b, c]

#eval report

end LTLLib.LTLtoTGBA.Tests.ConcreteVWAATests
