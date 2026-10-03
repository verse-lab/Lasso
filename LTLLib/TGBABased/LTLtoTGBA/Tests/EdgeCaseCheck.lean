module

/-
  One-off edge-case sweep against `Lasso.evalNNF`, end to end through `ltl3ba` and separately through `simplify`:
  heavier random trials, and `tt`/`ff`-heavy formulas the generator rarely produces. Not part of the aggregated suite.

  Sections:
  - Heavier random sweep through the whole pipeline
  - Constant-heavy formulas
-/
import LTLLib.TGBABased.LTLtoTGBA.Pipeline
import LTLLib.TGBABased.LTLtoTGBA.Preprocess.Simplify
import LTLLib.TGBABased.LTLtoTGBA.Tests.Eval
import LTLLib.TGBABased.LTLtoTGBA.Tests.Gen
import LTLLib.TGBABased.LTLtoTGBA.Tests.TGBAOnLasso
import LTLLib.TGBABased.Tests.TestUtil
meta import LTLLib.TGBABased.LTLtoTGBA.Pipeline
meta import LTLLib.TGBABased.LTLtoTGBA.Preprocess.Simplify
meta import LTLLib.TGBABased.LTLtoTGBA.Tests.Eval
meta import LTLLib.TGBABased.LTLtoTGBA.Tests.Gen
meta import LTLLib.TGBABased.LTLtoTGBA.Tests.TGBAOnLasso
meta import LTLLib.TGBABased.Tests.TestUtil

namespace LTLLib.LTLtoTGBA.Tests.EdgeCaseCheck

open LTLLib LTLLib.Tests LTLLib.LTLtoTGBA.Tests

/-! ## Heavier random sweep through the whole pipeline -/

private def genCases (seed trials fuel : Nat) : List (NNF String × Lasso String) :=
  go trials (mkStdGen seed)
where go : Nat → StdGen → List (NNF String × Lasso String)
  | 0, _ => []
  | n + 1, g =>
    let (φ, g1) := genFormula props fuel g
    let (l, g2) := genLasso props 8 6 g1
    (φ, l) :: go n g2

private def heavyCases : List (NNF String × Lasso String) := genCases 999983 3000 12

private def membershipAgrees (φ : NNF String) (l : Lasso String) : Bool :=
  match ltl3ba φ with
  | none => false
  | some tgba => l.holdsNNF φ == lassoAcceptsTGBA l tgba

private def simplifyPreservesAll (φ : NNF String) (l : Lasso String) : Bool :=
  (List.range l.size).all fun i => (l.evalNNF φ).getD i false == (l.evalNNF (simplify φ)).getD i false

/-! ## Constant-heavy formulas -/

private def genConstHeavy (props : Array String) : Nat → StdGen → NNF String × StdGen
  | 0, g => let (b, g') := randBool g; ((if b then .tt else .ff), g')
  | fuel + 1, g =>
    let (choice, g1) := randNat g 0 5
    match choice with
    | 0 => (.tt, g1)
    | 1 => (.ff, g1)
    | 2 => genLit props g1
    | 3 =>
      let (φ, g2) := genConstHeavy props (fuel / 2) g1
      let (ψ, g3) := genConstHeavy props (fuel / 2) g2
      (.and φ ψ, g3)
    | 4 =>
      let (φ, g2) := genConstHeavy props (fuel / 2) g1
      let (ψ, g3) := genConstHeavy props (fuel / 2) g2
      (.or φ ψ, g3)
    | _ =>
      let (φ, g2) := genConstHeavy props (fuel / 2) g1
      let (ψ, g3) := genConstHeavy props (fuel / 2) g2
      (.until φ ψ, g3)

private def constHeavyCases : List (NNF String × Lasso String) :=
  go 500 (mkStdGen 141421)
where go : Nat → StdGen → List (NNF String × Lasso String)
  | 0, _ => []
  | n + 1, g =>
    let (φ, g1) := genConstHeavy props 10 g
    let (l, g2) := genLasso props 6 5 g1
    (φ, l) :: go n g2

def report : IO Unit :=
  verdict "Edge case sweep" do
    let a ← check "ltl3ba agrees with the evaluator on 3000 heavier random cases"
      (heavyCases.all fun (φ, l) => membershipAgrees φ l)
    let b ← check "simplify preserves the evaluator on 3000 heavier random cases, every position"
      (heavyCases.all fun (φ, l) => simplifyPreservesAll φ l)
    let c ← check "ltl3ba agrees with the evaluator on tt/ff-heavy formulas"
      (constHeavyCases.all fun (φ, l) => membershipAgrees φ l)
    let d ← check "simplify preserves the evaluator on tt/ff-heavy formulas"
      (constHeavyCases.all fun (φ, l) => simplifyPreservesAll φ l)
    return [a, b, c, d]

#eval report

end LTLLib.LTLtoTGBA.Tests.EdgeCaseCheck
