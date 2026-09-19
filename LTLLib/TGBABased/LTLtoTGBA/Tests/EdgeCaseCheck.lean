/-
  One-off edge-case sweep against `Lasso.evalNNF`, end to end through `ltl3ba` and separately through `simplify`:
  heavier random trials, `tt`/`ff`-heavy formulas the generator rarely produces, and deeply nested fairness for `rehoist`.
  Not part of the aggregated suite.

  Sections:
  - Heavier random sweep through the whole pipeline
  - Constant-heavy formulas
  - Deeply nested fairness
-/
import LTLLib.TGBABased.LTLtoTGBA.Pipeline
import LTLLib.TGBABased.LTLtoTGBA.Preprocess.Rehoist
import LTLLib.TGBABased.LTLtoTGBA.Tests.Eval
import LTLLib.TGBABased.LTLtoTGBA.Tests.Gen
import LTLLib.TGBABased.LTLtoTGBA.Tests.TGBAOnLasso
import LTLLib.TGBABased.Tests.TestUtil

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

/-! ## Deeply nested fairness -/

private def a : NNF String := .prop "a"
private def b : NNF String := .prop "b"
private def p : NNF String := .prop "p"
private def q : NNF String := .prop "q"
private def gf (x : NNF String) : NNF String := .release .ff (.until .tt x)

-- G(GF a ∧ G(GF b ∧ p) ∧ q): a bare fairness conjunct, one nested inside another G, and a plain conjunct alongside both
private def deepNested : NNF String :=
  .release .ff (.and (gf a) (.and (.release .ff (.and (gf b) p)) q))

private def deepRehoistCases : List Bool :=
  let (hoisted, kept) := rehoist [deepNested]
  [hoisted.length == 2, kept.length == 1]

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
    let e ← check "rehoist recovers both fairness conjuncts nested two G-levels deep" deepRehoistCases.and
    return [a, b, c, d, e]

#eval report

end LTLLib.LTLtoTGBA.Tests.EdgeCaseCheck
