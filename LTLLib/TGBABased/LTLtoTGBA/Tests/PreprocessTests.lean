/-
  Differential tests of the preprocessing pass against `Lasso.evalNNF`: `synImpl`'s soundness, `simplify`'s semantic
  preservation including the X/F/G shape rules, and a hand-built example of `rehoist` exposing a fairness conjunct
  nested inside a rewritable shape.

  Sections:
  - Cases
  - synImpl soundness
  - simplify preserves semantics
  - rehoist exposes a nested fairness conjunct
  - X/F/G shape rules
-/
import LTLLib.TGBABased.LTLtoTGBA.Preprocess.Rehoist
import LTLLib.TGBABased.LTLtoTGBA.Tests.Eval
import LTLLib.TGBABased.LTLtoTGBA.Tests.Gen
import LTLLib.TGBABased.Tests.TestUtil

namespace LTLLib.LTLtoTGBA.Tests.PreprocessTests

open LTLLib LTLLib.Tests LTLLib.LTLtoTGBA.Tests

/-! ## Cases -/

private def genFormulas (seed trials fuel : Nat) : List (NNF String) :=
  go trials (mkStdGen seed)
where go : Nat → StdGen → List (NNF String)
  | 0, _ => []
  | n + 1, g => let (φ, g') := genFormula props fuel g; φ :: go n g'

private def baseFormulas : List (NNF String) := genFormulas 31415 60 6

/-- Pairs likely to trigger `synImpl`, so soundness is exercised on genuine positives and not only on random pairs. -/
private def structuredPairs : List (NNF String × NNF String) :=
  (baseFormulas.zip baseFormulas.tail).flatMap fun (x, y) =>
    [(x, x), (NNF.ff, x), (x, NNF.tt), (.and x y, x), (.and x y, y), (x, .or x y), (y, .or x y), (.until y y, y)]

private def genFormulaPairs (seed trials fuel : Nat) : List (NNF String × NNF String) :=
  go trials (mkStdGen seed)
where go : Nat → StdGen → List (NNF String × NNF String)
  | 0, _ => []
  | n + 1, g =>
    let (a, g1) := genFormula props fuel g
    let (b, g2) := genFormula props fuel g1
    (a, b) :: go n g2

private def randomPairs : List (NNF String × NNF String) := genFormulaPairs 271828 200 6

private def implicationCases : List (NNF String × NNF String × Lasso String × Nat) :=
  go (structuredPairs ++ randomPairs) (mkStdGen 161803)
where go : List (NNF String × NNF String) → StdGen → List (NNF String × NNF String × Lasso String × Nat)
  | [], _ => []
  | (a, b) :: rest, g =>
    let (l, g1) := genLasso props 6 5 g
    let (i, g2) := randNat g1 0 (l.size - 1)
    (a, b, l, i) :: go rest g2

private def simplifyCases : List (NNF String × Lasso String × Nat) :=
  go 400 (mkStdGen 555555)
where go : Nat → StdGen → List (NNF String × Lasso String × Nat)
  | 0, _ => []
  | n + 1, g =>
    let (φ, g1) := genFormula props 8 g
    let (l, g2) := genLasso props 6 5 g1
    let (i, g3) := randNat g2 0 (l.size - 1)
    (φ, l, i) :: go n g3

/-! ## synImpl soundness -/

private def synImplSound (a b : NNF String) (l : Lasso String) (i : Nat) : Bool :=
  !synImpl a b || !(l.evalNNF a).getD i false || (l.evalNNF b).getD i false

/-! ## simplify preserves semantics -/

private def simplifyPreserves (φ : NNF String) (l : Lasso String) (i : Nat) : Bool :=
  (l.evalNNF φ).getD i false == (l.evalNNF (simplify φ)).getD i false

/-! ## rehoist exposes a nested fairness conjunct -/

private def a : NNF String := .prop "a"
private def p : NNF String := .prop "p"
private def gfa : NNF String := .release .ff (.until .tt a)  -- G F a, a justice/fairness formula
private def nested : NNF String := .release .ff (.and gfa p)  -- G(GF a ∧ p), fairness only once G distributes

private def rehoistExposesNested : Bool :=
  !nested.isFairness &&  -- not directly hoistable before rewriting
  (rehoist [nested]).1.length == 1 &&  -- one conjunct gets hoisted after simplify exposes it
  (rehoist [nested]).2.length == 1  -- the G p remainder stays kept

/-! ## X/F/G shape rules -/

private def b : NNF String := .prop "b"
private def c : NNF String := .prop "c"
private def F (x : NNF String) : NNF String := .until .tt x
private def G (x : NNF String) : NNF String := .release .ff x
private def X (x : NNF String) : NNF String := .next x

/-- Each shape rule, the input and the normal form `simplify` must reach. -/
private def shapeCases : List (NNF String × NNF String) :=
  [(.or (G (F a)) (G (F b)), G (F (.or a b))),
   (.or (G (F a)) (.or (G (F b)) (G (F c))), G (F (.or a (.or b c)))),  -- C1-shaped, merged in one pass
   (.and (F (G a)) (F (G b)), F (G (.and a b))),
   (.and (X a) (X b), X (.and a b)),
   (.or (X a) (X b), X (.or a b)),
   (.until (X a) (X b), X (.until a b)),
   (.release (X a) (X b), X (.release a b)),
   (F (X a), X (F a)),
   (G (X a), X (G a))]

/-- The shape-rule inputs against random lassos, since the random formulas rarely have these shapes. -/
private def shapeSemanticCases : List (NNF String × Lasso String × Nat) :=
  go (shapeCases.flatMap fun (φ, _) => [φ, φ, φ, φ, φ]) (mkStdGen 424242)
where go : List (NNF String) → StdGen → List (NNF String × Lasso String × Nat)
  | [], _ => []
  | φ :: rest, g =>
    let (l, g1) := genLasso props 6 5 g
    let (i, g2) := randNat g1 0 (l.size - 1)
    (φ, l, i) :: go rest g2

def report : IO Unit :=
  verdict "Preprocess against Lasso.evalNNF" do
    let a ← check "synImpl is sound on structured and random pairs"
      (implicationCases.all fun (a, b, l, i) => synImplSound a b l i)
    let b ← check "simplify preserves the evaluator's verdict at every position"
      (simplifyCases.all fun (φ, l, i) => simplifyPreserves φ l i)
    let c ← check "rehoist exposes a fairness conjunct nested under a rewritable G(_ ∧ _)"
      rehoistExposesNested
    let d ← check "every X/F/G shape rule reaches its normal form"
      (shapeCases.all fun (φ, ψ) => simplify φ == ψ)
    let e ← check "the X/F/G shape rewrites preserve the evaluator's verdict"
      (shapeSemanticCases.all fun (φ, l, i) => simplifyPreserves φ l i)
    return [a, b, c, d, e]

#eval report

end LTLLib.LTLtoTGBA.Tests.PreprocessTests
