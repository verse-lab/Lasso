/-
  Differential tests of the fairness preprocessing against `Lasso.evalNNF`: `rehoist` exposing nested fairness conjuncts,
  the combinations of sides `branches` enumerates, and `modelCheckUnderFairnessDisjunctiveHoist` on random negated
  properties with mixed conjuncts. A lasso read as a one-run system makes the route's verdict comparable with the
  evaluator's.

  Sections:
  - Formulas
  - Re-hoisting
  - Combinations
  - The route on lassos
-/
import LTLLib.TGBABased.Fairness.DisjunctiveHoist
import LTLLib.TGBABased.Fairness.FairPipeline
import LTLLib.TGBABased.Fairness.Rehoist
import LTLLib.TGBABased.LTLtoTGBA.Tests.Eval
import LTLLib.TGBABased.LTLtoTGBA.Tests.Gen
import LTLLib.TGBABased.Tests.TestUtil

namespace LTLLib.Tests.FairPreprocess

open LTLLib LTLLib.Tests LTLLib.LTLtoTGBA.Tests

/-! ## Formulas -/

private def a : NNF String := .prop "a"
private def b : NNF String := .prop "b"
private def p : NNF String := .prop "p"
private def q : NNF String := .prop "q"
private def notP : NNF String := .nprop "p"
private def F (x : NNF String) : NNF String := .until .tt x
private def G (x : NNF String) : NNF String := .release .ff x
private def X (x : NNF String) : NNF String := .next x
private def GF (x : NNF String) : NNF String := G (F x)
private def FG (x : NNF String) : NNF String := F (G x)

/-! ## Re-hoisting -/

-- G(GF a ∧ p), a fairness conjunct only once G distributes over ∧
private def nested : NNF String := G (.and (GF a) p)

-- G(GF a ∧ G(GF b ∧ p) ∧ q), a bare fairness conjunct, one nested inside another G, and a plain conjunct alongside both
private def deepNested : NNF String := G (.and (GF a) (.and (G (.and (GF b) p)) q))

private def rehoistExposesNested : Bool :=
  !nested.isFairness && (rehoist [nested]).1.length == 1 && (rehoist [nested]).2.length == 1

private def rehoistExposesDeep : Bool :=
  (rehoist [deepNested]).1.length == 2 && (rehoist [deepNested]).2.length == 1

/-! ## Combinations -/

/-- A kept conjunct and its number of combinations, two for each shape disjunctive hoisting splits, one otherwise. -/
private def branchCases : List (NNF String × Nat) :=
  [(.or notP (GF a), 2),  -- p → GF a
   (.or (F notP) (GF a), 2),  -- G p → GF a
   (.or (G b) (GF a), 2),  -- G(b ∨ GF a) after simplify
   (.or (F notP) (.or (GF a) (FG b)), 2),  -- two fair disjuncts, one hoisted conjunct
   (.or notP (.and b (GF a)), 1),  -- fairness under ∧ inside ∨, untouched
   (.or notP (GF (.and a (X b))), 1),  -- fairness fnf does not flatten, untouched
   (b, 1)]

private def threeMixed : List (NNF String) := [.or notP (GF a), .or (F notP) (GF b), .or (G b) (FG a)]

/-! ## The route on lassos -/

/-- Negated properties with mixed conjuncts, built from random subformulas `r₁`, `r₂` and fairness over atoms. -/
private def mixedCases : List (NNF String × Lasso String) :=
  go 120 (mkStdGen 8675309)
where go : Nat → StdGen → List (NNF String × Lasso String)
  | 0, _ => []
  | n + 1, g =>
    let (r1, g1) := genFormula props 3 g
    let (r2, g2) := genFormula props 3 g1
    let (k, g3) := randNat g2 0 5
    let (x, g4) := randNat g3 0 (props.size - 1)
    let (y, g5) := randNat g4 0 (props.size - 1)
    let gx := GF (.prop props[x]!)
    let fy := FG (.prop props[y]!)
    let θ : NNF String := match k with
      | 0 => .and (.or r1 gx) (.or r2 fy)
      | 1 => .or r1 (.or gx fy)
      | 2 => .until gx r1
      | 3 => .release fy r1
      | 4 => G (.or r1 gx)
      | _ => .and r2 (.or (F r1) gx)
    let (l, g6) := genLasso props 5 4 g5
    (θ, l) :: go n g6

/-- The negated property `θ` on the lasso as a one-run system: the route answers `empty` iff the lasso violates `θ`. -/
private def routeAgrees (θ : NNF String) (l : Lasso String) : Bool :=
  let φ : Formula String := .not θ.toFormula
  isEmptyResult (modelCheckUnderFairnessDisjunctiveHoist φ [0] (fun i => #[l.next i]) l.wordAt) == !l.holdsNNF θ

private def routesAgree (θ : NNF String) (l : Lasso String) : Bool :=
  let φ : Formula String := .not θ.toFormula
  isEmptyResult (modelCheckUnderFairnessDisjunctiveHoist φ [0] (fun i => #[l.next i]) l.wordAt) ==
    isEmptyResult (modelCheckUnderFairnessRehoistPrune φ [0] (fun i => #[l.next i]) l.wordAt)

def report : IO Unit :=
  verdict "fairness preprocessing against Lasso.evalNNF" do
    let c1 ← check "rehoist exposes a fairness conjunct nested under a rewritable G(_ ∧ _)" rehoistExposesNested
    let c2 ← check "rehoist recovers both fairness conjuncts nested two G-levels deep" rehoistExposesDeep
    let c3 ← check "each example conjunct has its expected number of combinations"
      (branchCases.all fun (c, n) => (branches [c]).length == n)
    let c4 ← check "three mixed conjuncts give eight combinations, the all-hoisted one first"
      ((branches threeMixed).length == 8 && ((branches threeMixed).head?.map (·.2.isEmpty)) == some true)
    let c5 ← check "the route with disjunctive hoisting agrees with the evaluator on lassos"
      (mixedCases.all fun (θ, l) => routeAgrees θ l)
    let c6 ← check "the route with disjunctive hoisting agrees with the route without it"
      (mixedCases.all fun (θ, l) => routesAgree θ l)
    return [c1, c2, c3, c4, c5, c6]

#eval report

end LTLLib.Tests.FairPreprocess
