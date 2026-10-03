module

/-
  Differential tests of the `DNF` labels of `Label.lean` against brute force, every property checked on random pairs
  of labels at every valuation of a four-atom universe.

  Sections:
  - Brute force ground truth
  - Random DNF labels
  - Checks
-/
import LTLLib.TGBABased.LTLtoTGBA.Label
import LTLLib.TGBABased.LTLtoTGBA.Tests.Gen
import LTLLib.TGBABased.Tests.TestUtil
meta import LTLLib.TGBABased.LTLtoTGBA.Label
meta import LTLLib.TGBABased.LTLtoTGBA.Tests.Gen
meta import LTLLib.TGBABased.Tests.TestUtil

namespace LTLLib.LTLtoTGBA.Tests.LabelTests

open LTLLib LTLLib.Tests LTLLib.LTLtoTGBA.Tests

/-! ## Brute force ground truth -/

/-- Every valuation of `ps`, as the set of atoms it makes true. -/
def allValuations (ps : Array String) : List (Std.HashSet String) :=
  ps.toList.foldl (fun acc a => acc.flatMap fun v => [v, v.insert a]) [Std.HashSet.emptyWithCapacity 0]

/-! ## Random DNF labels -/

private def genDNFLit (g : StdGen) : DNF String × StdGen :=
  let (idx, g1) := randNat g 0 (props.size - 1)
  let (posBit, g2) := randBool g1
  (DNF.lit (props.getD idx "p") posBit, g2)

private def genDNFFormula : Nat → StdGen → DNF String × StdGen
  | 0, g => genDNFLit g
  | fuel + 1, g =>
    let (choice, g1) := randNat g 0 2
    match choice with
    | 0 => genDNFLit g1
    | 1 =>
      let (x, g2) := genDNFFormula (fuel / 2) g1
      let (y, g3) := genDNFFormula (fuel / 2) g2
      (DNF.and x y, g3)
    | _ =>
      let (x, g2) := genDNFFormula (fuel / 2) g1
      let (y, g3) := genDNFFormula (fuel / 2) g2
      (DNF.or x y, g3)

private def genPairs (seed trials fuel : Nat) : List (DNF String × DNF String) :=
  go trials (mkStdGen seed)
where go : Nat → StdGen → List (DNF String × DNF String)
  | 0, _ => []
  | n + 1, g =>
    let (x, g1) := genDNFFormula fuel g
    let (y, g2) := genDNFFormula fuel g1
    (x, y) :: go n g2

/-! ## Checks -/

private def pairs : List (DNF String × DNF String) := genPairs 20260915 300 6

private def vals : List (Std.HashSet String) := allValuations props

private def allPairsVals (p : DNF String → DNF String → Std.HashSet String → Bool) : Bool :=
  pairs.all fun (x, y) => vals.all (p x y)

def report : IO Unit :=
  verdict "DNF labels against brute force" do
    let a ← check "and agrees with pointwise conjunction"
      (allPairsVals fun x y v => DNF.eval (DNF.and x y) v == (DNF.eval x v && DNF.eval y v))
    let b ← check "or agrees with pointwise disjunction"
      (allPairsVals fun x y v => DNF.eval (DNF.or x y) v == (DNF.eval x v || DNF.eval y v))
    let c ← check "diff agrees with pointwise conjunction with the negation"
      (allPairsVals fun x y v => DNF.eval (DNF.diff x y) v == (DNF.eval x v && !DNF.eval y v))
    let d ← check "isEmpty agrees with no valuation satisfying"
      (pairs.all fun (x, _) => DNF.isEmpty x == !vals.any (DNF.eval x ·))
    let e ← check "implies agrees with satisfaction everywhere carrying over"
      (pairs.all fun (x, y) => DNF.implies x y == vals.all fun v => !DNF.eval x v || DNF.eval y v)
    let f ← check "cubes denote the same label as eval, disjoined"
      (pairs.all fun (x, _) => vals.all fun v => DNF.eval x v == (DNF.cubes x).any (Cube.eval · v))
    let g ← check "every exported cube is non-contradictory"
      (pairs.all fun (x, _) => (DNF.cubes x).all fun c => !c.isContradictory)
    let h ← check "top is satisfied everywhere"
      (vals.all (DNF.eval (DNF.top (α := String)) ·))
    let i ← check "bot is satisfied nowhere"
      (! vals.any (DNF.eval (DNF.bot (α := String)) ·))
    let j ← check "a positive literal agrees with membership"
      (vals.all fun v => DNF.eval (DNF.lit "a" true) v == v.contains "a")
    let k ← check "a negative literal agrees with non-membership"
      (vals.all fun v => DNF.eval (DNF.lit "a" false) v == !v.contains "a")
    return [a, b, c, d, e, f, g, h, i, j, k]

#eval report

end LTLLib.LTLtoTGBA.Tests.LabelTests
