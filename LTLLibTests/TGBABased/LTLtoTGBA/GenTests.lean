module

/-
  Sanity checks on the random generators of `Gen.lean`: generated lassos respect their bounds, and a batch
  of generated formulas is visibly varied rather than degenerating to a handful of shapes.

  Sections:
  - Lasso bounds
  - Formula variety
-/
import LTLLibTests.TGBABased.LTLtoTGBA.Gen
import LTLLibTests.TGBABased.TestUtil
meta import LTLLibTests.TGBABased.LTLtoTGBA.Gen
meta import LTLLibTests.TGBABased.TestUtil

namespace LTLLib.LTLtoTGBA.Tests.GenTests

open LTLLib LTLLib.Tests LTLLib.LTLtoTGBA.Tests

/-! ## Lasso bounds -/

private def lassos : List (Lasso String) :=
  (List.range 200).foldl (fun (acc : List (Lasso String) × StdGen) _n =>
    let (l, g') := genLasso props 8 6 acc.2
    (l :: acc.1, g')) ([], mkStdGen 7) |>.1

/-! ## Formula variety -/

private def formulas : List (NNF String) :=
  (List.range 200).foldl (fun (acc : List (NNF String) × StdGen) _n =>
    let (φ, g') := genFormula props 8 acc.2
    (φ :: acc.1, g')) ([], mkStdGen 11) |>.1

private def isTemporal : NNF String → Bool
  | .next _ | .until _ _ | .release _ _ => true
  | .and φ ψ | .or φ ψ => isTemporal φ || isTemporal ψ
  | _ => false

def report : IO Unit :=
  verdict "generator sanity" do
    let a ← check "every stem stays within its bound" (lassos.all fun l => l.stem.size ≤ 8)
    let b ← check "every loop stays within its bound, and nonempty" (lassos.all fun l => 1 ≤ l.loop.size && l.loop.size ≤ 6)
    let c ← check "at least half the formulas contain a temporal operator"
      (100 ≤ (formulas.filter isTemporal).length)
    let d ← check "not every formula is the same" (1 < (formulas.eraseDups).length)
    let e ← check "at least one formula uses every constructor" <|
      let hasNext := formulas.any fun | .next _ => true | _ => false
      let hasUntil := formulas.any fun | .until _ _ => true | _ => false
      let hasRelease := formulas.any fun | .release _ _ => true | _ => false
      let hasAnd := formulas.any fun | .and _ _ => true | _ => false
      let hasOr := formulas.any fun | .or _ _ => true | _ => false
      hasNext && hasUntil && hasRelease && hasAnd && hasOr
    return [a, b, c, d, e]

#eval report

end LTLLib.LTLtoTGBA.Tests.GenTests
