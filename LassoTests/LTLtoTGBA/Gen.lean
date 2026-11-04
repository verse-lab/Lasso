module

/-
  Seeded random generators for NNF formulas and lasso words, for the differential tests of this folder.
  Every generator threads a `StdGen` explicitly, so a failing case is reproducible from its seed alone.

  Defines:
  - `genFormula`: a random NNF formula of bounded size over a set of atoms
  - `genLasso`: a random lasso with a bounded stem and a nonempty bounded loop

  Sections:
  - Formula generation
  - Lasso generation
-/
public import Lasso.LTL.Syntax
public import LassoTests.LTLtoTGBA.Lasso

public section

namespace Lasso.LTLtoTGBA.Tests

/-- A small shared atom set, big enough for genuine overlap between random formulas and lassos. -/
def props : Array String := #["a", "b", "c", "d"]

/-! ## Formula generation -/

/-- A random literal over `props`, `props` assumed nonempty. -/
def genLit (props : Array String) (g : StdGen) : NNF String × StdGen :=
  let (idx, g1) := randNat g 0 (props.size - 1)
  let (posBit, g2) := randBool g1
  (if posBit then .prop (props.getD idx "p") else .nprop (props.getD idx "p"), g2)

/-- A random NNF formula, `fuel` bounding its size, halved at every binary node. Weighted towards the temporal operators
so a small `fuel` still reaches `X`/`U`/`R`, unlike `[BKŘS12]` Appendix A's lbtt weights (atom 50 of 100). -/
def genFormula (props : Array String) : Nat → StdGen → NNF String × StdGen
  | 0, g => genLit props g
  | fuel + 1, g =>
    let (choice, g1) := randNat g 0 99
    if choice < 15 then genLit props g1
    else if choice < 16 then (.tt, g1)
    else if choice < 17 then (.ff, g1)
    else if choice < 29 then
      let (φ, g2) := genFormula props (fuel / 2) g1
      let (ψ, g3) := genFormula props (fuel / 2) g2
      (.and φ ψ, g3)
    else if choice < 41 then
      let (φ, g2) := genFormula props (fuel / 2) g1
      let (ψ, g3) := genFormula props (fuel / 2) g2
      (.or φ ψ, g3)
    else if choice < 56 then
      let (φ, g2) := genFormula props fuel g1
      (.next φ, g2)
    else if choice < 71 then
      let (φ, g2) := genFormula props (fuel / 2) g1
      let (ψ, g3) := genFormula props (fuel / 2) g2
      (.release φ ψ, g3)
    else
      let (φ, g2) := genFormula props (fuel / 2) g1
      let (ψ, g3) := genFormula props (fuel / 2) g2
      (.until φ ψ, g3)

/-! ## Lasso generation -/

/-- A random position label, each atom of `props` included independently with probability `1/2`. -/
def genLabel (props : Array String) (g : StdGen) : Std.HashSet String × StdGen :=
  props.foldl (fun (acc : Std.HashSet String × StdGen) a =>
    let (b, g') := randBool acc.2
    (if b then acc.1.insert a else acc.1, g')) (Std.HashSet.emptyWithCapacity 0, g)

private def genPositions (props : Array String) : Nat → StdGen → Array (Std.HashSet String) × StdGen
  | 0, g => (#[], g)
  | n + 1, g =>
    let (lbl, g1) := genLabel props g
    let (rest, g2) := genPositions props n g1
    (#[lbl] ++ rest, g2)

/-- A random lasso, stem length in `[0, maxStem]` and loop length in `[1, maxLoop]`, `maxLoop ≥ 1`. -/
def genLasso (props : Array String) (maxStem maxLoop : Nat) (g : StdGen) : Lasso String × StdGen :=
  let (stemLen, g1) := randNat g 0 maxStem
  let (loopLen, g2) := randNat g1 1 maxLoop
  let (stemArr, g3) := genPositions props stemLen g2
  let (loopArr, g4) := genPositions props loopLen g3
  ({ stem := stemArr, loop := loopArr }, g4)

end Lasso.LTLtoTGBA.Tests
