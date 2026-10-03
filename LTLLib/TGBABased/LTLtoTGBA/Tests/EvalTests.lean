module

/-
  Tests `Lasso.holdsNNF` against hand-computed answers, pinning the until/release fixpoint before the other tests of
  this folder trust it as ground truth.

  Sections:
  - Lassos
  - Checks
-/
import LTLLib.TGBABased.LTLtoTGBA.Tests.Eval
import LTLLib.TGBABased.Tests.TestUtil
meta import LTLLib.TGBABased.LTLtoTGBA.Tests.Eval
meta import LTLLib.TGBABased.Tests.TestUtil

namespace LTLLib.LTLtoTGBA.Tests.EvalTests

open LTLLib LTLLib.Tests LTLLib.LTLtoTGBA.Tests NNF

/-! ## Lassos -/

private def hs (l : List String) : Std.HashSet String := Std.HashSet.ofList l

/-- `p` true at every position. -/
private def lAlways : Lasso String := { stem := #[], loop := #[hs ["p"]] }

/-- Position `0` empty, then `p` true forever. -/
private def lDelayed : Lasso String := { stem := #[hs []], loop := #[hs ["p"]] }

/-- `p`, `q` alternating, period `2`. -/
private def lAlternate : Lasso String := { stem := #[], loop := #[hs ["p"], hs ["q"]] }

/-- Nothing ever true. -/
private def lEmpty : Lasso String := { stem := #[], loop := #[hs []] }

/-! ## Checks -/

def report : IO Unit :=
  verdict "Lasso.holdsNNF against hand-computed answers" do
    let a ← check "p holds where it is always true" (lAlways.holdsNNF (.prop "p"))
    let b ← check "¬p fails where p is always true" (! lAlways.holdsNNF (.nprop "p"))
    let c ← check "G p holds where p is always true" (lAlways.holdsNNF (always (.prop "p")))
    let d ← check "F p holds where p is always true" (lAlways.holdsNNF (eventually (.prop "p")))
    let e ← check "p fails at the delayed position" (! lDelayed.holdsNNF (.prop "p"))
    let f ← check "X p holds one step before p starts" (lDelayed.holdsNNF (.next (.prop "p")))
    let g ← check "F p holds even though p is delayed" (lDelayed.holdsNNF (eventually (.prop "p")))
    let h ← check "G p fails at the delayed position" (! lDelayed.holdsNNF (always (.prop "p")))
    let i ← check "G(p ∨ q) holds on the alternating lasso"
      (lAlternate.holdsNNF (always (.or (.prop "p") (.prop "q"))))
    let j ← check "G p fails on the alternating lasso" (! lAlternate.holdsNNF (always (.prop "p")))
    let k ← check "p U q holds on the alternating lasso, q one step away"
      (lAlternate.holdsNNF (.until (.prop "p") (.prop "q")))
    let l ← check "q U p holds immediately, p true at position 0"
      (lAlternate.holdsNNF (.until (.prop "q") (.prop "p")))
    let m ← check "p U q fails where q never holds" (! lEmpty.holdsNNF (.until (.prop "p") (.prop "q")))
    let n ← check "p R q fails where neither ever holds" (! lEmpty.holdsNNF (.release (.prop "p") (.prop "q")))
    let o ← check "¬p holds everywhere nothing is ever true" (lEmpty.holdsNNF (always (.nprop "p")))
    return [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o]

#eval report

end LTLLib.LTLtoTGBA.Tests.EvalTests
