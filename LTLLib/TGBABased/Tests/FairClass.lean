module

/-
  Tests the recogniser and classifier of `LTL/FairClass.lean` on formulas of known membership, several from [LSFZ16].

  The published CONCUR'00 pure eventuality grammar reads the left operand of `U` rather than the right, which makes
  `(F b) U c` a pure eventuality and lets `a U ((F b) U c)` collapse to `(F b) U c`. The corrected grammar must reject it.
  The last two checks pin [LSFZ16, Definition 4]: `⋀ᵢ GF aᵢ` flattens linearly, while the semaphore fairness
  `⋀ᵢ (GF enterᵢ → GF criticalᵢ)` does not, the `2ⁿ` case.
-/
import LTLLib.LTL.FairClass
import LTLLib.TGBABased.Tests.TestUtil
meta import LTLLib.LTL.FairClass
meta import LTLLib.TGBABased.Tests.TestUtil

namespace LTLLib.Tests.FairClass

open LTLLib LTLLib.Tests NNF

abbrev A := NNF String

def gf (φ : A) : A := always (eventually φ)
def fg (φ : A) : A := eventually (always φ)

/-- `FG(a ∨ X(b U c))`, [LSFZ16, Section III-B]'s witness that `LTL(F, G)` fairness is not all of it. -/
def temporalFair : A := fg (.or (.prop "a") (.next (.until (.prop "b") (.prop "c"))))

/-- `(F b) U c`, which the published grammar wrongly accepts as a pure eventuality. -/
def typoWitness : A := .until (eventually (.prop "b")) (.prop "c")

/-- Weak fairness `□◇(¬e ∨ t)`. -/
def weakFair : A := gf (.or (.nprop "e") (.prop "t"))

/-- Strong fairness `□◇e → □◇t`, in negation normal form. -/
def strongFair : A := .or (fg (.nprop "e")) (gf (.prop "t"))

/-- `⋀ᵢ □◇aᵢ`, Spot's `--and-gf` pattern. -/
def andGF : A := .and (gf (.prop "a1")) (.and (gf (.prop "a2")) (gf (.prop "a3")))

/-- `⋀ᵢ (□◇enterᵢ → □◇criticalᵢ)`, [LSFZ16]'s semaphore assumption. -/
def semaphore : A :=
  .and (.or (fg (.nprop "e1")) (gf (.prop "c1"))) (.or (fg (.nprop "e2")) (gf (.prop "c2")))

def report : IO Unit :=
  verdict "fairness recogniser and route classifier" do
    let a ← check "GF a is a fairness" (gf (.prop "a")).isFairness
    let b ← check "FG a is a fairness" (fg (.prop "a")).isFairness
    let c ← check "a alone is not a fairness" (! (NNF.prop "a" : A).isFairness)
    let d ← check "F a is not a fairness, it is not suffix closed"
      (! (eventually (.prop "a") : A).isFairness)
    let e ← check "G a is not a fairness, it is not prefix closed"
      (! (always (.prop "a") : A).isFairness)
    let f ← check "(F b) U c is not a pure eventuality" (! typoWitness.isPureEventuality)
    let g ← check "GF a ∨ FG b routes to the LTL(F, G) fragment"
      ((NNF.or (gf (.prop "a")) (fg (.prop "b")) : A).classify == .fgFragment)
    let h ← check "FG(a ∨ X(b U c)) is a fairness" temporalFair.isFairness
    let i ← check "FG(a ∨ X(b U c)) routes to the temporal case"
      (temporalFair.classify == .temporal)
    let j ← check "weak fairness routes to the LTL(F, G) fragment"
      (weakFair.classify == .fgFragment)
    let k ← check "strong fairness routes to the LTL(F, G) fragment"
      (strongFair.classify == .fgFragment)
    let l ← check "⋀ᵢ GF aᵢ flattens linearly" andGF.isFastFair
    let m ← check "the semaphore assumption does not, it is the 2ⁿ case"
      (! semaphore.isFastFair)
    -- The two rules generalised from [EH00], which its `e R e` and `u U u` would both reject.
    let n ← check "a R F b is a pure eventuality"
      (NNF.release (.prop "a") (eventually (.prop "b")) : A).isPureEventuality
    let o ← check "a U G b is purely universal"
      (NNF.until (.prop "a") (always (.prop "b")) : A).isPurelyUniversal
    return [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o]

#eval report

end LTLLib.Tests.FairClass
