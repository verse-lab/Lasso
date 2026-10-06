module

/-
  Tests the flattening of `LTL/FairNormalForm.lean` against [LSFZ16]'s worked examples.

  For Example 3 `FG(a ∨ (Fb ∧ Gc))`, `gfPush` must produce the paper's intermediate `(FGa ∨ GFb) ∧ (FGa ∨ FGc)`,
  and `normalise` must drop the two implied disjuncts of the crossing, so `fnf` lands on the paper's `FGa ∨ (FGc ∧ GFb)`.
  [LSFZ16, Section III-B]'s fairness outside `LTL(F, G)` must come back `none`.
-/
import LTLLib.LTL.FairNormalForm
import LTLLibTests.TGBABased.TestUtil
meta import LTLLib.LTL.FairNormalForm
meta import LTLLibTests.TGBABased.TestUtil

namespace LTLLib.Tests.FairNormalForm

open LTLLib LTLLib.Tests NNF

abbrev A := NNF String

def gfOf (φ : A) : A := always (eventually φ)
def fgOf (φ : A) : A := eventually (always φ)

/-- `FG(a ∨ (Fb ∧ Gc))`, [LSFZ16] Example 3. -/
def ex3 : A := fgOf (.or (.prop "a") (.and (eventually (.prop "b")) (always (.prop "c"))))

/-- `FG(a ∨ X(b U c))`, which is a fairness but not in `LTL(F, G)`. -/
def temporalFair : A := fgOf (.or (.prop "a") (.next (.until (.prop "b") (.prop "c"))))

/-- Weak fairness `□◇(¬e ∨ t)`. -/
def weakFair : A := gfOf (.or (.nprop "e") (.prop "t"))

/-- Strong fairness `□◇e → □◇t`, in negation normal form. -/
def strongFair : A := .or (fgOf (.nprop "e")) (gfOf (.prop "t"))

/-- Render a disjunct as `◇□f ∧ □◇g ∧ …`. -/
def showDisjunct (d : FairDisjunct String) : String :=
  String.intercalate " ∧ " (s!"◇□{d.1}" :: d.2.map fun g => s!"□◇{g}")

def showFNF : Option (List (FairDisjunct String)) → String
  | none => "none"
  | some ds => String.intercalate "  ∨  " (ds.map showDisjunct)

def report : IO Unit :=
  verdict "fair normal form" do
    IO.println s!"  Example 3 pushed:    {NNF.toString (gfPush ex3)}"
    IO.println s!"  Example 3 disjuncts: {showFNF ex3.fnf}"
    let a ← check "Example 3 reaches the paper's intermediate form"
      (gfPush ex3 ==
        .and (.or (fgOf (.prop "a")) (gfOf (.prop "b"))) (.or (fgOf (.prop "a")) (fgOf (.prop "c"))))
    let b ← check "GF a flattens to one GF disjunct"
      ((gfOf (.prop "a")).fnf == some [(.tt, [.prop "a"])])
    let c ← check "FG a flattens to one FG disjunct"
      ((fgOf (.prop "a")).fnf == some [(.prop "a", [])])
    let d ← check "weak fairness splits into two GF disjuncts"
      (weakFair.fnf == some [(.tt, [.nprop "e"]), (.tt, [.prop "t"])])
    let e ← check "strong fairness splits into an FG and a GF disjunct"
      (strongFair.fnf == some [(.nprop "e", []), (.tt, [.prop "t"])])
    let f ← check "FG(a ∨ X(b U c)) does not flatten, it leaves the fragment"
      (temporalFair.fnf == none)
    -- the crossing offers ◇□(a ∧ a) and ◇□(a ∧ c) and ◇□a ∧ □◇b as well, all covered by ◇□a
    let g ← check "Example 3 lands on the paper's two disjuncts, the covered ones dropped"
      (ex3.fnf == some [(.prop "a", []), (.prop "c", [.prop "b"])])
    let h ← check "a disjunct repeating a mark keeps one copy"
      ((gfOf (.and (.prop "a") (eventually (.prop "a")))).fnf == some [(.tt, [.prop "a"])])
    return [a, b, c, d, e, f, g, h]

#eval report

end LTLLib.Tests.FairNormalForm
