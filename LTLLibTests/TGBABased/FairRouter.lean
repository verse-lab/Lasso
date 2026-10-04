module

/-
  Tests `modelCheckUnderFairness` end to end on an assumption split between both halves of the router.

  System: `start → spin | wait`, `spin → spin` labelled `{p, tk}`, `wait → wait | go` labelled `{en}`, `go → go` labelled
  `{tk, g}`. The property `◇g` is violated by exactly two runs, the `spin` self-loop and the `wait` stall.
  The fairness `□◇tk` is hoisted onto the product and rules out the stall, while `G ¬p`, not a fairness, stays in the
  property and rules out the self-loop, so `◇g` holds only under both. The strong fairness `□◇en → □◇tk` is the same
  assumption as two disjuncts, and `FG(a ∨ X(b U c))` does not flatten, so it is kept.

  Further checks pin what splits (conjunctive and disjunctive properties and assumptions, a property that is itself a
  fairness), and the fail-fast on an empty region and on `GF` marks that no single cycle carries together.
-/
import LTLLib.LTL.FairNormalForm
import LTLLib.LTL.Syntax
import LTLLib.TGBABased.Fairness.FairRouter
import LTLLibTests.TGBABased.TestUtil
meta import LTLLib.LTL.FairNormalForm
meta import LTLLib.LTL.Syntax
meta import LTLLib.TGBABased.Fairness.FairRouter
meta import LTLLibTests.TGBABased.TestUtil

namespace LTLLib.Tests.FairRouter

open LTLLib LTLLib.Tests

inductive Node where
  | start | spin | wait | go
deriving BEq, Hashable, Repr, Inhabited, DecidableEq

instance : LawfulBEq Node where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

instance : ToString Node where
  toString
    | .start => "start"
    | .spin => "spin"
    | .wait => "wait"
    | .go => "go"

def nodeSucc : Node → Array Node
  | .start => #[.spin, .wait]
  | .spin => #[.spin]  -- violates `◇g` and is ruled out only by the kept `G ¬p`
  | .wait => #[.wait, .go]  -- stalling here violates `◇g` and is ruled out only by the hoisted `□◇tk`
  | .go => #[.go]

def nodeLabel : Node → Std.HashSet String
  | .start => ∅
  | .spin => {"p", "tk"}
  | .wait => {"en"}
  | .go => {"tk", "g"}

def nodeInit : List Node := [.start]

def nodeFR : FiniteReach nodeInit nodeSucc :=
  .of_forall_mem [.start, .spin, .wait, .go] fun s => by cases s <;> simp

/-- `◇g`. -/
def ψ : Formula String := .eventually (.atom "g")

/-- `◇never`, which no run satisfies. -/
def ψnever : Formula String := .eventually (.atom "never")

/-- `□◇tk`, a fairness, hoisted onto the product. -/
def gfTk : Formula String := .always (.eventually (.atom "tk"))

/-- `□¬p`, purely universal but not a pure eventuality, so it stays in the property. -/
def gNotP : Formula String := .always (.not (.atom "p"))

/-- `□◇en → □◇tk`, the strong fairness whose normal form has two disjuncts. -/
def strongFair : Formula String := .implies (.always (.eventually (.atom "en"))) gfTk

/-- `□◇en`, a second fairness, for the conjunction and disjunction shapes. -/
def gfEn : Formula String := .always (.eventually (.atom "en"))

/-- `◇□(a ∨ X(b U c))`, [LSFZ16, Section III-B]'s fairness outside `LTL(F, G)`. -/
def temporalFair : Formula String :=
  .eventually (.always (.or (.atom "a") (.next (.until (.atom "b") (.atom "c")))))

def showDisjunct (d : NNF.FairDisjunct String) : String :=
  let gfs := d.2.map fun g => s!" ∧ □◇{g}"
  s!"◇□{d.1}{String.join gfs}"

def showSplit (φ : Formula String) : String :=
  let s := hoistFairness (NNF.splitConj (φ.toNNF false))
  let ds := (NNF.crossAllDNF s.1).map showDisjunct
  s!"kept {s.2.map NNF.toString}, disjuncts {ds}"

def report : IO Unit :=
  verdict "the router splits the negated property and checks each disjunct" do
    IO.println s!"    G¬p ∧ GFtk → ◇g: {showSplit (.implies (.and gNotP gfTk) ψ)}"
    IO.println s!"    G¬p ∧ strong → ◇g: {showSplit (.implies (.and gNotP strongFair) ψ)}"
    IO.println s!"    temporal → ◇g:  {showSplit (.implies temporalFair ψ)}"
    let a ← check "◇g fails with no assumption"
      (! isEmptyResult (modelCheckUnderFairness ψ nodeInit (LSys.unlabelled nodeSucc) nodeLabel))
    let b ← check "◇g fails under the hoisted □◇tk alone, the spin loop survives"
      (! isEmptyResult (modelCheckUnderFairness (.implies gfTk ψ) nodeInit (LSys.unlabelled nodeSucc) nodeLabel))
    let c ← check "◇g fails under the kept □¬p alone, the wait stall survives"
      (! isEmptyResult (modelCheckUnderFairness (.implies gNotP ψ) nodeInit (LSys.unlabelled nodeSucc) nodeLabel))
    let d ← check "◇g holds under both, one hoisted and one kept"
      (isEmptyResult (modelCheckUnderFairness (.implies (.and gNotP gfTk) ψ)
        nodeInit (LSys.unlabelled nodeSucc) nodeLabel))
    let e ← check "◇g holds under the strong fairness too, across its two disjuncts"
      (isEmptyResult (modelCheckUnderFairness (.implies (.and gNotP strongFair) ψ)
        nodeInit (LSys.unlabelled nodeSucc) nodeLabel))
    let f ← check "◇never still fails under the full assumption"
      (! isEmptyResult (modelCheckUnderFairness (.implies (.and gNotP gfTk) ψnever)
        nodeInit (LSys.unlabelled nodeSucc) nodeLabel))
    let g ← check "□◇tk is hoisted, □¬p is kept"
      ((hoistFairness (NNF.splitConj ((Formula.and gNotP gfTk).toNNF true))).1.length == 1 &&
        (hoistFairness (NNF.splitConj ((Formula.and gNotP gfTk).toNNF true))).2.length == 1)
    let h ← check "the strong fairness crosses to two disjuncts"
      ((NNF.crossAllDNF (hoistFairness (NNF.splitConj (strongFair.toNNF true))).1).length == 2)
    -- the split runs after `toNNF`, so a conjunction written under a negation still splits
    let deMorgan : Formula String := .not (.or (.not gNotP) (.not gfTk))
    let m ← check "a de Morgan conjunction still hoists its fairness half"
      ((hoistFairness (NNF.splitConj (deMorgan.toNNF true))).1.length == 1 &&
        (hoistFairness (NNF.splitConj (deMorgan.toNNF true))).2.length == 1)
    let n ← check "◇g holds under the de Morgan form of the same assumption"
      (isEmptyResult (modelCheckUnderFairness (.implies deMorgan ψ)
        nodeInit (LSys.unlabelled nodeSucc) nodeLabel))
    let i ← check "the temporal fairness is not hoisted, it is kept"
      ((hoistFairness (NNF.splitConj (temporalFair.toNNF true))).1.isEmpty &&
        (hoistFairness (NNF.splitConj (temporalFair.toNNF true))).2.length == 1)
    -- Only conjunction splits, and it is the negated property that is split.
    let hoistedKept (φ : Formula String) : Nat × Nat :=
      let sp := hoistFairness (φ.toNNF false).splitConj
      (sp.1.length, sp.2.length)
    let o ← check "a conjunctive property does not split, its negation is a disjunction"
      (hoistedKept (.implies gfTk (.and gfEn ψ)) == (1, 1))
    let p ← check "a disjunctive property splits, so its fairness half is hoisted too"
      (hoistedKept (.implies gfTk (.or gfEn ψ)) == (2, 1))
    let q ← check "a disjunctive assumption is hoisted whole when both sides are fairness"
      (hoistedKept (.implies (.or gfTk gfEn) ψ) == (1, 1))
    let r ← check "a disjunctive assumption is kept whole when one side is not a fairness"
      (hoistedKept (.implies (.or gfTk gNotP) ψ) == (0, 2))
    let s ← check "a property that is itself a fairness leaves nothing for the translator"
      (hoistedKept (.implies gfTk gfEn) == (2, 0))
    -- The fail-fast, on both halves of a disjunct.
    let j ← check "◇□(p ∧ g) is infeasible, the region is empty"
      (! disjunctFeasible (.and (.prop "p") (.prop "g")) [] nodeInit (LSys.unlabelled nodeSucc) nodeLabel)
    let k ← check "□◇p ∧ □◇g is infeasible, no one cycle carries both marks"
      (! disjunctFeasible .tt [.prop "p", .prop "g"] nodeInit (LSys.unlabelled nodeSucc) nodeLabel)
    let l ← check "□◇tk is feasible, both self-loops carry it"
      (disjunctFeasible .tt [.prop "tk"] nodeInit (LSys.unlabelled nodeSucc) nodeLabel)
    return [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s]

#eval report

end LTLLib.Tests.FairRouter
