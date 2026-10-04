module

/-
  Tests `modelCheckTGBADisjunct` on the case the latch exists for, an accepting cycle inside the `FG` region whose every
  path from an initial state leaves the region.

  System: `entry → gate → a → b → a → …`, labelled `{}`, `{}`, `{r, p}` and `{r}`. The only cycle `a ⇄ b` lies inside the
  `r`-region, while the stem `entry → gate` lies entirely outside it. Restricting `succs` globally while keeping the
  initial states would report `.empty` here, since `entry` would have no successors.

  Checks: the confined cycle is found through an unconfined stem, a region with no cycle is rejected, a `GF` conjunct
  satisfied on the cycle still passes, and one satisfied nowhere still fails.
-/
import LTLLib.TGBABased.Fairness.FairCheck
import LTLLibTests.TGBABased.TestUtil
meta import LTLLib.TGBABased.Fairness.FairCheck
meta import LTLLibTests.TGBABased.TestUtil

namespace LTLLib.Tests.RegionLatch

open LTLLib LTLLib.Tests

inductive Node where
  | entry | gate | a | b
deriving BEq, Hashable, Repr, Inhabited, DecidableEq

instance : LawfulBEq Node where
  eq_of_beq {x y} h := by cases x <;> cases y <;> first | rfl | exact absurd h (by decide)
  rfl {x} := by cases x <;> decide

instance : ToString Node where
  toString
    | .entry => "entry"
    | .gate => "gate"
    | .a => "a"
    | .b => "b"

def nodeSucc : Node → Array Node
  | .entry => #[.gate]
  | .gate => #[.a]
  | .a => #[.b]
  | .b => #[.a]

def nodeLabel : Node → Std.HashSet String
  | .entry => ∅
  | .gate => ∅          -- outside the r-region, so the stem must leave it
  | .a => {"r", "p"}
  | .b => {"r"}

def nodeInit : List Node := [.entry]

/-- Finitely many states, so the reachable set is trivially finite. -/
def nodeFR : FiniteReach nodeInit nodeSucc :=
  .of_forall_mem [.entry, .gate, .a, .b] fun s => by cases s <;> simp

/-- `◇goal`, which no run satisfies, so every run is a candidate counterexample. -/
def ψ : Formula String := .eventually (.atom "goal")

def report : IO Unit :=
  verdict "FG region confines the cycle but not the stem" do
    let confined := modelCheckTGBADisjunct ψ (.prop "r") [] nodeInit (LSys.unlabelled nodeSucc) nodeLabel
    let a ← check "cycle inside the r-region is found through a stem outside it"
      (! isEmptyResult confined)
    let b ← match confined with
      | .empty _ => pure [false]
      | .nonEmpty stem loop => do
        let sys := stem.map fun q => q.1.1
        let cyc := loop.tail.map fun q => q.1.1
        IO.println s!"  stem: {showPath nodeLabel sys}"
        IO.println s!"  loop: {showPath nodeLabel cyc} ⟲ (repeats forever)"
        let b1 ← check "stem is a real system run" (pathRespectsEdges nodeSucc sys)
        let b2 ← check "loop is a real system cycle" (cycleRespectsEdges nodeSucc cyc)
        let b3 ← check "loop stays inside the r-region"
          (cyc.all fun s => (nodeLabel s).contains "r")
        let b4 ← check "stem leaves the r-region"
          (sys.any fun s => ! (nodeLabel s).contains "r")
        pure [b1, b2, b3, b4]
    let c ← check "p-region holds no cycle, so the disjunct is rejected"
      (isEmptyResult (modelCheckTGBADisjunct ψ (.prop "p") [] nodeInit (LSys.unlabelled nodeSucc) nodeLabel))
    let d ← check "GF p on the cycle passes alongside FG r"
      (! isEmptyResult
        (modelCheckTGBADisjunct ψ (.prop "r") [.prop "p"] nodeInit (LSys.unlabelled nodeSucc) nodeLabel))
    let e ← check "GF never fails alongside FG r"
      (isEmptyResult
        (modelCheckTGBADisjunct ψ (.prop "r") [.prop "never"] nodeInit (LSys.unlabelled nodeSucc) nodeLabel))
    return a :: c :: d :: e :: b

#eval report

end LTLLib.Tests.RegionLatch
