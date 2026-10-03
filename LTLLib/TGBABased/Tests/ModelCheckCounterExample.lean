module

/-
  Tests that `modelCheckTGBA` answers a violated property with a counterexample whose stem and loop are a real run.

  System: a three-state traffic light cycling `red → green → yellow → red → …` forever, starting at `red`.
  Property: `□◇(red ∧ green)`, which cannot hold, no state has both atoms.
-/
import LTLLib.TGBABased.DijkstraCheck
import LTLLib.TGBABased.Tests.TestUtil
meta import LTLLib.TGBABased.DijkstraCheck
meta import LTLLib.TGBABased.Tests.TestUtil

namespace LTLLib.Tests.ModelCheckCounterExample

open LTLLib LTLLib.Tests

inductive Light where
  | red | yellow | green
deriving BEq, Hashable, Repr, Inhabited, DecidableEq

instance : LawfulBEq Light where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

instance : ToString Light where
  toString
    | .red => "red"
    | .yellow => "yellow"
    | .green => "green"

def lightSucc : Light → Array Light
  | .red => #[.green]
  | .green => #[.yellow]
  | .yellow => #[.red]

def lightLabel : Light → Std.HashSet String
  | .red => {"red"}
  | .green => {"green"}
  | .yellow => ∅   -- never asserted, needs no atomic proposition

def lightInit : List Light := [.red]

/-- Finitely many states, so the reachable set is trivially finite. -/
def lightFR : FiniteReach lightInit lightSucc :=
  .of_forall_mem [.red, .yellow, .green] fun s => by cases s <;> simp

/-- `□◇(red ∧ green)`, which no run of this system satisfies. -/
def ψ : Formula String := .always (.eventually (.and (.atom "red") (.atom "green")))

def report : IO Unit :=
  verdict "traffic light violates □◇(red ∧ green)" do
    match modelCheckTGBA ψ lightInit lightSucc lightLabel lightFR with
    | .empty n =>
      IO.println s!"  FAIL  reported sys ⊨ ψ ({n} product states), expected a counterexample"
      return [false]
    | .nonEmpty stem loop =>
      IO.println (showCounterexample lightLabel stem loop)
      let sys := stem.map Prod.fst
      let cyc := (loop.tail.map Prod.fst)
      let a ← check "stem is a real system run" (pathRespectsEdges lightSucc sys)
      let b ← check "loop is a real system cycle" (cycleRespectsEdges lightSucc cyc)
      let c ← check "loop starts where the stem ends" (sys.getLast? == cyc.head?)
      return [a, b, c]

#eval report

end LTLLib.Tests.ModelCheckCounterExample
