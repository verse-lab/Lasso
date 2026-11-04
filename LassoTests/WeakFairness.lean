module

/-
  Tests `modelCheckTGBAFair` end to end: a property fails without fairness and holds under a weak fairness assumption
  carried as one generalized Büchi mark rather than translated.

  System: `idle → ready`, `ready → ready | act`, `act → ready`, labelled `{}`, `{en}` and `{tk, goal}`. Property: `◇goal`.
  The run stalling in `ready` violates it, and weak fairness `◇□en → □◇tk` rules out exactly that run. A property no run
  satisfies must still fail under fairness, the control against the marks making every answer `.empty`.
-/
import Lasso.LTL.Fairness
import Lasso.DijkstraCheck
import LassoTests.TestUtil
meta import Lasso.LTL.Fairness
meta import Lasso.DijkstraCheck
meta import LassoTests.TestUtil

namespace Lasso.Tests.WeakFairness

open Lasso Lasso.Tests

inductive Step where
  | idle | ready | act
deriving BEq, Hashable, Repr, Inhabited, DecidableEq

instance : LawfulBEq Step where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

instance : ToString Step where
  toString
    | .idle => "idle"
    | .ready => "ready"
    | .act => "act"

def stepSucc : Step → Array Step
  | .idle => #[.ready]
  | .ready => #[.ready, .act]  -- may stall in `ready` forever, which is the unfair run
  | .act => #[.ready]

def stepLabel : Step → Std.HashSet String
  | .idle => ∅
  | .ready => {"en"}
  | .act => {"tk", "goal"}

def stepInit : List Step := [.idle]

/-- Finitely many states, so the reachable set is trivially finite. -/
theorem stepFR : FiniteReach stepInit stepSucc :=
  .of_forall_mem [.idle, .ready, .act] fun s => by cases s <;> simp

/-- `◇goal`, which holds on every run that eventually leaves `ready`. -/
def ψ : Formula String := .eventually (.atom "goal")

/-- `◇never`, which no run satisfies, fair or not. -/
def ψnever : Formula String := .eventually (.atom "never")

/-- Weak fairness `◇□en → □◇tk`, as the single conjunct `¬en ∨ tk`. -/
def fair : List (BoolFormula String) := [BoolFormula.weakFairMark (.prop "en") (.prop "tk")]

def report : IO Unit :=
  verdict "◇goal fails unfairly and holds under weak fairness" do
    let unfair := modelCheckTGBA ψ stepInit (LSys.unlabelled stepSucc) stepLabel
    let a ← check "◇goal fails without fairness" (! isEmptyResult unfair)
    let b ← match unfair with
      | .empty _ => pure [false]
      | .nonEmpty stem loop => do
        IO.println (showCounterexample stepLabel stem loop)
        let sys := stem.map Prod.fst
        let cyc := loop.tail.map Prod.fst
        let b1 ← check "unfair stem is a real system run" (pathRespectsEdges stepSucc sys)
        let b2 ← check "unfair loop is a real system cycle" (cycleRespectsEdges stepSucc cyc)
        let b3 ← check "unfair loop stalls in ready" (cyc.all (· == Step.ready))
        pure [b1, b2, b3]
    let c ← check "◇goal holds under weak fairness"
      (isEmptyResult (modelCheckTGBAFair ψ fair stepInit stepSucc stepLabel))
    let d ← check "◇never still fails under weak fairness"
      (! isEmptyResult (modelCheckTGBAFair ψnever fair stepInit stepSucc stepLabel))
    return a :: c :: d :: b

#eval report

end Lasso.Tests.WeakFairness
