module

/-
  Tests the `numMarks = 0` case of `modelCheckTGBA`. The automaton for the negated property carries one mark per Until
  subformula, so reachability properties such as `◇p`, whose negation `□¬p` has no Until, are the common zero-mark case.
  With zero marks the all-covered bitmask is `0`, so `UPDATE` reports as soon as any back edge closes a cycle.

  Two systems, both checked against `◇p`:
  - `A → B`, `B → B`, with `p` only at `B`: `◇p` holds and the product is empty.
  - `A → A`, with `p` nowhere: `◇p` fails and the product has an accepting, mark-free cycle.

  Sections:
  - A system where `◇p` holds
  - A system where `◇p` fails
  - Report
-/
import LTLLib.TGBABased.DijkstraCheck
import LTLLib.TGBABased.LTLtoTGBA.Pipeline
import LTLLibTests.TGBABased.TestUtil
meta import LTLLib.TGBABased.DijkstraCheck
meta import LTLLib.TGBABased.LTLtoTGBA.Pipeline
meta import LTLLibTests.TGBABased.TestUtil

namespace LTLLib.Tests.ZeroMarks

open LTLLib LTLLib.Tests

/-! ## A system where `◇p` holds -/

inductive Reaches where
  | a | b
deriving BEq, Hashable, Repr, Inhabited, DecidableEq

instance : LawfulBEq Reaches where
  eq_of_beq {x y} h := by cases x <;> cases y <;> first | rfl | exact absurd h (by decide)
  rfl {x} := by cases x <;> rfl

instance : ToString Reaches where
  toString | .a => "a" | .b => "b"

def reachesSucc : Reaches → Array Reaches
  | .a => #[.b]
  | .b => #[.b]

/-- `p` holds only at `b`. -/
def reachesLabel : Reaches → Std.HashSet String
  | .a => ∅
  | .b => {"p"}

def reachesInit : List Reaches := [.a]

def reachesFR : FiniteReach reachesInit reachesSucc :=
  .of_forall_mem [.a, .b] fun s => by cases s <;> simp

/-! ## A system where `◇p` fails -/

inductive Stuck where
  | a
deriving BEq, Hashable, Repr, Inhabited, DecidableEq

instance : LawfulBEq Stuck where
  eq_of_beq {x y} _ := by cases x; cases y; rfl
  rfl {x} := by cases x; rfl

instance : ToString Stuck where
  toString | .a => "a"

def stuckSucc : Stuck → Array Stuck
  | .a => #[.a]

/-- `p` holds nowhere. -/
def stuckLabel : Stuck → Std.HashSet String := fun _ => ∅

def stuckInit : List Stuck := [.a]

def stuckFR : FiniteReach stuckInit stuckSucc :=
  .of_forall_mem [.a] fun s => by cases s <;> simp

/-! ## Report -/

/-- Acceptance marks the automaton for `¬φ` ends up carrying. -/
def numMarksOf (φ : Formula String) : Nat :=
  match ltl3ba (φ.toNNF false) with
  | some t => t.numAcceptSets
  | none => 0

def eventuallyP : Formula String := .eventually (.atom "p")

def report : IO Unit :=
  verdict "zero acceptance marks" do
    let a ← check "◇p carries no marks" (numMarksOf eventuallyP == 0)
    let b ← check "p carries no marks" (numMarksOf (.atom "p") == 0)
    let c ← check "□p carries one mark" (numMarksOf (.always (.atom "p")) == 1)
    let d ← check "□◇p carries one mark" (numMarksOf (.always (.eventually (.atom "p"))) == 1)
    let e ← check "◇p holds on a → b → b↺"
      (isEmptyResult (modelCheckTGBA eventuallyP reachesInit reachesSucc reachesLabel reachesFR))
    let f ← check "◇p fails on a↺ with p nowhere"
      (!isEmptyResult (modelCheckTGBA eventuallyP stuckInit stuckSucc stuckLabel stuckFR))
    return [a, b, c, d, e, f]

#eval report

end LTLLib.Tests.ZeroMarks
