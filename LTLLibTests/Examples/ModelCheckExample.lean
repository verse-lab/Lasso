module

/-
  Minimal end-to-end example of `modelCheck`: given an
  external system as a plain Kripke structure:
    - initial states,
    - a successor function
    - labeling function assigning atomic propositions to states

  Check it against an LTL formula.

  System: a three-state traffic light, cycling `red → green → yellow →
  red → …` forever, starting at `red`.

  Formula: `□◇green` ("the light turns green infinitely often"): Holds
-/
import LTLLibTests.Examples.MCPrint
meta import LTLLibTests.Examples.MCPrint

namespace LTLLib.Tests.Examples

inductive Light where
  | red | yellow | green
deriving BEq, Hashable, Repr, Inhabited, DecidableEq

private theorem Light.beq_def (x y : Light) :
    (x == y) = (match x, y with
      | .red, .red | .yellow, .yellow | .green, .green => true
      | _, _ => false) := by
  cases x <;> cases y <;> rfl

instance : LawfulBEq Light where
  eq_of_beq {x y} h := by cases x <;> cases y <;> first | rfl | (rw [Light.beq_def] at h; contradiction)
  rfl {x} := by cases x <;> rfl

instance : LawfulHashable Light where
  hash_eq {a b} h := by have := eq_of_beq h; subst this; rfl

instance : ToString Light where
  toString
    | .red => "red"
    | .yellow => "yellow"
    | .green => "green"



abbrev Prop' := String -- Atomic Propositions type

def lightSucc : Light → Array Light
  | .red => #[.green]
  | .green => #[.yellow]
  | .yellow => #[.red]

def lightLabel : Light → Std.HashSet Prop'
  | .red => ∅
  -- Only green is ever asserted
  | .green => {"green"}
  | .yellow => ∅

def lightInit : List Light := [.red]

def lightFR : FiniteReach lightInit lightSucc :=
  .of_forall_mem [.red, .yellow, .green] fun s => by cases s <;> simp



/-- `□◇green`: the light turns green infinitely often. -/
def ψ : Formula Prop' := .always (.eventually (.atom "green"))
#eval report lightLabel (modelCheck (S := S) ψ lightInit lightSucc lightLabel lightFR)

end LTLLib.Tests.Examples
