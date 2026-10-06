module

/-
  Illustrates a bug fixed by `Product.totalizeSucc` (`Product.lean`): a
  client system with a genuinely terminal state (no outgoing edges at all)
  used to make `modelCheck` miss real counterexamples whose violation only
  manifests by the system stalling forever in that state.

  LTL/Büchi-automaton semantics are defined over infinite words, so a
  Kripke structure's successor function is required to be total:
    Every state has at least one successor.

  A "terminal" state is read as "the system stays here forever".
  A state with no outgoing edges became a dead end, so nested DFS
  could never close a lasso through it.

  `modelCheck` reported `.empty` (no counterexample) even though the system
  does violate `ψ` below.

  `Product.totalizeSucc` is automatically applied now, so the client need not
  to worry to provide a total Kripke structure.

  System: a light that switches on once, then off, then stops responding.
  `off` has no outgoing transitions at all.

  Formula: `□◇on` ("the light turns on infinitely often"): Does not hold.
-/
import LTLLibTests.Examples.MCPrint
meta import LTLLibTests.Examples.MCPrint

namespace LTLLib.Tests.Examples

/-- A light that switches on once, then off, then dead-ends
  `off` is a genuinely terminal state -/
inductive BreakableLight where
  | on | off
deriving BEq, Hashable, Repr, Inhabited, DecidableEq

private theorem BreakableLight.beq_def (x y : BreakableLight) :
    (x == y) = (match x, y with
      | .on, .on | .off, .off => true
      | _, _ => false) := by
  cases x <;> cases y <;> rfl

instance : LawfulBEq BreakableLight where
  eq_of_beq {x y} h := by cases x <;> cases y <;> first | rfl | (rw [BreakableLight.beq_def] at h; contradiction)
  rfl {x} := by cases x <;> rfl

instance : LawfulHashable BreakableLight where
  hash_eq {a b} h := by have := eq_of_beq h; subst this; rfl

instance : ToString BreakableLight where
  toString
    | .on => "on"
    | .off => "off"



abbrev Prop' := String -- Atomic Propositions type

def breakableLightSucc : BreakableLight → Array BreakableLight
  | .on => #[.off]
  | .off => #[] -- No outgoing transitions!

def breakableLightLabel : BreakableLight → Std.HashSet Prop'
  | .on => {"on"}
  | .off => ∅ -- No atomic propositon needed here as never asserted

/-- The system starts at `on`. -/
def breakableLightInit : List BreakableLight := [.on]

theorem breakableLightFR : FiniteReach breakableLightInit breakableLightSucc :=
  .of_forall_mem [.on, .off] fun s => by cases s <;> simp



/-- `□◇on`: the light turns on infinitely often: Does not hold. -/
def ψ : Formula Prop' := .always (.eventually (.atom "on"))
#eval report breakableLightLabel (modelCheck (S := S) ψ breakableLightInit breakableLightSucc breakableLightLabel breakableLightFR)

end LTLLib.Tests.Examples
