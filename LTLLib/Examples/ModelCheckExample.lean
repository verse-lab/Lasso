/-
  A minimal end-to-end example of `modelCheck` (`ModelCheck.lean`): given an
  external system as a plain Kripke structure — initial states, a successor
  function, and a labeling function assigning atomic propositions to
  states — check it against an LTL formula, with no manual BA/product
  construction required from the caller.

  System: a three-state traffic light, cycling `red → green → yellow →
  red → …` forever, starting at `red`.

  Formula: `□◇green` ("the light turns green infinitely often") — a
  liveness property that holds, since the light visits `green` on every
  cycle of the loop.
-/
import LTLLib

namespace LTLLib.Examples

/-- The three states of a traffic light, forming a fixed cycle
`red → green → yellow → red → …`. -/
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

/-- Atomic propositions labeling the traffic light's states. -/
abbrev Prop' := String

/-- The light cycles `red → green → yellow → red → …` with no branching. -/
def lightSucc : Light → Array Light
  | .red => #[.green]
  | .green => #[.yellow]
  | .yellow => #[.red]

/-- Only `green` is ever asserted; `red`/`yellow` states hold no
propositions in this example. -/
def lightLabel : Light → Std.HashSet Prop'
  | .red => ∅
  | .green => {"green"}
  | .yellow => ∅

/-- The system starts at `red`. -/
def lightInit : List Light := [.red]

/-- All three states are reachable from `red` and closed under `lightSucc`,
witnessing finite reachability for the emptiness checker. -/
def lightFR : FiniteReach lightSucc where
  univ := {Light.red, Light.yellow, Light.green}
  closed := by
    intro s hs t ht
    cases s <;> simp_all [lightSucc]

/-- `□◇green`: the light turns green infinitely often. -/
def ψ : Formula Prop' := .always (.eventually (.atom "green"))

/-- `Std.HashSet (NNF Prop')`, the finite-set representation `modelCheck`
needs for its internal tableau construction (matches `BuildPrint.S`). -/
abbrev S := Std.HashSet (NNF Prop')

#eval
  match modelCheck (S := S) ψ lightInit lightSucc lightLabel lightFR with
  | .empty n => s!"sys ⊨ ψ (no counterexample; explored {n} product states)"
  | .nonEmpty stem loop => s!"sys ⊭ ψ; counterexample stem={reprStr stem} loop={reprStr loop}"

end LTLLib.Examples
