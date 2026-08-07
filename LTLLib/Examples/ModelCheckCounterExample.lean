/-
  A minimal end-to-end example of `modelCheck` (`ModelCheck.lean`): given an
  external system as a plain Kripke structure — initial states, a successor
  function, and a labeling function assigning atomic propositions to
  states — check it against an LTL formula, with no manual BA/product
  construction required from the caller.

  System: a three-state traffic light, cycling `red → green → yellow →
  red → …` forever, starting at `red`.

  Formula: `□◇(red ∧ green)` ("the light turns red and green at the same time
  infinitely often") — a liveness property that does not hold, since the light
  cannot ever by in two states at the same time.
-/
import LTLLib
import Mathlib.Tactic.DeriveFintype

namespace LTLLib.Examples

/-- The three states of a traffic light, forming a fixed cycle
`red → green → yellow → red → …`. -/
inductive Light where
  | red | yellow | green
deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Fintype

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

/-- Only `red` and `green` is ever asserted; `yellow` state holds no
propositions in this example. -/
def lightLabel : Light → Std.HashSet Prop'
  | .red => {"red"}
  | .green => {"green"}
  | .yellow => ∅

instance : ToString Light where
  toString
    | .red => "red"
    | .yellow => "yellow"
    | .green => "green"

/-- The system starts at `red`. -/
def lightInit : List Light := [.red]

/-- `Light` is a `Fintype`, so *any* `Set Light` is finite for free — no
manual enumeration/closure proof needed, unlike the old `Std.HashSet`-witness
design. -/
def lightFR : FiniteReach lightInit lightSucc := Set.toFinite _

/-- `□◇(red ∧ green)`: the light turns green infinitely often. -/
def ψ : Formula Prop' := .always (.eventually (.and (.atom "red") (.atom "green")))

/-- `Std.HashSet (NNF Prop')`, the finite-set representation `modelCheck`
needs for its internal tableau construction (matches `BuildPrint.S`). -/
abbrev S := Std.HashSet (NNF Prop')

/-- Render one system state together with the atoms holding there, e.g.
`red{red}` or `yellow{}` — the labeling is what makes it legible *why* a
lasso violates `ψ`, not just which states it visits. -/
def showState (s : Light) : String :=
  let atoms := (lightLabel s).toList.mergeSort (· < ·)
  s!"{s}\{{String.intercalate ", " atoms}}"

/-- Render a lasso path as an arrow chain. -/
def showPath (path : List Light) : String :=
  String.intercalate " → " (path.map showState)

/-- Render a `modelCheck` counterexample: the product's `stem`/`loop` are
over `Light × BAState`, but the `BAState` half is the ¬ψ-automaton's own
internal bookkeeping, not something a reader needs to see *which system
run* violates `ψ` — so this drops it and prints only the `Light` states,
as a stem leading into a forever-repeating loop.

`loop.tail`, not `loop`: `EmptinessChecker.nonEmpty_valid`
(`EmptinessCheck.lean`) only promises `loop.tail` is the genuine,
successor-respecting cycle — `loop`'s own head is `nestedDFSChecker`'s
internal bookkeeping (`outerDFSLoopWF`, `NestedDFS/NestedDFSTermination.lean`:
`current :: cyclePath ++ loopTail`, where `cyclePath` already starts with
`current`), duplicating `stem`'s last state rather than naming a real
transition. Printing `loop` as-is would show a spurious edge (e.g.
`red → red`, which `lightSucc` never produces). -/
def showCounterexample (stem loop : List (Light × BAState)) : String :=
  s!"stem: {showPath (stem.map Prod.fst)}\n\
     loop: {showPath (loop.tail.map Prod.fst)} ⟲ (repeats forever)"

/-- `IO.println`, not a plain `String` result: `#eval` on a bare `String`
prints it `Repr`-quoted (escaped `\n` and all), same reason
`BuildPrint.runExample` prints via `IO.println` rather than returning text. -/
def report : IO Unit := do
  match modelCheck (S := S) ψ lightInit lightSucc lightLabel lightFR with
  | .empty n => IO.println s!"sys ⊨ ψ (no counterexample; explored {n} product states)"
  | .nonEmpty stem loop =>
    IO.println "sys ⊭ ψ"
    IO.println (showCounterexample stem loop)

#eval report

end LTLLib.Examples
