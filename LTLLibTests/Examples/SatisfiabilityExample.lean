module

/-
  Minimal end-to-end example of `fullPipeline` (`Satisfiability.lean`):
  decide satisfiability of an LTL formula directly, no external system
  needed. For `.nonEmpty`, also renders the witness lasso.

  `φSat = □◇a ∧ □◇¬a`:    Satisfiable, e.g. by alternating a, ¬a, a, ¬a, ….
  `φUnsat = □◇(a ∧ ¬a)`:  Unsatisfiable, `a`/`¬a` can't hold together.
-/
import LTLLibTests.Examples.BuildPrint
meta import LTLLibTests.Examples.BuildPrint

namespace LTLLib.Tests.Examples

abbrev Prop' := String

/-- `□◇a ∧ □◇¬a`. -/
def φSat : Formula Prop' :=
  .and (.always (.eventually (.atom "a"))) (.always (.eventually (.not (.atom "a"))))

/-- `□◇(a ∧ ¬a)`. -/
def φUnsat : Formula Prop' :=
  .always (.eventually (.and (.atom "a") (.not (.atom "a"))))

/-- Render one `BAState`'s positive atoms under `ba`'s own labeling. -/
def showBAState (ba : BA Prop') (s : BAState) : String :=
  let atoms := (ba.getLabeling s).1.toList.mergeSort (· < ·)
  s!"\{{String.intercalate ", " atoms}}"

def showRun (ba : BA Prop') (path : List BAState) : String :=
  String.intercalate " → " (path.map (showBAState ba))

/-- Decide satisfiability of `φ`. For `.nonEmpty`, also print the witness
lasso's atoms. `ba` here is `fullPipeline`'s own automaton, recomputed
just for display (same pure inputs, same `ba`, by determinism). -/
def report (φ : Formula Prop') : IO Unit := do
  let φNNF := φ.toNNF true
  match buildAll (α := Prop') φNNF, fullPipeline (S := S Prop') φNNF with
  | some (_, _, ba, _), .nonEmpty stem loop =>
    IO.println "satisfiable"
    IO.println s!"stem: {showRun ba stem}"
    IO.println s!"loop: {showRun ba loop.tail} ⟲ (repeats forever)"
  | _, .empty n => IO.println s!"unsatisfiable (explored {n} states)"
  | none, .nonEmpty .. => IO.println "createGraph failed (unexpected)"

#eval report φSat
#eval report φUnsat

end LTLLib.Tests.Examples
