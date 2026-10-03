module

/-
  Shared "print a `modelCheck`/`modelCheckTGBA` result" infrastructure
  for the `Examples/` directory.
-/
public import LTLLib

public section

namespace LTLLib.Examples

abbrev S := Std.HashSet (NNF String)

variable {σ : Type u} [ToString σ] {β : Type v}

/-- Render one system state together with the atoms holding there, e.g.
`red{red}` or `yellow{}`. -/
def showState (label : σ → Std.HashSet String) (s : σ) : String :=
  let atoms := (label s).toList.mergeSort (· < ·)
  s!"{s}\{{String.intercalate ", " atoms}}"

/-- Render a lasso path as an arrow chain. -/
def showPath (label : σ → Std.HashSet String) (path : List σ) : String :=
  String.intercalate " → " (path.map (showState label))

/-- Render a `modelCheck`/`modelCheckTGBA` counterexample: the
product's `stem`/`loop` are over `σ × β`, but the `β` half is the
¬ψ-automaton's own internal state id, so it is dropped.

`loop.tail`, not `loop`: both `nestedDFSChecker`'s and `dijkstraCheck`'s
witnesses follow the same `loop.head = stem.getLast` convention. -/
def showCounterexample (label : σ → Std.HashSet String) (stem loop : List (σ × β)) :
    String :=
  s!"stem: {showPath label (stem.map Prod.fst)}\n\
     loop: {showPath label (loop.tail.map Prod.fst)} ⟲ (repeats forever)"

/-- Print a `modelCheck`/`modelCheckTGBA` result. -/
def report (label : σ → Std.HashSet String) : EmptinessResult (σ × β) → IO Unit
  | .empty n => IO.println s!"sys ⊨ ψ (no counterexample; explored {n} product states)"
  | .nonEmpty stem loop => do
    IO.println "sys ⊭ ψ"
    IO.println (showCounterexample label stem loop)

end LTLLib.Examples
