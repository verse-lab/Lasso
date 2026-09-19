/-
  Shared helpers for the tests in this folder. Every test prints one line per property plus a final `PASS`/`FAIL`.
  The witness helpers re-check a `.nonEmpty` answer against its graph, every step a real edge, the cycle closing,
  and every mark covered, the `TAcceptingCycle` contract checked computationally.

  Sections:
  - Results
  - Witness checking
  - Counterexample rendering
-/
import LTLLib.AbstractSpec.EmptinessCheck

namespace LTLLib.Tests

open LTLLib

/-! ## Results -/

def isEmptyResult {σ : Type u} : EmptinessResult σ → Bool
  | .empty _ => true
  | .nonEmpty _ _ => false

/-- Print one checked property, and return it so a test can conjoin the results. -/
def check (name : String) (ok : Bool) : IO Bool := do
  IO.println s!"  {if ok then "ok  " else "FAIL"}  {name}"
  return ok

/-- Print a test's header and its final verdict. -/
def verdict (title : String) (body : IO (List Bool)) : IO Unit := do
  IO.println s!"{title}:"
  let results ← body
  IO.println (if results.all id then "PASS" else "FAIL")

/-! ## Witness checking -/

/-- Consecutive-pair edges of a path, wrapping the last element back to the first. -/
def cyclicPairs {σ : Type u} (path : List σ) : List (σ × σ) :=
  match path with
  | [] => []
  | h :: _ => path.zip (path.tail ++ [h])

/-- Every step of a non-cyclic path is a real `succs` edge. -/
def pathRespectsEdges {σ : Type u} [BEq σ] (succs : σ → Array σ) (path : List σ) : Bool :=
  (path.zip path.tail).all fun (a, b) => (succs a).contains b

/-- Every step of a cycle, including the closing wraparound edge, is a real `succs` edge. -/
def cycleRespectsEdges {σ : Type u} [BEq σ] (succs : σ → Array σ) (cyc : List σ) : Bool :=
  ¬ cyc.isEmpty && (cyclicPairs cyc).all fun (a, b) => (succs a).contains b

/-- Union of marks along a cycle, read cyclically so the closing edge counts too. -/
def cycleMarks {σ : Type u} (edgeMarks : σ → σ → Std.HashSet Nat) (cyc : List σ) : Std.HashSet Nat :=
  (cyclicPairs cyc).foldl (init := (∅ : Std.HashSet Nat)) fun acc (a, b) => acc ∪ edgeMarks a b

/-- Re-check a `.nonEmpty` answer: the stem is a real path, the cycle a real closed cycle, and every mark below `numMarks` lies on it. -/
def checkWitness {σ : Type u} [BEq σ] [Repr σ] (succs : σ → Array σ)
    (edgeMarks : σ → σ → Std.HashSet Nat) (numMarks : Nat) (r : EmptinessResult σ) : IO (List Bool) := do
  match r with
  | .empty n =>
    IO.println s!"  FAIL  reported empty ({n} explored), expected nonEmpty"
    return [false]
  | .nonEmpty stem loop =>
    let cyc := loop.tail
    IO.println s!"  stem {repr stem}, cycle {repr cyc}"
    let a ← check "stem uses only real edges" (pathRespectsEdges succs stem)
    let b ← check "cycle uses only real edges, closing edge included" (cycleRespectsEdges succs cyc)
    let c ← check s!"cycle covers all {numMarks} marks"
      ((List.range numMarks).all (cycleMarks edgeMarks cyc).contains)
    return [a, b, c]

/-! ## Counterexample rendering -/

variable {σ : Type u} [ToString σ] {β : Type v}

/-- One system state with the atoms holding there, e.g. `red{red}` or `yellow{}`. -/
def showState (label : σ → Std.HashSet String) (s : σ) : String :=
  let atoms := (label s).toList.mergeSort (· < ·)
  s!"{s}\{{String.intercalate ", " atoms}}"

def showPath (label : σ → Std.HashSet String) (path : List σ) : String :=
  String.intercalate " → " (path.map (showState label))

/-- Render a `modelCheckTGBA` counterexample, dropping the automaton half of each product state.
The loop shown is `loop.tail`, since `loop.head = stem.getLast`. -/
def showCounterexample (label : σ → Std.HashSet String) (stem loop : List (σ × β)) : String :=
  s!"stem: {showPath label (stem.map Prod.fst)}\n\
     loop: {showPath label (loop.tail.map Prod.fst)} ⟲ (repeats forever)"

end LTLLib.Tests
