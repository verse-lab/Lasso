module

/-
  Covers source-state plus edge letters, deadlock stuttering, parallel edges with different letters,
  and a region that keeps a product edge but excludes its only accepting realization. Positive controls
  add a single edge carrying both the region atom and the mark atom.
-/
import LTLLib.Fairness.FairCheck
import LTLLibTests.TestUtil
meta import LTLLib.Fairness.FairCheck
meta import LTLLibTests.TestUtil

namespace LTLLib.Tests.EdgeLabels

open LTLLib LTLLib.Tests

/-- The only action goes from state 0 to a terminal state 1. -/
def terminalSteps : Nat → Array (LStep String Nat)
  | 0 => #[({"action"}, 1)]
  | _ => #[]

def terminalLabel (s : Nat) : Std.HashSet String :=
  if s == 0 then {"source"} else {"target"}

def terminalCases : List (String × Formula String × Bool) :=
  [ ("the initial letter contains the source label", .atom "source", true),
    ("the initial letter contains the chosen edge atom", .atom "action", true),
    ("the target label is not read one step early", .atom "target", false),
    ("the source and edge atoms hold together", .and (.atom "source") (.atom "action"), true),
    ("the next letter contains the target label", .next (.atom "target"), true),
    ("deadlock stuttering preserves state labels", .next (.always (.atom "target")), true),
    ("deadlock stuttering does not repeat the incoming action",
      .next (.always (.not (.atom "action"))), true),
    ("an action taken only once is not GF action", .always (.eventually (.atom "action")), false) ]

def noLabel (_ : Nat) : Std.HashSet String := ∅

/-- Two self-loops with the same endpoints, but no letter contains both atoms. -/
def separate : Array (LStep String Nat) := #[({"r"}, 0), ({"g"}, 0)]

def together : Array (LStep String Nat) := separate.push ({"r", "g"}, 0)

/-- The mark is available exactly on letters containing g; r alone still permits an unmarked edge. -/
def markedAutomaton : TGBA String where
  states := {0}
  initialStates := {0}
  successors := (∅ : Std.HashMap Nat (Array (TGBA.Transition String))).insert 0
    #[{ target := 0, positiveProps := {"g"}, negativeProps := ∅, acceptMarks := {0} },
      { target := 0, positiveProps := ∅, negativeProps := {"g"}, acceptMarks := ∅ }]
  numAcceptSets := 1

def keepR (letter : Std.HashSet String) : Bool := letter.contains "r"

/-- Check the chosen concrete edge, not just the common pair of endpoints. -/
def validMarkedRealization (steps : Array (LStep String Nat)) : Bool :=
  let e := (TGBAProduct.keptEdgeWitness markedAutomaton (fun _ => steps) noLabel keepR [0]).markEdge
    (0, 0) (0, 0) 0
  steps.contains e.2.1 && e.1 == 0 && e.2.1.2 == 0 &&
    e.2.2.1 == 0 && e.2.2.2.target == 0 &&
    keepR e.2.1.1 && e.2.1.1.contains "g" && e.2.2.2.acceptMarks.contains 0 &&
    (markedAutomaton.getSuccessors 0).any (fun t =>
      t.target == e.2.2.2.target && t.positiveProps == e.2.2.2.positiveProps &&
        t.negativeProps == e.2.2.2.negativeProps && t.acceptMarks == e.2.2.2.acceptMarks) &&
    TGBAProduct.transCompatible e.2.2.2 e.2.1.1

def checkRegion (name : String) (steps : Array (LStep String Nat)) (accepting : Bool) : IO (List Bool) := do
  let succs := TGBAProduct.keptSuccs markedAutomaton (fun _ => steps) noLabel keepR
  let marks := TGBAProduct.keptEdgeMarks markedAutomaton (fun _ => steps) noLabel keepR
  let expand := TGBAProduct.keptExpand markedAutomaton (fun _ => steps) noLabel keepR
  let p := (0, 0)
  let a ← check s!"{name}: the ambient edge carries mark 0"
    ((TGBAProduct.edgeMarks markedAutomaton (fun _ => steps) noLabel p p).contains 0)
  let b ← check s!"{name}: the region still contains a self-loop" ((succs p).contains p)
  let c ← check s!"{name}: only in-region realizations contribute mark 0"
    ((marks p p).contains 0 == accepting)
  let expanded := expand p
  let d ← check s!"{name}: the fused expansion has the same restricted marks"
    (expanded.1.contains p && expanded.1.size == expanded.2.1.size &&
      expanded.2.1.all (fun ms => ms.contains 0 == accepting))
  let result := dijkstraCheck succs [p] marks expand 1
  let e ← check s!"{name}: accepting cycle exists exactly when a joint realization exists"
    (isEmptyResult result == !accepting)
  let f ← check s!"{name}: FG r and GF g use the same system steps"
    (isEmptyResult (modelCheckTGBADisjunct (.ff : Formula String) (.prop "r") [.prop "g"]
      [0] (fun _ => steps) noLabel) == !accepting)
  -- The fail-fast deliberately over-approximates marks across steps: true means "keep checking",
  -- not that the region and mark can share a realization (FairCheck's Feasibility section).
  let g ← check s!"{name}: the conservative prepass keeps this candidate for exact checking"
    (disjunctFeasible (.prop "r") [.prop "g"] [0] (fun _ => steps) noLabel)
  let fast ← check s!"{name}: the fast route still checks the exact restricted product"
    (isEmptyResult (modelCheckTGBADisjunctFast (.ff : Formula String) (.prop "r") [.prop "g"]
      [0] (fun _ => steps) noLabel) == !accepting)
  if accepting then
    let h ← check s!"{name}: the marked witness chooses a real edge carrying both r and g"
      (validMarkedRealization steps)
    let witness ← checkWitness succs marks 1 result
    return [a, b, c, d, e, f, g, fast, h] ++ witness
  else
    return [a, b, c, d, e, f, g, fast]

def report : IO Unit :=
  verdict "edge letters and region-restricted realizations" do
    let basics ← terminalCases.mapM fun (title, φ, expected) =>
      check title (isEmptyResult (modelCheckTGBA φ [0] terminalSteps terminalLabel) == expected)
    let parallel ← [separate, separate.reverse].mapM fun steps => do
      let a ← check "parallel letters are not unioned into a fictitious r-and-g step"
        (isEmptyResult (modelCheckTGBA (.always (.not (.and (.atom "r") (.atom "g"))))
          [0] (fun _ => steps) noLabel))
      let b ← check "every parallel step contains r or g"
        (isEmptyResult (modelCheckTGBA (.always (.or (.atom "r") (.atom "g")))
          [0] (fun _ => steps) noLabel))
      let c ← check "the g-only loop refutes GF r in either successor order"
        (!isEmptyResult (modelCheckTGBA (.always (.eventually (.atom "r")))
          [0] (fun _ => steps) noLabel))
      return [a, b, c]
    let negative ← checkRegion "separate edges" separate false
    let reordered ← checkRegion "separate edges reversed" separate.reverse false
    let positive ← checkRegion "joint edge added" together true
    let emptySuccs := TGBAProduct.keptSuccs markedAutomaton (fun _ => separate) noLabel (fun _ => false)
    let emptyMarks := TGBAProduct.keptEdgeMarks markedAutomaton (fun _ => separate) noLabel (fun _ => false)
    let emptyExpand := TGBAProduct.keptExpand markedAutomaton (fun _ => separate) noLabel (fun _ => false)
    let emptyRegion ← check "an empty region does not acquire a totalizing self-loop"
      ((emptySuccs (0, 0)).isEmpty &&
        isEmptyResult (dijkstraCheck emptySuccs [(0, 0)] emptyMarks emptyExpand 0))
    return basics ++ parallel.flatten ++ negative ++ reordered ++ positive ++ [emptyRegion]

#eval report

end LTLLib.Tests.EdgeLabels
