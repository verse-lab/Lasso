module

/-
  Tests `nestedDFST_fuel` against `dijkstraCheck` on the degeneralized `ltl3ba` automaton of each negated formula:
  the emptiness verdicts must agree, and every `.nonEmpty` witness must pass `checkWitness`.

  Covers zero marks, one mark, two marks (a round-robin before degeneralization, so the `TBA` has back edges and
  tree-edge marks), `p U q`, and `p ∧ ¬p`. Two hand-built graphs exercise the branches no formula above reaches,
  a marked tree edge closed only after a further search, and a marked forward edge onto a finished state.

  Sections:
  - Adversarial hand-built graphs
-/
import LTLLib.Degeneralization.DegeneralBridge
import LTLLib.LTLtoTGBA.Pipeline
import LTLLib.NestedDFS.NestedDFST
import LTLLib.SCC.DijkstraSCC
import LTLLibTests.TestUtil
meta import LTLLib.Degeneralization.DegeneralBridge
meta import LTLLib.LTLtoTGBA.Pipeline
meta import LTLLib.NestedDFS.NestedDFST
meta import LTLLib.SCC.DijkstraSCC
meta import LTLLibTests.TestUtil

namespace LTLLib.Tests.NestedDFST

open LTLLib LTLLib.Tests

def tbaOf (φ : Formula String) : Option (TBA String) := (ltl3ba (φ.toNNF false)).map TGBA.degeneralize

def bareEmpty (tba : TBA String) : Bool :=
  -- `dijkstraCheck` takes the fused expansion as well as the pointwise `edgeMarks` (`EdgeLabels.md` §9);
  -- for a materialized `TBA` the two are the same pair of lookups.
  isEmptyResult (dijkstraCheck tba.succStates tba.initialStates.toList tba.edgeMarks
    -- no options on this route, so the §13.17 option-bit payload is empty
    (fun s => let out := tba.succStates s; (out, out.map (tba.edgeMarks s), #[])) tba.numAcceptSets)

def ndfsResult (tba : TBA String) : Option (EmptinessResult TBAState) :=
  nestedDFST_fuel tba.initialStates.toList tba.succStates tba.cachedEdgeMarks 100000

/-- `nestedDFST_fuel`'s emptiness verdict agrees with `dijkstraCheck`'s, and a `.nonEmpty` witness passes `checkWitness`. -/
def agrees (φ : Formula String) : IO (List Bool) := do
  match tbaOf φ with
  | none => return [false]
  | some tba =>
    match ndfsResult tba with
    | none => return [false]
    | some r =>
      let a ← check "agrees with dijkstraCheck on emptiness" (isEmptyResult r == bareEmpty tba)
      let bs ← if isEmptyResult r then pure [] else
        checkWitness tba.succStates tba.edgeMarks tba.numAcceptSets r
      return a :: bs

def report : IO Unit :=
  verdict "nestedDFST_fuel agrees with dijkstraCheck, and its witnesses check out" do
    let a ← agrees (.atom "p")
    let b ← agrees (.eventually (.atom "p"))
    let c ← agrees (.always (.eventually (.atom "p")))
    let d ← agrees (.and (.always (.eventually (.atom "p"))) (.always (.eventually (.atom "q"))))
    let e ← agrees (.until (.atom "p") (.atom "q"))
    let f ← agrees (.and (.atom "p") (.not (.atom "p")))
    return (a ++ b ++ c ++ d ++ e ++ f)

#eval report

/-! ## Adversarial hand-built graphs -/

/-- The unmarked cycle `0 → 1 → 2 → 0` plus a marked shortcut `0 → 2`. `1`'s subtree finishes before `0` examines
`0 → 2`, a marked forward edge onto a finished state. -/
def forwardEdgeSuccs : Nat → Array Nat
  | 0 => #[1, 2]
  | 1 => #[2]
  | 2 => #[0]
  | _ => #[]

def forwardEdgeMarks (s t : Nat) : Std.HashSet Nat :=
  if s == 0 && t == 2 then (Std.HashSet.emptyWithCapacity 1).insert 0 else Std.HashSet.emptyWithCapacity 0

/-- `0 → 1 → 2 → 0` with the mark on the tree edge `0 → 1`, so the back-edge shortcut never fires and `1`'s postorder
search descends through `2` back to `0`. -/
def postorderSuccs : Nat → Array Nat
  | 0 => #[1]
  | 1 => #[2]
  | 2 => #[0]
  | _ => #[]

def postorderMarks (s t : Nat) : Std.HashSet Nat :=
  if s == 0 && t == 1 then (Std.HashSet.emptyWithCapacity 1).insert 0 else Std.HashSet.emptyWithCapacity 0

def graphReport : IO Unit :=
  verdict "outerDFST_fuel's postorder and forward-edge branches produce genuine witnesses" do
    let a ← match nestedDFST_fuel [0] forwardEdgeSuccs forwardEdgeMarks 1000 with
      | some r => checkWitness forwardEdgeSuccs forwardEdgeMarks 1 r
      | none => check "forward-edge graph: ran out of fuel" false >>= fun b => pure [b]
    let b ← match nestedDFST_fuel [0] postorderSuccs postorderMarks 1000 with
      | some r => checkWitness postorderSuccs postorderMarks 1 r
      | none => check "postorder graph: ran out of fuel" false >>= fun b => pure [b]
    return (a ++ b)

#eval graphReport

end LTLLib.Tests.NestedDFST
