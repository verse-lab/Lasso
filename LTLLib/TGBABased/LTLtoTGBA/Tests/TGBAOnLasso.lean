module

/-
  TGBA acceptance of a lasso word, decided on the finite product of the TGBA with the lasso's cycle, independent of
  `ltl3ba` and of the tableau route, the second referee next to `Lasso.evalNNF`. A word is accepted iff some reachable
  product state lies in a non-trivial strongly connected component whose internal edges together carry every mark.
  The graph search is test-only and not proven, hence `partial def`.

  Defines:
  - `ProdState`, `prodSucc`: the product graph
  - `lassoAcceptsTGBA`: the acceptance decision

  Sections:
  - The product graph
  - Strongly connected components and acceptance
-/
public import LTLLib.TGBA
public import LTLLib.TGBABased.LTLtoTGBA.Label
public import LTLLib.TGBABased.LTLtoTGBA.Tests.Lasso

public section

namespace LTLLib.LTLtoTGBA.Tests

/-! ## The product graph -/

/-- `(tgbaState, lassoPosition)`. -/
abbrev ProdState := Nat × Nat

/-- Enabled transitions of `tgba` from `q` at lasso position `i`. -/
def enabledTrans (l : Lasso String) (tgba : TGBA String) (q i : Nat) : Array (TGBA.Transition String) :=
  (tgba.getSuccessors q).filter fun t =>
    Cube.eval ({ pos := t.positiveProps, neg := t.negativeProps } : Cube String) (l.wordAt i)

/-- One product edge, its target and the marks it carries. -/
def prodSucc (l : Lasso String) (tgba : TGBA String) (s : ProdState) : Array (ProdState × Std.HashSet Nat) :=
  (enabledTrans l tgba s.1 s.2).map fun t => ((t.target, l.next s.2), t.acceptMarks)

/-! ## Strongly connected components and acceptance -/

private partial def bfsCollect (succ : ProdState → Array ProdState) :
    List ProdState → Std.HashSet ProdState → Std.HashSet ProdState
  | [], visited => visited
  | s :: rest, visited =>
    if visited.contains s then bfsCollect succ rest visited
    else bfsCollect succ ((succ s).toList ++ rest) (visited.insert s)

/-- Every product state reachable from `start`. -/
def reachableFrom (succ : ProdState → Array ProdState) (start : ProdState) : Std.HashSet ProdState :=
  bfsCollect succ [start] (Std.HashSet.emptyWithCapacity 16)

/-- `s`'s strongly connected component: forward reachable from `s`, and reaching `s` back. -/
def sccOf (succ : ProdState → Array ProdState) (s : ProdState) : Std.HashSet ProdState :=
  (reachableFrom succ s).toList.filter (fun v => (reachableFrom succ v).contains s) |> Std.HashSet.ofList

/-- The marks on the edges internal to `s`'s strongly connected component. -/
def sccMarks (l : Lasso String) (tgba : TGBA String) (s : ProdState) : Std.HashSet Nat :=
  let succUnmarked := fun s' => (prodSucc l tgba s').map (·.1)
  let comp := sccOf succUnmarked s
  comp.toList.foldl (fun acc u =>
    (prodSucc l tgba u).foldl (fun acc (v, marks) => if comp.contains v then acc.union marks else acc) acc)
    (Std.HashSet.emptyWithCapacity 0)

/-- Does `tgba` accept `l`, trying every reachable product state as the witness for its strongly connected component. -/
def lassoAcceptsTGBA (l : Lasso String) (tgba : TGBA String) : Bool :=
  tgba.initialStates.toList.any fun q0 =>
    let succUnmarked := fun s' => (prodSucc l tgba s').map (·.1)
    (reachableFrom succUnmarked (q0, 0)).toList.any fun s =>
      let hasCycle := (succUnmarked s).any fun s' => (reachableFrom succUnmarked s').contains s
      hasCycle && (List.range tgba.numAcceptSets).all fun m => (sccMarks l tgba s).contains m

end LTLLib.LTLtoTGBA.Tests
