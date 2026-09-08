/-
  Constructs a `GBA` from a finished GPVW95 (Gerth et al. 1995) expansion graph, i.e. the `ExpandState` produced by
  `createGraph`.

  Defines:
  - `buildStates`, `buildInitialStates`, `buildSuccessors`: states, initial states (marked by `expandInit` in
    `incoming`), and the successor map built from `incoming` edges
  - `buildAcceptSets`: one acceptance set per Until-subformula of φ
  - `buildLabeling`: positive/negative atomic propositions from `old`
  - `constructGBA`: assembles the above into a `GBA`
-/

import LTLLib.GBA
import LTLLib.LTLtoGBA.Expand
import LTLLib.LTL

namespace LTLLib

variable {α} {S : Type v} [FSet (NNF α) S]

/-- Collect all state names (the keys of the finished node graph). -/
def buildStates (nodes : Std.HashMap Nat (ExpansionNode α S)) : Std.HashSet Nat :=
  nodes.fold (init := Std.HashSet.emptyWithCapacity nodes.size) fun acc name _ =>
    acc.insert name

/-- Build the successor (adjacency) map: for each node q' and each predecessor p ∈ incoming(q'), add an
edge p → q'. -/
def buildSuccessors (nodes : Std.HashMap Nat (ExpansionNode α S))
    : Std.HashMap Nat (Array Nat) :=
  nodes.fold (init := Std.HashMap.emptyWithCapacity nodes.size) fun succMap _ node =>
    node.incoming.fold (init := succMap) fun succMap predName =>
      let existing := succMap[predName]?.getD #[]
      succMap.insert predName (existing.push node.name)

/-- Build acceptance sets from Until-subformulas: for each `(μ U η)`, `F_{μ,η} = {q | (μ U η) ∉ old(q) ∨ η ∈ old(q)}`
(obligation absent or satisfied). -/
def buildAcceptSets (nodes : Std.HashMap Nat (ExpansionNode α S))
    (untilSubs : List (NNF α × NNF α))
    : Array (Std.HashSet Nat) :=
  untilSubs.toArray.map fun (μ, η) =>
    let untilFormula := NNF.until μ η
    nodes.fold (init := Std.HashSet.emptyWithCapacity nodes.size) fun acc _ node =>
      if !FSet.contains node.old untilFormula || FSet.contains node.old η then
        acc.insert node.name
      else acc

/-- Build labeling map: for each node, extract the positive and negative atomic propositions from its `old` set. -/
def buildLabeling [BEq α] [Hashable α] (nodes : Std.HashMap Nat (ExpansionNode α S))
    : Std.HashMap Nat (Std.HashSet α × Std.HashSet α) :=
  nodes.fold (init := Std.HashMap.emptyWithCapacity nodes.size) fun labelMap _ node =>
    let (pos, neg) := FSet.foldl
      (fun (pos, neg) formula =>
        match formula with
        | .prop a => (pos.insert a, neg)
        | .nprop a => (pos, neg.insert a)
        | _ => (pos, neg))
      (Std.HashSet.emptyWithCapacity 4, Std.HashSet.emptyWithCapacity 4)
      node.old
    labelMap.insert node.name (pos, neg)

/-- Identify initial states: nodes whose `incoming` set contains `expandInit` (= 0). -/
def buildInitialStates (nodes : Std.HashMap Nat (ExpansionNode α S)) : Std.HashSet Nat :=
  nodes.fold (init := Std.HashSet.emptyWithCapacity 4) fun initSet _ node =>
    if node.incoming.contains expandInit then initSet.insert node.name
    else initSet

/-- Construct a GBA from the expanded node graph and the original LTL formula. -/
def constructGBA [BEq α] [Hashable α] (φ : NNF α) (expandResult : ExpandState α S) : GBA α :=
  let nodes := expandResult.nodes
  let untilSubs := φ.untilSubformulasDedup  -- one acceptance set per distinct Until-subformula
  {
    states := buildStates nodes
    initialStates := buildInitialStates nodes
    successors := buildSuccessors nodes
    labeling := buildLabeling nodes
    acceptSets := buildAcceptSets nodes untilSubs
  }

end LTLLib
