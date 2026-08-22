/-
  GBA construction from the expanded node graph.

  Given the output of `createGraph` (an ExpandState containing all
  finished nodes), this module constructs a GBA with:
  - States = node names
  - Edges based on incoming relationships
  - Initial states = nodes with expand_init ∈ incoming
  - Acceptance sets from Until-subformulas
  - Labeling from positive/negative atoms in node `old` sets
-/

import LTLLib.GBA
import LTLLib.LTLtoGBA.Expand
import LTLLib.LTL

namespace LTLLib

variable {α} {S : Type v} [FSet (NNF α) S]

/-- Collect all state names (the keys of the finished node graph). -/
def buildStates (nodes : Std.HashMap Nat (GBANode α S)) : Std.HashSet Nat :=
  nodes.fold (init := Std.HashSet.emptyWithCapacity nodes.size) fun acc name _ =>
    acc.insert name

/-- Build the successor (adjacency) map from the node graph.

For each node q', and for each predecessor name p ∈ incoming(q'),
we add an edge p → q'. -/
def buildSuccessors (nodes : Std.HashMap Nat (GBANode α S))
    : Std.HashMap Nat (Array Nat) :=
  nodes.fold (init := Std.HashMap.emptyWithCapacity nodes.size) fun succMap _ node =>
    -- For each predecessor p in node.incoming, add edge p → node.name
    node.incoming.fold (init := succMap) fun succMap predName =>
      -- Only add if predName is actually a node (or expandInit for initial states)
      let existing := succMap[predName]?.getD #[]
      succMap.insert predName (existing.push node.name)

/-- Build acceptance sets from Until-subformulas.

For each Until-subformula (μ U η) of φ:
  F_{μ,η} = {q.name | q ∈ nodes, (μ U η) ∉ old(q) ∨ η ∈ old(q)}

A node is in the acceptance set if:
- The Until formula is NOT in its `old` set (obligation doesn't apply), OR
- The right-hand side η IS in its `old` set (obligation is satisfied). -/
def buildAcceptSets (nodes : Std.HashMap Nat (GBANode α S))
    (untilSubs : List (NNF α × NNF α))
    : Array (Std.HashSet Nat) :=
  untilSubs.toArray.map fun (μ, η) =>
    let untilFormula := NNF.until μ η
    nodes.fold (init := Std.HashSet.emptyWithCapacity nodes.size) fun acc _ node =>
      -- q ∈ F_{μ,η} iff (μ U η) ∉ old(q) ∨ η ∈ old(q)
      if !FSet.contains node.old untilFormula || FSet.contains node.old η then
        acc.insert node.name
      else acc

/-- Build labeling map: for each node, extract the positive and negative
atomic propositions from its `old` set. -/
def buildLabeling [BEq α] [Hashable α] (nodes : Std.HashMap Nat (GBANode α S))
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
def buildInitialStates (nodes : Std.HashMap Nat (GBANode α S)) : Std.HashSet Nat :=
  nodes.fold (init := Std.HashSet.emptyWithCapacity 4) fun initSet _ node =>
    if node.incoming.contains expandInit then initSet.insert node.name
    else initSet

/-- Construct a GBA from the expanded node graph and the original LTL formula.

The steps are:
1. Collect all state names
2. Identify initial states (incoming contains expandInit)
3. Build successor map from incoming relationships
4. Build acceptance sets from Until-subformulas
5. Build labeling from positive/negative atoms -/
def constructGBA [BEq α] [Hashable α] (φ : NNF α) (expandResult : ExpandState α S) : GBA α :=
  let nodes := expandResult.nodes
  let untilSubs := φ.untilSubformulas  -- may contain duplicates, but that's OK for correctness
  {
    states := buildStates nodes
    initialStates := buildInitialStates nodes
    successors := buildSuccessors nodes
    labeling := buildLabeling nodes
    acceptSets := buildAcceptSets nodes untilSubs
  }

end LTLLib
