/-
  GBA construction from the expanded node graph.

  Corresponds to `create_gba_from_nodes` in LTL_to_GBA.thy, and the
  helper functions `build_succ`, `build_F`, and `pn_map` from
  LTL_to_GBA_impl.thy.

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

variable {S : Type} [FSet (NNF α) S]

/-- Build the successor (adjacency) map from the node graph.

Corresponds to `build_succ` in LTL_to_GBA_impl.thy:
  succ_of_E(q) = {q' | (q, q') ∈ E}
where E = {(q, q') | q∈qs ∧ q'∈qs ∧ name q ∈ incoming q'}.

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

Corresponds to `build_F nds φ` in LTL_to_GBA_impl.thy:
  build_F nds φ = (λ(μ,η). name ` {q ∈ nds. (Until_ltlr μ η ∈ old q → η ∈ old q)})
                  ` until_frmlsr φ

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
atomic propositions from its `old` set.

Corresponds to `pn_map` in LTL_to_GBA_impl.thy:
  pn_map(q) = (P_q, N_q)
  where P_q = {p | prop(p) ∈ old(q)}
        N_q = {p | nprop(p) ∈ old(q)} -/
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

/-- Identify initial states: nodes whose `incoming` set contains `expandInit` (= 0).

Corresponds to `g_V0 = {q∈qs. expand_init ∈ incoming q}` in `create_gba_from_nodes`
(LTL_to_GBA.thy). -/
def buildInitialStates (nodes : Std.HashMap Nat (GBANode α S)) : Std.HashSet Nat :=
  nodes.fold (init := Std.HashSet.emptyWithCapacity 4) fun initSet _ node =>
    if node.incoming.contains expandInit then initSet.insert node.name
    else initSet

/-- Construct a GBA from the expanded node graph and the original LTL formula.

Corresponds to `create_gba_from_nodes φ qs` in LTL_to_GBA.thy, combined with
the renaming phase `gba_rename_ext` that maps node objects to node names.

The steps are:
1. Collect all state names
2. Identify initial states (incoming contains expandInit)
3. Build successor map from incoming relationships
4. Build acceptance sets from Until-subformulas
5. Build labeling from positive/negative atoms -/
def constructGBA [BEq α] [Hashable α] (φ : NNF α) (expandResult : ExpandState α S) : GBA α :=
  let nodes := expandResult.nodes
  let allStates := nodes.fold
    (init := Std.HashSet.emptyWithCapacity nodes.size) fun acc name _ =>
      acc.insert name
  let untilSubs := φ.untilSubformulas  -- may contain duplicates, but that's OK for correctness
  {
    states := allStates
    initialStates := buildInitialStates nodes
    successors := buildSuccessors nodes
    labeling := buildLabeling nodes
    acceptSets := buildAcceptSets nodes untilSubs
  }

end LTLLib
