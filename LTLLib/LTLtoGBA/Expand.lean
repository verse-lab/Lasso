/-
  The GPVW95 (Gerth et al. 1995) `expand`/`createGraph` tableau construction: a recursive worklist algorithm converting
  an LTL formula into a graph of `ExpansionNode`s, later assembled into a GBA by `ToGBA.lean`.

  Nodes carry a `new` set (formulas to expand), an `old` set (already expanded), and a `next` set (obligations for
  successor states). When `new` is empty, expansion either merges with an existing node of the same (old, next)
  signature or spawns a successor node from `next`. When `new` is non-empty, it pops one formula and case-splits on its structure.

  Defines:
  - `new1`, `new2`, `next1`: the per-connective subgoal sets used by `expand`
  - `ExpandState`: the worklist algorithm's mutable state (fresh-name counter and finished-node map)
  - `findDuplicate`, `mergeIncoming`, `addToNew`, `addAllToSet`: expansion helpers
  - `expand`: the recursive tableau expansion
  - `createGraph`: runs `expand` from the initial node for a formula
  - `ExpandState.toNodes`: bridges a finished `ExpandState` to the abstract `NodeData` spec

  ## Sections
  - Expansion helper functions
  - Expand State and Algorithm
-/

import LTLLib.LTLtoGBA.ExpansionNode
import LTLLib.LTLtoGBA.AbstractSpec.ExpansionSpec

namespace LTLLib

open NNF

/-! ## Expansion helper functions -/

/-- First set of new formulas when expanding a formula. -/
def new1 {α} : NNF α → List (NNF α)
  | .and μ ψ => [μ, ψ]
  | .until μ _ => [μ]  -- take the "continue" branch
  | .release _ ψ => [ψ]  -- take the "continue" branch
  | .or μ _ => [μ]  -- take the first disjunct
  | _ => []

/-- Next-state formulas when expanding a formula. -/
def next1 {α} : NNF α → List (NNF α)
  | .next ψ => [ψ]
  | f@(.until _ _) => [f]  -- Until obligation carries to next state
  | f@(.release _ _) => [f]  -- Release obligation carries to next state
  | _ => []

/-- Second set of new formulas for non-deterministic expansion. -/
def new2 {α} : NNF α → List (NNF α)
  | .until _ ψ => [ψ]  -- take the "satisfy now" branch
  | .release μ ψ => [μ, ψ]  -- take the "release now" branch
  | .or _ ψ => [ψ]  -- take the second disjunct
  | _ => []

/-! ## Expand State and Algorithm -/

/-- Mutable state maintained during graph expansion. -/
structure ExpandState (α : Type u) (S : Type v) where
  nextName : Nat  -- monotonically increasing counter for fresh node names
  nodes : Std.HashMap Nat (ExpansionNode α S)  -- finished (fully expanded) nodes by name
deriving Inhabited

variable {α} {S : Type v} [FSet (NNF α) S]

/-- Generate a fresh node name and advance the counter. -/
def freshName (st : ExpandState α S) : Nat × ExpandState α S :=
  (st.nextName, { st with nextName := st.nextName + 1 })

/-- Find an existing node with the same (old, next) signature. Returns the node name if found. -/
def findDuplicate (st : ExpandState α S) (node : ExpansionNode α S) : Option Nat :=
  st.nodes.fold (init := none) fun acc name n =>
    match acc with
    | some _ => acc
    | none => if n.sameSignature node then some name else none

/-- Merge incoming edges of `node` into an existing node with matching signature. -/
def mergeIncoming (st : ExpandState α S) (node : ExpansionNode α S) (targetName : Nat)
    : ExpandState α S :=
  match st.nodes[targetName]? with
  | some target =>
    let merged := { target with incoming := target.incoming.union node.incoming }
    { st with nodes := st.nodes.insert targetName merged }
  | none => st  -- should not happen if findDuplicate returned this name

/-- Check if a formula is a proposition (prop or nprop). -/
def isLiteral : NNF α → Bool
  | .prop _ | .nprop _ => true
  | _ => false

/-- Get the negation of a literal for contradiction checking. -/
def negateLiteral : NNF α → NNF α
  | .prop a => .nprop a
  | .nprop a => .prop a
  | f => f  -- should not be called on non-literals

/-- Check if a formula is deterministic (And or Next). -/
def isDeterministic : NNF α → Bool
  | .and _ _ | .next _ => true
  | _ => false

/-- Add formulas to a node's `new` set, skipping those already present in `old`. -/
def addToNew (node : ExpansionNode α S) (formulas : List (NNF α)) : List (NNF α) :=
  let existing := node.old
  formulas.foldl (init := node.new) fun acc f =>
    if FSet.contains existing f then acc else f :: acc

/-- Add formulas to a set. -/
def addAllToSet (s : S) (fs : List (NNF α)) : S :=
  fs.foldl FSet.insert s

/-- The recursive worklist expansion algorithm (GPVW95 tableau construction). -/
def expand (node : ExpansionNode α S) (st : ExpandState α S)
    : Option (Nat × ExpandState α S) := do
  if node.new.isEmpty then
    -- node fully expanded: merge with a duplicate, or finish it and spawn a successor from `next`
    match findDuplicate st node with
    | some existingName =>
      pure (node.name, mergeIncoming st node existingName)
    | none =>
      let st := { st with nodes := st.nodes.insert node.name node }
      let (succName, st) := freshName st
      let successor : ExpansionNode α S := {
        name := succName
        incoming := Std.HashSet.emptyWithCapacity 4 |>.insert node.name
        new := FSet.foldl (fun acc f => f :: acc) [] node.next
        old := FSet.empty
        next := FSet.empty
      }
      expand successor st
  else
    let φ := node.new.head!
    let node := { node with new := node.new.tail! }
    if isLiteral φ then
      if FSet.contains node.old (negateLiteral φ) then
        pure (node.name, st)  -- contradicts an existing literal: dead end
      else
        expand { node with old := FSet.insert node.old φ } st
    else if φ matches .tt then
      expand { node with old := FSet.insert node.old φ } st
    else if φ matches .ff then
      pure (node.name, st)  -- dead end
    else if isDeterministic φ then
      -- deterministic (And/Next): single successor
      expand {
        node with
        new := addToNew node (new1 φ)
        old := FSet.insert node.old φ
        next := addAllToSet node.next (next1 φ)
      } st
    else do
      -- non-deterministic (Or/Until/Release): branch into two successors
      let (nm, st) ← expand {
        node with
        new := addToNew node (new1 φ)
        old := FSet.insert node.old φ
        next := addAllToSet node.next (next1 φ)
      } st
      expand {
        node with
        name := nm
        new := addToNew node (new2 φ)
        old := FSet.insert node.old φ
      } st
partial_fixpoint

/-- Create the full node graph from an LTL formula. -/
def createGraph (φ : NNF α) : Option (ExpandState α S) :=
  let initNode : ExpansionNode α S := {
    name := 1  -- first fresh name after expandInit = 0
    incoming := Std.HashSet.emptyWithCapacity 4 |>.insert expandInit
    new := [φ]
    old := FSet.empty
    next := FSet.empty
  }
  let initState : ExpandState α S := {
    nextName := 2  -- next available name after 1
    nodes := Std.HashMap.emptyWithCapacity 16
  }
  match expand initNode initState with
  | some (_, finalState) => some finalState
  | none => none


/-- Convert `ExpandState` into abstract spec: a `NodeData` is in the predicate iff it matches some finished node. -/
def ExpandState.toNodes (st : ExpandState α S) : NodeData α → Prop :=
  fun nd => ∃ n, st.nodes[nd.name]? = some n ∧
    (∀ k, nd.incoming k ↔ n.incoming.contains k) ∧
    (∀ ψ, nd.old ψ ↔ FSet.contains n.old ψ) ∧
    (∀ ψ, nd.next ψ ↔ FSet.contains n.next ψ)

end LTLLib
