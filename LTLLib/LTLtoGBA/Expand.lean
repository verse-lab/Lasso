/-
  Gerth et al.'s expand/createGraph algorithm for LTL-to-GBA conversion.

  This is the core algorithm that converts an LTL formula into a graph of nodes,
  which is then used to construct a Generalized Büchi Automaton.

  The algorithm is a recursive worklist procedure:
  - Nodes have a `new` set (formulas to expand), `old` set (already expanded),
    and `next` set (obligations for successor states).
  - When `new` is empty: either merge with an existing node that has the same
    (old, next) signature, or create a successor node.
  - When `new` is non-empty: pick a formula and case-split based on its structure.

  Corresponds to `expand_body` / `expand` in LTL_to_GBA.thy (lines 232-280),
  and `create_graph` (the entry point that calls expand with the initial node).
-/

import LTLLib.LTLtoGBA.Node

namespace LTLLib

open NNF

/-! ## Expansion helper functions

Correspond to `new1`, `next1`, `new2` in LTL_to_GBA.thy (lines 112-129).
These define how each temporal operator is decomposed during node expansion.
-/

/-- First set of new formulas when expanding a formula.
Corresponds to `new1` in LTL_to_GBA.thy (lines 112-117).
  new1 (μ ∧ ψ) = {μ, ψ}
  new1 (μ U ψ) = {μ}       -- take the "continue" branch
  new1 (μ R ψ) = {ψ}       -- take the "continue" branch
  new1 (μ ∨ ψ) = {μ}       -- take the first disjunct
  new1 _       = {} -/
def new1 : NNF α → List (NNF α)
  | .and μ ψ => [μ, ψ]
  | .until μ _ => [μ]
  | .release _ ψ => [ψ]
  | .or μ _ => [μ]
  | _ => []

/-- Next-state formulas when expanding a formula.
Corresponds to `next1` in LTL_to_GBA.thy (lines 119-123).
  next1 (X ψ)   = {ψ}
  next1 (μ U ψ) = {μ U ψ}  -- Until obligation carries to next state
  next1 (μ R ψ) = {μ R ψ}  -- Release obligation carries to next state
  next1 _       = {} -/
def next1 : NNF α → List (NNF α)
  | .next ψ => [ψ]
  | f@(.until _ _) => [f]
  | f@(.release _ _) => [f]
  | _ => []

/-- Second set of new formulas for non-deterministic expansion.
Corresponds to `new2` in LTL_to_GBA.thy (lines 125-129).
  new2 (μ U ψ) = {ψ}       -- take the "satisfy now" branch
  new2 (μ R ψ) = {μ, ψ}    -- take the "release now" branch
  new2 (μ ∨ ψ) = {ψ}       -- take the second disjunct
  new2 _       = {} -/
def new2 : NNF α → List (NNF α)
  | .until _ ψ => [ψ]
  | .release μ ψ => [μ, ψ]
  | .or _ ψ => [ψ]
  | _ => []

/-! ## Expand State and Algorithm -/

/-- Mutable state maintained during graph expansion.

- `nextName`: Counter for generating fresh node names. Monotonically increasing.
  Corresponds to `expand_new_name` in LTL_to_GBA.thy (line 135), which is `Suc`.
- `nodes`: Map from node name to finished (fully expanded) node.
  Corresponds to the `ns` (node set) parameter threaded through `expand`. -/
structure ExpandState (α : Type u) (S : Type v) where
  nextName : Nat
  nodes : Std.HashMap Nat (GBANode α S)
deriving Inhabited

/-- The special "init" node name, used as the incoming marker for initial states.
Corresponds to `expand_init ≡ 0` in LTL_to_GBA.thy (line 134). -/
def expandInit : Nat := 0

variable {S : Type v} [FSet (NNF α) S]

/-- Generate a fresh node name and advance the counter.
Corresponds to `expand_new_name ≡ Suc` in LTL_to_GBA.thy (line 135). -/
def freshName (st : ExpandState α S) : Nat × ExpandState α S :=
  (st.nextName, { st with nextName := st.nextName + 1 })

/-- Find an existing node with the same (old, next) signature.
Returns the node name if found.

Corresponds to the check `∃n'∈ns. old n' = old n ∧ next n' = next n`
in `expand_body` (LTL_to_GBA.thy, line 236). -/
def findDuplicate (st : ExpandState α S) (node : GBANode α S) : Option Nat :=
  -- Search through all finished nodes for one with matching signature
  st.nodes.fold (init := none) fun acc name n =>
    match acc with
    | some _ => acc
    | none => if n.sameSignature node then some name else none

/-- Merge incoming edges of `node` into an existing node with matching signature.
Corresponds to `upd_incoming n ns` in LTL_to_GBA.thy (lines 153-161).
  upd_incoming n ns = (λn'. if old n' = old n ∧ next n' = next n
                            then n'⟨incoming := incoming n ∪ incoming n'⟩
                            else n') ` ns -/
def mergeIncoming (st : ExpandState α S) (node : GBANode α S) (targetName : Nat)
    : ExpandState α S :=
  match st.nodes[targetName]? with
  | some target =>
    let merged := { target with incoming := node.incoming.fold (init := target.incoming) fun acc x => acc.insert x }
    { st with nodes := st.nodes.insert targetName merged }
  | none => st  -- should not happen if findDuplicate returned this name

/-- Check if a formula is a proposition (prop or nprop).
Corresponds to the check `∃q. φ = prop⁼(q) ∨ φ = nprop⁼(q)`
in `expand_body` (LTL_to_GBA.thy, line 251). -/
def isLiteral : NNF α → Bool
  | .prop _ | .nprop _ => true
  | _ => false

/-- Get the negation of a literal for contradiction checking.
Corresponds to `not⁼ φ` in `expand_body` (LTL_to_GBA.thy, line 252). -/
def negateLiteral : NNF α → NNF α
  | .prop a => .nprop a
  | .nprop a => .prop a
  | f => f  -- should not be called on non-literals

/-- Check if a formula is deterministic (And or Next).
Corresponds to the check `∃ν μ. (φ = ν and⁼ μ) ∨ (φ = X⁼ ν)`
in `expand_body` (LTL_to_GBA.thy, line 256). -/
def isDeterministic : NNF α → Bool
  | .and _ _ | .next _ => true
  | _ => false

/-- Add formulas to a node's `new` set, skipping those already in `old`.
This avoids re-expanding formulas that have already been processed. -/
def addToNew (node : GBANode α S) (formulas : List (NNF α)) : List (NNF α) :=
  let existing := node.old
  formulas.foldl (init := node.new) fun acc f =>
    if FSet.contains existing f then acc else f :: acc

/-- Add formulas to a set. -/
def addAllToSet (s : S) (fs : List (NNF α)) : S :=
  fs.foldl FSet.insert s

/-- The main expand algorithm.

Corresponds to `expand_body` / `expand` in LTL_to_GBA.thy (lines 232-280).

This is a recursive worklist algorithm:
1. If `node.new` is empty:
   a. If a node with the same (old, next) exists: merge incoming edges.
   b. Otherwise: add node to finished set, create successor node with
      `new := node.next`, and continue.
2. If `node.new` is non-empty: pick the first formula and case-split.

Defined using `partial_fixpoint` with `Option` return type, which provides:
- Equational rewrite rules (`rw [expand]`)
- A `partial_correctness` theorem for inductive reasoning
without requiring a termination proof. -/
def expand (node : GBANode α S) (st : ExpandState α S)
    : Option (Nat × ExpandState α S) := do
  if node.new.isEmpty then
    match findDuplicate st node with
    | some existingName =>
      pure (node.name, mergeIncoming st node existingName)
    | none =>
      let st := { st with nodes := st.nodes.insert node.name node }
      let (succName, st) := freshName st
      let successor : GBANode α S := {
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
        pure (node.name, st)
      else
        expand { node with old := FSet.insert node.old φ } st
    else if φ matches .tt then
      expand { node with old := FSet.insert node.old φ } st
    else if φ matches .ff then
      pure (node.name, st)
    else if isDeterministic φ then
      expand {
        node with
        new := addToNew node (new1 φ)
        old := FSet.insert node.old φ
        next := addAllToSet node.next (next1 φ)
      } st
    else do
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

/-- Create the full node graph from an LTL formula.

Corresponds to `create_graph` in LTL_to_GBA.thy:
  definition create_graph :: "'a frml ⇒ 'a node set nres" where
    "create_graph φ ≡ do {
      (_, nds) ← expand (⟨name = expand_new_name expand_init,
                           incoming = {expand_init},
                           new = {φ}, old = {}, next = {}⟩, {});
      RETURN nds }"

The initial node has:
- `name = expand_new_name expand_init = 1` (Suc 0)
- `incoming = {expand_init} = {0}` (marks it as reachable from init)
- `new = {φ}` (the formula to check)
- `old = {}, next = {}` (empty)
-/
def createGraph (φ : NNF α) : Option (ExpandState α S) :=
  let initNode : GBANode α S := {
    name := 1  -- expand_new_name expand_init = Suc 0 = 1
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

end LTLLib
