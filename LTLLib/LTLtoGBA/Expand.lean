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
structure ExpandState (α : Type) [BEq α] [Hashable α] where
  nextName : Nat
  nodes : Std.HashMap Nat (GBANode α)
deriving Inhabited

/-- The special "init" node name, used as the incoming marker for initial states.
Corresponds to `expand_init ≡ 0` in LTL_to_GBA.thy (line 134). -/
def expandInit : Nat := 0

variable [BEq α] [Hashable α]

/-- Generate a fresh node name and advance the counter.
Corresponds to `expand_new_name ≡ Suc` in LTL_to_GBA.thy (line 135). -/
def freshName (st : ExpandState α) : Nat × ExpandState α :=
  (st.nextName, { st with nextName := st.nextName + 1 })

/-- Find an existing node with the same (old, next) signature.
Returns the node name if found.

Corresponds to the check `∃n'∈ns. old n' = old n ∧ next n' = next n`
in `expand_body` (LTL_to_GBA.thy, line 236). -/
def findDuplicate (st : ExpandState α) (node : GBANode α) : Option Nat :=
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
def mergeIncoming (st : ExpandState α) (node : GBANode α) (targetName : Nat)
    : ExpandState α :=
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
def addToNew (node : GBANode α) (formulas : List (NNF α)) : List (NNF α) :=
  let existing := node.old
  formulas.foldl (init := node.new) fun acc f =>
    if existing.contains f then acc else f :: acc

/-- Add formulas to a HashSet. -/
def addAllToSet (s : Std.HashSet (NNF α)) (fs : List (NNF α))
    : Std.HashSet (NNF α) :=
  fs.foldl Std.HashSet.insert s

/-- The main expand algorithm.

Corresponds to `expand_body` / `expand` in LTL_to_GBA.thy (lines 232-280).

This is a recursive worklist algorithm:
1. If `node.new` is empty:
   a. If a node with the same (old, next) exists: merge incoming edges.
   b. Otherwise: add node to finished set, create successor node with
      `new := node.next`, and continue.
2. If `node.new` is non-empty: pick the first formula and case-split.

The function is `partial` because termination depends on the finiteness of
the subformula closure, which we don't prove here. -/
partial def expand (node : GBANode α) (st : ExpandState α)
    : Nat × ExpandState α :=
  if node.new.isEmpty then
    -- All formulas expanded
    -- Corresponds to `if new n = {}` branch in expand_body (line 235)
    match findDuplicate st node with
    | some existingName =>
      -- Found a node with the same (old, next) signature: merge incoming edges.
      -- Corresponds to `RETURN (name n, upd_incoming n ns)` (line 237)
      (node.name, mergeIncoming st node existingName)
    | none =>
      -- No duplicate: add this node to finished set, create successor.
      -- Corresponds to lines 239-247 in expand_body.
      let st := { st with nodes := st.nodes.insert node.name node }
      let (succName, st) := freshName st
      let successor : GBANode α := {
        name := succName
        incoming := Std.HashSet.emptyWithCapacity 4 |>.insert node.name
        new := node.next.fold (init := []) fun acc f => f :: acc
        old := Std.HashSet.emptyWithCapacity 8
        next := Std.HashSet.emptyWithCapacity 8
      }
      expand successor st
  else
    -- Pick a formula from `new` to expand
    -- Corresponds to `φ ← SPEC (λx. x∈(new n))` (line 249)
    let φ := node.new.head!
    let node := { node with new := node.new.tail! }

    if isLiteral φ then
      -- Prop or Nprop case
      -- Corresponds to lines 251-253 in expand_body
      if node.old.contains (negateLiteral φ) then
        -- Contradiction: discard this node
        -- Corresponds to `RETURN (name n, ns)` (line 252)
        (node.name, st)
      else
        -- Add to old and continue
        -- Corresponds to `expand (n⟨old := {φ} ∪ old n⟩, ns)` (line 253)
        expand { node with old := node.old.insert φ } st
    else if φ matches .tt then
      -- True: add to old and continue
      -- Corresponds to `if φ = true⁼ then expand (n⟨old := {φ} ∪ old n⟩, ns)` (line 254)
      expand { node with old := node.old.insert φ } st
    else if φ matches .ff then
      -- False: discard this node
      -- Corresponds to `if φ = false⁼ then RETURN (name n, ns)` (line 255)
      (node.name, st)
    else if isDeterministic φ then
      -- Deterministic case: And or Next
      -- Corresponds to lines 256-263 in expand_body
      let newFormulas := new1 φ
      let nextFormulas := next1 φ
      expand {
        node with
        new := addToNew node newFormulas
        old := node.old.insert φ
        next := addAllToSet node.next nextFormulas
      } st
    else
      -- Non-deterministic case: Or, Until, Release
      -- Corresponds to lines 264-273 in expand_body.
      -- Split into two branches:
      --   Branch 1: explore new1(φ) with next1(φ) obligations
      --   Branch 2: explore new2(φ) (using the name returned by branch 1)

      -- Branch 1
      let node1 : GBANode α := {
        node with
        new := addToNew node (new1 φ)
        old := node.old.insert φ
        next := addAllToSet node.next (next1 φ)
      }
      let (nm, st) := expand node1 st

      -- Branch 2 (uses the name counter returned by branch 1)
      let node2 : GBANode α := {
        node with
        name := nm
        new := addToNew node (new2 φ)
        old := node.old.insert φ
      }
      expand node2 st

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
def createGraph (φ : NNF α) : ExpandState α :=
  let initNode : GBANode α := {
    name := 1  -- expand_new_name expand_init = Suc 0 = 1
    incoming := Std.HashSet.emptyWithCapacity 4 |>.insert expandInit
    new := [φ]
    old := Std.HashSet.emptyWithCapacity 8
    next := Std.HashSet.emptyWithCapacity 8
  }
  let initState : ExpandState α := {
    nextName := 2  -- next available name after 1
    nodes := Std.HashMap.emptyWithCapacity 16
  }
  let (_, finalState) := expand initNode initState
  finalState

end LTLLib
