/-
  Concrete node type for the GPVW95 tableau construction (Gerth et al. 1995).

  Defines:
  - `ExpansionNode`: a node record with `old`/`new`/`next` formula sets and an `incoming` predecessor-name set
  - `ExpansionNode.sameSignature`: duplicate detection via (old, next) equality, plus lemmas relating it to `old`-set
    containment
  - `ExpansionNode.toNodeData`: bridge to the abstract `NodeData` spec
-/

import Std
import LTLLib.LTL
import LTLLib.LTLtoGBA.FSet
import LTLLib.LTLtoGBA.AbstractSpec.ExpansionSpec

namespace LTLLib

/-- A node in the LTL-to-GBA graph construction.

The type parameter `S` abstracts the set container used for `old` and `next`. Instantiate with `Std.HashSet (NNF α)` or
`Std.TreeSet (NNF α)` via `FSet`. -/
structure ExpansionNode (α : Type u) (S : Type v) where
  name : Nat
  -- predecessor node names
  incoming : Std.HashSet Nat
  -- Formulas yet to be expanded (worklist)
  new : List (NNF α)
  -- Already expanded formulas (constraints on current state)
  old : S
  -- Formulas that must hold in successor states
  next : S

namespace ExpansionNode

variable {α} {S : Type v} [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)]

/-- Check if two nodes have the same (old, next) signature. -/
def sameSignature (n₁ n₂ : ExpansionNode α S) : Bool :=
  FSet.setEq n₁.old n₂.old && FSet.setEq n₁.next n₂.next

omit [BEq (NNF α)] [LawfulBEq (NNF α)] in
/-- Under `sameSignature`, `n₂.old` is contained in `n₁.old`. -/
theorem sameSignature_old_left (n₁ n₂ : ExpansionNode α S)
    (h : n₁.sameSignature n₂ = true)
    (ψ : NNF α) (hψ : FSet.contains n₂.old ψ = true) : FSet.contains n₁.old ψ = true := by
  unfold sameSignature at h
  have h_old := (Bool.and_eq_true_iff.mp h).1
  exact ((FSet.setEq_correct n₁.old n₂.old).mp h_old).2 ψ hψ

omit [BEq (NNF α)] [LawfulBEq (NNF α)] in
/-- Under `sameSignature`, `n₁.old` is contained in `n₂.old`. -/
theorem sameSignature_old_right (n₁ n₂ : ExpansionNode α S)
    (h : n₁.sameSignature n₂ = true)
    (ψ : NNF α) (hψ : FSet.contains n₁.old ψ = true) : FSet.contains n₂.old ψ = true := by
  unfold sameSignature at h
  have h_old := (Bool.and_eq_true_iff.mp h).1
  exact ((FSet.setEq_correct n₁.old n₂.old).mp h_old).1 ψ hψ

/-- A formula is "in" a node's old set. -/
abbrev oldHas (n : ExpansionNode α S) (ψ : NNF α) : Prop := FSet.contains n.old ψ

/-- A formula is "in" a node's next set. -/
abbrev nextHas (n : ExpansionNode α S) (ψ : NNF α) : Prop := FSet.contains n.next ψ

/-- A formula is "reachable": Either already processed (old) or pending (new). -/
def reachable (n : ExpansionNode α S) (ψ : NNF α) : Prop :=
  FSet.contains n.old ψ ∨ ψ ∈ n.new

/-- Convert a computational node to its abstract representation. -/
def toNodeData (n : ExpansionNode α S) : NodeData α where
  name := n.name
  incoming k := n.incoming.contains k
  old ψ := FSet.contains n.old ψ
  next ψ := FSet.contains n.next ψ

end ExpansionNode

end LTLLib
