module

/-
  Concrete node type for the GPVW95 tableau construction (Gerth et al. 1995).

  Defines:
  - `ExpansionNode`: a node record with `old`/`new`/`next` formula sets and an `incoming` predecessor-name set
  - `ExpansionNode.sameSignature`: duplicate detection via (old, next) equality, plus lemmas relating it to `old`-set
    containment
  - `ExpansionNode.sigHash`: order-independent hash of that signature, the bucket key for `findDuplicate`'s index
  - `ExpansionNode.toNodeData`: bridge to the abstract `NodeData` spec

  Sections:
  - Node signatures
  - Signature hashing
  - Abstract bridge
-/

public import Std
public import LTLLib.LTL
public import LTLLib.LTLtoGBA.FSet
public import LTLLib.LTLtoGBA.AbstractSpec.ExpansionSpec

public section

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

/-! ## Node signatures -/

/-- Check if two nodes have the same (old, next) signature. -/
@[expose] def sameSignature (n₁ n₂ : ExpansionNode α S) : Bool :=
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

/-! ## Signature hashing -/

/-- Order-independent hash of a node's `(old, next)` signature, the bucket key `findDuplicate` indexes on.
Summing element hashes is commutative and associative, so this is a function of the two sets and not of
`FSet.toList`'s implementation-defined order. -/
@[expose] def sigHash [Hashable (NNF α)] (n : ExpansionNode α S) : UInt64 :=
  mixHash ((FSet.toList n.old).foldl (fun acc f => acc + hash f) 0)
    (mixHash ((FSet.toList n.next).foldl (fun acc f => acc + hash f) 0) 0x9e3779b97f4a7c15)

omit [BEq (NNF α)] [LawfulBEq (NNF α)] in
/-- Nodes sharing a signature share a hash, which is what makes a hash-bucketed `findDuplicate` exact rather
than merely sound. The converse is not claimed and not needed, a collision only lengthens a bucket. -/
theorem sigHash_eq_of_sameSignature [Hashable (NNF α)] {n₁ n₂ : ExpansionNode α S}
    (h : n₁.sameSignature n₂ = true) : n₁.sigHash = n₂.sigHash := by
  have hrc : ∀ (b : UInt64) (x y : NNF α), (b + hash x) + hash y = (b + hash y) + hash x := by
    intro b x y
    rw [UInt64.add_assoc, UInt64.add_comm (hash x) (hash y), ← UInt64.add_assoc]
  unfold sameSignature at h
  obtain ⟨hold, hnext⟩ := Bool.and_eq_true_iff.mp h
  unfold sigHash
  rw [FSet.foldl_toList_eq_of_setEq _ hrc _ hold, FSet.foldl_toList_eq_of_setEq _ hrc _ hnext]

/-! ## Abstract bridge -/

/-- A formula is "in" a node's old set. -/
abbrev oldHas (n : ExpansionNode α S) (ψ : NNF α) : Prop := FSet.contains n.old ψ

/-- A formula is "in" a node's next set. -/
abbrev nextHas (n : ExpansionNode α S) (ψ : NNF α) : Prop := FSet.contains n.next ψ

/-- A formula is "reachable": Either already processed (old) or pending (new). -/
@[expose] def reachable (n : ExpansionNode α S) (ψ : NNF α) : Prop :=
  FSet.contains n.old ψ ∨ ψ ∈ n.new

/-- Convert a computational node to its abstract representation. -/
def toNodeData (n : ExpansionNode α S) : NodeData α where
  name := n.name
  incoming k := n.incoming.contains k
  old ψ := FSet.contains n.old ψ
  next ψ := FSet.contains n.next ψ

end ExpansionNode

end LTLLib
