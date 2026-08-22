/-
  Node record for the LTL-to-GBA graph construction (Gerth et al.).
-/

import Std
import LTLLib.LTL
import LTLLib.LTLtoGBA.FSet

namespace LTLLib

/-- A node in the LTL-to-GBA graph construction.

The type parameter `S` abstracts the set container used for `old` and `next`.
Instantiate with `Std.HashSet (NNF α)` or `Std.TreeSet (NNF α)` via `FSet`. -/
structure GBANode (α : Type u) (S : Type v) where
  -- Unique identifier
  name : Nat
  -- Set of predecessor node names
  incoming : Std.HashSet Nat
  -- Formulas yet to be expanded (worklist)
  new : List (NNF α)
  -- Already expanded formulas (constraints on current state)
  old : S
  -- Formulas that must hold in successor states
  next : S

namespace GBANode

variable {α} {S : Type v} [FSet (NNF α) S]

/-- Check if two nodes have the same (old, next) signature.
Used to detect duplicate nodes during expansion. -/
def sameSignature (n₁ n₂ : GBANode α S) : Bool :=
  FSet.setEq n₁.old n₂.old && FSet.setEq n₁.next n₂.next

theorem sameSignature_old_left (n₁ n₂ : GBANode α S)
    (h : n₁.sameSignature n₂ = true)
    (ψ : NNF α) (hψ : FSet.contains n₂.old ψ = true) : FSet.contains n₁.old ψ = true := by
  unfold sameSignature at h
  have h_old := (Bool.and_eq_true_iff.mp h).1
  exact ((FSet.setEq_correct n₁.old n₂.old).mp h_old).2 ψ hψ

theorem sameSignature_old_right (n₁ n₂ : GBANode α S)
    (h : n₁.sameSignature n₂ = true)
    (ψ : NNF α) (hψ : FSet.contains n₁.old ψ = true) : FSet.contains n₂.old ψ = true := by
  unfold sameSignature at h
  have h_old := (Bool.and_eq_true_iff.mp h).1
  exact ((FSet.setEq_correct n₁.old n₂.old).mp h_old).1 ψ hψ

end GBANode

end LTLLib
