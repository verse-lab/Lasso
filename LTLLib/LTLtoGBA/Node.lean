/-
  Node record for the LTL-to-GBA graph construction (Gerth et al.).

  Corresponds to the `'a node` record type in LTL_to_GBA.thy (lines 102-107):
    record 'a node =
      name :: node_name          -- unique node identifier (nat)
      incoming :: "node_name set"  -- predecessor nodes
      new :: "'a frml set"         -- formulas to expand
      old :: "'a frml set"         -- expanded formulas
      next :: "'a frml set"        -- formulas for next state
-/

import Std
import LTLLib.LTL
import LTLLib.LTLtoGBA.FSet

namespace LTLLib

/-- A node in the LTL-to-GBA graph construction.

Corresponds to `'a node` in LTL_to_GBA.thy (lines 102-107).

Fields:
- `name`: Unique identifier. Corresponds to `name :: node_name` (a Nat).
- `incoming`: Set of predecessor node names. Corresponds to `incoming :: "node_name set"`.
- `new`: Formulas yet to be expanded (worklist). Corresponds to `new :: "'a frml set"`.
- `old`: Already expanded formulas (constraints on current state).
  Corresponds to `old :: "'a frml set"`.
- `next`: Formulas that must hold in successor states.
  Corresponds to `next :: "'a frml set"`.

The type parameter `S` abstracts the set container used for `old` and `next`.
Instantiate with `Std.HashSet (NNF α)` or `Std.TreeSet (NNF α)` via `FSet`. -/
structure GBANode (α : Type u) (S : Type v) where
  name : Nat
  incoming : Std.HashSet Nat
  new : List (NNF α)
  old : S
  next : S

namespace GBANode

variable {S : Type v} [FSet (NNF α) S]

/-- Check if two nodes have the same (old, next) signature.
Used to detect duplicate nodes during expansion.

Corresponds to the condition `old n' = old n ∧ next n' = next n`
in `expand_body` (LTL_to_GBA.thy, line 236). -/
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
