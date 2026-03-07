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

namespace LTLLib

-- CHECK `TreeMap` or `HashMap`?

/-- A node in the LTL-to-GBA graph construction.

Corresponds to `'a node` in LTL_to_GBA.thy (lines 102-107).

Fields:
- `name`: Unique identifier. Corresponds to `name :: node_name` (a Nat).
- `incoming`: Set of predecessor node names. Corresponds to `incoming :: "node_name set"`.
- `new`: Formulas yet to be expanded (worklist). Corresponds to `new :: "'a frml set"`.
- `old`: Already expanded formulas (constraints on current state).
  Corresponds to `old :: "'a frml set"`.
- `next`: Formulas that must hold in successor states.
  Corresponds to `next :: "'a frml set"`. -/
structure GBANode (α : Type) [BEq α] [Hashable α] where
  name : Nat
  incoming : Std.HashSet Nat
  new : List (NNF α)
  old : Std.HashSet (NNF α)
  next : Std.HashSet (NNF α)

namespace GBANode

variable [BEq α] [Hashable α]

/-- Check if two HashSets have the same elements.
(Std.HashSet doesn't provide a BEq instance by default.) -/
private def hashSetEq (s₁ s₂ : Std.HashSet (NNF α)) : Bool :=
  s₁.all s₂.contains && s₂.all s₁.contains

/-- Check if two nodes have the same (old, next) signature.
Used to detect duplicate nodes during expansion.

Corresponds to the condition `old n' = old n ∧ next n' = next n`
in `expand_body` (LTL_to_GBA.thy, line 236). -/
def sameSignature (n₁ n₂ : GBANode α) : Bool :=
  hashSetEq n₁.old n₂.old && hashSetEq n₁.next n₂.next

variable [LawfulBEq α] [LawfulHashable α]

private theorem hashset_all_mem (s : Std.HashSet (NNF α)) (f : NNF α → Bool)
    (h : s.all f = true) (x : NNF α) (hx : x ∈ s) : f x = true := by
  have hlist : x ∈ s.toList := Std.HashSet.mem_toList.mpr hx
  rw [show s.all f = s.toList.all f from by simp [Std.HashSet.all]] at h
  exact List.all_eq_true.mp h x hlist

theorem sameSignature_old_left (n₁ n₂ : GBANode α)
    (h : n₁.sameSignature n₂ = true)
    (ψ : NNF α) (hψ : n₂.old.contains ψ = true) : n₁.old.contains ψ = true := by
  unfold sameSignature at h
  have := Bool.and_eq_true_iff.mp h |>.1
  have := Bool.and_eq_true_iff.mp this |>.2
  -- this : n₂.old.all n₁.old.contains = true
  exact hashset_all_mem n₂.old n₁.old.contains this ψ
    (Std.HashSet.mem_iff_contains.mpr hψ)

theorem sameSignature_old_right (n₁ n₂ : GBANode α)
    (h : n₁.sameSignature n₂ = true)
    (ψ : NNF α) (hψ : n₁.old.contains ψ = true) : n₂.old.contains ψ = true := by
  unfold sameSignature at h
  have := Bool.and_eq_true_iff.mp h |>.1
  have := Bool.and_eq_true_iff.mp this |>.1
  exact hashset_all_mem n₁.old n₂.old.contains this ψ
    (Std.HashSet.mem_iff_contains.mpr hψ)

end GBANode

end LTLLib
