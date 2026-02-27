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
  s₁.size == s₂.size && s₁.all s₂.contains

/-- Check if two nodes have the same (old, next) signature.
Used to detect duplicate nodes during expansion.

Corresponds to the condition `old n' = old n ∧ next n' = next n`
in `expand_body` (LTL_to_GBA.thy, line 236). -/
def sameSignature (n₁ n₂ : GBANode α) : Bool :=
  hashSetEq n₁.old n₂.old && hashSetEq n₁.next n₂.next

end GBANode

end LTLLib
