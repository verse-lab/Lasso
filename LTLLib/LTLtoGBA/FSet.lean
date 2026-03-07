/-
  Abstract finite set interface for the LTL-to-GBA construction.

  Defines `FSet`, a typeclass capturing the set operations and laws needed
  by the expand algorithm and its correctness proofs. Instances are provided
  for `Std.HashSet` and `Std.TreeSet`, allowing the implementation to be
  swapped without changing the algorithm or proofs.
-/

import Std
import Std.Data.TreeSet.Lemmas

namespace LTLLib

/-- Abstract finite set with element type `α` and container type `S`.

**Operations** (all needed by the GBA expand algorithm):
- `empty`, `insert`, `contains` — basic set operations
- `foldl` — left fold over elements (used in `mergeIncoming`, successor creation)
- `all` — universal predicate check (used in `sameSignature`)
- `toList` — conversion to list (for proofs only)

**Laws** (all needed by the correctness proofs in `Invariants.lean`):
- `contains_empty`, `contains_insert_self`, `contains_insert_other` —
  containment behavior
- `foldl_eq_foldl_toList` — connects fold to list fold (for inductive proofs)
- `all_eq_toList_all` — connects `all` to `List.all` (for `sameSignature` proofs)
- `mem_toList_iff` — connects list membership to `contains` -/
class FSet (α : outParam Type) (S : Type) where
  /-- Empty set. -/
  empty : S
  /-- Insert an element. -/
  insert : S → α → S
  /-- Membership test. -/
  contains : S → α → Bool
  /-- Left fold over elements. Iteration order is implementation-defined. -/
  foldl {β : Type} : (β → α → β) → β → S → β
  /-- Check if all elements satisfy a predicate. -/
  all : S → (α → Bool) → Bool
  /-- Convert to list (for proofs). Order is implementation-defined. -/
  toList : S → List α

  /-- Empty set contains nothing. -/
  contains_empty (a : α) : contains empty a = false
  /-- Inserting makes the element contained. -/
  contains_insert_self (a : α) (s : S) : contains (insert s a) a = true
  /-- Inserting a different element preserves containment. -/
  contains_insert_other (a b : α) (s : S) : a ≠ b →
    contains (insert s b) a = contains s a
  /-- `foldl` on the set equals `List.foldl` on its `toList`. -/
  foldl_eq_foldl_toList {β : Type} (f : β → α → β) (init : β) (s : S) :
    foldl f init s = (toList s).foldl f init
  /-- `all` on the set equals `List.all` on its `toList`. -/
  all_eq_toList_all (s : S) (p : α → Bool) :
    all s p = (toList s).all p
  /-- `toList` membership is equivalent to `contains`. -/
  mem_toList_iff (a : α) (s : S) : a ∈ toList s ↔ contains s a = true

namespace FSet

variable {α : Type} {S : Type} [FSet α S]

/-- Combined `contains_insert` law (requires `LawfulBEq`).
Matches the form of `Std.HashSet.contains_insert`. -/
theorem contains_insert [BEq α] [LawfulBEq α] (a b : α) (s : S) :
    FSet.contains (FSet.insert s b) a = (a == b || FSet.contains s a) := by
  by_cases h : a = b
  · subst h; simp [FSet.contains_insert_self]
  · simp [FSet.contains_insert_other _ _ _ h, beq_iff_eq, h]

/-- Set equality via mutual containment.
With `Std.TreeSet`, this can be replaced by the built-in `BEq` instance
for better performance (structural comparison on sorted trees). -/
def setEq (s₁ s₂ : S) : Bool :=
  FSet.all s₁ (FSet.contains s₂ ·) && FSet.all s₂ (FSet.contains s₁ ·)

theorem setEq_correct (s₁ s₂ : S) :
    setEq s₁ s₂ = true ↔
      (∀ a, FSet.contains s₁ a = true → FSet.contains s₂ a = true) ∧
      (∀ a, FSet.contains s₂ a = true → FSet.contains s₁ a = true) := by
  simp only [setEq, Bool.and_eq_true, FSet.all_eq_toList_all, List.all_eq_true]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨fun a ha => h1 a ((FSet.mem_toList_iff a s₁).mpr ha),
           fun a ha => h2 a ((FSet.mem_toList_iff a s₂).mpr ha)⟩
  · intro ⟨h1, h2⟩
    exact ⟨fun a ha => h1 a ((FSet.mem_toList_iff a s₁).mp ha),
           fun a ha => h2 a ((FSet.mem_toList_iff a s₂).mp ha)⟩

end FSet

/-! ## `Std.HashSet` instance

Requires `[BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]`.

Individual operations are O(1) amortized. No canonical `BEq`/`Hashable`
instance on the set type itself (internal layout depends on insertion order),
so `findDuplicate` cannot easily use hash-based signature lookup. -/

instance instFSetHashSet [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] :
    FSet α (Std.HashSet α) where
  empty := Std.HashSet.emptyWithCapacity 0
  insert s a := s.insert a
  contains s a := s.contains a
  foldl f init s := Std.HashSet.fold f init s
  all s p := s.all p
  toList s := s.toList
  contains_empty a := by simp
  contains_insert_self a s := by simp [Std.HashSet.contains_insert]
  contains_insert_other a b s h := by
    rw [Std.HashSet.contains_insert]
    simp [beq_iff_eq, Ne.symm h]
  foldl_eq_foldl_toList _ _ _ := Std.HashSet.fold_eq_foldl_toList
  all_eq_toList_all s p := by simp [Std.HashSet.all]
  mem_toList_iff a s := by
    rw [Std.HashSet.mem_toList, Std.HashSet.contains_iff_mem]

/-! ## `Std.TreeSet` instance

Requires `[Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α]`.

Individual operations are O(log n). The key advantage is that `Std.TreeSet`
has a canonical `BEq` instance (structural equality on sorted trees), enabling
efficient `findDuplicate` via signature-based lookup:

```
-- With TreeSet, (old, next) pairs can be used as map keys:
signatureMap : Std.TreeMap (Std.TreeSet (NNF α) × Std.TreeSet (NNF α)) Nat
```

This reduces `findDuplicate` from O(|nodes| · |φ|) to O(|φ| log |φ|) per call. -/

instance instFSetTreeSet [Ord α] [Std.TransOrd α] [Std.LawfulEqOrd α] :
    FSet α (Std.TreeSet α) where
  empty := Std.TreeSet.empty
  insert s a := s.insert a
  contains s a := s.contains a
  foldl f init s := s.foldl f init
  all s p := s.all p
  toList s := s.toList
  contains_empty a := by
    show Std.TreeSet.empty.contains a = false
    simp
  contains_insert_self a s := by
    show (s.insert a).contains a = true
    rw [Std.TreeSet.contains_insert]; simp
  contains_insert_other a b s h := by
    show (s.insert b).contains a = s.contains a
    rw [Std.TreeSet.contains_insert]
    have : (compare b a == Ordering.eq) = false := by
      rw [Bool.eq_false_iff]
      exact fun heq => h (Std.LawfulEqOrd.compare_beq_iff_eq.mp heq).symm
    simp [this]
  foldl_eq_foldl_toList _ _ _ := Std.TreeSet.foldl_eq_foldl_toList
  all_eq_toList_all s p := by
    show s.all p = s.toList.all p
    unfold Std.TreeSet.all Std.TreeMap.all Std.DTreeMap.all
    unfold Std.TreeSet.toList Std.TreeMap.keys Std.DTreeMap.keys
    rw [Std.DTreeMap.Internal.Impl.all_eq_all_toListModel,
        Std.DTreeMap.Internal.Impl.keys_eq_keys]
    induction s.inner.inner.inner.toListModel with
    | nil => rfl
    | cons x xs ih => simp [Std.Internal.List.keys, List.all_cons, ih]
  mem_toList_iff a s := by
    rw [Std.TreeSet.mem_toList, Std.TreeSet.contains_iff_mem]

end LTLLib
