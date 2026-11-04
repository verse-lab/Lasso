module

/-
  Finite sets as predicates enumerated by a list.

  Declared under `Lasso` (with `List.toFinSet` under `List`). The lemmas mirror Mathlib's `Finset` API, same
  names and argument shapes, but nothing requires `DecidableEq`: the set operations work on the predicate, and
  only counting and enumeration (`card`, `sum`, `toList`) and deciding membership or equality go through choice.

  Key definitions:
  - `FinSet`: a predicate together with a list enumerating exactly its members
  - `List.toFinSet`, `FinSet.image`, `FinSet.biUnion`, `FinSet.filter`, `FinSet.range`, `FinSet.powerset`,
    `FinSet.product`, `FinSet.erase`: the set operations, alongside `∅`, `{a}`, `insert`, `∪`, `∩` and `\`
  - `FinSet.toList`, `FinSet.card`, `FinSet.sum`: enumeration and counting (noncomputable), with the scoped
    notation `∑ x ∈ s, f x`

  Key theorems:
  - `FinSet.ext`: sets with the same members are equal
  - `FinSet.card_le_card`, `FinSet.card_lt_card`, `FinSet.sum_le_sum_of_subset`: monotonicity of the counts
  - `FinSet.finite`: the members of a `FinSet` form a `FinitePred`

  Sections:
  - Extensionality and inclusion
  - Deciding membership and equality, by choice
  - Empty set, singletons and insertion
  - Union, intersection and difference
  - Filter, erase and range
  - Image and indexed union
  - Powerset and product
  - Enumeration and counting
  - Finiteness
  - `List.toFinSet`
-/
import Batteries.Data.List.Perm
public import Lasso.Data.List
public import Lasso.Data.FinitePred

public section

namespace Lasso

/-- A finite set: a predicate together with the fact that some list enumerates exactly its members. -/
@[expose] def FinSet (α : Type u) : Type u :=
  { s : α → Prop // ∃ l : List α, ∀ a, s a ↔ a ∈ l }

namespace FinSet

variable {α : Type u}

instance : Membership α (FinSet α) := ⟨fun s a => s.1 a⟩

theorem exists_list (s : FinSet α) : ∃ l : List α, ∀ a, a ∈ s ↔ a ∈ l :=
  s.2

end FinSet

end Lasso

/-- The members of a list, as a `FinSet`. -/
@[expose] def List.toFinSet {α : Type u} (l : List α) : Lasso.FinSet α :=
  ⟨fun a => a ∈ l, l, fun _ => Iff.rfl⟩

@[simp] theorem List.mem_toFinSet {α : Type u} {l : List α} {a : α} : a ∈ l.toFinSet ↔ a ∈ l :=
  Iff.rfl

namespace Lasso

namespace FinSet

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## Extensionality and inclusion -/

@[ext] theorem ext {s₁ s₂ : FinSet α} (h : ∀ a, a ∈ s₁ ↔ a ∈ s₂) : s₁ = s₂ :=
  Subtype.ext (funext fun a => propext (h a))

/-- `s ⊆ t`: every member of `s` is a member of `t`. -/
@[expose] protected def Subset (s t : FinSet α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → a ∈ t

instance : HasSubset (FinSet α) := ⟨FinSet.Subset⟩

/-- `s ⊂ t`: `s ⊆ t` but not the other way. -/
@[expose] protected def SSubset (s t : FinSet α) : Prop :=
  s ⊆ t ∧ ¬ t ⊆ s

instance : HasSSubset (FinSet α) := ⟨FinSet.SSubset⟩

theorem subset_iff {s₁ s₂ : FinSet α} : s₁ ⊆ s₂ ↔ ∀ ⦃x⦄, x ∈ s₁ → x ∈ s₂ :=
  Iff.rfl

@[refl] theorem Subset.refl (s : FinSet α) : s ⊆ s :=
  fun _ h => h

theorem Subset.trans {s₁ s₂ s₃ : FinSet α} (h₁ : s₁ ⊆ s₂) (h₂ : s₂ ⊆ s₃) : s₁ ⊆ s₃ :=
  fun _ h => h₂ (h₁ h)

theorem Subset.antisymm {s₁ s₂ : FinSet α} (h₁ : s₁ ⊆ s₂) (h₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
  ext fun _ => ⟨fun h => h₁ h, fun h => h₂ h⟩

@[simp] theorem subset_refl (s : FinSet α) : s ⊆ s :=
  Subset.refl s

theorem subset_of_eq {s₁ s₂ : FinSet α} (h : s₁ = s₂) : s₁ ⊆ s₂ :=
  h ▸ Subset.refl _

theorem Subset.ssubset_of_ne {s₁ s₂ : FinSet α} (h : s₁ ⊆ s₂) (hne : s₁ ≠ s₂) : s₁ ⊂ s₂ :=
  ⟨h, fun h' => hne (Subset.antisymm h h')⟩

theorem SSubset.subset {s₁ s₂ : FinSet α} (h : s₁ ⊂ s₂) : s₁ ⊆ s₂ :=
  h.1

/-! ## Deciding membership and equality, by choice -/

noncomputable instance decidableMem (a : α) (s : FinSet α) : Decidable (a ∈ s) :=
  Classical.propDecidable _

noncomputable instance decidableEq : DecidableEq (FinSet α) :=
  fun _ _ => Classical.propDecidable _

/-! ## Empty set, singletons and insertion -/

instance : EmptyCollection (FinSet α) := ⟨⟨fun _ => False, [], fun _ => by simp⟩⟩

instance : Inhabited (FinSet α) := ⟨∅⟩

@[simp] theorem notMem_empty (a : α) : a ∉ (∅ : FinSet α) :=
  id

@[simp] theorem empty_subset (s : FinSet α) : ∅ ⊆ s :=
  fun _ h => h.elim

instance : Singleton α (FinSet α) := ⟨fun a => ⟨fun x => x = a, [a], fun _ => by simp⟩⟩

@[simp] theorem mem_singleton {a b : α} : b ∈ ({a} : FinSet α) ↔ b = a :=
  Iff.rfl

theorem mem_singleton_self (a : α) : a ∈ ({a} : FinSet α) :=
  rfl

instance : Insert α (FinSet α) := ⟨fun a s => ⟨fun x => x = a ∨ x ∈ s, by
  obtain ⟨l, hl⟩ := s.exists_list
  exact ⟨a :: l, fun x => by simp [hl]⟩⟩⟩

@[simp] theorem mem_insert {a b : α} {s : FinSet α} : a ∈ insert b s ↔ a = b ∨ a ∈ s :=
  Iff.rfl

/-! ## Union, intersection and difference -/

instance : Union (FinSet α) := ⟨fun s t => ⟨fun x => x ∈ s ∨ x ∈ t, by
  obtain ⟨l₁, h₁⟩ := s.exists_list
  obtain ⟨l₂, h₂⟩ := t.exists_list
  exact ⟨l₁ ++ l₂, fun x => by simp [h₁, h₂]⟩⟩⟩

instance : Inter (FinSet α) := ⟨fun s t => ⟨fun x => x ∈ s ∧ x ∈ t, by
  obtain ⟨l, hl⟩ := s.exists_list
  exact ⟨l.filter fun x => decide (x ∈ t), fun x => by simp [hl]⟩⟩⟩

instance : SDiff (FinSet α) := ⟨fun s t => ⟨fun x => x ∈ s ∧ x ∉ t, by
  obtain ⟨l, hl⟩ := s.exists_list
  exact ⟨l.filter fun x => decide (x ∉ t), fun x => by simp [hl]⟩⟩⟩

@[simp] theorem mem_union {s t : FinSet α} {a : α} : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
  Iff.rfl

theorem mem_union_left {s : FinSet α} {a : α} (t : FinSet α) (h : a ∈ s) : a ∈ s ∪ t :=
  Or.inl h

theorem mem_union_right {t : FinSet α} {a : α} (s : FinSet α) (h : a ∈ t) : a ∈ s ∪ t :=
  Or.inr h

theorem union_subset {s t u : FinSet α} (hs : s ⊆ u) (ht : t ⊆ u) : s ∪ t ⊆ u :=
  fun _ h => h.elim (fun h => hs h) (fun h => ht h)

theorem union_subset_union {s t u v : FinSet α} (h₁ : s ⊆ u) (h₂ : t ⊆ v) : s ∪ t ⊆ u ∪ v :=
  fun _ h => h.imp (fun h => h₁ h) (fun h => h₂ h)

@[simp] theorem empty_union (s : FinSet α) : ∅ ∪ s = s :=
  ext fun _ => by simp

@[simp] theorem union_empty (s : FinSet α) : s ∪ ∅ = s :=
  ext fun _ => by simp

@[simp] theorem mem_inter {a : α} {s₁ s₂ : FinSet α} : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ :=
  Iff.rfl

theorem mem_of_mem_inter_left {a : α} {s₁ s₂ : FinSet α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₁ :=
  h.1

theorem mem_of_mem_inter_right {a : α} {s₁ s₂ : FinSet α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₂ :=
  h.2

@[simp] theorem mem_sdiff {a : α} {s t : FinSet α} : a ∈ s \ t ↔ a ∈ s ∧ a ∉ t :=
  Iff.rfl

/-! ## Filter, erase and range -/

/-- The members of `s` satisfying `p`. -/
@[expose] def filter (p : α → Prop) (s : FinSet α) : FinSet α := ⟨fun x => x ∈ s ∧ p x, by
  classical
  obtain ⟨l, hl⟩ := s.exists_list
  exact ⟨l.filter fun x => decide (p x), fun x => by simp [hl]⟩⟩

@[simp] theorem mem_filter {p : α → Prop} {s : FinSet α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a :=
  Iff.rfl

theorem filter_subset (p : α → Prop) (s : FinSet α) : s.filter p ⊆ s :=
  fun _ h => h.1

/-- `s` without `a`. -/
@[expose] def erase (s : FinSet α) (a : α) : FinSet α := ⟨fun x => x ≠ a ∧ x ∈ s, by
  classical
  obtain ⟨l, hl⟩ := s.exists_list
  exact ⟨l.filter fun x => decide (x ≠ a), fun x => by simp [hl, and_comm]⟩⟩

@[simp] theorem mem_erase {a b : α} {s : FinSet α} : a ∈ s.erase b ↔ a ≠ b ∧ a ∈ s :=
  Iff.rfl

/-- The numbers below `n`. -/
@[expose] def range (n : Nat) : FinSet Nat :=
  ⟨fun m => m < n, List.range n, fun _ => by simp⟩

@[simp] theorem mem_range {n m : Nat} : m ∈ range n ↔ m < n :=
  Iff.rfl

/-! ## Image and indexed union -/

/-- The image of `s` under `f`. -/
@[expose] def image (f : α → β) (s : FinSet α) : FinSet β := ⟨fun b => ∃ a ∈ s, f a = b, by
  obtain ⟨l, hl⟩ := s.exists_list
  exact ⟨l.map f, fun b => by simp [hl]⟩⟩

@[simp] theorem mem_image {f : α → β} {s : FinSet α} {b : β} : b ∈ s.image f ↔ ∃ a ∈ s, f a = b :=
  Iff.rfl

theorem mem_image_of_mem {s : FinSet α} (f : α → β) {a : α} (h : a ∈ s) : f a ∈ s.image f :=
  ⟨a, h, rfl⟩

theorem image_subset_image {f : α → β} {s₁ s₂ : FinSet α} (h : s₁ ⊆ s₂) : s₁.image f ⊆ s₂.image f :=
  fun _ ⟨a, ha, e⟩ => ⟨a, h ha, e⟩

theorem image_congr {f g : α → β} {s : FinSet α} (h : ∀ ⦃x⦄, x ∈ s → f x = g x) : s.image f = s.image g :=
  ext fun _ => ⟨fun ⟨a, ha, e⟩ => ⟨a, ha, (h ha).symm.trans e⟩, fun ⟨a, ha, e⟩ => ⟨a, ha, (h ha).trans e⟩⟩

@[simp] theorem image_empty (f : α → β) : (∅ : FinSet α).image f = ∅ :=
  ext fun _ => ⟨fun ⟨_, ha, _⟩ => ha.elim, False.elim⟩

@[simp] theorem image_id {s : FinSet α} : s.image id = s :=
  ext fun b => ⟨fun ⟨_, ha, e⟩ => e ▸ ha, fun h => ⟨b, h, rfl⟩⟩

theorem image_image {f : α → β} {s : FinSet α} {g : β → γ} : (s.image f).image g = s.image (g ∘ f) :=
  ext fun _ => ⟨fun ⟨_, ⟨a, ha, e₁⟩, e₂⟩ => ⟨a, ha, by subst e₁; exact e₂⟩, fun ⟨a, ha, e⟩ => ⟨f a, ⟨a, ha, rfl⟩, e⟩⟩

@[simp] theorem image_singleton (f : α → β) (a : α) : ({a} : FinSet α).image f = {f a} :=
  ext fun _ => ⟨fun ⟨_, ha, e⟩ => (mem_singleton.mp ha) ▸ e.symm, fun h => ⟨a, rfl, h.symm⟩⟩

@[simp] theorem image_insert (f : α → β) (a : α) (s : FinSet α) : (insert a s).image f = insert (f a) (s.image f) :=
  ext fun _ => ⟨fun ⟨x, hx, e⟩ => hx.elim (fun h => Or.inl (h ▸ e.symm)) (fun h => Or.inr ⟨x, h, e⟩),
    fun h => h.elim (fun h => ⟨a, Or.inl rfl, h.symm⟩) (fun ⟨x, hx, e⟩ => ⟨x, Or.inr hx, e⟩)⟩

theorem image_union {f : α → β} (s₁ s₂ : FinSet α) : (s₁ ∪ s₂).image f = s₁.image f ∪ s₂.image f :=
  ext fun _ => ⟨fun ⟨a, ha, e⟩ => ha.imp (fun h => ⟨a, h, e⟩) (fun h => ⟨a, h, e⟩),
    fun h => h.elim (fun ⟨a, ha, e⟩ => ⟨a, Or.inl ha, e⟩) (fun ⟨a, ha, e⟩ => ⟨a, Or.inr ha, e⟩)⟩

/-- The union of `t a` over the members `a` of `s`. -/
@[expose] def biUnion (s : FinSet α) (t : α → FinSet β) : FinSet β := ⟨fun b => ∃ a ∈ s, b ∈ t a, by
  obtain ⟨l, hl⟩ := s.exists_list
  refine ⟨l.flatMap fun a => Classical.choose (t a).exists_list, fun b => ⟨fun ⟨a, ha, hb⟩ => ?_, fun h => ?_⟩⟩
  · exact List.mem_flatMap.mpr ⟨a, (hl a).mp ha, (Classical.choose_spec (t a).exists_list b).mp hb⟩
  · obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp h
    exact ⟨a, (hl a).mpr ha, (Classical.choose_spec (t a).exists_list b).mpr hb⟩⟩

@[simp] theorem mem_biUnion {s : FinSet α} {t : α → FinSet β} {b : β} : b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t a :=
  Iff.rfl

@[simp] theorem biUnion_empty {t : α → FinSet β} : (∅ : FinSet α).biUnion t = ∅ :=
  ext fun _ => ⟨fun ⟨_, ha, _⟩ => ha.elim, False.elim⟩

theorem subset_biUnion_of_mem {s : FinSet α} (u : α → FinSet β) {x : α} (h : x ∈ s) : u x ⊆ s.biUnion u :=
  fun _ hb => ⟨x, h, hb⟩

theorem biUnion_subset {s : FinSet α} {t : α → FinSet β} {s' : FinSet β} :
    s.biUnion t ⊆ s' ↔ ∀ x ∈ s, t x ⊆ s' :=
  ⟨fun h x hx _ hb => h ⟨x, hx, hb⟩, fun h _ ⟨x, hx, hb⟩ => h x hx hb⟩

theorem biUnion_congr {s₁ s₂ : FinSet α} {t₁ t₂ : α → FinSet β} (hs : s₁ = s₂) (ht : ∀ a ∈ s₁, t₁ a = t₂ a) :
    s₁.biUnion t₁ = s₂.biUnion t₂ := by
  subst hs
  exact ext fun _ => ⟨fun ⟨a, ha, hb⟩ => ⟨a, ha, ht a ha ▸ hb⟩, fun ⟨a, ha, hb⟩ => ⟨a, ha, (ht a ha).symm ▸ hb⟩⟩

theorem biUnion_insert {s : FinSet α} {t : α → FinSet β} {a : α} :
    (insert a s).biUnion t = t a ∪ s.biUnion t :=
  ext fun _ => ⟨fun ⟨x, hx, hb⟩ => hx.elim (fun e => Or.inl (e ▸ hb)) (fun hx => Or.inr ⟨x, hx, hb⟩),
    fun h => h.elim (fun hb => ⟨a, Or.inl rfl, hb⟩) (fun ⟨x, hx, hb⟩ => ⟨x, Or.inr hx, hb⟩)⟩

/-! ## Powerset and product -/

/-- Every sublist of `l` obtained by keeping or dropping each element. -/
private def sublistsOf : List α → List (List α)
  | [] => [[]]
  | a :: l => (sublistsOf l).map (a :: ·) ++ sublistsOf l

private theorem filter_mem_sublistsOf (p : α → Bool) : ∀ l : List α, l.filter p ∈ sublistsOf l
  | [] => by simp [sublistsOf]
  | a :: l => by
    by_cases hp : p a = true
    · simp only [List.filter_cons, hp, ↓reduceIte, sublistsOf, List.mem_append, List.mem_map]
      exact Or.inl ⟨_, filter_mem_sublistsOf p l, rfl⟩
    · simp only [List.filter_cons, hp, sublistsOf, List.mem_append]
      exact Or.inr (filter_mem_sublistsOf p l)

private theorem subset_of_mem_sublistsOf : ∀ {l m : List α}, m ∈ sublistsOf l → ∀ x ∈ m, x ∈ l
  | [], m, h, x, hx => by simp [sublistsOf] at h; subst h; simp at hx
  | a :: l, m, h, x, hx => by
    simp only [sublistsOf, List.mem_append, List.mem_map] at h
    rcases h with ⟨m', hm', rfl⟩ | h
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (subset_of_mem_sublistsOf hm' x hx)
    · exact List.mem_cons_of_mem _ (subset_of_mem_sublistsOf h x hx)

/-- The subsets of `s`. -/
@[expose] def powerset (s : FinSet α) : FinSet (FinSet α) := ⟨fun t => t ⊆ s, by
  obtain ⟨l, hl⟩ := s.exists_list
  refine ⟨(sublistsOf l).map List.toFinSet, fun t => ⟨fun ht => ?_, fun h => ?_⟩⟩
  · refine List.mem_map.mpr ⟨l.filter fun x => decide (x ∈ t), filter_mem_sublistsOf _ l, ext fun x => ?_⟩
    simp only [List.mem_toFinSet, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨(hl x).mp (ht h), h⟩⟩
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h
    exact fun x hx => (hl x).mpr (subset_of_mem_sublistsOf hm x hx)⟩

@[simp] theorem mem_powerset {s t : FinSet α} : s ∈ t.powerset ↔ s ⊆ t :=
  Iff.rfl

/-- The pairs with first component in `s` and second in `t`. -/
@[expose] def product (s : FinSet α) (t : FinSet β) : FinSet (α × β) := ⟨fun p => p.1 ∈ s ∧ p.2 ∈ t, by
  obtain ⟨l₁, h₁⟩ := s.exists_list
  obtain ⟨l₂, h₂⟩ := t.exists_list
  exact ⟨l₁.flatMap fun a => l₂.map fun b => (a, b), fun p => by simp [h₁, h₂, Prod.ext_iff]⟩⟩

@[simp] theorem mem_product {s : FinSet α} {t : FinSet β} {p : α × β} : p ∈ s.product t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

/-! ## Enumeration and counting -/

private theorem exists_nodup_of_list (l : List α) : ∃ m : List α, m.Nodup ∧ ∀ a, a ∈ l ↔ a ∈ m := by
  induction l with
  | nil => exact ⟨[], List.nodup_nil, fun _ => Iff.rfl⟩
  | cons x l ih =>
    obtain ⟨m, hm, hml⟩ := ih
    by_cases hx : x ∈ m
    · refine ⟨m, hm, fun a => ?_⟩
      simp only [List.mem_cons, hml]
      exact ⟨fun h => h.elim (fun e => e ▸ hx) id, Or.inr⟩
    · exact ⟨x :: m, List.nodup_cons.mpr ⟨hx, hm⟩, fun a => by simp [hml]⟩

theorem exists_nodup_list (s : FinSet α) : ∃ l : List α, l.Nodup ∧ ∀ a, a ∈ s ↔ a ∈ l :=
  let ⟨l, hl⟩ := s.exists_list
  let ⟨m, hm, hml⟩ := exists_nodup_of_list l
  ⟨m, hm, fun a => (hl a).trans (hml a)⟩

/-- The members of `s`, without repetition, in some order. -/
@[expose] noncomputable def toList (s : FinSet α) : List α :=
  Classical.choose s.exists_nodup_list

theorem nodup_toList (s : FinSet α) : s.toList.Nodup :=
  (Classical.choose_spec s.exists_nodup_list).1

@[simp] theorem mem_toList {a : α} {s : FinSet α} : a ∈ s.toList ↔ a ∈ s :=
  ((Classical.choose_spec s.exists_nodup_list).2 a).symm

/-- The number of members of `s`. -/
@[expose] noncomputable def card (s : FinSet α) : Nat :=
  s.toList.length

theorem card_eq_length {s : FinSet α} {l : List α} (hl : l.Nodup) (h : ∀ a, a ∈ s ↔ a ∈ l) :
    s.card = l.length :=
  Nat.le_antisymm (List.subperm_of_subset s.nodup_toList fun a ha => (h a).mp (mem_toList.mp ha)).length_le
    (List.subperm_of_subset hl fun a ha => mem_toList.mpr ((h a).mpr ha)).length_le

theorem card_le_card {s t : FinSet α} (h : s ⊆ t) : s.card ≤ t.card :=
  (List.subperm_of_subset s.nodup_toList fun _ ha => mem_toList.mpr (h (mem_toList.mp ha))).length_le

theorem card_lt_card {s t : FinSet α} (h : s ⊂ t) : s.card < t.card := by
  obtain ⟨hst, hts⟩ := h
  obtain ⟨x, hxt, hxs⟩ : ∃ x, x ∈ t ∧ x ∉ s := Classical.byContradiction fun hne =>
    hts fun x hx => Classical.byContradiction fun hxs => hne ⟨x, hx, hxs⟩
  open Classical in
  have hsub : s.toList ⊆ t.toList.erase x := fun a ha => by
    have has := mem_toList.mp ha
    exact (List.mem_erase_of_ne fun (e : a = x) => hxs (e ▸ has)).mpr (mem_toList.mpr (hst has))
  have hle := (List.subperm_of_subset s.nodup_toList hsub).length_le
  have hpos := List.length_pos_of_mem (mem_toList.mpr hxt)
  rw [List.length_erase_of_mem (mem_toList.mpr hxt)] at hle
  simp only [card]
  omega

theorem eq_of_subset_of_card_le {s t : FinSet α} (h : s ⊆ t) (h₂ : t.card ≤ s.card) : s = t :=
  Subset.antisymm h (Classical.byContradiction fun hts => absurd (card_lt_card ⟨h, hts⟩) (Nat.not_lt.mpr h₂))

theorem card_erase_lt_of_mem {s : FinSet α} {a : α} (h : a ∈ s) : (s.erase a).card < s.card :=
  card_lt_card ⟨fun _ hx => hx.2, fun hsub => (hsub h).1 rfl⟩

/-- The sum of `f` over the members of `s`. -/
@[expose] noncomputable def sum (s : FinSet α) (f : α → Nat) : Nat :=
  (s.toList.map f).sum

/-- `∑ x ∈ s, f x` is `s.sum fun x => f x`. -/
scoped macro "∑ " x:ident " ∈ " s:term ", " f:term:67 : term => `(FinSet.sum $s fun $x => $f)

theorem sum_eq_list {s : FinSet α} {l : List α} (hl : l.Nodup) (h : ∀ a, a ∈ s ↔ a ∈ l) (f : α → Nat) :
    s.sum f = (l.map f).sum :=
  (((List.perm_ext_iff_of_nodup s.nodup_toList hl).mpr fun a => mem_toList.trans (h a)).map f).sum_nat

theorem sum_congr {s₁ s₂ : FinSet α} {f g : α → Nat} (h₁ : s₁ = s₂) (h₂ : ∀ x ∈ s₂, f x = g x) :
    s₁.sum f = s₂.sum g := by
  subst h₁
  exact congrArg List.sum (List.map_congr_left fun x hx => h₂ x (mem_toList.mp hx))

theorem sum_le_sum {s : FinSet α} {f g : α → Nat} (h : ∀ i ∈ s, f i ≤ g i) : s.sum f ≤ s.sum g :=
  Lasso.List.sum_map_le_sum_map fun x hx => h x (mem_toList.mp hx)

theorem sum_le_sum_of_subset {f : α → Nat} {s t : FinSet α} (h : s ⊆ t) : s.sum f ≤ t.sum f := by
  obtain ⟨l, hperm, hsub⟩ :=
    List.subperm_of_subset s.nodup_toList fun _ ha => mem_toList.mpr (h (mem_toList.mp ha))
  simp only [sum]
  rw [← (hperm.map f).sum_nat]
  exact Lasso.List.sum_le_sum_of_sublist (hsub.map f)

/-! ## Finiteness -/

/-- The members of a `FinSet` form a finite predicate. -/
theorem finite (s : FinSet α) : FinitePred (· ∈ s) :=
  let ⟨l, hl⟩ := s.exists_list
  ⟨l, fun a ha => (hl a).mp ha⟩

end FinSet

end Lasso

/-! ## `List.toFinSet` -/

namespace List

variable {α : Type u}

@[simp] theorem toFinSet_nil : ([] : List α).toFinSet = ∅ :=
  Lasso.FinSet.ext fun _ => by simp

@[simp] theorem toFinSet_cons {l : List α} {a : α} : (a :: l).toFinSet = insert a l.toFinSet :=
  Lasso.FinSet.ext fun _ => by simp

theorem toFinSet_filter (s : List α) (p : α → Bool) :
    (s.filter p).toFinSet = s.toFinSet.filter fun x => p x = true :=
  Lasso.FinSet.ext fun _ => by simp

theorem toFinSet_card_of_nodup {l : List α} (h : l.Nodup) : l.toFinSet.card = l.length :=
  Lasso.FinSet.card_eq_length h fun _ => Iff.rfl

theorem sum_toFinSet (f : α → Nat) {l : List α} (hl : l.Nodup) : l.toFinSet.sum f = (l.map f).sum :=
  Lasso.FinSet.sum_eq_list hl (fun _ => Iff.rfl) f

end List
