module

/-
  `List` lemmas that core Lean does not provide.

  Declared under `LTLLib.List`.

  Key theorems:
  - `List.sum_map_le_sum_map`, `List.sum_le_sum_of_sublist`: monotonicity of `Nat` list sums
  - `List.mem_sublists`: membership in Batteries' `List.sublists` is being a sublist
  - `List.flatten_splitBy`: the groups of `List.splitBy` flatten back to the original list
    (proof from Mathlib's `Mathlib/Data/List/SplitBy.lean`)
-/
public import Batteries.Data.List.Basic

public section

namespace LTLLib.List

/-! ## Sums of `Nat` lists -/

theorem sum_map_le_sum_map {β : Type u} {l : List β} {f g : β → Nat} (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem sum_le_sum_of_sublist {l₁ l₂ : List Nat} (h : l₁.Sublist l₂) : l₁.sum ≤ l₂.sum := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons a _ ih => simp only [List.sum_cons]; omega
  | cons_cons a _ ih => simp only [List.sum_cons]; omega

/-! ## `countP` -/

/-- A weaker predicate counts strictly more once some element satisfies it but not the stronger one. -/
theorem countP_lt_countP {α : Type u} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = true → q x = true)
    {a : α} (ha : a ∈ l) (hpa : p a = false) (hqa : q a = true) : l.countP p < l.countP q := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    have htail : ∀ x ∈ l, p x = true → q x = true := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hle := List.countP_mono_left htail
    have hb : p b = true → q b = true := h b List.mem_cons_self
    simp only [List.countP_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · simp only [hpa, hqa, Bool.false_eq_true, ↓reduceIte]; omega
    · have hlt := ih htail ha
      cases hpb : p b <;> cases hqb : q b <;> simp_all <;> omega

/-! ## `sublists` -/

/-- Membership in Batteries' `List.sublists` is being a sublist. -/
theorem mem_sublists {α : Type u} {s l : List α} : s ∈ l.sublists ↔ s.Sublist l := by
  induction l generalizing s with
  | nil => simp [List.sublists]
  | cons a l ih =>
    have hdef : (a :: l).sublists = l.sublists.flatMap fun x => [x, a :: x] := rfl
    rw [hdef, List.mem_flatMap, List.sublist_cons_iff]
    constructor
    · rintro ⟨x, hx, hs⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact Or.inl (ih.mp hx)
      · exact Or.inr ⟨x, rfl, ih.mp hx⟩
    · rintro (hs | ⟨r, rfl, hr⟩)
      · exact ⟨s, ih.mpr hs, List.mem_cons_self⟩
      · exact ⟨r, ih.mpr hr, List.mem_cons_of_mem _ List.mem_cons_self⟩

/-! ## `splitBy` -/

section SplitBy

variable {α : Type u}

private theorem splitByLoop_eq_append {r : α → α → Bool} {l : List α} {a : α} {g : List α}
    (gs : List (List α)) : List.splitBy.loop r l a g gs = gs.reverse ++ List.splitBy.loop r l a g [] := by
  induction l generalizing a g gs with
  | nil => simp [List.splitBy.loop]
  | cons b l IH =>
    simp only [List.splitBy.loop]
    split <;> rw [IH]
    conv => rhs; rw [IH]
    simp

private theorem flatten_splitByLoop {r : α → α → Bool} {l : List α} {a : α} {g : List α} :
    (List.splitBy.loop r l a g []).flatten = g.reverse ++ a :: l := by
  induction l generalizing a g with
  | nil => simp [List.splitBy.loop]
  | cons b l IH =>
    rw [List.splitBy.loop, splitByLoop_eq_append [_]]
    split <;> simp [IH]

theorem flatten_splitBy (r : α → α → Bool) (l : List α) : (l.splitBy r).flatten = l :=
  match l with
  | [] => rfl
  | _ :: _ => flatten_splitByLoop

end SplitBy

end LTLLib.List
