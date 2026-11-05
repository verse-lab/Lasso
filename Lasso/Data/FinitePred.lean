module

/-
  Finiteness of a predicate, witnessed by a list covering it.

  Declared under `Lasso`.

  Key definitions:
  - `FinitePred`: only finitely many values satisfy a predicate (some list contains all of them)

  Key theorems:
  - `FinitePred.subset`, `FinitePred.prod`, `FinitePred.union`, `FinitePred.image`: closure properties
  - `FinitePred.exists_lt_eq`: pigeonhole, a sequence confined to a finite predicate repeats a value
  - `FinitePred.nat_iff`: on `Nat`, finite means bounded (with `not_ge`, `not_of_forall_exists_gt`,
    `exists_gt_of_not` for the infinite side)

  Sections:
  - Predicates on `Nat`
-/
import Batteries.Data.List.Perm

public section

namespace Lasso

/-- Only finitely many values satisfy `p`: some list contains all of them. -/
@[expose] def FinitePred {α : Type u} (p : α → Prop) : Prop :=
  ∃ l : List α, ∀ a, p a → a ∈ l

namespace FinitePred

variable {α : Type u} {β : Type v}

/-- A list containing every value makes every predicate finite. -/
theorem of_forall_mem {p : α → Prop} (l : List α) (h : ∀ a, a ∈ l) : FinitePred p :=
  ⟨l, fun a _ => h a⟩

theorem subset {p q : α → Prop} (hp : FinitePred p) (h : ∀ ⦃a⦄, q a → p a) : FinitePred q :=
  let ⟨l, hl⟩ := hp
  ⟨l, fun a ha => hl a (h ha)⟩

theorem prod {p : α → Prop} {q : β → Prop} (hp : FinitePred p) (hq : FinitePred q) :
    FinitePred (fun x : α × β => p x.1 ∧ q x.2) :=
  let ⟨l₁, h₁⟩ := hp
  let ⟨l₂, h₂⟩ := hq
  ⟨l₁.flatMap fun a => l₂.map fun b => (a, b), fun x hx =>
    List.mem_flatMap.mpr ⟨x.1, h₁ _ hx.1, List.mem_map.mpr ⟨x.2, h₂ _ hx.2, rfl⟩⟩⟩

theorem union {p q : α → Prop} (hp : FinitePred p) (hq : FinitePred q) : FinitePred fun a => p a ∨ q a :=
  let ⟨l₁, h₁⟩ := hp
  let ⟨l₂, h₂⟩ := hq
  ⟨l₁ ++ l₂, fun a ha => List.mem_append.mpr (ha.imp (h₁ a) (h₂ a))⟩

theorem insert {p : α → Prop} (hp : FinitePred p) (a : α) : FinitePred fun x => x = a ∨ p x :=
  let ⟨l, hl⟩ := hp
  ⟨a :: l, fun x hx => hx.elim (fun e => e ▸ List.mem_cons_self) (fun h => List.mem_cons_of_mem _ (hl x h))⟩

theorem image {p : α → Prop} (hp : FinitePred p) (f : α → β) : FinitePred fun b => ∃ a, p a ∧ f a = b :=
  let ⟨l, hl⟩ := hp
  ⟨l.map f, fun _ ⟨a, ha, e⟩ => List.mem_map.mpr ⟨a, hl a ha, e⟩⟩

/-- A predicate whose image under a map injective on it is finite is itself finite. -/
theorem of_finite_image {p : α → Prop} {f : α → β} (h : FinitePred fun b => ∃ a, p a ∧ f a = b)
    (hinj : ∀ a₁, p a₁ → ∀ a₂, p a₂ → f a₁ = f a₂ → a₁ = a₂) : FinitePred p := by
  classical
  obtain ⟨L, hL⟩ := h
  refine ⟨L.filterMap fun b => if hb : ∃ a, p a ∧ f a = b then some (Classical.choose hb) else none,
    fun a ha => ?_⟩
  have hb : ∃ a', p a' ∧ f a' = f a := ⟨a, ha, rfl⟩
  refine List.mem_filterMap.mpr ⟨f a, hL _ hb, ?_⟩
  rw [dite_eq_left hb]
  exact congrArg some (hinj _ (Classical.choose_spec hb).1 _ ha (Classical.choose_spec hb).2)

/-- Pigeonhole: a sequence confined to a finite predicate takes some value twice. -/
theorem exists_lt_eq {p : α → Prop} (hp : FinitePred p) {σ : Nat → α} (h : ∀ n, p (σ n)) :
    ∃ i j, i < j ∧ σ i = σ j := by
  obtain ⟨l, hl⟩ := hp
  -- the first `l.length + 1` samples all lie in `l`, so they cannot be pairwise distinct
  let samples := (List.range (l.length + 1)).map σ
  have hsub : samples ⊆ l := fun a ha => by
    obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    exact hl _ (h n)
  refine Classical.byContradiction fun hne => ?_
  have hnd : samples.Nodup := List.pairwise_iff_getElem.mpr fun i j hi hj hij heq =>
    hne ⟨i, j, hij, by simpa [samples] using heq⟩
  have := (List.subperm_of_subset hnd hsub).length_le
  simp only [samples, List.length_map, List.length_range] at this
  omega

/-! ## Predicates on `Nat` -/

private theorem lt_sum_succ : ∀ {l : List Nat} {i : Nat}, i ∈ l → i < (l.map (· + 1)).sum
  | a :: l, i, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp only [List.map_cons, List.sum_cons]; omega
    · have := lt_sum_succ h
      simp only [List.map_cons, List.sum_cons]; omega

/-- On `Nat`, finite means bounded. -/
theorem nat_iff {p : Nat → Prop} : FinitePred p ↔ ∃ N, ∀ i, p i → i < N :=
  ⟨fun ⟨l, hl⟩ => ⟨(l.map (· + 1)).sum, fun i hi => lt_sum_succ (hl i hi)⟩,
    fun ⟨N, hN⟩ => ⟨List.range N, fun i hi => List.mem_range.mpr (hN i hi)⟩⟩

theorem lt (n : Nat) : FinitePred (· < n) :=
  nat_iff.mpr ⟨n, fun _ h => h⟩

/-- An upward-closed set of naturals is not finite. -/
theorem not_ge (n : Nat) : ¬ FinitePred (n ≤ ·) := fun h =>
  let ⟨N, hN⟩ := nat_iff.mp h
  absurd (hN (max n N) (Nat.le_max_left n N)) (Nat.not_lt.mpr (Nat.le_max_right n N))

/-- Arbitrarily large witnesses make a predicate infinite. -/
theorem not_of_forall_exists_gt {p : Nat → Prop} (h : ∀ a, ∃ b, p b ∧ a < b) : ¬ FinitePred p := fun hp =>
  let ⟨N, hN⟩ := nat_iff.mp hp
  let ⟨b, hb, hNb⟩ := h N
  absurd (hN b hb) (Nat.not_lt.mpr (Nat.le_of_lt hNb))

/-- An infinite predicate has witnesses above every bound. -/
theorem exists_gt_of_not {p : Nat → Prop} (h : ¬ FinitePred p) (a : Nat) : ∃ b, p b ∧ a < b :=
  Classical.byContradiction fun hne => h (nat_iff.mpr ⟨a + 1, fun i hi =>
    Nat.lt_succ_of_le (Nat.not_lt.mp fun hlt => hne ⟨i, hi, hlt⟩)⟩)

end FinitePred

end Lasso
