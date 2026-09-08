/-
  Subformula operations for NNF formulas.

  - `IsSubformula` relation + transitive closure
  - Generic fold (`NNF.fold`) and derived operations (`subformulas`, `untilSubformulas`)
  - `untilSubformulasDedup`: the Until-subformula list `constructGBA` builds acceptance sets from, one entry per distinct `.until`

  Sections:
  - Subformula relation
  - Subformula folding
  - untilSubformulas completeness
  - untilSubformulasDedup completeness
-/

import Std
import LTLLib.LTL.Syntax

namespace LTLLib

namespace NNF

/-! ## Subformula relation -/

/-- `IsSubformula ψ φ` means ψ is a (reflexive) subformula of φ. -/
inductive IsSubformula {α} : NNF α → NNF α → Prop where
  | refl                {φ} : IsSubformula φ φ
  | and_left      {ψ φ₁ φ₂} : IsSubformula ψ φ₁ → IsSubformula ψ (.and φ₁ φ₂)
  | and_right     {ψ φ₂ φ₁} : IsSubformula ψ φ₂ → IsSubformula ψ (.and φ₁ φ₂)
  | or_left       {ψ φ₁ φ₂} : IsSubformula ψ φ₁ → IsSubformula ψ (.or φ₁ φ₂)
  | or_right      {ψ φ₂ φ₁} : IsSubformula ψ φ₂ → IsSubformula ψ (.or φ₁ φ₂)
  | until_left    {ψ φ₁ φ₂} : IsSubformula ψ φ₁ → IsSubformula ψ (.until φ₁ φ₂)
  | until_right   {ψ φ₂ φ₁} : IsSubformula ψ φ₂ → IsSubformula ψ (.until φ₁ φ₂)
  | release_left  {ψ φ₁ φ₂} : IsSubformula ψ φ₁ → IsSubformula ψ (.release φ₁ φ₂)
  | release_right {ψ φ₂ φ₁} : IsSubformula ψ φ₂ → IsSubformula ψ (.release φ₁ φ₂)
  | next_sub          {ψ φ} : IsSubformula ψ φ  → IsSubformula ψ (.next φ)

namespace IsSubformula

variable {α : Type u} {φ ψ χ : NNF α}

/-- Subformula is transitive. -/
theorem trans (h₁ : IsSubformula ψ χ) (h₂ : IsSubformula χ φ) :
    IsSubformula ψ φ := by
  induction h₂ with
  | refl => exact h₁
  | and_left _ ih => exact .and_left ih
  | and_right _ ih => exact .and_right ih
  | or_left _ ih => exact .or_left ih
  | or_right _ ih => exact .or_right ih
  | until_left _ ih => exact .until_left ih
  | until_right _ ih => exact .until_right ih
  | release_left _ ih => exact .release_left ih
  | release_right _ ih => exact .release_right ih
  | next_sub _ ih => exact .next_sub ih

end IsSubformula

/-! ## Subformula folding -/

/-- Fold `f` over `φ` and all its subformulas (pre-order, root first). -/
def fold {β α} (f : β → NNF α → β) (init : β) : NNF α → β
  | φ@(.tt)
  | φ@(.ff)
  | φ@(.prop _)
  | φ@(.nprop _) => f init φ
  | φ@(.next ψ) => ψ.fold f (f init φ)
  | φ@(.and ψ₁ ψ₂)
  | φ@(.or ψ₁ ψ₂)
  | φ@(.until ψ₁ ψ₂)
  | φ@(.release ψ₁ ψ₂) => ψ₂.fold f (ψ₁.fold f (f init φ))

/-- Compute the list of all subformulas (pre-order). -/
def subformulas {α} (φ : NNF α) : List (NNF α) :=
  φ.fold (fun acc f => f :: acc) []

/-- Deduplicated subformulas. -/
def subformulasDedup {α} [BEq α] [Hashable α] (φ : NNF α) : List (NNF α) :=
  (φ.fold (fun state f =>
    if state.2.contains f then state
    else (f :: state.1, state.2.insert f))
    ([], Std.HashSet.emptyWithCapacity (16 : Nat))).1

private abbrev untilFoldFn (α : Type u) :=
  fun (acc : List (NNF α × NNF α)) (f : NNF α) =>
    match f with | .until a b => (a, b) :: acc | _ => acc

/-- Extract all Until-subformulas as (left, right) pairs.
Used for defining acceptance conditions: one accepting set per Until-subformula. -/
def untilSubformulas {α} (φ : NNF α) : List (NNF α × NNF α) :=
  φ.fold (untilFoldFn α) []

private abbrev untilDedupState (α : Type u) [BEq α] [Hashable α] : Type u :=
  List (NNF α × NNF α) × Std.HashSet (NNF α)

private abbrev untilDedupFn (α : Type u) [BEq α] [Hashable α] :
    untilDedupState α → NNF α → untilDedupState α :=
  fun st f =>
    match f with
    | .until a b =>
      if st.2.contains (.until a b) then st
      else ((a, b) :: st.1, st.2.insert (.until a b))
    | _ => st

/-- Deduplicated Until-subformulas: one `(left, right)` pair per distinct `.until` subformula.
For GBA construction, a repeated `.until` would otherwise cost a redundant acceptance set. -/
def untilSubformulasDedup {α} [BEq α] [Hashable α] (φ : NNF α) : List (NNF α × NNF α) :=
  (φ.fold (untilDedupFn α) ([], Std.HashSet.emptyWithCapacity 8)).1

/-! ### untilSubformulas completeness -/

/-- The fold preserves accumulator elements. -/
private theorem fold_until_mono (φ : NNF α)
    (acc : List (NNF α × NNF α)) (x : NNF α × NNF α)
    (hx : x ∈ acc) :
    x ∈ φ.fold (untilFoldFn α) acc := by
  induction φ generalizing acc with
  | tt | ff | prop _ | nprop _ => exact hx
  | next ψ ih => exact ih _ hx
  | and ψ₁ ψ₂ ih₁ ih₂ | or ψ₁ ψ₂ ih₁ ih₂ | «release» ψ₁ ψ₂ ih₁ ih₂ =>
    exact ih₂ _ (ih₁ _ hx)
  | «until» ψ₁ ψ₂ ih₁ ih₂ =>
    exact ih₂ _ (ih₁ _ (.tail _ hx))

/-- For any accumulator, if ψ is a subformula and ψ = until μ η,
    then (μ, η) appears in the fold result. -/
private theorem fold_until_complete (φ : NNF α) (acc : List (NNF α × NNF α))
    (μ η : NNF α) (hsub : NNF.IsSubformula (.until μ η) φ) :
    (μ, η) ∈ φ.fold (untilFoldFn α) acc := by
  induction φ generalizing acc with
  | tt | ff | prop _ | nprop _ => cases hsub
  | next ψ ih =>
    cases hsub with
    | next_sub h => exact ih _ h
  | and ψ₁ ψ₂ ih₁ ih₂ =>
    cases hsub with
    | and_left h => exact fold_until_mono ψ₂ _ _ (ih₁ _ h)
    | and_right h => exact ih₂ _ h
  | or ψ₁ ψ₂ ih₁ ih₂ =>
    cases hsub with
    | or_left h => exact fold_until_mono ψ₂ _ _ (ih₁ _ h)
    | or_right h => exact ih₂ _ h
  | «until» ψ₁ ψ₂ ih₁ ih₂ =>
    cases hsub with
    | refl =>
      show (μ, η) ∈ η.fold (untilFoldFn α) (μ.fold (untilFoldFn α) ((μ, η) :: acc))
      exact fold_until_mono η _ _ (fold_until_mono μ _ _ (.head _))
    | until_left h =>
      show (μ, η) ∈ ψ₂.fold (untilFoldFn α) (ψ₁.fold (untilFoldFn α) ((ψ₁, ψ₂) :: acc))
      exact fold_until_mono ψ₂ _ _ (ih₁ _ h)
    | until_right h =>
      show (μ, η) ∈ ψ₂.fold (untilFoldFn α) (ψ₁.fold (untilFoldFn α) ((ψ₁, ψ₂) :: acc))
      exact ih₂ _ h
  | «release» ψ₁ ψ₂ ih₁ ih₂ =>
    cases hsub with
    | release_left h => exact fold_until_mono ψ₂ _ _ (ih₁ _ h)
    | release_right h => exact ih₂ _ h

/-- Every until-subformula appears in `φ.untilSubformulas`. -/
theorem untilSubformulas_complete (φ : NNF α) (μ η : NNF α)
    (hsub : NNF.IsSubformula (.until μ η) φ) :
    (μ, η) ∈ φ.untilSubformulas :=
  fold_until_complete φ [] μ η hsub

/-- `untilSubformulas_complete` as an index lookup. -/
theorem untilSubformulas_index (φ : NNF α) (μ η : NNF α)
    (hsub : NNF.IsSubformula (.until μ η) φ) :
    ∃ i : Fin φ.untilSubformulas.length,
      φ.untilSubformulas[i] = (μ, η) := by
  have hmem := untilSubformulas_complete φ μ η hsub
  exact List.mem_iff_get.mp hmem

/-! ### untilSubformulasDedup completeness -/

variable {α : Type u} [BEq α] [Hashable α]

private def UntilDedupInv (st : untilDedupState α) : Prop :=
  ∀ a b, (a, b) ∈ st.1 ↔ st.2.contains (.until a b) = true

private theorem untilDedupFn_until (st : untilDedupState α) (a b : NNF α) :
    untilDedupFn α st (.until a b) =
      if st.2.contains (.until a b) then st
      else ((a, b) :: st.1, st.2.insert (.until a b)) := rfl

private theorem untilDedupFn_mono (st : untilDedupState α) (a b : NNF α) (x : NNF α × NNF α)
    (hx : x ∈ st.1) : x ∈ (untilDedupFn α st (.until a b)).1 := by
  rw [untilDedupFn_until]; split
  · exact hx
  · exact List.mem_cons_of_mem _ hx

private theorem untilDedupFn_inv [LawfulBEq α] [LawfulHashable α]
    (st : untilDedupState α) (a b : NNF α) (h : UntilDedupInv st) :
    UntilDedupInv (untilDedupFn α st (.until a b)) := by
  rw [untilDedupFn_until]; split
  · exact h
  · intro x y
    have := h x y
    simp only [List.mem_cons, Prod.mk.injEq, Std.HashSet.contains_insert]
    grind

private theorem fold_dedup_inv [LawfulBEq α] [LawfulHashable α]
    (φ : NNF α) (st : untilDedupState α) (h : UntilDedupInv st) :
    UntilDedupInv (φ.fold (untilDedupFn α) st) := by
  induction φ generalizing st with
  | tt | ff | prop _ | nprop _ => exact h
  | next ψ ih => exact ih _ h
  | and ψ₁ ψ₂ ih₁ ih₂ | or ψ₁ ψ₂ ih₁ ih₂ | «release» ψ₁ ψ₂ ih₁ ih₂ => exact ih₂ _ (ih₁ _ h)
  | «until» ψ₁ ψ₂ ih₁ ih₂ => exact ih₂ _ (ih₁ _ (untilDedupFn_inv st ψ₁ ψ₂ h))

private theorem fold_dedup_mono (φ : NNF α) (st : untilDedupState α) (x : NNF α × NNF α)
    (hx : x ∈ st.1) :
    x ∈ (φ.fold (untilDedupFn α) st).1 := by
  induction φ generalizing st with
  | tt | ff | prop _ | nprop _ => exact hx
  | next ψ ih => exact ih _ hx
  | and ψ₁ ψ₂ ih₁ ih₂ | or ψ₁ ψ₂ ih₁ ih₂ | «release» ψ₁ ψ₂ ih₁ ih₂ => exact ih₂ _ (ih₁ _ hx)
  | «until» ψ₁ ψ₂ ih₁ ih₂ => exact ih₂ _ (ih₁ _ (untilDedupFn_mono st ψ₁ ψ₂ x hx))

private theorem untilDedupFn_root [LawfulBEq α] [LawfulHashable α]
    (st : untilDedupState α) (a b : NNF α) (hinv : UntilDedupInv st) :
    (a, b) ∈ (untilDedupFn α st (.until a b)).1 := by
  rw [untilDedupFn_until]; split
  · next hc => exact (hinv a b).mpr hc
  · exact List.mem_cons_self ..

private theorem fold_dedup_complete [LawfulBEq α] [LawfulHashable α]
    (φ : NNF α) (st : untilDedupState α) (hinv : UntilDedupInv st)
    (μ η : NNF α) (hsub : NNF.IsSubformula (.until μ η) φ) :
    (μ, η) ∈ (φ.fold (untilDedupFn α) st).1 := by
  induction φ generalizing st with
  | tt | ff | prop _ | nprop _ => cases hsub
  | next ψ ih =>
    cases hsub with
    | next_sub h => exact ih _ hinv h
  | and ψ₁ ψ₂ ih₁ ih₂ =>
    cases hsub with
    | and_left h => exact fold_dedup_mono ψ₂ _ _ (ih₁ _ hinv h)
    | and_right h => exact ih₂ _ (fold_dedup_inv ψ₁ _ hinv) h
  | or ψ₁ ψ₂ ih₁ ih₂ =>
    cases hsub with
    | or_left h => exact fold_dedup_mono ψ₂ _ _ (ih₁ _ hinv h)
    | or_right h => exact ih₂ _ (fold_dedup_inv ψ₁ _ hinv) h
  | «release» ψ₁ ψ₂ ih₁ ih₂ =>
    cases hsub with
    | release_left h => exact fold_dedup_mono ψ₂ _ _ (ih₁ _ hinv h)
    | release_right h => exact ih₂ _ (fold_dedup_inv ψ₁ _ hinv) h
  | «until» ψ₁ ψ₂ ih₁ ih₂ =>
    have hstep := untilDedupFn_inv st ψ₁ ψ₂ hinv
    cases hsub with
    | refl => exact fold_dedup_mono η _ _ (fold_dedup_mono μ _ _ (untilDedupFn_root st μ η hinv))
    | until_left h => exact fold_dedup_mono ψ₂ _ _ (ih₁ _ hstep h)
    | until_right h => exact ih₂ _ (fold_dedup_inv ψ₁ _ hstep) h

/-- Every until-subformula appears in `φ.untilSubformulasDedup`. -/
theorem untilSubformulasDedup_complete [LawfulBEq α] [LawfulHashable α]
    (φ : NNF α) (μ η : NNF α) (hsub : NNF.IsSubformula (.until μ η) φ) :
    (μ, η) ∈ φ.untilSubformulasDedup :=
  fold_dedup_complete φ _ (by intro a b; simp) μ η hsub

/-- `untilSubformulasDedup_complete` as an index lookup. -/
theorem untilSubformulasDedup_index [LawfulBEq α] [LawfulHashable α]
    (φ : NNF α) (μ η : NNF α) (hsub : NNF.IsSubformula (.until μ η) φ) :
    ∃ i : Fin φ.untilSubformulasDedup.length,
      φ.untilSubformulasDedup[i] = (μ, η) :=
  List.mem_iff_get.mp (untilSubformulasDedup_complete φ μ η hsub)

end NNF

end LTLLib
