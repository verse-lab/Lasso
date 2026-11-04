module

/-
  Generic run theory for `VWAA`, mirroring `[HOL4-ltl]`'s `alterAScript`. Along a branch the rank never rises and drops at
  every change of state, so every branch is eventually constant without any finiteness assumption, and co-Büchi acceptance
  reduces to no branch settling in a final state. Runs can be restricted to a subset of level 0, merged with node sharing,
  and shifted by one level in either direction (`[HOL4-ltl]`'s `REPL_RUN_CONSTR_LEMM`), each preserving acceptance.

  Proves:
  - `mem_level_of_infBranch`: a branch is alive on every level it passes through
  - `rank_step_of_infBranch`: one branch step repeats the state or strictly drops the rank (`[HOL4-ltl]` `BRANCH_WAA_LEMM`)
  - `exists_stabilizesAt`: every infinite branch is eventually constant (`[HOL4-ltl]` `BRANCH_FIXP`)
  - `acceptingRun_iff`: acceptance is exactly the absence of a branch settling in a final state (`[HOL4-ltl]` `BRANCH_ACC_LEMM`)
  - `restrict_level_subset`: restricting only shrinks levels (`[HOL4-ltl]` `RUN_RESTR_LEMM`)
  - `restrict_validFrom`: the restriction is a run from the smaller level-0 set
  - `infBranch_of_restrict`: a branch of the restriction is a branch of the original (`[HOL4-ltl]` `RUN_RESTR_FIXP_LEMM`)
  - `acceptingRun_restrict`, `acceptsFrom_subset`: acceptance survives restriction, so a subset of an accepting level-0 set accepts
  - `exists_path_to`: a state alive on a level is reached from level 0 (`[HOL4-ltl]` `BRANCH_SUFF_LEMM`)
  - `conj_level_subset`, `conj_validFrom`: the union stays within the two runs and is itself a run
  - `acceptingRun_conj`: acceptance survives run union (`[HOL4-ltl]` `CONJ_RUN_FIXP_LEMM`)
  - `acceptsFrom_union`: two satisfiable level-0 sets are satisfiable together
  - `shift_validFrom`: the shifted run is a run of the dropped word from the old level 1
  - `exists_infBranch_of_shift`, `acceptingRun_shift`: acceptance survives dropping level 0
  - `prepend_validFrom`: a fresh level 0 with a chosen successor set gives a run of the un-dropped word
  - `prepend_shift`: shift undoes prepend exactly
  - `acceptingRun_prepend`: acceptance survives prepending a level

  References:
  - `[JN18]` Jantsch, Norrish. Verifying the LTL to Büchi Automata Translation via Very Weak Alternating
    Automata. ITP'18, and its HOL4 `alterAScript`, whose lemma names are cited above.
  - `[TV21]` Tsay, Vardi. From Linear Temporal Logics to Büchi Automata. LNCS 13030, Lemma 3 and Definition 10.

  Sections:
  - Branches stay alive
  - Branch stabilisation
  - Co-Büchi acceptance
  - Run restriction
  - Backwards extension
  - Run union
  - Level shift
-/
public import Lasso.LTLtoTGBA.AbstractSpec.VWAA
public import Lasso.Data.Nat
public import Lasso.Data.FinSet

public section

namespace Lasso

universe u v

variable {Q : Type v} {α : Type u}
variable {A : VWAA Q α} {r : VWAA.Run Q} {S T : FinSet Q} {ξ : OmegaWord α} {b : Nat → Q}

/-! ## Branches stay alive -/

/-- A branch only visits states alive on their own level. -/
theorem mem_level_of_infBranch (hv : r.ValidFrom A S ξ) (hb : r.InfBranch b) :
    ∀ i, b i ∈ r.level i := by
  intro i
  induction i with
  | zero => exact hb.1
  | succ i ih => exact hv.succ_sub i (b i) ih (hb.2 i)

/-! ## Branch stabilisation -/

/-- `[HOL4-ltl]` `BRANCH_WAA_LEMM`: one step of a branch either stays put or strictly drops the rank. -/
theorem rank_step_of_infBranch (hv : r.ValidFrom A S ξ) (hb : r.InfBranch b) (i : Nat) :
    b (i + 1) = b i ∨ A.rank (b (i + 1)) < A.rank (b i) := by
  obtain ⟨g, hmem, _⟩ := hv.step i (b i) (mem_level_of_infBranch hv hb i)
  exact A.veryWeak (b i) g (r.succ i (b i)) hmem (b (i + 1)) (hb.2 i)

/-- The rank along a branch never rises. -/
private theorem rank_antitone (hv : r.ValidFrom A S ξ) (hb : r.InfBranch b) {i j : Nat} (hij : i ≤ j) :
    A.rank (b j) ≤ A.rank (b i) := by
  induction j, hij using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ j hij ih =>
    rcases rank_step_of_infBranch hv hb j with h | h
    · rw [h]; exact ih
    · exact Nat.le_trans (Nat.le_of_lt h) ih

/-- `[HOL4-ltl]` `BRANCH_FIXP`: every infinite branch is eventually constant. -/
theorem exists_stabilizesAt (hv : r.ValidFrom A S ξ) (hb : r.InfBranch b) :
    ∃ q, VWAA.StabilizesAt b q := by
  obtain ⟨v, -, ⟨i₀, hi₀⟩, hvmin⟩ :=
    LentilLib.Nat.find_min (p := fun v => ∃ i, A.rank (b i) = v) (A.rank (b 0)) ⟨0, rfl⟩
  have hconst : ∀ m, i₀ ≤ m → A.rank (b m) = A.rank (b i₀) := by
    intro m hm
    refine Nat.le_antisymm (rank_antitone hv hb hm) ?_
    rw [hi₀]
    exact Nat.not_lt.mp fun h => hvmin _ h ⟨m, rfl⟩
  refine ⟨b i₀, i₀, ?_⟩
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rcases rank_step_of_infBranch hv hb m with h | h
    · rw [h]; exact ih
    · exfalso
      have h1 := hconst m hm
      have h2 := hconst (m + 1) (Nat.le_succ_of_le hm)
      omega

/-! ## Co-Büchi acceptance -/

/-- `[HOL4-ltl]` `BRANCH_ACC_LEMM`: a run of a very weak automaton is accepting exactly when no branch
settles in a final state. -/
theorem acceptingRun_iff (hv : r.ValidFrom A S ξ) :
    A.AcceptingRun r ↔ ∀ b q, r.InfBranch b → VWAA.StabilizesAt b q → ¬ A.final q := by
  constructor
  · intro hacc b q hb hst hfin
    obtain ⟨i₀, hst⟩ := hst
    refine FinitePred.not_ge i₀ (FinitePred.subset (hacc b hb) ?_)
    intro m hm
    simp only [hst m hm]
    exact hfin
  · intro hno b hb
    obtain ⟨q, i₀, hst⟩ := exists_stabilizesAt hv hb
    refine FinitePred.subset (FinitePred.lt i₀) ?_
    intro m hm
    by_contra hcon
    rw [Nat.not_lt] at hcon
    rw [hst m hcon] at hm
    exact hno b q hb ⟨i₀, hst⟩ hm

/-! ## Run restriction -/

/-- `[HOL4-ltl]` `RUN_RESTR_LEMM`: restricting only ever shrinks a level. -/
theorem restrict_level_subset (hv : r.ValidFrom A S ξ) (hsub : T ⊆ r.level 0) :
    ∀ i, (r.restrict T).level i ⊆ r.level i := by
  intro i
  induction i with
  | zero => exact hsub
  | succ i ih =>
    intro x hx
    simp only [VWAA.Run.restrict, VWAA.Run.restrictLevel, FinSet.mem_biUnion] at hx
    obtain ⟨q, hq, hxq⟩ := hx
    exact hv.succ_sub i q (ih hq) hxq

/-- The restriction of a run is a run from the smaller level-0 set. -/
theorem restrict_validFrom (hv : r.ValidFrom A S ξ) (hsub : T ⊆ r.level 0) :
    (r.restrict T).ValidFrom A T ξ :=
  { init := rfl
    step := fun i q hq => hv.step i q (restrict_level_subset hv hsub i hq)
    succ_sub := fun _ _ hq => FinSet.subset_biUnion_of_mem _ hq
    no_orphan := fun _ _ hq => FinSet.mem_biUnion.mp hq }

/-- `[HOL4-ltl]` `RUN_RESTR_FIXP_LEMM`: a branch of the restriction is a branch of the original run. -/
theorem infBranch_of_restrict (hsub : T ⊆ r.level 0) (hb : (r.restrict T).InfBranch b) : r.InfBranch b :=
  ⟨hsub hb.1, hb.2⟩

/-- Acceptance survives restriction. -/
theorem acceptingRun_restrict (hsub : T ⊆ r.level 0) (hacc : A.AcceptingRun r) :
    A.AcceptingRun (r.restrict T) :=
  fun b hb => hacc b (infBranch_of_restrict hsub hb)

/-- The per-state language is antitone in its level-0 set. -/
theorem acceptsFrom_subset (h : A.AcceptsFrom S ξ) (hsub : T ⊆ S) : A.AcceptsFrom T ξ := by
  obtain ⟨r, hv, hacc⟩ := h
  have hsub' : T ⊆ r.level 0 := by rw [hv.init]; exact hsub
  exact ⟨r.restrict T, restrict_validFrom hv hsub', acceptingRun_restrict hsub' hacc⟩

/-! ## Backwards extension -/

/-- `[HOL4-ltl]` `BRANCH_SUFF_LEMM`: a state alive on level `n` is reached by a path from level 0. -/
theorem exists_path_to (hv : r.ValidFrom A S ξ) :
    ∀ n x, x ∈ r.level n → ∃ p : Nat → Q, p n = x ∧ p 0 ∈ r.level 0 ∧
      ∀ i, i < n → p (i + 1) ∈ r.succ i (p i) := by
  intro n
  induction n with
  | zero => exact fun x hx => ⟨fun _ => x, rfl, hx, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hv.no_orphan n x hx
    obtain ⟨p, hpn, hp0, hpstep⟩ := ih y hy
    refine ⟨fun i => if i = n + 1 then x else p i, by simp, by simpa using hp0, ?_⟩
    intro i hi
    rcases (by omega : i < n ∨ i = n) with h | h
    · show (if i + 1 = n + 1 then x else p (i + 1)) ∈ r.succ i (if i = n + 1 then x else p i)
      rw [if_neg (by omega : ¬ (i + 1 = n + 1)), if_neg (by omega : ¬ (i = n + 1))]
      exact hpstep i h
    · subst h
      show (if i + 1 = i + 1 then x else p (i + 1)) ∈ r.succ i (if i = i + 1 then x else p i)
      rw [if_pos rfl, if_neg (by omega : ¬ (i = i + 1)), hpn]
      exact hxy

/-! ## Run union -/

variable {r₁ r₂ : VWAA.Run Q} {S₁ S₂ : FinSet Q}

/-- The union never leaves the two runs' own levels. -/
theorem conj_level_subset (hv₁ : r₁.ValidFrom A S₁ ξ) (hv₂ : r₂.ValidFrom A S₂ ξ) :
    ∀ i, (r₁.conj r₂).level i ⊆ r₁.level i ∪ r₂.level i := by
  intro i
  induction i with
  | zero => exact fun x hx => hx
  | succ i ih =>
    intro x hx
    simp only [VWAA.Run.conj, VWAA.Run.conjLevel, FinSet.mem_biUnion] at hx
    obtain ⟨p, hp, hxp⟩ := hx
    simp only [VWAA.Run.conjSucc] at hxp
    by_cases hp1 : p ∈ r₁.level i
    · rw [if_pos hp1] at hxp
      exact FinSet.mem_union_left _ (hv₁.succ_sub i p hp1 hxp)
    · rw [if_neg hp1] at hxp
      have hp2 : p ∈ r₂.level i := by
        rcases FinSet.mem_union.mp (ih hp) with h | h
        · exact absurd h hp1
        · exact h
      exact FinSet.mem_union_right _ (hv₂.succ_sub i p hp2 hxp)

/-- The union of two runs on the same word is a run from the union of their level-0 sets. -/
theorem conj_validFrom (hv₁ : r₁.ValidFrom A S₁ ξ) (hv₂ : r₂.ValidFrom A S₂ ξ) :
    (r₁.conj r₂).ValidFrom A (S₁ ∪ S₂) ξ :=
  { init := by simp only [VWAA.Run.conj, VWAA.Run.conjLevel, hv₁.init, hv₂.init]
    step := by
      intro i q hq
      simp only [VWAA.Run.conj, VWAA.Run.conjSucc]
      by_cases hq1 : q ∈ r₁.level i
      · rw [if_pos hq1]; exact hv₁.step i q hq1
      · rw [if_neg hq1]
        have hq2 : q ∈ r₂.level i := by
          rcases FinSet.mem_union.mp (conj_level_subset hv₁ hv₂ i hq) with h | h
          · exact absurd h hq1
          · exact h
        exact hv₂.step i q hq2
    succ_sub := fun _ _ hq => FinSet.subset_biUnion_of_mem _ hq
    no_orphan := fun _ _ hq => FinSet.mem_biUnion.mp hq }

/-- Once a branch of the union is on the first run's levels it stays on them. -/
private theorem conj_absorbing (hv₁ : r₁.ValidFrom A S₁ ξ) (hb : (r₁.conj r₂).InfBranch b)
    {i₀ : Nat} (h : b i₀ ∈ r₁.level i₀) : ∀ i, i₀ ≤ i → b i ∈ r₁.level i := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact h
  | succ i _ ih =>
    have hstep := hb.2 i
    simp only [VWAA.Run.conj, VWAA.Run.conjSucc, if_pos ih] at hstep
    exact hv₁.succ_sub i (b i) ih hstep

/-- Acceptance survives run union, `[HOL4-ltl]` `CONJ_RUN_FIXP_LEMM`. -/
theorem acceptingRun_conj (hv₁ : r₁.ValidFrom A S₁ ξ)
    (hacc₁ : A.AcceptingRun r₁) (hacc₂ : A.AcceptingRun r₂) : A.AcceptingRun (r₁.conj r₂) := by
  intro b hb
  by_cases hcase : ∃ i, b i ∈ r₁.level i
  · obtain ⟨i₀, hi₀⟩ := hcase
    obtain ⟨p, hpn, hp0, hpstep⟩ := exists_path_to hv₁ i₀ (b i₀) hi₀
    have habs := conj_absorbing hv₁ hb hi₀
    have hb' : r₁.InfBranch fun i => if i < i₀ then p i else b i := by
      refine ⟨?_, ?_⟩
      · show (if 0 < i₀ then p 0 else b 0) ∈ r₁.level 0
        by_cases h0 : 0 < i₀
        · rw [if_pos h0]; exact hp0
        · rw [if_neg h0]
          have : i₀ = 0 := by omega
          subst this
          exact hi₀
      · intro i
        show (if i + 1 < i₀ then p (i + 1) else b (i + 1)) ∈ r₁.succ i (if i < i₀ then p i else b i)
        rcases Nat.lt_trichotomy (i + 1) i₀ with h | h | h
        · rw [if_pos h, if_pos (by omega : i < i₀)]
          exact hpstep i (by omega)
        · rw [if_neg (by omega : ¬ (i + 1 < i₀)), if_pos (by omega : i < i₀)]
          rw [← h] at hpn
          rw [← hpn]
          exact hpstep i (by omega)
        · have hmem := habs i (by omega)
          have hstep := hb.2 i
          simp only [VWAA.Run.conj, VWAA.Run.conjSucc, if_pos hmem] at hstep
          rw [if_neg (by omega : ¬ (i + 1 < i₀)), if_neg (by omega : ¬ (i < i₀))]
          exact hstep
    refine FinitePred.subset (FinitePred.union (FinitePred.lt i₀) (hacc₁ _ hb')) ?_
    intro m hm
    by_cases hmlt : m < i₀
    · exact Or.inl hmlt
    · refine Or.inr ?_
      show A.final (if m < i₀ then p m else b m)
      rw [if_neg hmlt]
      exact hm
  · simp only [_root_.not_exists] at hcase
    refine hacc₂ b ⟨?_, ?_⟩
    · have h0 := hb.1
      simp only [VWAA.Run.conj, VWAA.Run.conjLevel, FinSet.mem_union] at h0
      rcases h0 with h | h
      · exact absurd h (hcase 0)
      · exact h
    · intro i
      have hstep := hb.2 i
      simp only [VWAA.Run.conj, VWAA.Run.conjSucc, if_neg (hcase i)] at hstep
      exact hstep

/-- Two satisfiable level-0 sets are satisfiable together. -/
theorem acceptsFrom_union (h₁ : A.AcceptsFrom S₁ ξ) (h₂ : A.AcceptsFrom S₂ ξ) :
    A.AcceptsFrom (S₁ ∪ S₂) ξ := by
  obtain ⟨r₁, hv₁, hacc₁⟩ := h₁
  obtain ⟨r₂, hv₂, hacc₂⟩ := h₂
  exact ⟨r₁.conj r₂, conj_validFrom hv₁ hv₂, acceptingRun_conj hv₁ hacc₁ hacc₂⟩

/-! ## Level shift -/

/-- The shifted run is a run of the dropped word from `r`'s old level 1. -/
theorem shift_validFrom (hv : r.ValidFrom A S ξ) : r.shift.ValidFrom A (r.level 1) (ξ.drop 1) where
  init := rfl
  step i q hq := hv.step (i + 1) q hq
  succ_sub i q hq := hv.succ_sub (i + 1) q hq
  no_orphan i q hq := hv.no_orphan (i + 1) q hq

/-- A branch of the shifted run extends one level backwards to a branch of `r`. -/
theorem exists_infBranch_of_shift (hv : r.ValidFrom A S ξ) (hb : r.shift.InfBranch b) :
    ∃ b', r.InfBranch b' ∧ ∀ i, b i = b' (i + 1) := by
  obtain ⟨p, hp, hbp⟩ := hv.no_orphan 0 (b 0) hb.1
  refine ⟨fun i => if i = 0 then p else b (i - 1), ⟨by simpa using hp, ?_⟩, fun i => by simp⟩
  intro i
  match i with
  | 0 => simpa using hbp
  | i + 1 => simpa [VWAA.Run.shift] using hb.2 i

/-- Acceptance survives dropping level 0. -/
theorem acceptingRun_shift (hv : r.ValidFrom A S ξ) (hacc : A.AcceptingRun r) :
    A.AcceptingRun r.shift := by
  intro b hb
  obtain ⟨b', hb', heq⟩ := exists_infBranch_of_shift hv hb
  refine FinitePred.subset ((hacc b' hb').image (· - 1)) ?_
  intro i hi
  exact ⟨i + 1, show A.final (b' (i + 1)) from heq i ▸ hi, by simp⟩

/-- A fresh level 0 with a chosen successor set gives a run of the un-dropped word. -/
theorem prepend_validFrom {succ0 : Q → FinSet Q} (hv : r.ValidFrom A (r.level 0) (ξ.drop 1))
    (hstep0 : ∀ q ∈ S, ∃ g, (g, succ0 q) ∈ A.trans q ∧ g (ξ 0)) (hsub0 : ∀ q ∈ S, succ0 q ⊆ r.level 0)
    (horphan0 : ∀ q ∈ r.level 0, ∃ p ∈ S, q ∈ succ0 p) : (r.prepend S succ0).ValidFrom A S ξ where
  init := rfl
  step i q hq := by match i, hq with
    | 0, hq => exact hstep0 q hq
    | i + 1, hq => exact hv.step i q hq
  succ_sub i q hq := by match i, hq with
    | 0, hq => exact hsub0 q hq
    | i + 1, hq => exact hv.succ_sub i q hq
  no_orphan i q hq := by match i, hq with
    | 0, hq => exact horphan0 q hq
    | i + 1, hq => exact hv.no_orphan i q hq

/-- Shift undoes prepend exactly. -/
theorem prepend_shift {succ0 : Q → FinSet Q} : (r.prepend S succ0).shift = r := rfl

/-- Acceptance survives prepending a level. -/
theorem acceptingRun_prepend {succ0 : Q → FinSet Q} (hsub0 : ∀ q ∈ S, succ0 q ⊆ r.level 0)
    (hacc : A.AcceptingRun r) : A.AcceptingRun (r.prepend S succ0) := by
  intro b hb
  have hb' : r.InfBranch fun i => b (i + 1) :=
    ⟨hsub0 (b 0) hb.1 (hb.2 0), fun i => hb.2 (i + 1)⟩
  refine FinitePred.subset ((hacc _ hb').image (· + 1) |>.insert 0) ?_
  intro i hi
  match i with
  | 0 => exact Or.inl rfl
  | i + 1 => exact Or.inr ⟨i, hi, rfl⟩

end Lasso
