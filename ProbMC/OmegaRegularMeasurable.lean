/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of ω-Regular Acceptance Conditions

We prove that acceptance sets of deterministic ω-automata are measurable in the
product σ-algebra on `ℕ → Alph`. This is the key ingredient for defining `Pr(φ)`.

The proof strategy:
1. The run function of a deterministic automaton on input `ξ` at step `n` depends
   only on `ξ(0), ..., ξ(n-1)`, hence is measurable.
2. Büchi acceptance ("visit F infinitely often") is a G_δ set:
   `⋂_n ⋃_k {ξ | run(ξ, n+k) ∈ F}` — countable intersection of countable unions
   of measurable sets.
3. Rabin acceptance is a Boolean combination of such sets, hence measurable.

## Main Definitions

* `DetOmegaAut`: deterministic ω-automaton (general, no acceptance condition)
* `DetOmegaAut.run`: the unique run on an input word
* `DetOmegaAut.buchiAcceptSet`: set of words accepted under Büchi condition

## Main Results

* `DetOmegaAut.measurable_run_at`: `fun ξ => run ξ n` is measurable
* `DetOmegaAut.measurableSet_buchiAcceptSet`: Büchi acceptance set is measurable
* `DetOmegaAut.measurableSet_rabinAcceptSet`: Rabin acceptance set is measurable
-/

open MeasureTheory Set

namespace ProbMC

/-- A deterministic ω-automaton over alphabet `Alph` with states `Q`.
No acceptance condition specified — that's layered on top. -/
structure DetOmegaAut (Q : Type*) (Alph : Type*) where
  /-- Initial state. -/
  init : Q
  /-- Transition function. -/
  trans : Q → Alph → Q

namespace DetOmegaAut

variable {Q : Type*} {Alph : Type*}

/-- The unique run of a deterministic automaton on input word `ξ`. -/
def run (A : DetOmegaAut Q Alph) (ξ : ℕ → Alph) : ℕ → Q
  | 0 => A.init
  | n + 1 => A.trans (A.run ξ n) (ξ n)

@[simp] theorem run_zero (A : DetOmegaAut Q Alph) (ξ : ℕ → Alph) :
    A.run ξ 0 = A.init := rfl

@[simp] theorem run_succ (A : DetOmegaAut Q Alph) (ξ : ℕ → Alph) (n : ℕ) :
    A.run ξ (n + 1) = A.trans (A.run ξ n) (ξ n) := rfl

/-- The set of words accepted under Büchi condition: visit `F` infinitely often. -/
def buchiAcceptSet (A : DetOmegaAut Q Alph) (F : Set Q) : Set (ℕ → Alph) :=
  {ξ | ∀ n, ∃ m, n ≤ m ∧ A.run ξ m ∈ F}

/-- "Visit F only finitely often": the complement of Büchi acceptance. -/
def finitelyOftenSet (A : DetOmegaAut Q Alph) (F : Set Q) : Set (ℕ → Alph) :=
  {ξ | ∃ n, ∀ m, n ≤ m → A.run ξ m ∉ F}

/-- Büchi acceptance as a countable intersection of countable unions. -/
theorem buchiAcceptSet_eq (A : DetOmegaAut Q Alph) (F : Set Q) :
    A.buchiAcceptSet F =
      ⋂ n, ⋃ k, (fun ξ => A.run ξ (n + k)) ⁻¹' F := by
  ext ξ
  simp only [buchiAcceptSet, mem_setOf_eq, mem_iInter, mem_iUnion, mem_preimage]
  constructor
  · intro h n
    obtain ⟨m, hnm, hm⟩ := h n
    refine ⟨m - n, ?_⟩
    rwa [Nat.add_sub_cancel' hnm]
  · intro h n
    obtain ⟨k, hk⟩ := h n
    exact ⟨n + k, Nat.le_add_right n k, hk⟩

/-- "Finitely often" as a countable union of countable intersections. -/
theorem finitelyOftenSet_eq (A : DetOmegaAut Q Alph) (F : Set Q) :
    A.finitelyOftenSet F =
      ⋃ n, ⋂ k, (fun ξ => A.run ξ (n + k)) ⁻¹' Fᶜ := by
  ext ξ
  simp only [finitelyOftenSet, mem_setOf_eq, mem_iUnion, mem_iInter, mem_preimage, mem_compl_iff]
  constructor
  · intro ⟨n, hn⟩
    exact ⟨n, fun k => hn (n + k) (Nat.le_add_right n k)⟩
  · intro ⟨n, hn⟩
    exact ⟨n, fun m hm => by have := hn (m - n); simp [Nat.add_sub_cancel' hm] at this; exact this⟩

/-- The set of words accepted under Rabin condition: for some pair (L, K),
visit K infinitely often and visit L only finitely often. -/
def rabinAcceptSet (A : DetOmegaAut Q Alph) (pairs : List (Set Q × Set Q)) :
    Set (ℕ → Alph) :=
  ⋃ p ∈ pairs, A.buchiAcceptSet p.2 ∩ A.finitelyOftenSet p.1

section Measurability

variable [MeasurableSpace Q] [MeasurableSpace Alph]

/-- The run function at time `n` is measurable, provided the transition function is. -/
theorem measurable_run_at (A : DetOmegaAut Q Alph)
    (hδ : Measurable (Function.uncurry A.trans)) (n : ℕ) :
    Measurable (fun ξ : ℕ → Alph => A.run ξ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    show Measurable (fun ξ => A.trans (A.run ξ n) (ξ n))
    exact hδ.comp (ih.prodMk (measurable_pi_apply n))

/-- The Büchi acceptance set is measurable (it's a G_δ set). -/
theorem measurableSet_buchiAcceptSet (A : DetOmegaAut Q Alph)
    (hδ : Measurable (Function.uncurry A.trans))
    {F : Set Q} (hF : MeasurableSet F) :
    MeasurableSet (A.buchiAcceptSet F) := by
  rw [buchiAcceptSet_eq]
  exact .iInter fun n => .iUnion fun k => (A.measurable_run_at hδ (n + k)) hF

/-- "Visit F only finitely often" is measurable (it's an F_σ set). -/
theorem measurableSet_finitelyOftenSet (A : DetOmegaAut Q Alph)
    (hδ : Measurable (Function.uncurry A.trans))
    {F : Set Q} (hF : MeasurableSet F) :
    MeasurableSet (A.finitelyOftenSet F) := by
  rw [finitelyOftenSet_eq]
  exact .iUnion fun n => .iInter fun k => (A.measurable_run_at hδ (n + k)) hF.compl

/-- The Rabin acceptance set is measurable. -/
theorem measurableSet_rabinAcceptSet (A : DetOmegaAut Q Alph)
    (hδ : Measurable (Function.uncurry A.trans))
    {pairs : List (Set Q × Set Q)}
    (hK : ∀ p ∈ pairs, MeasurableSet p.2) (hL : ∀ p ∈ pairs, MeasurableSet p.1) :
    MeasurableSet (A.rabinAcceptSet pairs) := by
  unfold rabinAcceptSet
  apply MeasurableSet.biUnion pairs.finite_toSet.countable
  intro p hp
  exact (A.measurableSet_buchiAcceptSet hδ (hK p hp)).inter
    (A.measurableSet_finitelyOftenSet hδ (hL p hp))

end Measurability

end DetOmegaAut

end ProbMC
