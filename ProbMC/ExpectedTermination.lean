/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProbMC.IndependentEpochs
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Expected Termination Bounds

Many randomized protocols terminate in expected O(1) rounds. The proof pattern:

1. Each epoch succeeds independently with probability ≥ p > 0
2. Pr(no success in first k+1 epochs) ≤ (1-p)^(k+1)   [geometric tail]
3. E[first success epoch] ≤ 1/p                          [geometric series]

This file provides the geometric tail bound and expected value bound,
building on the almost-sure termination from `IndependentEpochs.lean`.

## Main Results

* `geometric_tail_bound`: Pr(⋂ᵢ≤ₖ Eᵢᶜ) ≤ (1-p)^(k+1) from independence
* `expected_stopping_time_le`: ∑ₖ Pr(T > k) ≤ p⁻¹
* `MDP.expected_epoch_bound`: MDP-level version for all strategies
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal

namespace ProbMC

/-! ### Independence of complements -/

/-- If events are independent, their complements satisfy the product formula.
This follows from `iIndepSet_iff`: `(E i)ᶜ` is measurable w.r.t. `generateFrom {E i}`. -/
theorem iIndepSet_compl_meas_biInter {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : ℕ → Set Ω}
    (hindep : iIndepSet E μ)
    (s : Finset ℕ) :
    μ (⋂ i ∈ s, (E i)ᶜ) = ∏ i ∈ s, μ ((E i)ᶜ) := by
  rw [iIndepSet_iff] at hindep
  exact hindep s (fun i _ =>
    (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)).compl)

/-! ### Complement probability -/

/-- For a probability measure, μ(Eᶜ) = 1 - μ(E). -/
theorem prob_compl_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Set Ω} (hE : MeasurableSet E) :
    μ Eᶜ = 1 - μ E :=
  prob_compl_eq_one_sub hE

/-- If μ(E) ≥ p, then μ(Eᶜ) ≤ 1 - p. -/
theorem prob_compl_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Set Ω} (hE : MeasurableSet E)
    {p : ℝ≥0∞} (hbound : μ E ≥ p) :
    μ Eᶜ ≤ 1 - p := by
  rw [prob_compl_eq hE]
  exact tsub_le_tsub_left hbound 1

/-! ### Geometric tail bound -/

/-- If independent events each have Pr(Eₙ) ≥ p, then
Pr(none of E₀, ..., Eₖ occurs) ≤ (1-p)^(k+1). -/
theorem geometric_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : ℕ → Set Ω}
    (hmeas : ∀ n, MeasurableSet (E n))
    (hindep : iIndepSet E μ)
    {p : ℝ≥0∞}
    (hbound : ∀ n, μ (E n) ≥ p)
    (k : ℕ) :
    μ (⋂ i ∈ Finset.range (k + 1), (E i)ᶜ) ≤ (1 - p) ^ (k + 1) := by
  rw [iIndepSet_compl_meas_biInter hindep]
  calc ∏ i ∈ Finset.range (k + 1), μ ((E i)ᶜ)
      ≤ ∏ i ∈ Finset.range (k + 1), (1 - p) := by
        apply Finset.prod_le_prod'
        intro i _
        exact prob_compl_le (hmeas i) (hbound i)
    _ = (1 - p) ^ (k + 1) := by
        rw [Finset.prod_const, Finset.card_range]

/-! ### Expected value bound -/

/-- The tail sum ∑ₖ Pr(T > k) ≤ p⁻¹, where Pr(T > k) ≤ (1-p)^(k+1).
Combined with the tail-sum formula E[T] = ∑ₖ Pr(T ≥ k+1), this gives
E[first success epoch] ≤ 1/p.

Proof: ∑ₖ (1-p)^(k+1) = (1-p) · ∑ₖ (1-p)^k = (1-p) · (1-(1-p))⁻¹ ≤ p⁻¹ -/
theorem expected_stopping_time_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : ℕ → Set Ω}
    (hmeas : ∀ n, MeasurableSet (E n))
    (hindep : iIndepSet E μ)
    {p : ℝ≥0∞} (hp1 : p ≤ 1)
    (hbound : ∀ n, μ (E n) ≥ p) :
    ∑' k, μ (⋂ i ∈ Finset.range (k + 1), (E i)ᶜ) ≤ p⁻¹ := by
  calc ∑' k, μ (⋂ i ∈ Finset.range (k + 1), (E i)ᶜ)
      ≤ ∑' k, (1 - p) ^ (k + 1) := by
        apply ENNReal.tsum_le_tsum
        exact geometric_tail_bound hmeas hindep hbound
    _ = (1 - p) * (1 - (1 - p))⁻¹ :=
        ENNReal.tsum_geometric_add_one (1 - p)
    _ ≤ 1 * p⁻¹ := by
        gcongr
        · exact tsub_le_self
        · rw [ENNReal.sub_sub_cancel (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hp1]
    _ = p⁻¹ := one_mul _

/-! ### MDP-level expected termination bound -/

/-- If for every strategy, the events "epoch n succeeds" are independent with
probability ≥ p > 0, then for every strategy the expected stopping time is ≤ 1/p.

This is expressed as: ∑ₖ Pr(no success in first k+1 epochs) ≤ p⁻¹.
Combined with `almostSurelyForAll_of_epoch_bound` (Pr = 1), this gives
both almost-sure termination and a finite expected time bound. -/
theorem MDP.expected_epoch_bound
    {S : Type*} [MeasurableSpace S] {Act : Type*} [MeasurableSpace Act]
    (M : MDP S Act) (μ₀ : Measure S) [IsProbabilityMeasure μ₀]
    {E : ℕ → Set (ℕ → S)}
    (hmeas : ∀ n, MeasurableSet (E n))
    (hindep : ∀ π : M.Strategy, iIndepSet E (M.pathMeasure π μ₀))
    {p : ℝ≥0∞} (hp1 : p ≤ 1)
    (hbound : ∀ n, M.probLowerBoundForAll μ₀ (E n) p) :
    ∀ π : M.Strategy,
      ∑' k, M.pathMeasure π μ₀ (⋂ i ∈ Finset.range (k + 1), (E i)ᶜ) ≤ p⁻¹ := by
  intro π
  exact expected_stopping_time_le hmeas (hindep π) hp1 (fun n => hbound n π)

end ProbMC
