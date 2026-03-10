/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProbMC.MDP
import Mathlib.Probability.BorelCantelli

/-!
# Independent Epochs Termination

Many randomized distributed protocols (Ben-Or, Bracha, randomized leader election)
share the same probabilistic termination argument:

1. Group execution into "epochs" (pairs of rounds, phases, etc.)
2. Each epoch succeeds with probability ≥ p > 0, regardless of adversary
3. Different epochs involve independent coin tosses
4. By the second Borel-Cantelli lemma: Pr(some epoch succeeds) = 1

This file provides reusable infrastructure for this pattern.

## Main Results

* `almostSure_of_independent_events`: if independent events each have
  probability ≥ p > 0, then some event occurs with probability 1
* `MDP.almostSurelyForAll_of_epoch_bound`: lifts this to MDPs —
  if each epoch succeeds with probability ≥ p for all strategies,
  then success is almost sure for all strategies
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace ProbMC

/-! ### Tsum divergence helper -/

/-- If `f n ≥ p > 0` for all `n : ℕ`, then `∑' n, f n = ∞`. -/
theorem ENNReal.tsum_eq_top_of_pos_lower_bound {f : ℕ → ℝ≥0∞} {p : ℝ≥0∞}
    (hp : p ≠ 0) (hf : ∀ n, p ≤ f n) : ∑' n, f n = ∞ := by
  have h1 : ∑' (_ : ℕ), p ≤ ∑' n, f n := ENNReal.tsum_le_tsum hf
  have h2 : ∑' (_ : ℕ), p = ∞ := ENNReal.tsum_const_eq_top_of_ne_zero hp
  rw [h2] at h1
  exact top_unique h1

/-! ### Pure measure-theoretic result -/

/-- If a sequence of independent measurable events each has probability at least
`p > 0`, then the union has probability 1. This follows from the second
Borel-Cantelli lemma: limsup (infinitely often) has measure 1, and
limsup ⊆ union. -/
theorem almostSure_of_independent_events {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : ℕ → Set Ω}
    (hmeas : ∀ n, MeasurableSet (E n))
    (hindep : iIndepSet E μ)
    {p : ℝ≥0∞} (hp : 0 < p)
    (hbound : ∀ n, μ (E n) ≥ p) :
    μ (⋃ n, E n) = 1 := by
  have htsum : ∑' n, μ (E n) = ∞ :=
    ENNReal.tsum_eq_top_of_pos_lower_bound hp.ne' hbound
  have hlimsup : μ (limsup E atTop) = 1 :=
    measure_limsup_eq_one hmeas hindep htsum
  have hsub : μ (limsup E atTop) ≤ μ (⋃ n, E n) :=
    measure_mono limsup_le_iSup
  exact le_antisymm prob_le_one (hlimsup ▸ hsub)

/-! ### MDP-level result -/

/-- If for every adversary strategy, the events "epoch `n` succeeds" are
independent with probability ≥ p > 0, then success is almost sure
for all strategies.

This is the key reusable pattern for probabilistic liveness of
randomized distributed protocols. -/
theorem MDP.almostSurelyForAll_of_epoch_bound
    {S : Type*} [MeasurableSpace S] {Act : Type*} [MeasurableSpace Act]
    (M : MDP S Act) (μ₀ : Measure S) [IsProbabilityMeasure μ₀]
    {E : ℕ → Set (ℕ → S)}
    (hmeas : ∀ n, MeasurableSet (E n))
    (hindep : ∀ π : M.Strategy, iIndepSet E (M.pathMeasure π μ₀))
    {p : ℝ≥0∞} (hp : 0 < p)
    (hbound : ∀ n, M.probLowerBoundForAll μ₀ (E n) p) :
    M.almostSurelyForAll μ₀ (⋃ n, E n) := by
  intro π
  exact (almostSure_of_independent_events hmeas (hindep π) hp (fun n => hbound n π)).ge

end ProbMC
