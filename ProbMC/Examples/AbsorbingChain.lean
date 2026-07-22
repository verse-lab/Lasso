/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProbMC.Refinement.FiniteDTMC
import ProbMC.Refinement.TraceProduct
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Example: Absorbing Chain — Pr[◇(v = 0)] = 1

A minimal end-to-end example of the ProbMC verification pipeline.

## The System

State `v ∈ Fin (n+2)`, parameterized by `n : ℕ`:
- If `v ≠ 0`: uniformly pick a new `v` from `Fin (n+2)`
- If `v = 0`: stay at 0 (absorbing)

## Architecture

```
Layer 1: RelationalTransitionSystem (Veil-style, with prob as state variable)
    ↓  [rts_trace_prob_eq_traceWeight]
Layer 2: FiniteDTMC (PMF-based)
    ↓  [pathMeasure_cylinder_eq_nStepDist — existing, sorry-free]
Layer 3: Pr[◇(v = 0)] = 1 (measure-theoretic)
```
-/

open MeasureTheory ProbabilityTheory ENNReal Finset
open scoped ENNReal

namespace ProbMC.Examples

variable (n : ℕ)

/-! ### Layer 1: Relational transition system with `prob` as state variable -/

/-- Minimal relational transition system (no Veil dependency). -/
structure SimpleRTS (ρ σ l : Type) where
  assumptions : ρ → Prop
  init : ρ → σ → Prop
  tr : ρ → σ → l → σ → Prop

/-- State of the absorbing chain, including the probability accumulator. -/
structure ACState (n : ℕ) where
  v : Fin (n + 2)
  prob : ℝ≥0∞

/-- The absorbing chain as a relational transition system.
- Background theory: `Unit` (no parameters beyond `n`)
- State: `ACState n` (value + probability accumulator)
- Labels: `Unit` (single transition type)

When `v ≠ 0`, the successor's `v` is unconstrained (nondeterministic, modeling
the uniform random choice), and `prob` is divided by `n+2` (the number of branches).
When `v = 0`, the state is absorbing. -/
noncomputable def absorbingChainRTS :
    SimpleRTS Unit (ACState n) Unit where
  assumptions := fun _ => True
  init := fun _ s => s.prob = 1
  tr := fun _ s _ s' =>
    (s.v ≠ 0 ∧ s'.prob = s.prob / (↑(n + 2) : ℝ≥0∞)) ∨
    (s.v = 0 ∧ s'.v = 0 ∧ s'.prob = s.prob)

/-! ### Layer 2: FiniteDTMC definition -/

/-- The uniform PMF on `Fin (n+2)`. Each element has probability `1 / (n+2)`. -/
noncomputable def uniformFin : PMF (Fin (n + 2)) :=
  PMF.ofFintype (fun _ => (1 : ℝ≥0∞) / (↑(n + 2) : ℝ≥0∞)) (by
    simp [Fintype.card_fin]
    exact ENNReal.mul_inv_cancel (by simp) (by simp))

@[simp]
theorem uniformFin_apply (v : Fin (n + 2)) :
    uniformFin n v = 1 / (↑(n + 2) : ℝ≥0∞) := by
  simp [uniformFin]

/-- The transition PMF: uniform from nonzero states, absorbing at 0. -/
noncomputable def absorbingStep (v : Fin (n + 2)) : PMF (Fin (n + 2)) :=
  if v = 0 then PMF.pure 0 else uniformFin n

/-- The absorbing chain as a `FiniteDTMC`. -/
noncomputable def absorbingChain : FiniteDTMC (Fin (n + 2)) where
  step := absorbingStep n

/-! ### Step lemmas -/

theorem absorbingStep_zero : absorbingStep n (0 : Fin (n + 2)) = PMF.pure 0 := by
  simp [absorbingStep]

theorem absorbingStep_nonzero (v : Fin (n + 2)) (hv : v ≠ 0) :
    absorbingStep n v = uniformFin n := by
  simp [absorbingStep, hv]

theorem absorbingStep_zero_at_zero :
    absorbingStep n (0 : Fin (n + 2)) (0 : Fin (n + 2)) = 1 := by
  simp [absorbingStep_zero, PMF.pure_apply]

theorem absorbingStep_nonzero_apply (v : Fin (n + 2)) (hv : v ≠ 0) (w : Fin (n + 2)) :
    absorbingStep n v w = 1 / (↑(n + 2) : ℝ≥0∞) := by
  simp [absorbingStep_nonzero n v hv]

/-! ### PMF arithmetic: N-step bound -/

/-- The decay ratio: probability of NOT reaching 0 in one step from a nonzero state. -/
noncomputable def decayRatio : ℝ≥0∞ := ↑(n + 1) / ↑(n + 2)

theorem decayRatio_le_one : decayRatio n ≤ 1 := by
  unfold decayRatio
  apply ENNReal.div_le_of_le_mul
  simp

theorem decayRatio_lt_one : decayRatio n < 1 := by
  unfold decayRatio
  rw [ENNReal.div_lt_iff (by simp) (by simp)]
  simp only [one_mul]
  exact_mod_cast Nat.lt_succ_of_le (Nat.le_refl (n + 1))

private theorem sum_nonzero_step_zero :
    ∑ v ∈ univ.erase (0 : Fin (n + 2)), absorbingStep n 0 v = 0 := by
  apply Finset.sum_eq_zero
  intro v hv
  simp [absorbingStep, PMF.pure_apply, Finset.ne_of_mem_erase hv]

private theorem sum_nonzero_step_nonzero (w : Fin (n + 2)) (hw : w ≠ 0) :
    ∑ v ∈ univ.erase (0 : Fin (n + 2)), absorbingStep n w v =
    decayRatio n := by
  simp only [absorbingStep, hw, ↓reduceIte, uniformFin, PMF.ofFintype_apply, decayRatio,
    ENNReal.div_eq_inv_mul]
  rw [Finset.sum_const, nsmul_eq_mul,
    Finset.card_erase_of_mem (mem_univ (0 : Fin (n + 2)))]
  simp [Fintype.card_fin]; ring

/-- The probability of being at a nonzero state after `k` steps. -/
private noncomputable def notAtZeroProb (s₀ : Fin (n + 2)) (k : ℕ) : ℝ≥0∞ :=
  ∑ v ∈ univ.erase (0 : Fin (n + 2)), (absorbingChain n).nStepDist s₀ k v

private theorem notAtZeroProb_add (s₀ : Fin (n + 2)) (k : ℕ) :
    (absorbingChain n).nStepDist s₀ k 0 + notAtZeroProb n s₀ k = 1 := by
  unfold notAtZeroProb
  have h1 : ∑ v : Fin (n + 2), (absorbingChain n).nStepDist s₀ k v = 1 := by
    have := PMF.tsum_coe ((absorbingChain n).nStepDist s₀ k)
    rwa [tsum_fintype] at this
  rw [← h1, ← Finset.add_sum_erase _ _ (mem_univ (0 : Fin (n + 2)))]

private theorem notAtZeroProb_succ_le (s₀ : Fin (n + 2)) (k : ℕ) :
    notAtZeroProb n s₀ (k + 1) ≤ notAtZeroProb n s₀ k * decayRatio n := by
  unfold notAtZeroProb
  simp only [FiniteDTMC.nStepDist_succ, PMF.bind_apply, absorbingChain]
  simp_rw [tsum_fintype]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.add_sum_erase _ _ (mem_univ (0 : Fin (n + 2)))]
  rw [sum_nonzero_step_zero, mul_zero, zero_add]
  have : ∀ w ∈ univ.erase (0 : Fin (n + 2)),
      ({ step := absorbingStep n } : FiniteDTMC _).nStepDist s₀ k w *
        ∑ i ∈ univ.erase 0, (absorbingStep n w) i =
      ({ step := absorbingStep n } : FiniteDTMC _).nStepDist s₀ k w *
        decayRatio n := fun w hw =>
    congr_arg _ (sum_nonzero_step_nonzero n w (Finset.ne_of_mem_erase hw))
  rw [Finset.sum_congr rfl this, Finset.sum_mul]

private theorem notAtZeroProb_le_pow (s₀ : Fin (n + 2)) (k : ℕ) :
    notAtZeroProb n s₀ k ≤ (decayRatio n) ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    unfold notAtZeroProb
    calc ∑ v ∈ univ.erase 0, (absorbingChain n).nStepDist s₀ 0 v
        ≤ ∑ v : Fin (n + 2), (absorbingChain n).nStepDist s₀ 0 v :=
          Finset.sum_le_sum_of_subset (Finset.erase_subset 0 univ)
      _ = 1 := by
          have := PMF.tsum_coe ((absorbingChain n).nStepDist s₀ 0)
          rwa [tsum_fintype] at this
  | succ k ih =>
    calc notAtZeroProb n s₀ (k + 1)
        ≤ notAtZeroProb n s₀ k * decayRatio n := notAtZeroProb_succ_le n s₀ k
      _ ≤ (decayRatio n) ^ k * decayRatio n := by gcongr
      _ = (decayRatio n) ^ (k + 1) := (pow_succ _ _).symm

/-- After k steps, the probability of being at state 0 is at least `1 - decayRatio^k`. -/
theorem nStepDist_zero_ge (s₀ : Fin (n + 2)) (k : ℕ) :
    (absorbingChain n).nStepDist s₀ k 0 ≥ 1 - (decayRatio n) ^ k := by
  have hadd := notAtZeroProb_add n s₀ k
  have hle := notAtZeroProb_le_pow n s₀ k
  have hle1 : notAtZeroProb n s₀ k ≤ 1 := by
    rw [← hadd]; exact le_add_left le_rfl
  have hne_top : notAtZeroProb n s₀ k ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top hle1
  have heq : (absorbingChain n).nStepDist s₀ k 0 = 1 - notAtZeroProb n s₀ k :=
    (ENNReal.cancel_of_ne hne_top).tsub_eq_of_eq_add hadd.symm |>.symm
  rw [heq]
  exact tsub_le_tsub_left hle 1

/-! ### Main theorem: Pr[◇(v = 0)] = 1 -/

/-- The event "eventually reach state 0" is measurable. -/
theorem measurableSet_eventually_zero :
    MeasurableSet {ξ : ℕ → Fin (n + 2) | ∃ k, ξ k = 0} := by
  have : {ξ : ℕ → Fin (n + 2) | ∃ k, ξ k = 0} =
      ⋃ k, (fun ξ => ξ k) ⁻¹' {(0 : Fin (n + 2))} := by ext; simp
  rw [this]
  exact MeasurableSet.iUnion fun k =>
    (measurable_pi_apply k) (measurableSet_singleton 0)

/-- **Main theorem**: Starting from any state, the absorbing chain reaches
state 0 with probability 1. -/
theorem prob_eventually_zero_eq_one (s₀ : Fin (n + 2)) :
    (absorbingChain n).toDTMC.pathMeasureFrom s₀
      {ξ : ℕ → Fin (n + 2) | ∃ k, ξ k = 0} = 1 := by
  apply le_antisymm
  · exact prob_le_one
  · suffices h : ∀ k, 1 - (decayRatio n) ^ k ≤
        (absorbingChain n).toDTMC.pathMeasureFrom s₀
          {ξ : ℕ → Fin (n + 2) | ∃ k, ξ k = 0} by
      set m := (absorbingChain n).toDTMC.pathMeasureFrom s₀
        {ξ : ℕ → Fin (n + 2) | ∃ k, ξ k = 0}
      have h_le_pow : ∀ k, 1 - m ≤ (decayRatio n) ^ k := fun k =>
        calc 1 - m ≤ 1 - (1 - (decayRatio n) ^ k) := tsub_le_tsub_left (h k) 1
          _ ≤ (decayRatio n) ^ k := tsub_tsub_le
      have h_tendsto := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (decayRatio_lt_one n)
      have h_zero : 1 - m ≤ 0 := ge_of_tendsto' h_tendsto h_le_pow
      simp only [nonpos_iff_eq_zero, tsub_eq_zero_iff_le] at h_zero
      exact h_zero
    intro k
    have hsub : {ξ : ℕ → Fin (n + 2) | ξ k = 0} ⊆
        {ξ : ℕ → Fin (n + 2) | ∃ j, ξ j = 0} := fun ξ hξ => ⟨k, hξ⟩
    have hcyl : (absorbingChain n).toDTMC.pathMeasureFrom s₀
        {ξ : ℕ → Fin (n + 2) | ξ k = 0} =
        (absorbingChain n).nStepDist s₀ k 0 := by
      have heq : {ξ : ℕ → Fin (n + 2) | ξ k = 0} =
          {ξ : ℕ → Fin (n + 2) | ξ k ∈ ({0} : Set (Fin (n + 2)))} := by
        ext; simp
      rw [heq, FiniteDTMC.pathMeasure_cylinder_eq_nStepDist _ _
        k {0} (measurableSet_singleton _),
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    calc 1 - (decayRatio n) ^ k
        ≤ (absorbingChain n).nStepDist s₀ k 0 := nStepDist_zero_ge n s₀ k
      _ = (absorbingChain n).toDTMC.pathMeasureFrom s₀
            {ξ : ℕ → Fin (n + 2) | ξ k = 0} := hcyl.symm
      _ ≤ (absorbingChain n).toDTMC.pathMeasureFrom s₀
            {ξ : ℕ → Fin (n + 2) | ∃ j, ξ j = 0} := measure_mono hsub

/-! ### Layer 1 ↔ Layer 2: RTS traces produce traceWeight -/

/-- Extract the `v`-components from an RTS trace (the "path" in FiniteDTMC terms). -/
def rtsPath (states : Fin (N + 1) → ACState n) : Fin N → Fin (n + 2) :=
  fun i => (states i.succ).v

/-- Each RTS step multiplies `prob` by exactly `absorbingStep v v'`. -/
theorem rts_step_prob (s s' : ACState n) (htr : (absorbingChainRTS n).tr () s () s') :
    s'.prob = s.prob * absorbingStep n s.v s'.v := by
  rcases htr with ⟨hv, hp⟩ | ⟨hv, hv', hp⟩
  · -- Case v ≠ 0: prob' = prob / (n+2) = prob * (1/(n+2)) = prob * absorbingStep v v'
    rw [hp, absorbingStep_nonzero_apply n s.v hv, ENNReal.div_eq_inv_mul,
      ENNReal.div_eq_inv_mul]
    ring
  · -- Case v = 0: prob' = prob, v' = 0, absorbingStep 0 0 = 1
    rw [hp, hv, hv', absorbingStep_zero_at_zero, mul_one]

/-- The accumulated `prob` in an RTS trace equals the initial prob times the
`traceWeight` of the corresponding FiniteDTMC path. This is the key connection
between Layer 1 (RTS with prob as state variable) and Layer 2 (FiniteDTMC
trace weights).

Generalized: does not require initial prob = 1, making induction work cleanly. -/
theorem rts_trace_prob_eq_traceWeight (states : Fin (N + 1) → ACState n)
    (hsteps : ∀ i : Fin N, (absorbingChainRTS n).tr ()
      (states i.castSucc) () (states i.succ)) :
    (states (Fin.last N)).prob =
      (states 0).prob *
        FiniteDTMC.traceWeight (absorbingChain n) (states 0).v N (rtsPath n states) := by
  induction N with
  | zero => simp [FiniteDTMC.traceWeight]
  | succ N ih =>
    -- First step: prob(1) = prob(0) * absorbingStep(v₀, v₁)
    have htr0 := hsteps ⟨0, Nat.zero_lt_succ _⟩
    have hstep0 := rts_step_prob n (states 0) (states 1) htr0
    -- Tail trace: shift by 1
    let tail : Fin (N + 1) → ACState n := fun j => states j.succ
    have htail_steps : ∀ i : Fin N, (absorbingChainRTS n).tr ()
        (tail i.castSucc) () (tail i.succ) := by
      intro ⟨i, hi⟩
      have h := hsteps ⟨i + 1, by omega⟩
      simp only [tail]
      convert h using 2
    have hih := ih tail htail_steps
    -- tail's last = states' last
    have hlast_eq : (states (Fin.last (N + 1))).prob = (tail (Fin.last N)).prob :=
      congr_arg ACState.prob (show states (Fin.last (N + 1)) = tail (Fin.last N) from
        congr_arg states (Fin.ext (by simp)))
    rw [hlast_eq, hih]
    -- Goal: (tail 0).prob * traceWeight(tail(0).v, N, rtsPath tail)
    --     = (states 0).prob * traceWeight(v₀, N+1, rtsPath states)
    -- Key: tail 0 = states 1 (up to Fin equality)
    have htail0_eq : tail 0 = states 1 := by
      show states (Fin.succ 0) = _; congr 1
    rw [show (tail 0).prob = (states 1).prob from congr_arg _ htail0_eq,
        hstep0,
        show (tail 0).v = (states 1).v from congr_arg _ htail0_eq]
    -- Goal: p₀ * step(v₀,v₁) * traceWeight(v₁, N, rtsPath tail)
    --     = p₀ * traceWeight(v₀, N+1, rtsPath states)
    -- rtsPath states 0 = (states 1).v
    have hpath0 : rtsPath n states 0 = (states 1).v := by
      show (states (Fin.succ 0)).v = _; congr 1
    -- rtsPath states ∘ Fin.succ = rtsPath tail
    have hpath_tail : rtsPath n states ∘ Fin.succ = rtsPath n tail := by
      ext ⟨i, hi⟩; simp only [rtsPath, tail, Function.comp]
    conv_rhs =>
      rw [show FiniteDTMC.traceWeight (absorbingChain n) (states 0).v (N + 1) (rtsPath n states) =
        (absorbingChain n).step (states 0).v (rtsPath n states 0) *
          FiniteDTMC.traceWeight (absorbingChain n) (rtsPath n states 0) N
            (rtsPath n states ∘ Fin.succ) from rfl]
    rw [hpath0, hpath_tail]
    exact mul_assoc _ _ _

/-- Corollary: for a valid RTS trace starting with `prob = 1`, the final `prob`
equals the trace weight. -/
theorem rts_trace_prob_eq_traceWeight' (states : Fin (N + 1) → ACState n)
    (hinit : (states 0).prob = 1)
    (hsteps : ∀ i : Fin N, (absorbingChainRTS n).tr ()
      (states i.castSucc) () (states i.succ)) :
    (states (Fin.last N)).prob =
      FiniteDTMC.traceWeight (absorbingChain n) (states 0).v N (rtsPath n states) := by
  rw [rts_trace_prob_eq_traceWeight n states hsteps, hinit, one_mul]

end ProbMC.Examples
