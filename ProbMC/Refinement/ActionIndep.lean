/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProbMC.Refinement.FiniteDTMC
import ProbMC.FiniteMDP

/-!
# Action-Independent MDP Refinement (No Bellman Principle Needed)

For MDPs with **action-independent transitions** (`∀ s a₁ a₂, step s a₁ = step s a₂`),
the adversary's strategy has no effect on the path measure. This means:
1. The MDP reduces to a DTMC (any action gives the same kernel)
2. The path measure is the same for ALL strategies
3. A PMF bound on the DTMC's N-step distribution directly gives `probLowerBoundForAll`

This avoids the Bellman principle entirely. The common case: coin-toss protocols
(Ben-Or, VABA, DAG-Rider) where probabilistic steps are coin flips independent of
the adversary's scheduling decisions.

## Main Results

* `FiniteMDP.itKernelUnderStrategy_eq_of_stepIndep`: all strategies give the same
  Ionescu-Tulcea kernel when transitions are action-independent
* `FiniteMDP.pathMeasure_eq_of_stepIndep`: path measure is strategy-independent
* `FiniteMDP.probLowerBoundForAll_of_stepIndep_dtmc`: the user-facing theorem —
  PMF bound → `probLowerBoundForAll`, no Bellman sorry
-/

open MeasureTheory ProbabilityTheory Kernel Finset
open scoped ENNReal

namespace ProbMC

namespace FiniteMDP

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S]
variable {Act : Type*} [Fintype Act] [DecidableEq Act] [MeasurableSpace Act]
    [MeasurableSingletonClass Act]

/-! ### Extracting a FiniteDTMC from an action-independent FiniteMDP -/

/-- When transitions are action-independent, extract a `FiniteDTMC` by picking
any fixed action. The choice doesn't matter since all actions give the same PMF. -/
noncomputable def toFiniteDTMC (T : FiniteMDP S Act) [Inhabited Act] : FiniteDTMC S where
  step s := T.step s default

omit [MeasurableSingletonClass S] [MeasurableSingletonClass Act] in
/-- For action-independent transitions, `toFiniteDTMC.step` agrees with `T.step s a`
for any action `a`. -/
theorem toFiniteDTMC_step_eq (T : FiniteMDP S Act) [Inhabited Act]
    (hstep : ∀ s : S, ∀ a₁ a₂ : Act, T.step s a₁ = T.step s a₂)
    (s : S) (a : Act) : T.toFiniteDTMC.step s = T.step s a := by
  exact hstep s default a

/-! ### Strategy independence of the kernel -/

/-- The MDP kernel at `(s, a)` depends only on `s` when transitions are
action-independent. -/
theorem toMDP_step_eq_of_stepIndep (T : FiniteMDP S Act)
    (hstep : ∀ s : S, ∀ a₁ a₂ : Act, T.step s a₁ = T.step s a₂)
    (s : S) (a₁ a₂ : Act) : T.toMDP.step (s, a₁) = T.toMDP.step (s, a₂) := by
  simp only [toMDP_step_apply]
  congr 1
  exact hstep s a₁ a₂

/-- For action-independent transitions, the Ionescu-Tulcea kernel under any
strategy gives the same measure as the DTMC's IT kernel on each set.

**Proof idea**: Both IT kernels apply a transition to the current state `h_n`.
The MDP version uses `step(h_n, π(h))`, the DTMC version uses `step(h_n, default)`.
By action-independence, these give the same PMF, hence the same measure. -/
theorem itKernelUnderStrategy_apply_eq_of_stepIndep (T : FiniteMDP S Act) [Inhabited Act]
    (hstep : ∀ s : S, ∀ a₁ a₂ : Act, T.step s a₁ = T.step s a₂)
    (π : T.toMDP.Strategy) (n : ℕ)
    (h : ∀ _ : Iic n, S) (E : Set S) (_hE : MeasurableSet E) :
    T.toMDP.itKernelUnderStrategy π n h E =
    T.toFiniteDTMC.toDTMC.itKernel n h E := by
  -- Unfold: itKernelUnderStrategy = step ∘ₖ det(h ↦ (h_n, π n h))
  --         itKernel = kernel ∘ₖ det(h ↦ h_n)
  -- After comp + det: step(h_n, π n h)(E) = kernel(h_n)(E)
  unfold MDP.itKernelUnderStrategy DTMC.itKernel
  simp only [comp_apply, deterministic_apply]
  -- Simplify ∘ₘ Dirac to direct application
  rw [Measure.dirac_bind (Kernel.measurable _),
      Measure.dirac_bind (Kernel.measurable _)]
  -- Action-independence: step with any action = step with default
  have : T.toMDP.step (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩, π.policy n h) =
      T.toFiniteDTMC.toDTMC.kernel (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
    rw [toMDP_step_apply, FiniteDTMC.toDTMC_kernel_apply]
    congr 1
    exact hstep _ _ _
  rw [this]

theorem itKernelUnderStrategy_eq_of_stepIndep (T : FiniteMDP S Act) [Inhabited Act]
    (hstep : ∀ s : S, ∀ a₁ a₂ : Act, T.step s a₁ = T.step s a₂)
    (π : T.toMDP.Strategy) (n : ℕ) :
    T.toMDP.itKernelUnderStrategy π n = T.toFiniteDTMC.toDTMC.itKernel n := by
  ext h E hE
  exact itKernelUnderStrategy_apply_eq_of_stepIndep T hstep π n h E hE

/-- For action-independent transitions, the path measure under any strategy
equals the DTMC path measure. -/
theorem pathMeasure_eq_dtmc_of_stepIndep (T : FiniteMDP S Act) [Inhabited Act]
    (hstep : ∀ s : S, ∀ a₁ a₂ : Act, T.step s a₁ = T.step s a₂)
    (π : T.toMDP.Strategy) (μ₀ : Measure S) [IsProbabilityMeasure μ₀] :
    T.toMDP.pathMeasure π μ₀ = T.toFiniteDTMC.toDTMC.pathMeasure μ₀ := by
  simp only [MDP.pathMeasure, DTMC.pathMeasure]
  congr 1
  funext n
  exact itKernelUnderStrategy_eq_of_stepIndep T hstep π n

/-! ### The user-facing refinement theorem (sorry-free modulo cylinder measure) -/

/-- **Main theorem for action-independent protocols.**

If the N-step PMF distribution of the DTMC gives probability ≥ `p` of
reaching `Good` from state `s₀`, then `probLowerBoundForAll` holds for the
MDP under any initial distribution `Dirac s₀`.

This avoids the Bellman principle: since all strategies produce the same
path measure, the DTMC bound directly transfers to the MDP.

**Dependencies**: uses `pathMeasure_marginal_eq_nStep` (1 sorry in FiniteDTMC.lean)
for connecting `trajMeasure` to kernel power. -/
theorem probLowerBoundForAll_of_stepIndep_dtmc
    (T : FiniteMDP S Act) [Inhabited Act] (s₀ : S)
    (Good : Set S) (hGood : MeasurableSet Good) (N : ℕ) (p : ℝ≥0∞)
    (hstep : ∀ s : S, ∀ a₁ a₂ : Act, T.step s a₁ = T.step s a₂)
    (hbound : (T.toFiniteDTMC.nStepDist s₀ N).toMeasure Good ≥ p) :
    T.toMDP.probLowerBoundForAll (Measure.dirac s₀)
      {ξ : ℕ → S | ξ N ∈ Good} p := by
  intro π
  rw [pathMeasure_eq_dtmc_of_stepIndep T hstep π]
  exact FiniteDTMC.probBound_of_nStepDist_bound T.toFiniteDTMC s₀ N Good hGood p hbound

end FiniteMDP

end ProbMC
