/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProbMC.DTMC

/-!
# Markov Decision Processes

An MDP models systems with both nondeterministic choices (adversary/scheduler)
and probabilistic transitions (coin tosses). Fixing an adversary strategy
reduces an MDP to a DTMC, enabling path measure construction via Ionescu-Tulcea.

This is the compilation target for Veil protocol specifications that use both
`pick` (adversarial) and `coin_toss` (probabilistic) primitives.

## Main Definitions

* `MDP`: Markov Decision Process with state space `S` and action space `Act`
* `MDP.MemorylessStrategy`: stationary strategy mapping states to actions
* `MDP.resolveKernel`: transition kernel obtained by fixing a strategy
* `MDP.toDTMC`: the DTMC obtained from an MDP under a fixed strategy
* `MDP.probLowerBoundForAll`: probability lower bound uniform over all strategies
* `MDP.almostSurelyForAll`: almost-sure property uniform over all strategies

## Design Notes

For finite-state protocols (e.g., Ben-Or consensus with fixed `n`), all
measurability obligations are trivially satisfied since the discrete
σ-algebra makes everything measurable.

History-dependent strategies are needed for the full Ben-Or proof (the
adversary sees all past states and coin outcomes). These are supported via
`Strategy`, which uses Ionescu-Tulcea to construct path measures for
non-Markovian executions.
-/

open Finset MeasureTheory ProbabilityTheory Kernel
open scoped ENNReal

namespace ProbMC

/-- A Markov Decision Process on state space `S` with action space `Act`.
At each step, the adversary picks an action `a : Act`, and the system
transitions according to the Markov kernel `step` applied to `(s, a)`. -/
structure MDP (S : Type*) [MeasurableSpace S] (Act : Type*) [MeasurableSpace Act] where
  /-- Transition kernel: given current state and adversary action,
      a probability distribution on next states. -/
  step : Kernel (S × Act) S
  /-- The transition kernel is Markov. -/
  [step_markov : IsMarkovKernel step]

attribute [instance] MDP.step_markov

namespace MDP

variable {S : Type*} [MeasurableSpace S] {Act : Type*} [MeasurableSpace Act]

/-! ### Memoryless (stationary) strategies -/

/-- A memoryless (stationary) strategy: maps current state to action.
Sufficient for optimal control in discounted/average-reward MDPs,
but the full Ben-Or proof requires history-dependent strategies. -/
structure MemorylessStrategy (M : MDP S Act) where
  /-- The policy function. -/
  policy : S → Act
  /-- The policy is measurable. -/
  measurable_policy : Measurable policy

/-- The transition kernel obtained by fixing a memoryless strategy:
at state `s`, pair it with `π(s)` and apply the MDP step kernel. -/
noncomputable def resolveKernel (M : MDP S Act) (π : M.MemorylessStrategy) : Kernel S S :=
  M.step ∘ₖ Kernel.deterministic
    (fun s => (s, π.policy s))
    (measurable_id.prodMk π.measurable_policy)

instance resolveKernel_isMarkov (M : MDP S Act) (π : M.MemorylessStrategy) :
    IsMarkovKernel (M.resolveKernel π) := by
  unfold resolveKernel; infer_instance

/-- The DTMC obtained by fixing a memoryless strategy in an MDP. -/
noncomputable def toDTMC (M : MDP S Act) (π : M.MemorylessStrategy) : DTMC S where
  kernel := M.resolveKernel π

/-- Path measure of an MDP under a memoryless strategy and initial distribution. -/
noncomputable def pathMeasureMemoryless (M : MDP S Act) (π : M.MemorylessStrategy)
    (μ₀ : Measure S) [IsProbabilityMeasure μ₀] : Measure (ℕ → S) :=
  (M.toDTMC π).pathMeasure μ₀

instance pathMeasureMemoryless_isProbability (M : MDP S Act) (π : M.MemorylessStrategy)
    (μ₀ : Measure S) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (M.pathMeasureMemoryless π μ₀) := by
  unfold pathMeasureMemoryless; infer_instance

/-! ### History-dependent strategies

A history-dependent strategy can base its action on the full execution history.
This is needed for modeling strong adversaries (as in Ben-Or's consensus)
that observe all past states and coin outcomes.

Fixing a history-dependent strategy yields a non-homogeneous Markov chain,
whose path measure is constructed via Ionescu-Tulcea with step-dependent kernels. -/

/-- A history-dependent strategy: at step `n`, maps the partial trajectory
`(s₀, s₁, ..., sₙ)` to an action. -/
structure Strategy (M : MDP S Act) where
  /-- At step `n`, given history up to step `n`, choose an action. -/
  policy : (n : ℕ) → (∀ _ : Iic n, S) → Act
  /-- Each step's policy is measurable. -/
  measurable_policy : ∀ n, Measurable (policy n)

/-- Ionescu-Tulcea kernel for an MDP under a history-dependent strategy:
at step `n`, read the partial trajectory, apply the strategy to get an action,
pair the current state with the action, and apply the MDP step kernel. -/
noncomputable def itKernelUnderStrategy (M : MDP S Act) (π : M.Strategy) (n : ℕ) :
    Kernel (∀ _ : Iic n, S) S :=
  M.step ∘ₖ Kernel.deterministic
    (fun (h : ∀ _ : Iic n, S) =>
      (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩, π.policy n h))
    ((measurable_pi_apply _).prodMk (π.measurable_policy n))

instance itKernelUnderStrategy_isMarkov (M : MDP S Act) (π : M.Strategy) (n : ℕ) :
    IsMarkovKernel (M.itKernelUnderStrategy π n) := by
  unfold itKernelUnderStrategy; infer_instance

/-- Path measure of an MDP under a history-dependent strategy and initial distribution,
constructed via the Ionescu-Tulcea theorem. -/
noncomputable def pathMeasure (M : MDP S Act) (π : M.Strategy)
    (μ₀ : Measure S) [IsProbabilityMeasure μ₀] : Measure (ℕ → S) :=
  trajMeasure μ₀ (M.itKernelUnderStrategy π)

instance pathMeasure_isProbability (M : MDP S Act) (π : M.Strategy)
    (μ₀ : Measure S) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (M.pathMeasure π μ₀) := by
  unfold pathMeasure; infer_instance

/-! ### Probabilistic properties quantified over all strategies -/

/-- A measurable set of paths has probability at least `p` under all
history-dependent adversary strategies. -/
def probLowerBoundForAll (M : MDP S Act) (μ₀ : Measure S) [IsProbabilityMeasure μ₀]
    (E : Set (ℕ → S)) (p : ℝ≥0∞) : Prop :=
  ∀ π : M.Strategy, M.pathMeasure π μ₀ E ≥ p

/-- A measurable set of paths has probability 1 under all
history-dependent adversary strategies. -/
def almostSurelyForAll (M : MDP S Act) (μ₀ : Measure S) [IsProbabilityMeasure μ₀]
    (E : Set (ℕ → S)) : Prop :=
  M.probLowerBoundForAll μ₀ E 1

theorem almostSurelyForAll_iff (M : MDP S Act) (μ₀ : Measure S) [IsProbabilityMeasure μ₀]
    (E : Set (ℕ → S)) :
    M.almostSurelyForAll μ₀ E ↔ ∀ π : M.Strategy, M.pathMeasure π μ₀ E = 1 := by
  constructor
  · intro h π
    have h1 := h π
    have h2 := measure_ne_top (M.pathMeasure π μ₀) E
    exact le_antisymm (prob_le_one) h1
  · intro h π
    exact (h π).ge

/-- Lifting a memoryless strategy to a history-dependent strategy. -/
def MemorylessStrategy.toStrategy {M : MDP S Act} (π : M.MemorylessStrategy) : M.Strategy where
  policy := fun n h => π.policy (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  measurable_policy := fun _ =>
    π.measurable_policy.comp (measurable_pi_apply _)

end MDP

end ProbMC
