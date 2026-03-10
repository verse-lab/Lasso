/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Discrete-Time Markov Chains

A DTMC is defined as a Markov kernel `κ : Kernel S S` on a measurable state space `S`.
The path measure on infinite trajectories `ℕ → S` is constructed via the Ionescu-Tulcea
theorem from Mathlib.

## Main Definitions

* `DTMC`: a DTMC with state space `S` and a Markov transition kernel
* `DTMC.itKernel`: the Ionescu-Tulcea kernel lifting `κ` to history-dependent form
* `DTMC.pathMeasure`: probability measure on `ℕ → S` via Ionescu-Tulcea

## Main Results

* `DTMC.pathMeasure_isProbability`: the path measure is a probability measure
-/

open Finset MeasureTheory ProbabilityTheory Kernel
open scoped ENNReal

namespace ProbMC

/-- A Discrete-Time Markov Chain on a measurable state space `S`. -/
structure DTMC (S : Type*) [MeasurableSpace S] where
  /-- The transition kernel. -/
  kernel : Kernel S S
  /-- The transition kernel is Markov (each row is a probability distribution). -/
  [isMarkov : IsMarkovKernel kernel]

attribute [instance] DTMC.isMarkov

namespace DTMC

variable {S : Type*} [MeasurableSpace S]

section ITKernel

/-- The Ionescu-Tulcea kernel for a DTMC at step `n`: project the partial trajectory
`(X₀, ..., Xₙ)` to its last coordinate `Xₙ`, then apply the transition kernel. -/
noncomputable def itKernel (D : DTMC S) (n : ℕ) :
    Kernel (∀ _i : Iic n, S) S :=
  D.kernel ∘ₖ Kernel.deterministic
    (fun (x : ∀ _i : Iic n, S) => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

instance itKernel_isMarkov (D : DTMC S) (n : ℕ) : IsMarkovKernel (D.itKernel n) := by
  unfold itKernel; infer_instance

end ITKernel

section PathMeasure

/-- The path measure on infinite trajectories `ℕ → S`, starting from initial
distribution `μ₀`. Constructed via the Ionescu-Tulcea theorem. -/
noncomputable def pathMeasure (D : DTMC S) (μ₀ : Measure S) [IsProbabilityMeasure μ₀] :
    Measure (ℕ → S) :=
  trajMeasure μ₀ D.itKernel

instance pathMeasure_isProbability (D : DTMC S) (μ₀ : Measure S) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (D.pathMeasure μ₀) := by
  unfold pathMeasure; infer_instance

/-- The path measure starting from a single state `s`, using the Dirac distribution. -/
noncomputable def pathMeasureFrom [MeasurableSingletonClass S] (D : DTMC S) (s : S) :
    Measure (ℕ → S) :=
  D.pathMeasure (Measure.dirac s)

instance pathMeasureFrom_isProbability [MeasurableSingletonClass S] (D : DTMC S) (s : S) :
    IsProbabilityMeasure (D.pathMeasureFrom s) := by
  unfold pathMeasureFrom; infer_instance

end PathMeasure

section NStep

/-- The `n`-step transition kernel: probability of reaching state `s'` from `s`
in exactly `n` steps. -/
noncomputable def nStep (D : DTMC S) (n : ℕ) : Kernel S S := D.kernel ^ n

/-- The 0-step kernel is the identity. -/
theorem nStep_zero (D : DTMC S) : D.nStep 0 = Kernel.id := pow_zero _

/-- The 1-step kernel is the transition kernel itself. -/
theorem nStep_one (D : DTMC S) : D.nStep 1 = D.kernel := pow_one _

/-- Chapman-Kolmogorov: `(m+n)`-step = compose `m`-step then `n`-step. -/
theorem nStep_add (D : DTMC S) (m n : ℕ) :
    D.nStep (m + n) = D.nStep m ∘ₖ D.nStep n := by
  simp [nStep, pow_add]

end NStep

end DTMC

end ProbMC
