/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProbMC.MDP
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Finite MDPs via Probability Mass Functions

For finite-state protocols (e.g., Ben-Or consensus), transitions can be defined
via concrete probability mass functions `S → Act → PMF S` instead of abstract
Markov kernels. This avoids measure theory at the definition site.

## Main Definitions

* `FiniteMDP`: MDP defined via `step : S → Act → PMF S`
* `FiniteMDP.toMDP`: converts to the measure-theoretic `MDP` via `Kernel.ofFunOfCountable`

## Main Results

* `FiniteMDP.toMDP_step_apply`: the kernel at `(s, a)` equals `(step s a).toMeasure`
* `FiniteMDP.toMDP_step_apply_singleton`: the kernel at `{s'}` equals `step s a s'`
-/

open MeasureTheory ProbabilityTheory Kernel Finset
open scoped ENNReal

namespace ProbMC

/-- An MDP on finite state and action spaces, defined via probability mass functions.
Users specify `step s a : PMF S` giving the distribution over next states
when the current state is `s` and the adversary plays action `a`. -/
structure FiniteMDP (S : Type*) [Fintype S] [DecidableEq S] [MeasurableSpace S]
    (Act : Type*) [Fintype Act] [DecidableEq Act] [MeasurableSpace Act] where
  /-- Transition function: given current state and action, a PMF over next states. -/
  step : S → Act → PMF S

namespace FiniteMDP

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S]
variable {Act : Type*} [Fintype Act] [DecidableEq Act] [MeasurableSpace Act]
    [MeasurableSingletonClass Act]

/-! ### Conversion to measure-theoretic MDP -/

/-- The Markov kernel obtained from a `FiniteMDP` by converting each PMF to a measure.
For finite types with the discrete σ-algebra, `Kernel.ofFunOfCountable` provides
measurability for free. -/
noncomputable def toKernel (T : FiniteMDP S Act) : Kernel (S × Act) S :=
  Kernel.ofFunOfCountable (fun sa => (T.step sa.1 sa.2).toMeasure)

instance toKernel_isMarkov (T : FiniteMDP S Act) : IsMarkovKernel T.toKernel :=
  ⟨fun (s, a) => PMF.toMeasure.isProbabilityMeasure (T.step s a)⟩

/-- Convert a `FiniteMDP` to a measure-theoretic `MDP`. -/
noncomputable def toMDP (T : FiniteMDP S Act) : MDP S Act where
  step := T.toKernel

/-- The kernel of `toMDP` at `(s, a)` equals `(step s a).toMeasure`. -/
theorem toMDP_step_apply (T : FiniteMDP S Act) (s : S) (a : Act) :
    T.toMDP.step (s, a) = (T.step s a).toMeasure := rfl

/-- Pointwise: the kernel evaluated on a measurable set equals the PMF's measure. -/
theorem toMDP_step_apply_set (T : FiniteMDP S Act) (s : S) (a : Act) (E : Set S) :
    T.toMDP.step (s, a) E = (T.step s a).toMeasure E := rfl

/-- The kernel evaluated at a singleton `{s'}` equals `step s a s'`. -/
theorem toMDP_step_apply_singleton (T : FiniteMDP S Act) (s : S) (a : Act) (s' : S) :
    T.toMDP.step (s, a) {s'} = T.step s a s' := by
  rw [toMDP_step_apply]
  exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)

end FiniteMDP

end ProbMC
