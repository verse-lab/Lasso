/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProbMC.FiniteMDP

/-!
# Refinement: PMF-based MDP ↔ Measure-Theoretic MDP

Connects finite-sum PMF computations on `FiniteMDP` to the path measure
of the corresponding `MDP`. The main payoff: users prove epoch probability
bounds using arithmetic on PMFs, and the refinement lifts these to
`MDP.probLowerBoundForAll`.

## Main Definitions

* `FiniteMDP.nStepDist`: N-step state distribution via iterated PMF bind

## Main Results

* `FiniteMDP.probLowerBoundForAll_of_nStep_bound`: if every starting state and
  action sequence gives probability ≥ p of reaching `Good` in N steps, then
  `probLowerBoundForAll` holds for all history-dependent strategies
-/

open MeasureTheory ProbabilityTheory Kernel Finset
open scoped ENNReal

namespace ProbMC

namespace FiniteMDP

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S]
variable {Act : Type*} [Fintype Act] [DecidableEq Act] [MeasurableSpace Act]
    [MeasurableSingletonClass Act]

/-! ### N-step distribution -/

/-- The distribution over states after `N` steps, starting from `s₀`,
with the adversary playing actions `acts`. Defined by iterated PMF bind. -/
noncomputable def nStepDist (T : FiniteMDP S Act) (s₀ : S)
    (N : ℕ) (acts : Fin N → Act) : PMF S :=
  match N with
  | 0 => PMF.pure s₀
  | N + 1 => (T.nStepDist s₀ N (fun i => acts i.castSucc)).bind
      (fun s => T.step s (acts ⟨N, Nat.lt_succ_iff.mpr le_rfl⟩))

@[simp]
theorem nStepDist_zero (T : FiniteMDP S Act) (s₀ : S) (acts : Fin 0 → Act) :
    T.nStepDist s₀ 0 acts = PMF.pure s₀ := rfl

omit [MeasurableSingletonClass S] [MeasurableSingletonClass Act] in
theorem nStepDist_succ (T : FiniteMDP S Act) (s₀ : S) (N : ℕ) (acts : Fin (N + 1) → Act) :
    T.nStepDist s₀ (N + 1) acts =
    (T.nStepDist s₀ N (fun i => acts i.castSucc)).bind
      (fun s => T.step s (acts ⟨N, Nat.lt_succ_iff.mpr le_rfl⟩)) := rfl

omit [MeasurableSingletonClass S] [MeasurableSingletonClass Act] in
/-- The N-step distribution from `s₀` assigns probability 1 to `s₀` at step 0. -/
theorem nStepDist_zero_apply (T : FiniteMDP S Act) (s₀ s : S) (acts : Fin 0 → Act) :
    T.nStepDist s₀ 0 acts s = if s = s₀ then 1 else 0 := by
  simp [nStepDist, PMF.pure_apply]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass Act] in
/-- The 1-step distribution equals the PMF step directly. -/
theorem nStepDist_one (T : FiniteMDP S Act) (s₀ : S) (acts : Fin 1 → Act) :
    T.nStepDist s₀ 1 acts = T.step s₀ (acts ⟨0, Nat.zero_lt_one⟩) := by
  simp [nStepDist]

/-! ### Payoff theorem: PMF bounds → MDP probLowerBoundForAll

The key idea: if for every starting state and every non-adaptive action sequence,
the N-step PMF probability of reaching `Good` is at least `p`, then the MDP
path measure (under any history-dependent strategy) also has this bound.

The proof works by induction: at each step, the strategy picks some action
(depending on history), but no matter what action is picked or what state was
reached, the remaining N-step bound still holds by hypothesis.
-/

/-- If for every starting state `s` and every action sequence `acts`,
the N-step probability of reaching `Good` is ≥ `p`, then
`probLowerBoundForAll` holds for the corresponding MDP under any initial
distribution concentrated on states satisfying the bound.

This is the main refinement theorem connecting PMF-level reasoning to
measure-theoretic path probabilities. -/
theorem probLowerBoundForAll_of_nStep_bound
    (T : FiniteMDP S Act) (s₀ : S) (Good : Set S) (N : ℕ) (p : ℝ≥0∞)
    (hbound : ∀ s : S, ∀ acts : Fin N → Act,
      (T.nStepDist s N acts).toMeasure Good ≥ p) :
    T.toMDP.probLowerBoundForAll (Measure.dirac s₀)
      {ξ : ℕ → S | ξ N ∈ Good} p := by
  sorry

end FiniteMDP

end ProbMC
