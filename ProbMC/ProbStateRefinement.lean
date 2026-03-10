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
  (non-adaptive actions)
* `FiniteMDP.nStepDistAdaptive`: N-step distribution with Markovian adaptive
  actions `(i : Fin N) → S → Act`

## Main Results

* `FiniteMDP.probLowerBoundForAll_of_adaptive_bound`: if every starting state
  and every Markovian adaptive action sequence gives probability ≥ p of
  reaching `Good` in N steps, then `probLowerBoundForAll` holds
* `FiniteMDP.probLowerBoundForAll_of_stepIndep_bound`: corollary for
  action-independent transitions (the common case in coin-toss protocols)

## Design Note: Why Adaptive Actions?

A non-adaptive action sequence `acts : Fin N → Act` cannot model a
history-dependent adversary that adapts actions to the current state.
An adaptive adversary can achieve strictly lower probability than any
fixed action sequence (counterexample: 2-state MDP where the adversary
picks the worst action per state at each step).

For protocols with action-independent transitions (e.g., coin tosses),
the non-adaptive and adaptive bounds coincide, so both formulations work.
-/

open MeasureTheory ProbabilityTheory Kernel Finset
open scoped ENNReal

namespace ProbMC

namespace FiniteMDP

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S]
variable {Act : Type*} [Fintype Act] [DecidableEq Act] [MeasurableSpace Act]
    [MeasurableSingletonClass Act]

/-! ### N-step distribution (non-adaptive) -/

/-- The distribution over states after `N` steps, starting from `s₀`,
with the adversary playing actions `acts`. Defined by iterated PMF bind. -/
noncomputable def nStepDist (T : FiniteMDP S Act) (s₀ : S)
    (N : ℕ) (acts : Fin N → Act) : PMF S :=
  match N with
  | 0 => PMF.pure s₀
  | N + 1 => (T.nStepDist s₀ N (fun i => acts i.castSucc)).bind
      (fun s => T.step s (acts ⟨N, Nat.lt_succ_iff.mpr le_rfl⟩))

omit [MeasurableSingletonClass S] [MeasurableSingletonClass Act] in
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

/-! ### N-step distribution (Markovian adaptive)

A Markovian adaptive action sequence picks the action at step `i` based on
the current state: `acts i s` gives the action when at state `s` at step `i`.
This models adversaries that can observe the current state but not the
full history. For finite-horizon problems, Markovian strategies are
without loss of generality (by the Bellman principle). -/

/-- The distribution over states after `N` steps with Markovian adaptive actions.
At step `i`, the adversary observes the current state `s` and plays `acts i s`. -/
noncomputable def nStepDistAdaptive (T : FiniteMDP S Act) (s₀ : S)
    (N : ℕ) (acts : (i : Fin N) → S → Act) : PMF S :=
  match N with
  | 0 => PMF.pure s₀
  | N + 1 => (T.nStepDistAdaptive s₀ N (fun i => acts i.castSucc)).bind
      (fun s => T.step s (acts ⟨N, Nat.lt_succ_iff.mpr le_rfl⟩ s))

omit [MeasurableSingletonClass S] [MeasurableSingletonClass Act] in
@[simp]
theorem nStepDistAdaptive_zero (T : FiniteMDP S Act) (s₀ : S)
    (acts : (i : Fin 0) → S → Act) :
    T.nStepDistAdaptive s₀ 0 acts = PMF.pure s₀ := rfl

omit [MeasurableSingletonClass S] [MeasurableSingletonClass Act] in
theorem nStepDistAdaptive_succ (T : FiniteMDP S Act) (s₀ : S) (N : ℕ)
    (acts : (i : Fin (N + 1)) → S → Act) :
    T.nStepDistAdaptive s₀ (N + 1) acts =
    (T.nStepDistAdaptive s₀ N (fun i => acts i.castSucc)).bind
      (fun s => T.step s (acts ⟨N, Nat.lt_succ_iff.mpr le_rfl⟩ s)) := rfl

omit [MeasurableSingletonClass S] [MeasurableSingletonClass Act] in
/-- Non-adaptive is a special case of adaptive: a fixed action sequence
is a constant function of the state. -/
theorem nStepDist_eq_nStepDistAdaptive_const (T : FiniteMDP S Act) (s₀ : S)
    (N : ℕ) (acts : Fin N → Act) :
    T.nStepDist s₀ N acts = T.nStepDistAdaptive s₀ N (fun i _ => acts i) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [nStepDist, nStepDistAdaptive]
    congr 1
    exact ih (fun i => acts i.castSucc)

omit [MeasurableSingletonClass S] [MeasurableSingletonClass Act] in
/-- If steps are action-independent, adaptive distributions equal non-adaptive ones. -/
theorem nStepDistAdaptive_eq_of_stepIndep (T : FiniteMDP S Act) (s₀ : S)
    (N : ℕ) (acts : (i : Fin N) → S → Act) (acts' : Fin N → Act)
    (hstep : ∀ s : S, ∀ a₁ a₂ : Act, T.step s a₁ = T.step s a₂) :
    T.nStepDistAdaptive s₀ N acts = T.nStepDist s₀ N acts' := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [nStepDistAdaptive, nStepDist]
    congr 1
    · exact ih (fun i => acts i.castSucc) (fun i => acts' i.castSucc)
    · ext s : 1
      exact hstep s _ _

/-! ### Payoff theorems -/

/-- **Main refinement theorem (adaptive version).**
If for every starting state `s` and every Markovian adaptive action
sequence `acts`, the N-step probability of reaching `Good` is ≥ `p`,
then `probLowerBoundForAll` holds for the corresponding MDP.

The hypothesis quantifies over all starting states and all Markovian
adaptive strategies, which is sufficient because optimal adversaries
for finite-horizon problems are Markovian. -/
theorem probLowerBoundForAll_of_adaptive_bound
    (T : FiniteMDP S Act) (s₀ : S) (Good : Set S) (N : ℕ) (p : ℝ≥0∞)
    (hbound : ∀ s : S, ∀ acts : (i : Fin N) → S → Act,
      (T.nStepDistAdaptive s N acts).toMeasure Good ≥ p) :
    T.toMDP.probLowerBoundForAll (Measure.dirac s₀)
      {ξ : ℕ → S | ξ N ∈ Good} p := by
  sorry

/-- **Corollary for action-independent transitions.**
When `T.step s a₁ = T.step s a₂` for all states and actions (transitions
don't depend on the adversary's action, e.g., coin tosses), any non-adaptive
bound automatically holds for all strategies. -/
theorem probLowerBoundForAll_of_stepIndep_bound
    (T : FiniteMDP S Act) (s₀ : S) (Good : Set S) (N : ℕ) (p : ℝ≥0∞)
    (hstep : ∀ s : S, ∀ a₁ a₂ : Act, T.step s a₁ = T.step s a₂)
    (hbound : ∀ s : S, ∀ acts : Fin N → Act,
      (T.nStepDist s N acts).toMeasure Good ≥ p) :
    T.toMDP.probLowerBoundForAll (Measure.dirac s₀)
      {ξ : ℕ → S | ξ N ∈ Good} p := by
  apply probLowerBoundForAll_of_adaptive_bound
  intro s acts
  have h := hbound s (fun i => acts i s)
  rw [nStepDistAdaptive_eq_of_stepIndep T s N acts (fun i => acts i s) hstep]
  exact h

end FiniteMDP

end ProbMC
