/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProbMC.DTMC
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Finite DTMCs via Probability Mass Functions

A `FiniteDTMC` defines a Discrete-Time Markov Chain on a finite state space using
concrete probability mass functions `S → PMF S` instead of abstract Markov kernels.

This is the building block for the "implicit adversary" approach: the user models
adversarial choices as part of the state, resulting in a DTMC (no separate action
space). Transition probabilities are defined via PMFs, and a refinement theorem
connects PMF-level reasoning to the measure-theoretic `pathMeasure`.

## Main Definitions

* `FiniteDTMC`: DTMC defined via `step : S → PMF S`
* `FiniteDTMC.toDTMC`: converts to the measure-theoretic `DTMC`
* `FiniteDTMC.nStepDist`: N-step state distribution via iterated PMF bind

## Main Results

* `FiniteDTMC.nStepDist_eq_toDTMC_nStep`: PMF N-step distribution equals
  kernel power applied to a singleton
* `FiniteDTMC.pathMeasure_cylinder_eq_nStepDist`: pathMeasure of
  `{ξ | ξ N ∈ Good}` equals `nStepDist.toMeasure Good`
-/

open MeasureTheory ProbabilityTheory Kernel Finset Preorder
open scoped ENNReal

namespace ProbMC

/-- A Discrete-Time Markov Chain on a finite state space, defined via probability
mass functions. Users specify `step s : PMF S` giving the distribution over next
states when the current state is `s`. -/
structure FiniteDTMC (S : Type*) [Fintype S] [DecidableEq S] [MeasurableSpace S] where
  /-- Transition function: given current state, a PMF over next states. -/
  step : S → PMF S

namespace FiniteDTMC

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S]

/-! ### Conversion to measure-theoretic DTMC -/

/-- The Markov kernel obtained from a `FiniteDTMC` by converting each PMF to a measure.
For finite types with the discrete σ-algebra, `Kernel.ofFunOfCountable` provides
measurability for free. -/
noncomputable def toKernel (T : FiniteDTMC S) : Kernel S S :=
  Kernel.ofFunOfCountable (fun s => (T.step s).toMeasure)

instance toKernel_isMarkov (T : FiniteDTMC S) : IsMarkovKernel T.toKernel :=
  ⟨fun s => PMF.toMeasure.isProbabilityMeasure (T.step s)⟩

/-- Convert a `FiniteDTMC` to a measure-theoretic `DTMC`. -/
noncomputable def toDTMC (T : FiniteDTMC S) : DTMC S where
  kernel := T.toKernel

/-- The kernel of `toDTMC` at state `s` equals `(step s).toMeasure`. -/
theorem toDTMC_kernel_apply (T : FiniteDTMC S) (s : S) :
    T.toDTMC.kernel s = (T.step s).toMeasure := rfl

/-- The kernel evaluated at a singleton `{s'}` equals `step s s'`. -/
theorem toDTMC_kernel_apply_singleton (T : FiniteDTMC S) (s s' : S) :
    T.toDTMC.kernel s {s'} = T.step s s' := by
  rw [toDTMC_kernel_apply]
  exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)

/-! ### N-step distribution via iterated PMF bind -/

/-- The distribution over states after `N` steps, starting from `s₀`.
Defined by iterated PMF bind:
- 0 steps: `PMF.pure s₀`
- N+1 steps: bind the N-step distribution with one more step -/
noncomputable def nStepDist (T : FiniteDTMC S) (s₀ : S) : (N : ℕ) → PMF S
  | 0 => PMF.pure s₀
  | N + 1 => (T.nStepDist s₀ N).bind T.step

omit [MeasurableSingletonClass S] in
@[simp]
theorem nStepDist_zero (T : FiniteDTMC S) (s₀ : S) :
    T.nStepDist s₀ 0 = PMF.pure s₀ := rfl

omit [MeasurableSingletonClass S] in
theorem nStepDist_succ (T : FiniteDTMC S) (s₀ : S) (N : ℕ) :
    T.nStepDist s₀ (N + 1) = (T.nStepDist s₀ N).bind T.step := rfl

omit [MeasurableSingletonClass S] in
/-- The 0-step distribution assigns probability 1 to `s₀`. -/
theorem nStepDist_zero_apply (T : FiniteDTMC S) (s₀ s : S) :
    T.nStepDist s₀ 0 s = if s = s₀ then 1 else 0 := by
  simp [nStepDist, PMF.pure_apply]

omit [MeasurableSingletonClass S] in
/-- The 1-step distribution equals the step PMF. -/
theorem nStepDist_one (T : FiniteDTMC S) (s₀ : S) :
    T.nStepDist s₀ 1 = T.step s₀ := by
  simp [nStepDist]

/-! ### Kernel power equals iterated PMF bind

The N-step kernel `T.toDTMC.kernel ^ N` applied at `s₀` should agree with
`T.nStepDist s₀ N` pointwise. -/

/-- The N-step kernel applied to a singleton equals the N-step PMF value. -/
theorem nStep_apply_singleton_eq_nStepDist (T : FiniteDTMC S) (s₀ : S) (N : ℕ) (s : S) :
    T.toDTMC.nStep N s₀ {s} = T.nStepDist s₀ N s := by
  induction N generalizing s₀ s with
  | zero =>
    -- κ^0 = id = Dirac, nStepDist 0 = pure; (PMF.pure).toMeasure = Dirac
    change Kernel.id s₀ {s} = (PMF.pure s₀) s
    rw [Kernel.id_apply,
      ← PMF.toMeasure_apply_singleton (PMF.pure s₀) s (measurableSet_singleton s),
      PMF.toMeasure_pure]
  | succ N ih =>
    -- Chapman-Kolmogorov: κ^(N+1) s₀ {s} = ∫ κ(b, {s}) d(κ^N s₀)(b)
    rw [DTMC.nStep,
      Kernel.pow_add_apply_eq_lintegral T.toDTMC.kernel N 1 s₀
        (measurableSet_singleton s),
      pow_one, lintegral_fintype]
    simp only [nStepDist_succ, PMF.bind_apply, tsum_fintype]
    apply Finset.sum_congr rfl
    intro b _
    rw [toDTMC_kernel_apply_singleton,
      show ((T.toDTMC.kernel ^ N) s₀) {b} = (T.nStepDist s₀ N) b from ih s₀ b]
    ring

/-- The N-step kernel as a measure equals the N-step PMF's toMeasure. -/
theorem nStep_eq_nStepDist_toMeasure (T : FiniteDTMC S) (s₀ : S) (N : ℕ) :
    T.toDTMC.nStep N s₀ = (T.nStepDist s₀ N).toMeasure := by
  apply Measure.ext_of_singleton
  intro s
  rw [nStep_apply_singleton_eq_nStepDist]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

/-! ### Cylinder set measure = N-step distribution

The key refinement theorem: the path measure of `{ξ | ξ N ∈ Good}` equals
the N-step PMF distribution applied to `Good`.

**Proof strategy**: The path measure marginal at step N should equal the
N-step kernel `D.kernel ^ N` applied to the initial distribution. For a
DTMC (homogeneous Markov chain), this is the standard marginal computation.
Combined with `nStep_eq_nStepDist_toMeasure`, we get the PMF connection.

The proof decomposes into:
1. `pathMeasure_marginal_eq_nStep`: marginal at step N = `kernel^N ∘ₘ μ₀`
   (standard Markov chain property, proved from `trajMeasure` API)
2. `nStep_eq_nStepDist_toMeasure`: kernel power = PMF bind (proved above) -/

omit [Fintype S] [DecidableEq S] [MeasurableSingletonClass S] in
/-- The N-th marginal of the DTMC path measure equals `kernel^N ∘ₘ μ₀`.

Proof by induction on N:
- Base case: the 0-th marginal of `trajMeasure` is the initial distribution.
- Inductive step: from `map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`,
  taking `Measure.snd` yields `marginal(N+1) = itKernel(N) ∘ₘ (... map frestrictLe N)`.
  For a DTMC, `itKernel N = kernel ∘ₖ det(proj_last)`, so this simplifies to
  `kernel ∘ₘ marginal(N)`. -/
private theorem map_eval_pathMeasure_eq_nStep (D : DTMC S) (μ₀ : Measure S)
    [IsProbabilityMeasure μ₀] (N : ℕ) :
    (D.pathMeasure μ₀).map (fun ξ => ξ N) = D.nStep N ∘ₘ μ₀ := by
  induction N with
  | zero =>
    rw [show D.nStep 0 = Kernel.id from pow_zero _, Measure.id_comp]
    unfold DTMC.pathMeasure trajMeasure
    rw [Measure.map_comp _ _ (measurable_pi_apply 0)]
    have hkernel : (traj D.itKernel 0).map (fun f : ℕ → S => f 0) =
        Kernel.deterministic
          (fun (h : ∀ _ : Iic 0, S) => h ⟨0, mem_Iic.mpr le_rfl⟩)
          (measurable_pi_apply _) := by
      have hfact : (fun (f : ℕ → S) => f 0) =
          (fun (h : ∀ _ : Iic 0, S) => h ⟨0, mem_Iic.mpr le_rfl⟩) ∘ (frestrictLe 0) := rfl
      rw [hfact, map_comp_right _ (measurable_frestrictLe 0) (measurable_pi_apply _),
        traj_map_frestrictLe, partialTraj_self, Kernel.id_map]
    rw [hkernel, Measure.deterministic_comp_eq_map (measurable_pi_apply _),
      Measure.map_map (measurable_pi_apply _) (MeasurableEquiv.piUnique _).symm.measurable]
    have : (fun (h : ∀ _ : Iic 0, S) => h ⟨0, mem_Iic.mpr le_rfl⟩) ∘
        (MeasurableEquiv.piUnique (fun _ : Iic 0 => S)).symm = id := by
      ext s; simp [MeasurableEquiv.piUnique]
    rw [this, Measure.map_id]
  | succ N ih =>
    -- Recurrence: marginal(N+1) = itKernel(N) ∘ₘ (pathMeasure.map (frestrictLe N))
    -- from snd of map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have h : (D.pathMeasure μ₀).map (frestrictLe N) ⊗ₘ D.itKernel N =
        (D.pathMeasure μ₀).map (fun x ↦ (frestrictLe N x, x (N + 1))) :=
      map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have step1 : D.itKernel N ∘ₘ ((D.pathMeasure μ₀).map (frestrictLe N)) =
        (D.pathMeasure μ₀).map (fun x => x (N + 1)) := by
      have hsnd := Measure.snd_compProd ((D.pathMeasure μ₀).map (frestrictLe N)) (D.itKernel N)
      rw [h] at hsnd; rw [← hsnd, Measure.snd]
      exact Measure.map_map measurable_snd (by fun_prop)
    rw [← step1]
    -- Decompose itKernel = kernel ∘ₖ det(proj_last), simplify via map_map
    unfold DTMC.itKernel
    rw [← Measure.comp_assoc, Measure.deterministic_comp_eq_map (measurable_pi_apply _)]
    have step3 : Measure.map (fun f : ∀ _ : Iic N, S => f ⟨N, mem_Iic.mpr le_rfl⟩)
        (Measure.map (frestrictLe N) (D.pathMeasure μ₀)) =
      (D.pathMeasure μ₀).map (fun ξ => ξ N) :=
      Measure.map_map (measurable_pi_apply _) (measurable_frestrictLe N)
    rw [step3, ih, Measure.comp_assoc]
    congr 1; unfold DTMC.nStep; congr 1
    exact (pow_succ' D.kernel N).symm

omit [Fintype S] [DecidableEq S] [MeasurableSingletonClass S] in
/-- The marginal distribution at step N of the path measure equals the N-step
kernel applied to the initial distribution.

This is the fundamental property of the Ionescu-Tulcea construction for
homogeneous Markov chains: the finite-dimensional marginals of `trajMeasure`
are given by kernel powers. -/
theorem pathMeasure_marginal_eq_nStep (D : DTMC S) (μ₀ : Measure S)
    [IsProbabilityMeasure μ₀] (N : ℕ) (Good : Set S) (hGood : MeasurableSet Good) :
    D.pathMeasure μ₀ {ξ : ℕ → S | ξ N ∈ Good} = (D.nStep N ∘ₘ μ₀) Good := by
  have : {ξ : ℕ → S | ξ N ∈ Good} = (fun ξ => ξ N) ⁻¹' Good := rfl
  rw [this, ← Measure.map_apply (measurable_pi_apply N) hGood,
    map_eval_pathMeasure_eq_nStep]

/-- **Main refinement theorem**: The path measure of `{ξ | ξ N ∈ Good}`
starting from state `s₀` equals the N-step PMF distribution applied to `Good`.

Users prove probability bounds using finite PMF arithmetic. This theorem
lifts those bounds to the measure-theoretic path measure. -/
theorem pathMeasure_cylinder_eq_nStepDist (T : FiniteDTMC S) (s₀ : S)
    (N : ℕ) (Good : Set S) (hGood : MeasurableSet Good) :
    T.toDTMC.pathMeasureFrom s₀ {ξ : ℕ → S | ξ N ∈ Good} =
    (T.nStepDist s₀ N).toMeasure Good := by
  unfold DTMC.pathMeasureFrom
  rw [pathMeasure_marginal_eq_nStep T.toDTMC (Measure.dirac s₀) N Good hGood]
  -- Goal: (⇑(D.kernel ^ N) ∘ₘ Measure.dirac s₀) Good = ...
  -- ∘ₘ is Measure.bind, so unfold and use dirac_bind
  change (Measure.dirac s₀).bind (⇑(T.toDTMC.kernel ^ N)) Good = _
  rw [Measure.dirac_bind (Kernel.measurable _)]
  -- Goal: (T.toDTMC.kernel ^ N) s₀ Good = ...
  rw [← DTMC.nStep, nStep_eq_nStepDist_toMeasure]

/-! ### User-facing probability bound -/

/-- If the N-step PMF distribution gives probability ≥ `p` of reaching `Good`
from every starting state, then the DTMC path measure satisfies the same bound. -/
theorem probBound_of_nStepDist_bound (T : FiniteDTMC S) (s₀ : S)
    (N : ℕ) (Good : Set S) (hGood : MeasurableSet Good)
    (p : ℝ≥0∞)
    (hbound : (T.nStepDist s₀ N).toMeasure Good ≥ p) :
    T.toDTMC.pathMeasureFrom s₀ {ξ : ℕ → S | ξ N ∈ Good} ≥ p := by
  rw [pathMeasure_cylinder_eq_nStepDist T s₀ N Good hGood]
  exact hbound

end FiniteDTMC

end ProbMC
