/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProbMC.Refinement.FiniteDTMC
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Trace Product Theorem

The **trace product theorem** connects `nStepDist` (the N-step distribution of a
`FiniteDTMC`) to the sum of **trace weights** — products of transition probabilities
along all paths of length N.

## Main results

* `nStepDist_first_step`: first-step decomposition of `nStepDist`
* `nStepDist_eq_sum_traceWeight`: `nStepDist s₀ N s` equals the sum of trace weights
  over all N-step paths from `s₀` that end at `s`
-/

open MeasureTheory ProbabilityTheory ENNReal Finset
open scoped ENNReal

namespace ProbMC.FiniteDTMC

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S]

/-! ### Trace weight and trace product theorem -/

/-- The endpoint of an N-step path starting from `s₀`. -/
def pathEnd (s₀ : S) : (N : ℕ) → (Fin N → S) → S
  | 0, _ => s₀
  | _ + 1, f => f (Fin.last _)

/-- The weight of an N-step path `s₀ → f 0 → f 1 → ... → f (N-1)`.
First-step recursive definition. -/
noncomputable def traceWeight (T : FiniteDTMC S) (s₀ : S) : (N : ℕ) → (Fin N → S) → ℝ≥0∞
  | 0, _ => 1
  | N + 1, f => T.step s₀ (f 0) * traceWeight T (f 0) N (f ∘ Fin.succ)

omit [DecidableEq S] [MeasurableSpace S] in
/-- Decompose a sum over `Fin (N+1) → S` via `Fin.cons`. -/
private theorem sum_fin_cons_decomp {N : ℕ}
    (F : (Fin (N + 1) → S) → ℝ≥0∞) :
    ∑ g : Fin (N + 1) → S, F g = ∑ s₁ : S, ∑ f : Fin N → S, F (Fin.cons s₁ f) := by
  have := (Fin.consEquiv (fun _ => S)).sum_comp F
  rw [Fintype.sum_prod_type] at this
  exact this.symm

/-- First-step decomposition of `nStepDist`. -/
theorem nStepDist_first_step [MeasurableSingletonClass S]
    (T : FiniteDTMC S) (s₀ : S) (N : ℕ) :
    T.nStepDist s₀ (N + 1) = (T.step s₀).bind (fun s₁ => T.nStepDist s₁ N) := by
  induction N with
  | zero => simp [nStepDist_succ, PMF.bind_pure]
  | succ N ih =>
    rw [nStepDist_succ, ih, PMF.bind_bind]; simp [nStepDist_succ]

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] in
-- Cons decomposition lemma for pathEnd
private theorem pathEnd_cons {s₀ : S} (s₁ : S) (N : ℕ) (f : Fin N → S) :
    pathEnd s₀ (N + 1) (Fin.cons s₁ f) = pathEnd s₁ N f := by
  cases N with
  | zero => rfl
  | succ k =>
    unfold pathEnd
    exact @Fin.cons_succ (k + 1) (fun _ => S) s₁ f (Fin.last k)

-- Cons decomposition lemma for traceWeight
private theorem traceWeight_cons (T : FiniteDTMC S) (s₀ s₁ : S) (N : ℕ) (f : Fin N → S) :
    traceWeight T s₀ (N + 1) (Fin.cons s₁ f) = T.step s₀ s₁ * traceWeight T s₁ N f := by
  show T.step s₀ ((Fin.cons s₁ f : Fin (N + 1) → S) 0) *
    traceWeight T ((Fin.cons s₁ f : Fin (N + 1) → S) 0) N
      ((Fin.cons s₁ f : Fin (N + 1) → S) ∘ Fin.succ) = _
  simp only [@Fin.cons_zero N (fun _ => S) s₁ f,
    show (Fin.cons s₁ f : Fin (N + 1) → S) ∘ Fin.succ = f from
      funext (fun i => @Fin.cons_succ N (fun _ => S) s₁ f i)]

/-- **Trace product theorem**: `nStepDist s₀ N s` equals the sum of trace weights
over all N-step paths from `s₀` that end at `s`. -/
theorem nStepDist_eq_sum_traceWeight [MeasurableSingletonClass S]
    (T : FiniteDTMC S) (s₀ s : S) (N : ℕ) :
    T.nStepDist s₀ N s =
      ∑ f : Fin N → S,
        if pathEnd s₀ N f = s then traceWeight T s₀ N f else 0 := by
  induction N generalizing s₀ with
  | zero =>
    simp only [pathEnd, traceWeight]
    simp [eq_comm]
  | succ N ih =>
    rw [nStepDist_first_step, PMF.bind_apply, tsum_fintype]
    simp_rw [ih]
    rw [sum_fin_cons_decomp]
    congr 1; ext s₁
    simp_rw [pathEnd_cons, traceWeight_cons]
    rw [Finset.mul_sum]
    congr 1; ext f
    split <;> simp

end ProbMC.FiniteDTMC
