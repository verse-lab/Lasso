/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProbMC.Refinement.FiniteDTMC
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Loom.MonadAlgebras.NonDetT'.Basic
import Loom.MonadAlgebras.Instances.Basic

/-!
# Probabilistic Handler for NonDetT

A **probabilistic interpretation** of `NonDetT` programs, complementing the existing
demonic (∀) and angelic (∃) WP interpretations from Loom.

- `pickCont τ p f` → **uniform distribution** over `{t : τ // p t}`
- `vis x f` → run base monad via a provided lifting into `VeilProbM`
- `pure` → deterministic (stay at current state, return value)

## Main definitions

* `VeilProbM`: probabilistic monad with reader and state, `ReaderT ρ (StateT σ PMF)`.
* `ProbConstraint`: inductive predicate relating a `NonDetT` program to a `VeilProbM`
  computation, mirroring Loom's `ExtractConstraint`.
* `ProbConstraint.bind`: compositional bind, mirroring `ExtractConstraint.bind`.
* `ConstrainedProbResult`: boxed target + proof, for compositional extraction.
-/

open MeasureTheory ProbabilityTheory ENNReal Finset
open scoped ENNReal

namespace ProbMC.ProbHandler

/-! ### VeilProbM -/

/-- Probabilistic monad with reader environment `ρ` and state `σ`.
Equivalent to `ρ → σ → PMF (α × σ)`. -/
abbrev VeilProbM (ρ σ : Type) := ReaderT ρ (StateT σ PMF)

/-! ### Running the base monad -/

/-- Run a VeilExecM-like computation deterministically. Returns `none` if the
computation diverges (`DivM.div`) or throws an exception (`Except.error`).
On success, returns the result value and the updated state.

The base monad is `ReaderT ρ (ExceptT ε (StateT σ DivM))`. -/
def runReaderExceptStateDivM {ρ σ ε β : Type} (r : ρ)
    (x : ReaderT ρ (ExceptT ε (StateT σ DivM)) β) (s : σ) : Option (β × σ) :=
  match StateT.run (ExceptT.run (x r)) s with
  | .div => none
  | .res (.error _, _) => none
  | .res (.ok b, s') => some (b, s')

/-! ### ProbConstraint inductive -/

/-- `ProbConstraint prog target` witnesses that the `NonDetT` program `prog`
corresponds to the `VeilProbM` computation `target` under the probabilistic
interpretation. This mirrors `ExtractConstraint` from Loom.

- `pure x` → `Pure.pure x` (deterministic return)
- `vis x f` → `x' >>= f'` (run lifted base monad, continue)
- `pickCont τ p f` → uniform choice over `{t : τ // p t}`, then continue
- `assumeCont` → conditional: continue if assumption holds, else `deadBranch` -/
inductive ProbConstraint
    {m : Type → Type} {ρ σ : Type}
    : {α : Type} → NonDetT m α → VeilProbM ρ σ α → Prop where
  /-- Return: deterministic, no state change. -/
  | pure {α : Type} (x : α) :
      ProbConstraint (.pure x) (Pure.pure x)
  /-- Base monad effect: lift `x` into `VeilProbM` via `x'`, continue with `f'`. -/
  | vis {α β : Type} (x : m β) (f : β → NonDetT m α) (f' : β → VeilProbM ρ σ α)
      (x' : VeilProbM ρ σ β)
      (hf : ∀ y, ProbConstraint (f y) (f' y)) :
      ProbConstraint (.vis x f) (x' >>= f')
  /-- Nondeterministic choice: uniform distribution over satisfying elements. -/
  | pickCont {α τ : Type} {p : τ → Prop} (f : τ → NonDetT m α)
      (f' : τ → VeilProbM ρ σ α)
      [Fintype τ] [DecidablePred p]
      (hne : (Finset.univ.filter p).Nonempty)
      (hf : ∀ y, ProbConstraint (f y) (f' y)) :
      ProbConstraint (.pickCont τ p f)
        (fun r s => (PMF.uniformOfFinset (Finset.univ.filter p) hne).bind (fun t => f' t r s))
  /-- Assume: continue if holds, else `deadBranch`. -/
  | assumeCont {α : Type} (p : PUnit.{1} → Prop) (f : PUnit.{1} → NonDetT m α)
      (f' : PUnit.{1} → VeilProbM ρ σ α) [Decidable (p .unit)]
      (deadBranch : VeilProbM ρ σ α)
      (hcont : ProbConstraint (f .unit) (f' .unit)) :
      ProbConstraint (.pickCont PUnit.{1} p f)
        (if p .unit then f' .unit else deadBranch)

/-! ### ProbConstraint.bind -/

private theorem pickCont_bind_eq {ρ σ α β τ : Type}
    (U : PMF τ) (g' : τ → VeilProbM ρ σ α) (f' : α → VeilProbM ρ σ β) :
    (fun r s => U.bind (fun t => g' t r s)) >>= f' =
    fun r s => U.bind (fun t => (g' t >>= f') r s) := by
  funext r s
  show (U.bind (fun t => g' t r s)).bind (fun p => f' p.1 r p.2) =
       U.bind (fun t => (g' t r s).bind (fun p => f' p.1 r p.2))
  exact PMF.bind_bind ..

/-- Bind for `ProbConstraint`: if `prog` corresponds to `s'` and for every `x`,
`f x` corresponds to `f' x`, then `prog >>= f` corresponds to `s' >>= f'`.
This directly mirrors `ExtractConstraint.bind`. -/
theorem ProbConstraint.bind
    {m : Type → Type} [Monad m] {ρ σ : Type}
    {α β : Type} {prog : NonDetT m α} {prog' : VeilProbM ρ σ α}
    {f : α → NonDetT m β} {f' : α → VeilProbM ρ σ β}
    (hs : ProbConstraint prog prog')
    (hf : ∀ x, ProbConstraint (f x) (f' x)) :
    ProbConstraint (prog >>= f) (prog' >>= f') := by
  induction hs generalizing f f' with
  | pure x =>
    show ProbConstraint (f x) ((Pure.pure x : VeilProbM ρ σ α) >>= f')
    rw [pure_bind]
    convert hf x
  | vis x k k' x' hk ih =>
    show ProbConstraint (.vis x (fun y => NonDetT.bind (k y) f)) ((x' >>= k') >>= f')
    rw [bind_assoc]
    exact .vis x _ (fun y => k' y >>= f') x' (fun y => ih y hf)
  | pickCont g g' hne hg ih =>
    show ProbConstraint (.pickCont _ _ (fun t => NonDetT.bind (g t) f))
      ((fun r s => (PMF.uniformOfFinset _ hne).bind (fun t => g' t r s)) >>= f')
    rw [pickCont_bind_eq]
    exact .pickCont _ (fun t => g' t >>= f') hne (fun t => ih t hf)
  | assumeCont p g g' deadBranch hg ih =>
    show ProbConstraint (.pickCont PUnit.{1} p (fun t => NonDetT.bind (g t) f))
      ((if p .unit then g' .unit else deadBranch) >>= f')
    simp only [apply_ite (· >>= f')]
    exact .assumeCont p _ (fun _ => g' .unit >>= f') (deadBranch >>= f') (ih hf)

/-! ### ConstrainedProbResult -/

/-- Boxed result: carries both the target `VeilProbM` computation and the proof
that it satisfies `ProbConstraint`. Used for compositional extraction. -/
structure ConstrainedProbResult
    {m : Type → Type} {ρ σ : Type}
    {α : Type} (prog : NonDetT m α) where
  target : VeilProbM ρ σ α
  proof : ProbConstraint prog target

/-! ### Smart constructors -/

noncomputable def ConstrainedProbResult.ofPure
    {m : Type → Type} {ρ σ : Type} (x : α) :
    ConstrainedProbResult (m := m) (ρ := ρ) (σ := σ) (.pure x) :=
  ⟨Pure.pure x, .pure x⟩

noncomputable def ConstrainedProbResult.ofVis
    {m : Type → Type} {ρ σ : Type}
    {β : Type} (x : m β) (f : β → NonDetT m α)
    (x' : VeilProbM ρ σ β)
    (hf : ∀ y, ConstrainedProbResult (ρ := ρ) (σ := σ) (f y)) :
    ConstrainedProbResult (ρ := ρ) (σ := σ) (.vis x f) :=
  ⟨x' >>= (fun y => (hf y).target), .vis x f (fun y => (hf y).target) x' (fun y => (hf y).proof)⟩

/-- Bind for `ConstrainedProbResult`: compositional extraction.
Mirrors `ConstrainedExtractResult.bind`. -/
noncomputable def ConstrainedProbResult.bind
    {m : Type → Type} [Monad m] {ρ σ : Type}
    {α β : Type} {prog : NonDetT m α} {f : α → NonDetT m β}
    (hs : ConstrainedProbResult (ρ := ρ) (σ := σ) prog)
    (hf : ∀ x, ConstrainedProbResult (ρ := ρ) (σ := σ) (f x)) :
    ConstrainedProbResult (ρ := ρ) (σ := σ) (prog >>= f) where
  target := hs.target >>= (fun x => (hf x).target)
  proof := ProbConstraint.bind hs.proof (fun x => (hf x).proof)

/-! ### FiniteDTMC construction -/

/-- Extract a `PMF σ` from a `VeilProbM ρ σ Unit` computation by marginalizing
out the trivial `Unit` component. -/
noncomputable def VeilProbM.toPMF {ρ σ : Type}
    (target : VeilProbM ρ σ Unit) (r : ρ) (s : σ) : PMF σ :=
  (target r s).map Prod.snd

/-- Construct a `FiniteDTMC` from a `NonDetT` program via the probabilistic handler.
Requires a `ConstrainedProbResult` for the program and a reader value `r`. -/
noncomputable def toFiniteDTMC
    {m : Type → Type} {ρ σ : Type} [Fintype σ] [DecidableEq σ] [MeasurableSpace σ]
    (prog : NonDetT m Unit) (r : ρ)
    (h : ConstrainedProbResult (ρ := ρ) (σ := σ) prog)
    : FiniteDTMC σ where
  step s := VeilProbM.toPMF h.target r s

end ProbMC.ProbHandler
