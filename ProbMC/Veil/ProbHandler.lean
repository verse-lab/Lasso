/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProbMC.Refinement.FiniteDTMC
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-!
# Probabilistic Handler for NonDetT

A **probabilistic interpretation** of `NonDetT` programs, complementing the existing
demonic (∀) and angelic (∃) WP interpretations from Loom.

- `pickCont τ p f` → **uniform distribution** over `{t : τ // p t}`
- `vis x f` → run base monad deterministically; **stutter** on failure/divergence
- `pure` → deterministic (stay at current state)

## Main definitions

* `NonDetT`: free monad with nondeterminism (replicated from Loom for import compatibility)
* `ProbConstraint`: inductive predicate witnessing that a `NonDetT` program
  produces a specific PMF, mirroring Loom's `ExtractConstraint`.
* `ConstrainedProbResult`: boxed PMF + proof, for compositional extraction.
-/

open MeasureTheory ProbabilityTheory ENNReal Finset
open scoped ENNReal

namespace ProbMC.ProbHandler

/-! ### NonDetT (replicated from Loom for import compatibility)

Loom's `Cont` type conflicts with Mathlib's `Cont`, so we replicate the
`NonDetT` definition here. This is structurally identical to
`Loom.MonadAlgebras.NonDetT'.Basic`. -/

/-- Free monad transformer with nondeterminism.
- `pure ret`: return a value
- `vis x f`: execute base monad effect `x`, continue with `f`
- `pickCont τ p f`: nondeterministically choose `t : τ` satisfying `p`, continue with `f t` -/
inductive NonDetT (m : Type → Type) : Type → Type 1 where
  | pure {α : Type} (ret : α) : NonDetT m α
  | vis {α β : Type} (x : m β) (f : β → NonDetT m α) : NonDetT m α
  | pickCont {α : Type} (τ : Type) (p : τ → Prop) (f : τ → NonDetT m α) : NonDetT m α

def NonDetT.bind {m : Type → Type} {α β : Type}
    (x : NonDetT m α) (f : α → NonDetT m β) : NonDetT m β :=
  match x with
  | .pure ret => f ret
  | .vis x f' => .vis x fun y => (f' y).bind f
  | .pickCont τ p f' => .pickCont τ p fun t => (f' t).bind f

instance {m : Type → Type} : Monad (NonDetT m) where
  pure := NonDetT.pure
  bind := NonDetT.bind

/-- Nondeterministically choose any value of type `τ`. -/
def NonDetT.pick {m : Type → Type} (τ : Type) : NonDetT m τ :=
  NonDetT.pickCont τ (fun _ => True) .pure

/-- Assume a proposition holds (filter out branches where it doesn't). -/
def NonDetT.assume {m : Type → Type} (p : Prop) : NonDetT m PUnit :=
  NonDetT.pickCont PUnit (fun _ => p) fun _ => .pure .unit

/-- Nondeterministically choose a value satisfying a predicate. -/
def NonDetT.pickSuchThat {m : Type → Type} (τ : Type) (p : τ → Prop) : NonDetT m τ :=
  NonDetT.pickCont τ p .pure

/-! ### DivM (replicated from Loom) -/

/-- Divergence monad: computation may produce a result or diverge. -/
inductive DivM (α : Type) where
  | res (x : α)
  | div

instance : Monad DivM where
  pure := DivM.res
  bind := fun x f => match x with
    | .res x => f x
    | .div => .div

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

/-- `ProbConstraint prog s pmf` witnesses that the `NonDetT` program `prog`,
starting from state `s`, produces the probability distribution `pmf` over final states,
under the probabilistic interpretation:

- `pure ()` → `PMF.pure s` (stay at current state)
- `vis x f` with result `(b, s')` → continue with `f b` from `s'`
- `vis x f` that fails → **stutter** (`PMF.pure s`)
- `pickCont τ p f` → uniform distribution over `{t : τ // p t}`, bind with continuations

At `vis_ok` nodes, the user provides the execution result `(b, s')`. The
proof that `(b, s')` actually comes from running the base monad is established
externally (e.g., via `runVeilExecM`). -/
inductive ProbConstraint
    {m : Type → Type} {σ : Type} [Fintype σ] [DecidableEq σ]
    : NonDetT m Unit → σ → PMF σ → Prop where
  /-- Return: stay at current state. -/
  | pure {s : σ} :
      ProbConstraint (.pure ()) s (PMF.pure s)
  /-- Base monad computation succeeds with result `(b, s')`: continue. -/
  | vis_ok {β : Type} {s : σ} (x : m β) (f : β → NonDetT m Unit)
      (b : β) (s' : σ) {pmf : PMF σ}
      (hcont : ProbConstraint (f b) s' pmf)
      : ProbConstraint (.vis x f) s pmf
  /-- Base monad computation fails (diverges or throws): stutter. -/
  | vis_stutter {β : Type} {s : σ} (x : m β) (f : β → NonDetT m Unit)
      : ProbConstraint (.vis x f) s (PMF.pure s)
  /-- Nondeterministic choice: uniform distribution over satisfying elements. -/
  | pickCont {τ : Type} {p : τ → Prop} {s : σ} (f : τ → NonDetT m Unit)
      [Fintype τ] [DecidablePred p]
      (hne : (Finset.univ.filter p).Nonempty)
      (f' : τ → PMF σ)
      (hf : ∀ t, t ∈ Finset.univ.filter p → ProbConstraint (f t) s (f' t))
      : ProbConstraint (.pickCont τ p f) s
          ((PMF.uniformOfFinset (Finset.univ.filter p) hne).bind f')
  /-- Assume succeeds: continue deterministically. -/
  | assumeCont_ok {p : PUnit → Prop} {s : σ} (f : PUnit → NonDetT m Unit)
      [Decidable (p .unit)]
      {pmf : PMF σ}
      (hp : p .unit)
      (hcont : ProbConstraint (f .unit) s pmf)
      : ProbConstraint (.pickCont PUnit p f) s pmf
  /-- Assume fails: stutter. -/
  | assumeCont_fail {p : PUnit → Prop} {s : σ} (f : PUnit → NonDetT m Unit)
      [Decidable (p .unit)]
      (hp : ¬ p .unit)
      : ProbConstraint (.pickCont PUnit p f) s (PMF.pure s)

/-! ### ConstrainedProbResult -/

/-- Boxed result: carries both the PMF and the proof that it satisfies
the `ProbConstraint`. Used for compositional extraction. -/
structure ConstrainedProbResult
    {m : Type → Type} {σ : Type} [Fintype σ] [DecidableEq σ]
    (prog : NonDetT m Unit) (s : σ) where
  pmf : PMF σ
  proof : ProbConstraint prog s pmf

/-! ### Smart constructors -/

noncomputable def ConstrainedProbResult.ofPure
    {m : Type → Type} {σ : Type} [Fintype σ] [DecidableEq σ]
    (s : σ) :
    ConstrainedProbResult (m := m) (.pure ()) s :=
  ⟨PMF.pure s, .pure⟩

noncomputable def ConstrainedProbResult.ofVisOk
    {m : Type → Type} {σ : Type} [Fintype σ] [DecidableEq σ]
    {β : Type} {s : σ} (x : m β) (f : β → NonDetT m Unit)
    (b : β) (s' : σ)
    (hcont : ConstrainedProbResult (f b) s') :
    ConstrainedProbResult (.vis x f) s :=
  ⟨hcont.pmf, .vis_ok x f b s' hcont.proof⟩

noncomputable def ConstrainedProbResult.ofVisStutter
    {m : Type → Type} {σ : Type} [Fintype σ] [DecidableEq σ]
    {β : Type} {s : σ} (x : m β) (f : β → NonDetT m Unit) :
    ConstrainedProbResult (.vis x f) s :=
  ⟨PMF.pure s, .vis_stutter x f⟩

/-! ### FiniteDTMC construction -/

/-- Construct a `FiniteDTMC` from a `NonDetT` program via the probabilistic handler.
Requires a `ConstrainedProbResult` at every state. -/
noncomputable def toFiniteDTMC
    {m : Type → Type} {σ : Type} [Fintype σ] [DecidableEq σ] [MeasurableSpace σ]
    (prog : NonDetT m Unit)
    (h : ∀ s : σ, ConstrainedProbResult prog s)
    : FiniteDTMC σ where
  step s := (h s).pmf

end ProbMC.ProbHandler
