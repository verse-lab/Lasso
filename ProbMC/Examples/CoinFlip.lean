/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProbMC.Veil.ProbHandler

/-!
# CoinFlip Example

Minimal example demonstrating the probabilistic handler pipeline:
1. Define a `NonDetT` program that picks a `Bool`
2. Build a `ProbConstraint` proving it produces a uniform PMF
3. Wrap into a `FiniteDTMC`
-/

open ProbMC.ProbHandler ProbMC.FiniteDTMC
open MeasureTheory ProbabilityTheory ENNReal Finset
open scoped ENNReal

namespace ProbMC.Examples.CoinFlip

/-- Two-state type. -/
inductive S where | s0 | s1
  deriving Fintype, DecidableEq, Repr

instance : MeasurableSpace S := ⊤
instance : MeasurableSingletonClass S := ⟨fun _ => trivial⟩

/-- Simple base monad: `StateT S Id`. -/
abbrev BaseM := StateT S Id

/-- Set the state to a given value. -/
def setState (s : S) : NonDetT BaseM Unit :=
  .vis (StateT.set s) fun () => .pure ()

/-- CoinFlip action: pick a Bool, go to s0 if true, s1 if false. -/
def coinAction : NonDetT BaseM Unit :=
  .pickCont Bool (fun _ => True) fun b =>
    if b then setState .s0 else setState .s1

/-- Running `StateT S Id` is always deterministic (never fails). -/
def runBaseM {β : Type} (x : BaseM β) (s : S) : Option (β × S) :=
  some (StateT.run x s)

/-- The PMF for `setState s'` from any state `s`: it's deterministic at `s'`. -/
theorem setState_constraint (s s' : S) :
    ProbConstraint (setState s') s (PMF.pure s') := by
  exact .vis_ok _ _ () s' .pure

/-- Helper: `Bool` satisfying `fun _ => True` is all of `Bool`. -/
private theorem bool_filter_true :
    Finset.univ.filter (fun (_ : Bool) => True) = Finset.univ := by
  ext x; simp

private theorem bool_filter_true_nonempty :
    (Finset.univ.filter (fun (_ : Bool) => True)).Nonempty := by
  rw [bool_filter_true]; exact Finset.univ_nonempty

/-- The coin action produces a uniform distribution over {s0, s1}. -/
theorem coinAction_constraint (s : S) :
    ProbConstraint coinAction s
      ((PMF.uniformOfFinset (Finset.univ.filter (fun (_ : Bool) => True))
        bool_filter_true_nonempty).bind
        (fun b => if b then PMF.pure S.s0 else PMF.pure S.s1)) := by
  unfold coinAction
  exact .pickCont _ bool_filter_true_nonempty
    (fun b => if b then PMF.pure S.s0 else PMF.pure S.s1)
    (fun t _ => by cases t <;> simp [setState] <;> exact .vis_ok _ _ () _ .pure)

/-- Build `ConstrainedProbResult` for every state. -/
noncomputable def coinResult (s : S) : ConstrainedProbResult coinAction s :=
  ⟨_, coinAction_constraint s⟩

/-- The `FiniteDTMC` for the coin flip action. -/
noncomputable def coinDTMC : FiniteDTMC S :=
  toFiniteDTMC coinAction coinResult

/-- The step function of the coin DTMC is independent of the starting state
(both states lead to the same uniform distribution). -/
theorem coinDTMC_step_eq (s s' : S) : coinDTMC.step s = coinDTMC.step s' := rfl

end ProbMC.Examples.CoinFlip
