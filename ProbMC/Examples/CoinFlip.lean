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

/-- Lift `StateT.set s'` into `VeilProbM`: deterministically set the state. -/
noncomputable def setStateVPM (s' : S) : VeilProbM Unit S Unit :=
  fun _r _s => PMF.pure ((), s')

/-- `setState s'` corresponds to `setStateVPM s' >>= pure` under ProbConstraint.
    This is: vis (StateT.set s') (fun () => .pure ()) maps to (setStateVPM s') >>= (fun () => pure ()). -/
theorem setState_constraint (s' : S) :
    ProbConstraint (setState s') (setStateVPM s' >>= fun () => Pure.pure ()) :=
  .vis (StateT.set s') (fun () => .pure ()) (fun () => Pure.pure ()) (setStateVPM s')
    (fun () => .pure ())

/-- Helper: `Bool` satisfying `fun _ => True` is all of `Bool`. -/
private theorem bool_filter_true_nonempty :
    (Finset.univ.filter (fun (_ : Bool) => True)).Nonempty :=
  ⟨true, by simp⟩

/-- The coin action corresponds to a uniform distribution over {s0, s1}. -/
theorem coinAction_constraint :
    ProbConstraint (m := BaseM) (ρ := Unit) (σ := S) coinAction
      (fun r s => (PMF.uniformOfFinset (Finset.univ.filter (fun (_ : Bool) => True))
        bool_filter_true_nonempty).bind
        (fun b => (if b then setStateVPM .s0 >>= fun () => Pure.pure ()
                   else setStateVPM .s1 >>= fun () => Pure.pure ()) r s)) := by
  unfold coinAction
  apply ProbConstraint.pickCont
    (fun b => if b then setState .s0 else setState .s1)
    (fun b => if b then setStateVPM .s0 >>= fun () => Pure.pure ()
              else setStateVPM .s1 >>= fun () => Pure.pure ())
    bool_filter_true_nonempty
  intro b; cases b
  · exact setState_constraint .s1
  · exact setState_constraint .s0

/-- Build `ConstrainedProbResult` for the coin action. -/
noncomputable def coinResult : ConstrainedProbResult (m := BaseM) (ρ := Unit) (σ := S) coinAction :=
  ⟨_, coinAction_constraint⟩

/-- The `FiniteDTMC` for the coin flip action. -/
noncomputable def coinDTMC : FiniteDTMC S :=
  toFiniteDTMC coinAction () coinResult

/-- The step function of the coin DTMC is independent of the starting state
(both states lead to the same uniform distribution). -/
theorem coinDTMC_step_eq (s s' : S) : coinDTMC.step s = coinDTMC.step s' := by
  unfold coinDTMC toFiniteDTMC VeilProbM.toPMF coinResult
  ext ⟨⟩ <;> simp [PMF.map_apply, PMF.bind_apply, setStateVPM, PMF.pure_apply,
    PMF.uniformOfFinset_apply]

end ProbMC.Examples.CoinFlip
