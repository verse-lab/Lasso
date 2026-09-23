/-
  Model checking a system against a degeneralized TGBA product, searched by the transition-based Nested DFS, no
  fairness. The `¬φ`-automaton comes from `ltl3ba` (`LTLtoTGBA/Pipeline.lean`). `nestedDFSTWF` is sound only for a
  single-mark product, so the automaton is degeneralized to a `TBA` before it is crossed with the system
  (`TBAProduct.lean`).

  Defines:
  - `modelCheckTBA`: runs `nestedDFSTWF` on the product of `sys` and the degeneralized `¬φ`-automaton

  Proves:
  - `modelCheckTBA_empty_unsat`: (Soundness) an `.empty` result implies every run of `sys` satisfies `φ`
  - `modelCheckTBA_nonEmpty_sat`: (Completeness) a `.nonEmpty` result yields a concrete violating run

  Sections:
  - Checker obligations
  - Model checking
  - Soundness
  - Completeness
-/
import LTLLib.LTL.Semantics
import LTLLib.Product
import LTLLib.TGBABased.Degeneralization.DegeneralBridge
import LTLLib.TGBABased.Degeneralization.TBAProduct
import LTLLib.TGBABased.LTLtoTGBA.Pipeline
import LTLLib.TGBABased.NestedDFS.NestedDFSTTermination

namespace LTLLib

variable {α : Type u} {SysState : Type v} [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
  [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]

/-! ## Checker obligations -/

/-- The degeneralized product's `FiniteReach` witness. -/
def modelCheckTBA_finiteReach (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {tgba : TGBA α} (htg : ltl3ba (φ.toNNF false) = some tgba) :
    FiniteReach (TBAProduct.initialStates tgba.degeneralize sysInit)
      (TBAProduct.getSuccessors tgba.degeneralize sysSucc sysLabel) :=
  TBAProduct.finiteReach _ (TGBA.degeneralize_wellFormed _ (ltl3ba_wellFormed _ htg)) sysSucc sysLabel sysInit sysFR

/-! ## Model checking -/

/-- Does `sys` satisfy `φ`? `.empty` means it does, `.nonEmpty stem loop` witnesses a violating run as
`(system state, TBA state)` pairs. `sysFR` is needed only for the proofs. -/
def modelCheckTBA (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) :
    EmptinessResult (SysState × TBAState) :=
  match htg : ltl3ba (φ.toNNF false) with
  | some tgba =>
    let tba := tgba.degeneralize
    -- PERF: the fused `expand` is what the search walks with, so `sysLabel` and `sysSucc` are entered
    -- once per product state instead of once per outgoing edge. `edgeMarks` stays as the *spec* callback
    -- the correctness theorems are stated in terms of; `expand_coherent` ties the two together. Without
    -- it this route paid a full `sys.tr` per edge — see `EdgeLabels.md` §12.11.
    nestedDFSTWF (TBAProduct.getSuccessors tba sysSucc sysLabel) (TBAProduct.edgeMarks tba sysSucc sysLabel)
      (TBAProduct.expand tba sysSucc sysLabel)
      (TBAProduct.initialStates tba sysInit) (modelCheckTBA_finiteReach φ sysInit sysSucc sysLabel sysFR htg)
  | none => .empty 0

/-- `modelCheckTBA` over one system callback. §15 -/
def modelCheckTBAOfStep (φ : Formula α) (sysInit : List SysState)
    (sysStep : LSys.StepFn α SysState)
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) :
    EmptinessResult (SysState × TBAState) :=
  match htg : ltl3ba (φ.toNNF false) with
  | some tgba =>
    let tba := tgba.degeneralize
    nestedDFSTWF (TBAProduct.getSuccessorsOfStep tba sysStep) (TBAProduct.edgeMarksOfStep tba sysStep)
      (TBAProduct.expandOfStep tba sysStep)
      (TBAProduct.initialStates tba sysInit)
      (by rw [TBAProduct.getSuccessorsOfStep_eq']
          exact modelCheckTBA_finiteReach φ sysInit _ _ sysFR htg)
  | none => .empty 0

theorem modelCheckTBAOfStep_eq (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) :
    modelCheckTBAOfStep φ sysInit (fun s => (sysSucc s, sysLabel s)) sysFR
      = modelCheckTBA φ sysInit sysSucc sysLabel sysFR := rfl

theorem modelCheckTBA_eq (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {tgba : TGBA α} (htg : ltl3ba (φ.toNNF false) = some tgba) :
    modelCheckTBA φ sysInit sysSucc sysLabel sysFR =
      nestedDFSTWF (TBAProduct.getSuccessors tgba.degeneralize sysSucc sysLabel)
        (TBAProduct.edgeMarks tgba.degeneralize sysSucc sysLabel)
        (TBAProduct.expand tgba.degeneralize sysSucc sysLabel)
        (TBAProduct.initialStates tgba.degeneralize sysInit)
        (modelCheckTBA_finiteReach φ sysInit sysSucc sysLabel sysFR htg) := by
  unfold modelCheckTBA
  split
  next tgba' htg' =>
    obtain rfl : tgba' = tgba := Option.some.inj (htg'.symm.trans htg)
    rfl
  next htg' => exact absurd (htg'.symm.trans htg) (by simp)

/-! ## Soundness -/

/-- An `.empty` result means every run of `sys` satisfies `φ`. -/
theorem modelCheckTBA_empty_unsat [DecidableEq α] (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {n : Nat}
    (h : modelCheckTBA φ sysInit sysSucc sysLabel sysFR = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  intro ρ hρ
  by_contra hviolate
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome (φ.toNNF false))
  rw [modelCheckTBA_eq φ sysInit sysSucc sysLabel sysFR htg] at h
  have htba_acc : tgba.degeneralize.toSpec.accepts (LSys.valuation sysLabel ρ) :=
    (TGBA.degeneralize_accepts_any _ (ltl3ba_wellFormed _ htg) _).mpr
      ((ltl3ba_accepts _ htg _).mpr ((Formula.toNNF_correct_neg _ φ).mp hviolate))
  obtain ⟨σ, -, hrun, hacc⟩ := TBAProduct.gsp_correct2 _ sysSucc sysLabel sysInit hρ htba_acc
  exact nestedDFSTWF_empty_no_cycle _ (modelCheckTBA_finiteReach φ sysInit sysSucc sysLabel sysFR htg) _ _
    (TBAProduct.expand_coherent _ sysSucc sysLabel) n h
    (TBAProduct.exists_TAcceptingCycle_of_acceptingRun _ sysSucc sysLabel sysInit
      (modelCheckTBA_finiteReach φ sysInit sysSucc sysLabel sysFR htg) hrun hacc)

/-! ## Completeness -/

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckTBA_nonEmpty_sat [DecidableEq α] (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {stem loop : List (SysState × TBAState)}
    (h : modelCheckTBA φ sysInit sysSucc sysLabel sysFR = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome (φ.toNNF false))
  rw [modelCheckTBA_eq φ sysInit sysSucc sysLabel sysFR htg] at h
  obtain ⟨ac, -, -⟩ := nestedDFSTWF_nonEmpty_valid _ (modelCheckTBA_finiteReach φ sysInit sysSucc sysLabel sysFR htg)
    _ _ (TBAProduct.expand_coherent _ sysSucc sysLabel) stem loop h
  obtain ⟨hρrun, hlang⟩ := TBAProduct.gsp_correct1 _ sysSucc sysLabel sysInit
    ⟨ac.toTValidLassoTBAProduct.run_isRun, ac.toTValidLassoTBAProduct.run_isAccepting⟩
  refine ⟨fun n => ((ac.toTValidLassoTBAProduct.run n).1, (ac.toTValidLassoTBAProduct.run n).2.1),
    hρrun, fun hsat => ?_⟩
  have htgba_acc : tgba.toSpec.accepts (LSys.valuation sysLabel
      (fun n => ((ac.toTValidLassoTBAProduct.run n).1, (ac.toTValidLassoTBAProduct.run n).2.1))) :=
    (TGBA.degeneralize_accepts_any _ (ltl3ba_wellFormed _ htg) _).mp hlang
  exact (Formula.toNNF_correct_neg _ φ).mpr ((ltl3ba_accepts _ htg _).mp htgba_acc) hsat

end LTLLib
