/-
  Model checking a system against a TGBA product, searched by Dijkstra's SCC-based emptiness check, no fairness. The
  `¬φ`-automaton comes from `ltl3ba` (`LTLtoTGBA/Pipeline.lean`).

  `modelCheckTGBAFair` adds propositional fairness assumptions without translating them. Each `□◇ψ` becomes one extra
  generalized Büchi mark on the product, so an `.empty` result means every run that satisfies all of them satisfies `φ`.

  Defines:
  - `modelCheckTGBA`: runs a `TEmptinessChecker` on the product of `sys` and the `¬φ`-automaton
  - `modelCheckTGBAFair`: the same under a list of propositional `□◇` assumptions

  Proves:
  - `modelCheckTGBA_empty_unsat`: (Soundness) an `.empty` result implies every run of `sys` satisfies `φ`
  - `modelCheckTGBA_nonEmpty_sat`: (Completeness) a `.nonEmpty` result yields a concrete violating run
  - `modelCheckTGBAFair_empty_unsat`, `modelCheckTGBAFair_nonEmpty_sat`: the same two under the fairness assumptions

  Sections:
  - Model checking
  - Model checking under fairness
  - Checker obligations
  - Soundness
  - Completeness
-/
import LTLLib.LTL.Propositional
import LTLLib.LTL.Semantics
import LTLLib.Product
import LTLLib.TGBABased.AbstractSpec.EmptinessCheck
import LTLLib.TGBABased.Fairness.FairProduct
import LTLLib.TGBABased.LTLtoTGBA.Pipeline
import LTLLib.TGBABased.Product
import LTLLib.TGBABased.SCC.DijkstraSCC

namespace LTLLib

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]

section Search

variable [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [Inhabited SysState]

/-! ## Model checking -/

/-- Does `sys` satisfy `φ`? `.empty` means it does, `.nonEmpty stem loop` witnesses a violating run as
`(system state, TGBA state)` pairs. -/
def modelCheckTGBA (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (checker : TEmptinessChecker (SysState × Nat) := dijkstraTChecker) :
    EmptinessResult (SysState × Nat) :=
  match ltl3ba (φ.toNNF false) with
  | some tgba =>
    checker.check (TGBAProduct.getSuccessors tgba sysSucc sysLabel)
      (TGBAProduct.initialStates tgba sysInit)
      (TGBAProduct.edgeMarks tgba sysSucc sysLabel) (TGBAProduct.expand tgba sysSucc sysLabel)
      tgba.numAcceptSets
  | none => .empty 0

/-- `modelCheckTGBA` over one system callback. -/
def modelCheckTGBAOfStep (φ : Formula α) (sysInit : List SysState)
    (sysStep : LSys.StepFn α SysState)
    (checker : TEmptinessChecker (SysState × Nat) := dijkstraTChecker) :
    EmptinessResult (SysState × Nat) :=
  match ltl3ba (φ.toNNF false) with
  | some tgba =>
    checker.check (TGBAProduct.getSuccessorsOfStep tgba sysStep)
      (TGBAProduct.initialStates tgba sysInit)
      (TGBAProduct.edgeMarksOfStep tgba sysStep) (TGBAProduct.expandOfStep tgba sysStep)
      tgba.numAcceptSets
  | none => .empty 0

theorem modelCheckTGBAOfStep_eq (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (checker : TEmptinessChecker (SysState × Nat)) :
    modelCheckTGBAOfStep φ sysInit (fun s => (sysSucc s, sysLabel s)) checker
      = modelCheckTGBA φ sysInit sysSucc sysLabel checker := rfl

theorem modelCheckTGBA_eq (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (checker : TEmptinessChecker (SysState × Nat))
    {tgba : TGBA α} (htg : ltl3ba (φ.toNNF false) = some tgba) :
    modelCheckTGBA φ sysInit sysSucc sysLabel checker =
      checker.check (TGBAProduct.getSuccessors tgba sysSucc sysLabel) (TGBAProduct.initialStates tgba sysInit)
        (TGBAProduct.edgeMarks tgba sysSucc sysLabel) (TGBAProduct.expand tgba sysSucc sysLabel)
      tgba.numAcceptSets := by
  unfold modelCheckTGBA
  split
  next tgba' htg' =>
    obtain rfl : tgba' = tgba := Option.some.inj (htg'.symm.trans htg)
    rfl
  next htg' => exact absurd (htg'.symm.trans htg) (by simp)

/-! ## Model checking under fairness -/

/-- Does `sys` satisfy `φ` on every run that also satisfies every `□◇ b` for `b` in `fair`? The assumptions
never reach the translator, they become marks on the product. `modelCheckTGBA` is the `fair = []` case. -/
def modelCheckTGBAFair (φ : Formula α) (fair : List (BoolFormula α)) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (checker : TEmptinessChecker (SysState × Nat) := dijkstraTChecker) :
    EmptinessResult (SysState × Nat) :=
  match ltl3ba (φ.toNNF false) with
  | some tgba =>
    checker.check (TGBAProduct.getSuccessors tgba (LSys.unlabelled sysSucc) sysLabel)
      (TGBAProduct.initialStates tgba sysInit)
      (TGBAProduct.edgeMarksFair tgba (LSys.unlabelled sysSucc) sysLabel fair)
      (TGBAProduct.expandFair tgba (LSys.unlabelled sysSucc) sysLabel fair)
      (tgba.numAcceptSets + fair.length)
  | none => .empty 0

theorem modelCheckTGBAFair_eq (φ : Formula α) (fair : List (BoolFormula α))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α)
    (checker : TEmptinessChecker (SysState × Nat)) {tgba : TGBA α} (htg : ltl3ba (φ.toNNF false) = some tgba) :
    modelCheckTGBAFair φ fair sysInit sysSucc sysLabel checker =
      checker.check (TGBAProduct.getSuccessors tgba (LSys.unlabelled sysSucc) sysLabel) (TGBAProduct.initialStates tgba sysInit)
        (TGBAProduct.edgeMarksFair tgba (LSys.unlabelled sysSucc) sysLabel fair)
      (TGBAProduct.expandFair tgba (LSys.unlabelled sysSucc) sysLabel fair)
      (tgba.numAcceptSets + fair.length) := by
  unfold modelCheckTGBAFair
  split
  next tgba' htg' =>
    obtain rfl : tgba' = tgba := Option.some.inj (htg'.symm.trans htg)
    rfl
  next htg' => exact absurd (htg'.symm.trans htg) (by simp)

end Search

variable [LawfulBEq α] [LawfulHashable α]

/-! ## Checker obligations

The finiteness and marks-bound hypotheses `TEmptinessChecker` asks of a caller, discharged once for the `¬φ` product. -/

/-- Every product mark is below `numAcceptSets`. -/
theorem modelCheckTGBA_marksBound [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (φ : Formula α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    {tgba : TGBA α} (htg : ltl3ba (φ.toNNF false) = some tgba) (p p' : SysState × Nat) (m : Nat)
    (hm : m ∈ TGBAProduct.edgeMarks tgba sysSucc sysLabel p p') : m < tgba.numAcceptSets :=
  TGBAProduct.edgeMarks_lt _ sysSucc sysLabel (ltl3ba_marks_lt _ htg) p p' m hm

/-- Every extended product mark is below `numAcceptSets + fair.length`, the conjunct marks being indexed from
`numAcceptSets`. -/
theorem modelCheckTGBAFair_marksBound [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (φ : Formula α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (fair : List (BoolFormula α)) {tgba : TGBA α} (htg : ltl3ba (φ.toNNF false) = some tgba)
    (p p' : SysState × Nat) (m : Nat)
    (hm : m ∈ TGBAProduct.edgeMarksFair tgba sysSucc sysLabel fair p p') :
    m < tgba.numAcceptSets + fair.length :=
  TGBAProduct.edgeMarksFair_lt _ sysSucc sysLabel (ltl3ba_marks_lt _ htg) fair p p' m hm

/-- The product's `FiniteReach` witness. -/
theorem modelCheckTGBA_finiteReach (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {tgba : TGBA α} (htg : ltl3ba (φ.toNNF false) = some tgba) :
    FiniteReach (TGBAProduct.initialStates tgba sysInit) (TGBAProduct.getSuccessors tgba sysSucc sysLabel) :=
  TGBAProduct.finiteReach _ (ltl3ba_wellFormed _ htg) sysSucc sysLabel sysInit sysFR

section Search

variable [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [Inhabited SysState]

/-! ## Soundness -/

/-- An `.empty` result means every run of `sys` satisfies `φ`. -/
theorem modelCheckTGBA_empty_unsat [DecidableEq α] [LawfulHashable SysState] (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) (checker : TEmptinessChecker (SysState × Nat)) {n : Nat}
    (h : modelCheckTGBA φ sysInit sysSucc sysLabel checker = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  intro ρ hρ
  by_contra hviolate
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome (φ.toNNF false))
  rw [modelCheckTGBA_eq φ sysInit sysSucc sysLabel checker htg] at h
  obtain ⟨σ, -, hrun, hacc⟩ := TGBAProduct.gsp_correct2 _ sysSucc sysLabel sysInit hρ
    ((ltl3ba_accepts _ htg _).mpr ((Formula.toNNF_correct_neg _ φ).mp hviolate))
  have hFR := modelCheckTGBA_finiteReach φ sysInit sysSucc sysLabel sysFR htg
  exact checker.empty_no_cycle hFR (TGBAProduct.expand_coherent tgba sysSucc sysLabel)
    (fun p p' m hm => modelCheckTGBA_marksBound φ sysSucc sysLabel htg p p' m hm) h
    (TGBAProduct.exists_TAcceptingCycle_of_acceptingRun _ sysSucc sysLabel sysInit hFR hrun hacc)

/-- An `.empty` result means every run of `sys` that satisfies every fairness assumption satisfies `φ`. -/
theorem modelCheckTGBAFair_empty_unsat [DecidableEq α] (φ : Formula α) (fair : List (BoolFormula α))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker (SysState × Nat)) {n : Nat}
    (h : modelCheckTGBAFair φ fair sysInit sysSucc sysLabel checker = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      (∀ b ∈ fair, (BoolFormula.alwaysEventually b).satisfies (fun i a => a ∈ sysLabel (τ i))) →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  intro τ hτ hfair
  by_contra hviolate
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome (φ.toNNF false))
  rw [modelCheckTGBAFair_eq φ fair sysInit sysSucc sysLabel checker htg] at h
  have hrunL := LSys.toSpec_isRun_ofRun hτ
  obtain ⟨σ, -, hrun, hacc⟩ := TGBAProduct.gsp_correct2Fair _ (LSys.unlabelled sysSucc) sysLabel sysInit fair
    hrunL
    ((ltl3ba_accepts _ htg _).mpr ((Formula.toNNF_correct_neg _ φ).mp hviolate))
    -- the conjuncts are now read on the letters; unlabelled, those are the state labels
    (fun i hi n => by
      obtain ⟨j, hj⟩ := (TGBAProduct.fair_iff_indexed fair sysLabel τ).mp hfair i hi n
      exact ⟨j, by rw [LSys.letter_of_isRun_unlabelled hrunL (n + j)]; exact hj⟩)
  have hFR := modelCheckTGBA_finiteReach φ sysInit (LSys.unlabelled sysSucc) sysLabel
    (LSys.finiteReach_unlabelled sysFR) htg
  exact checker.empty_no_cycle hFR (TGBAProduct.expandFair_coherent tgba (LSys.unlabelled sysSucc) sysLabel fair)
    (fun p p' m hm => modelCheckTGBAFair_marksBound φ (LSys.unlabelled sysSucc) sysLabel fair htg p p' m hm) h
    (TGBAProduct.exists_TAcceptingCycle_of_acceptingRunFair _ (LSys.unlabelled sysSucc) sysLabel sysInit fair
      hFR hrun hacc)

/-! ## Completeness -/

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckTGBA_nonEmpty_sat [DecidableEq α] [LawfulHashable SysState] (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) (checker : TEmptinessChecker (SysState × Nat))
    {stem loop : List (SysState × Nat)}
    (h : modelCheckTGBA φ sysInit sysSucc sysLabel checker = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome (φ.toNNF false))
  rw [modelCheckTGBA_eq φ sysInit sysSucc sysLabel checker htg] at h
  obtain ⟨ac, -, -⟩ := checker.nonEmpty_valid (modelCheckTGBA_finiteReach φ sysInit sysSucc sysLabel sysFR htg)
    (TGBAProduct.expand_coherent tgba sysSucc sysLabel)
    (fun p p' m hm => modelCheckTGBA_marksBound φ sysSucc sysLabel htg p p' m hm) h
  obtain ⟨hρrun, hlang⟩ := TGBAProduct.gsp_correct1 _ sysSucc sysLabel sysInit
    ⟨ac.toTValidLassoProduct.run_isRun, ac.toTValidLassoProduct.run_isAccepting⟩
  refine ⟨fun n => ((ac.toTValidLassoProduct.run n).1, (ac.toTValidLassoProduct.run n).2.1),
    hρrun, fun hsat => ?_⟩
  exact (Formula.toNNF_correct_neg _ φ).mpr ((ltl3ba_accepts _ htg _).mp hlang) hsat

/-- A `.nonEmpty` result yields one concrete run of `sys` that satisfies every fairness assumption and still
violates `φ`. -/
theorem modelCheckTGBAFair_nonEmpty_sat [DecidableEq α] (φ : Formula α) (fair : List (BoolFormula α))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker (SysState × Nat)) {stem loop : List (SysState × Nat)}
    (h : modelCheckTGBAFair φ fair sysInit sysSucc sysLabel checker = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      (∀ b ∈ fair, (BoolFormula.alwaysEventually b).satisfies (fun i a => a ∈ sysLabel (τ i))) ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome (φ.toNNF false))
  rw [modelCheckTGBAFair_eq φ fair sysInit sysSucc sysLabel checker htg] at h
  obtain ⟨ac, -, -⟩ := checker.nonEmpty_valid
    (modelCheckTGBA_finiteReach φ sysInit (LSys.unlabelled sysSucc) sysLabel (LSys.finiteReach_unlabelled sysFR) htg)
    (TGBAProduct.expandFair_coherent tgba (LSys.unlabelled sysSucc) sysLabel fair)
    (fun p p' m hm => modelCheckTGBAFair_marksBound φ (LSys.unlabelled sysSucc) sysLabel fair htg p p' m hm) h
  have lasso := TGBAProduct.toTValidLassoProductFair _ (LSys.unlabelled sysSucc) sysLabel sysInit fair (ltl3ba_marks_lt _ htg) ac
  obtain ⟨hτrun, hlang, hfair⟩ := TGBAProduct.gsp_correct1Fair _ (LSys.unlabelled sysSucc) sysLabel sysInit fair
    lasso.run_isRun lasso.run_isAccepting
  rw [LSys.valuation_unlabelled hτrun] at hlang
  refine ⟨fun n => (lasso.run n).1, LSys.isRun_of_toSpec_unlabelled hτrun,
    (TGBAProduct.fair_iff_indexed fair sysLabel _).mpr (fun i hi n => by
      obtain ⟨j, hj⟩ := hfair i hi n
      exact ⟨j, by rwa [LSys.letter_of_isRun_unlabelled hτrun (n + j)] at hj⟩),
    fun hsat => ?_⟩
  exact (Formula.toNNF_correct_neg _ φ).mpr ((ltl3ba_accepts _ htg _).mp hlang) hsat

end Search

end LTLLib
