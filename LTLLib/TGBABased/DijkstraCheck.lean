/-
  Model checking a system against a TGBA product, searched by Dijkstra's SCC-based emptiness check, no
  fairness. This is the real logic and both directions of proof, `ModelCheck.lean`'s `modelCheckDijkstra` is a
  thin wrapper over it, one of the four search modes listed there.

  `modelCheckTGBAFair` adds propositional fairness assumptions without translating them. Each `□◇ψ` becomes
  one extra generalized Büchi mark on the product, so an `.empty` result means every run that satisfies all of
  them satisfies `φ`. This is Route 1 of `Fairness.md`, and it leaves the emptiness checker untouched.

  Defines:
  - `modelCheckTGBA`: runs a `TEmptinessChecker` on the product of `sys` and the `¬φ`-automaton
  - `modelCheckTGBA_eq`: unfolds `modelCheckTGBA` once `createGraph` is known to succeed
  - `modelCheckTGBA_empty_unsat`:  (Soundness)    an `.empty` result implies every run of `sys` satisfies `φ`
  - `modelCheckTGBA_nonEmpty_sat`: (Completeness) a `.nonEmpty` result yields a concrete violating run
  - `modelCheckTGBAFair`: the same under a list of propositional `□◇` assumptions, with both directions

  Sections:
  - Checker obligations
  - Model checking
  - Soundness
  - Completeness
  - Model checking under fairness
-/
import LTLLib.LTL.Propositional
import LTLLib.LTL.Semantics
import LTLLib.LTLtoGBA.Bridge
import LTLLib.LTLtoGBA.Completeness
import LTLLib.LTLtoGBA.Correctness
import LTLLib.LTLtoGBA.ExpandTermination
import LTLLib.Product
import LTLLib.TGBABased.AbstractSpec.EmptinessCheck
import LTLLib.TGBABased.FairProduct
import LTLLib.TGBABased.LTLtoTGBA.GBAToTGBA
import LTLLib.TGBABased.Product
import LTLLib.TGBABased.SCC.DijkstraSCC

namespace LTLLib

variable {α : Type u} {S : Type w} [FSet (NNF α) S]
  {SysState : Type v} [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [Inhabited SysState]
  [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α]

/-! ## Checker obligations

The two hypotheses `TEmptinessChecker` asks of a caller, discharged here once for the `¬φ` product.
-/

/-- The product's `FiniteReach` witness. -/
def modelCheckTGBA_finiteReach (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc) {st : ExpandState α S}
    (hcg : createGraph (S := S) (φ.toNNF false) = some st) :
    FiniteReach
      (TGBAProduct.initialStates (constructGBA (φ.toNNF false) st).toTGBA sysInit)
      (TGBAProduct.getSuccessors (constructGBA (φ.toNNF false) st).toTGBA sysSucc sysLabel) :=
  TGBAProduct.finiteReach _ (GBA.toTGBA_wellFormed _ (constructGBA_wellFormed hcg))
    sysSucc sysLabel sysInit sysFR

omit [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [Inhabited SysState] [LawfulBEq α]
  [LawfulHashable α] [DecidableEq α] in
/-- Every product mark is below `numAcceptSets`, `toTGBA` bounds its marks by construction. -/
theorem modelCheckTGBA_marksBound (φ : Formula α) (sysLabel : SysState → Std.HashSet α)
    (st : ExpandState α S) (p p' : SysState × Nat) (m : Nat)
    (hm : m ∈ TGBAProduct.edgeMarks (constructGBA (φ.toNNF false) st).toTGBA sysLabel p p') :
    m < (constructGBA (φ.toNNF false) st).toTGBA.numAcceptSets :=
  TGBAProduct.edgeMarks_lt _ sysLabel (GBA.toTGBA_marks_lt _) p p' m hm

/-! ## Model checking -/

/-- Does `sys` (given by `sysInit`/`sysSucc`/`sysLabel`) satisfy `φ`? `.empty` means it does, `.nonEmpty stem loop`
witnesses a violating run as `(system state, TGBA state)` pairs.

`sysFR` is a bare existence certificate that `sys` is finitely reachable, needed only for the proofs.
The emptiness check is supplied via an algorithm-agnostic `checker`. -/
def modelCheckTGBA (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker (SysState × Nat) := dijkstraTChecker) :
    EmptinessResult (SysState × Nat) :=
  match hcg : createGraph (S := S) (φ.toNNF false) with
  | some st =>
    let tgba := (constructGBA (φ.toNNF false) st).toTGBA
    checker.check (TGBAProduct.getSuccessors tgba sysSucc sysLabel)
      (TGBAProduct.initialStates tgba sysInit)
      (modelCheckTGBA_finiteReach φ sysInit sysSucc sysLabel sysFR hcg)
      (TGBAProduct.edgeMarks tgba sysLabel) tgba.numAcceptSets
  | none => .empty 0

omit [LawfulBEq α] [LawfulHashable α] [DecidableEq α] in
theorem modelCheckTGBA_eq (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc) (checker : TEmptinessChecker (SysState × Nat))
    {st : ExpandState α S} (hcg : createGraph (S := S) (φ.toNNF false) = some st) :
    modelCheckTGBA (S := S) φ sysInit sysSucc sysLabel sysFR checker =
      checker.check
        (TGBAProduct.getSuccessors (constructGBA (φ.toNNF false) st).toTGBA sysSucc sysLabel)
        (TGBAProduct.initialStates (constructGBA (φ.toNNF false) st).toTGBA sysInit)
        (modelCheckTGBA_finiteReach φ sysInit sysSucc sysLabel sysFR hcg)
        (TGBAProduct.edgeMarks (constructGBA (φ.toNNF false) st).toTGBA sysLabel)
        (constructGBA (φ.toNNF false) st).toTGBA.numAcceptSets := by
  unfold modelCheckTGBA
  split
  next st' hcg' =>
    obtain rfl : st' = st := Option.some.inj (hcg'.symm.trans hcg)
    rfl
  next hcg' => exact absurd (hcg'.symm.trans hcg) (by simp)

/-! ## Soundness -/

/-- An `.empty` result means every real run of the caller's system satisfies `φ`, a violating run would make the product accept. -/
theorem modelCheckTGBA_empty_unsat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc) (checker : TEmptinessChecker (SysState × Nat)) {n : Nat}
    (h : modelCheckTGBA (S := S) φ sysInit sysSucc sysLabel sysFR checker = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  intro τ hτ
  by_contra hviolate
  obtain ⟨st, hcg, _⟩ := createGraph_term (S := S) (φ.toNNF false)
  rw [modelCheckTGBA_eq φ sysInit sysSucc sysLabel sysFR checker hcg] at h
  have hgba_acc : (constructGBA (φ.toNNF false) st).toSpec.accepts (fun i a => a ∈ sysLabel (τ i)) :=
    (constructGBA_correct hcg _).mpr ((Formula.toNNF_correct_neg _ φ).mp hviolate)
  obtain ⟨σ, -, hrun, hacc⟩ := TGBAProduct.gsp_correct2 _ sysSucc sysLabel sysInit hτ
    ((GBA.toTGBA_toSpec_accepts _ _).mpr hgba_acc)
  exact checker.empty_no_cycle
    (fun p p' m hm => modelCheckTGBA_marksBound φ sysLabel st p p' m hm) h
    (TGBAProduct.exists_TAcceptingCycle_of_acceptingRun _ sysSucc sysLabel sysInit
      (modelCheckTGBA_finiteReach φ sysInit sysSucc sysLabel sysFR hcg) hrun hacc)

/-! ## Completeness -/

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckTGBA_nonEmpty_sat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc) (checker : TEmptinessChecker (SysState × Nat))
    {stem loop : List (SysState × Nat)}
    (h : modelCheckTGBA (S := S) φ sysInit sysSucc sysLabel sysFR checker = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  obtain ⟨st, hcg, _⟩ := createGraph_term (S := S) (φ.toNNF false)
  rw [modelCheckTGBA_eq φ sysInit sysSucc sysLabel sysFR checker hcg] at h
  obtain ⟨ac, -, -⟩ := checker.nonEmpty_valid
    (fun p p' m hm => modelCheckTGBA_marksBound φ sysLabel st p p' m hm) h
  obtain ⟨hτrun, hlang⟩ := TGBAProduct.gsp_correct1 _ sysSucc sysLabel sysInit
    ⟨ac.toTValidLassoProduct.run_isRun, ac.toTValidLassoProduct.run_isAccepting⟩
  refine ⟨fun n => (ac.toTValidLassoProduct.run n).1, hτrun, fun hsat => ?_⟩
  exact (Formula.toNNF_correct_neg _ φ).mpr
    ((constructGBA_correct hcg _).mp ((GBA.toTGBA_toSpec_accepts _ _).mp hlang)) hsat

/-! ## Model checking under fairness -/

omit [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [Inhabited SysState] [LawfulBEq α]
  [LawfulHashable α] [DecidableEq α] in
/-- Every extended product mark is below `numAcceptSets + fair.length`, the conjunct marks being indexed from
`numAcceptSets`. -/
theorem modelCheckTGBAFair_marksBound (φ : Formula α) (sysLabel : SysState → Std.HashSet α)
    (fair : List (BoolFormula α)) (st : ExpandState α S) (p p' : SysState × Nat) (m : Nat)
    (hm : m ∈ TGBAProduct.edgeMarksFair (constructGBA (φ.toNNF false) st).toTGBA sysLabel fair p p') :
    m < (constructGBA (φ.toNNF false) st).toTGBA.numAcceptSets + fair.length :=
  TGBAProduct.edgeMarksFair_lt _ sysLabel (GBA.toTGBA_marks_lt _) fair p p' m hm

/-- Does `sys` satisfy `φ` on every run that also satisfies every `□◇ b` for `b` in `fair`? The assumptions
never reach the translator, they become marks on the product. `modelCheckTGBA` is the `fair = []` case. -/
def modelCheckTGBAFair (φ : Formula α) (fair : List (BoolFormula α)) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker (SysState × Nat) := dijkstraTChecker) :
    EmptinessResult (SysState × Nat) :=
  match hcg : createGraph (S := S) (φ.toNNF false) with
  | some st =>
    let tgba := (constructGBA (φ.toNNF false) st).toTGBA
    checker.check (TGBAProduct.getSuccessors tgba sysSucc sysLabel)
      (TGBAProduct.initialStates tgba sysInit)
      (modelCheckTGBA_finiteReach φ sysInit sysSucc sysLabel sysFR hcg)
      (TGBAProduct.edgeMarksFair tgba sysLabel fair) (tgba.numAcceptSets + fair.length)
  | none => .empty 0

omit [LawfulBEq α] [LawfulHashable α] [DecidableEq α] in
theorem modelCheckTGBAFair_eq (φ : Formula α) (fair : List (BoolFormula α))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker (SysState × Nat))
    {st : ExpandState α S} (hcg : createGraph (S := S) (φ.toNNF false) = some st) :
    modelCheckTGBAFair (S := S) φ fair sysInit sysSucc sysLabel sysFR checker =
      checker.check
        (TGBAProduct.getSuccessors (constructGBA (φ.toNNF false) st).toTGBA sysSucc sysLabel)
        (TGBAProduct.initialStates (constructGBA (φ.toNNF false) st).toTGBA sysInit)
        (modelCheckTGBA_finiteReach φ sysInit sysSucc sysLabel sysFR hcg)
        (TGBAProduct.edgeMarksFair (constructGBA (φ.toNNF false) st).toTGBA sysLabel fair)
        ((constructGBA (φ.toNNF false) st).toTGBA.numAcceptSets + fair.length) := by
  unfold modelCheckTGBAFair
  split
  next st' hcg' =>
    obtain rfl : st' = st := Option.some.inj (hcg'.symm.trans hcg)
    rfl
  next hcg' => exact absurd (hcg'.symm.trans hcg) (by simp)

/-- An `.empty` result means every run of `sys` that satisfies every fairness assumption satisfies `φ`. The
witness the checker rules out is one run that both violates `φ` and is fair, not two independent facts. -/
theorem modelCheckTGBAFair_empty_unsat (φ : Formula α) (fair : List (BoolFormula α))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker (SysState × Nat)) {n : Nat}
    (h : modelCheckTGBAFair (S := S) φ fair sysInit sysSucc sysLabel sysFR checker = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      (∀ b ∈ fair, (BoolFormula.alwaysEventually b).satisfies (fun i a => a ∈ sysLabel (τ i))) →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  intro τ hτ hfair
  by_contra hviolate
  obtain ⟨st, hcg, _⟩ := createGraph_term (S := S) (φ.toNNF false)
  rw [modelCheckTGBAFair_eq φ fair sysInit sysSucc sysLabel sysFR checker hcg] at h
  have hgba_acc : (constructGBA (φ.toNNF false) st).toSpec.accepts (fun i a => a ∈ sysLabel (τ i)) :=
    (constructGBA_correct hcg _).mpr ((Formula.toNNF_correct_neg _ φ).mp hviolate)
  obtain ⟨σ, -, hrun, hacc⟩ := TGBAProduct.gsp_correct2Fair _ sysSucc sysLabel sysInit fair hτ
    ((GBA.toTGBA_toSpec_accepts _ _).mpr hgba_acc)
    ((TGBAProduct.fair_iff_indexed fair sysLabel τ).mp hfair)
  exact checker.empty_no_cycle
    (fun p p' m hm => modelCheckTGBAFair_marksBound φ sysLabel fair st p p' m hm) h
    (TGBAProduct.exists_TAcceptingCycle_of_acceptingRunFair _ sysSucc sysLabel sysInit fair
      (modelCheckTGBA_finiteReach φ sysInit sysSucc sysLabel sysFR hcg) hrun hacc)

/-- A `.nonEmpty` result yields one concrete run of `sys` that satisfies every fairness assumption and still
violates `φ`. -/
theorem modelCheckTGBAFair_nonEmpty_sat (φ : Formula α) (fair : List (BoolFormula α))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker (SysState × Nat)) {stem loop : List (SysState × Nat)}
    (h : modelCheckTGBAFair (S := S) φ fair sysInit sysSucc sysLabel sysFR checker
      = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      (∀ b ∈ fair, (BoolFormula.alwaysEventually b).satisfies (fun i a => a ∈ sysLabel (τ i))) ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  obtain ⟨st, hcg, _⟩ := createGraph_term (S := S) (φ.toNNF false)
  rw [modelCheckTGBAFair_eq φ fair sysInit sysSucc sysLabel sysFR checker hcg] at h
  obtain ⟨ac, -, -⟩ := checker.nonEmpty_valid
    (fun p p' m hm => modelCheckTGBAFair_marksBound φ sysLabel fair st p p' m hm) h
  have lasso := TGBAProduct.toTValidLassoProductFair _ sysSucc sysLabel sysInit fair
    (GBA.toTGBA_marks_lt _) ac
  obtain ⟨hτrun, hlang, hfair⟩ := TGBAProduct.gsp_correct1Fair _ sysSucc sysLabel sysInit fair
    lasso.run_isRun lasso.run_isAccepting
  refine ⟨fun n => (lasso.run n).1, hτrun,
    (TGBAProduct.fair_iff_indexed fair sysLabel _).mpr hfair, fun hsat => ?_⟩
  exact (Formula.toNNF_correct_neg _ φ).mpr
    ((constructGBA_correct hcg _).mp ((GBA.toTGBA_toSpec_accepts _ _).mp hlang)) hsat

end LTLLib
