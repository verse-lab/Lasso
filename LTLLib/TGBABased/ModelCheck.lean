/-
  End-to-end model checking: system × LTL formula φ → does the system satisfy φ? Negate `φ`, build the
  `¬φ`-`TGBA`, product it against the caller's system (`Product.lean`), and check the product for emptiness.
  `sys ⊨ φ` iff the product is empty.

  Defines:
  - `modelCheckTGBA`: runs a `TEmptinessChecker` on the product of `sys` and the `¬φ`-automaton
  - `modelCheckTGBA_eq`: unfolds `modelCheckTGBA` once `createGraph` is known to succeed
  - `modelCheckTGBA_empty_unsat`:  (Soundness)    an `.empty` result implies every run of `sys` satisfies `φ`
  - `modelCheckTGBA_nonEmpty_sat`: (Completeness) a `.nonEmpty` result yields a concrete violating run

  Sections:
  - Checker obligations
  - Model checking
  - Soundness
  - Completeness
-/
import LTLLib.LTL.Semantics
import LTLLib.LTLtoGBA.Bridge
import LTLLib.LTLtoGBA.Completeness
import LTLLib.LTLtoGBA.Correctness
import LTLLib.LTLtoGBA.ExpandTermination
import LTLLib.Product
import LTLLib.TGBABased.AbstractSpec.EmptinessCheck
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

end LTLLib
