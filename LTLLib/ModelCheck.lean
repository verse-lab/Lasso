/-
  End-to-end model checking: system × LTL formula φ → does the system satisfy φ?

  Standard automata-theoretic model checking: negate `φ`, build a `BA` for `¬φ`, product it against the
  caller's system (`Product.lean`), and check the product for emptiness. `sys ⊨ φ` iff the product is empty.

  Defines:
  - `modelCheck`: runs an `EmptinessChecker` on the product of `sys` and the `¬φ`-automaton
  - `modelCheck_eq`: unfolds `modelCheck` once `createGraph` is known to succeed
  - `modelCheck_empty_unsat`:   (Soundness)    An `.empty` result implies every real run of `sys` satisfies `φ`
  - `modelCheck_nonEmpty_sat`:  (Completeness) A `.nonEmpty` result yields a concrete violating run

  Sections:
  - Model checking
  - Helper: unfolding modelCheck
  - Soundness
  - Completeness
-/
import LTLLib.LTLtoGBA.Correctness
import LTLLib.DegeneralBridge
import LTLLib.LTLtoGBA.ExpandTermination
import LTLLib.Product
import LTLLib.Tactic.Set

namespace LTLLib

variable {α : Type u} {S : Type w} [FSet (NNF α) S]
  {SysState : Type v} [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
  [LawfulHashable SysState]
  [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]

/-! ## Model checking -/

/-- Does `sys` (given by `sysInit`/`sysSucc`/`sysLabel`) satisfy `φ`?

`sysFR` is a bare existence certificate (no witness) that `sys` is finitely reachable, needed only to
prove termination. Callers uninterested in termination may discharge it with `sorry`. The emptiness
check itself is supplied via an algorithm-agnostic `checker : EmptinessChecker` (`EmptinessCheck.lean`).

`.empty` means `sys ⊨ φ` whereas `.nonEmpty stem loop` witnesses a run of `sys` violating `φ`, given by
`(system state, ¬φ-automaton state)` pairs along `stem`/`loop`. -/
def modelCheck (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc)
    (checker : EmptinessChecker (SysState × BAState) := nestedDFSChecker) :
    EmptinessResult (SysState × BAState) :=
  let negNNF := φ.toNNF false
  match hcg : createGraph (S := S) negNNF with
  | some st =>
    let ba := (constructGBA negNNF st).degeneralize
    let hbawf := degeneralize_wellFormed_any (constructGBA negNNF st)
      (constructGBA_wellFormed hcg)
    checker.check (Product.getSuccessors ba sysSucc sysLabel)
      (Product.initialStates ba sysInit)
      (Product.finiteReach ba hbawf sysSucc sysLabel sysInit sysFR) (Product.isAccepting ba)
  | none => .empty 0

/-! ## Helper: unfolding modelCheck -/

omit [LawfulHashable SysState] [LawfulBEq α] [LawfulHashable α] in
theorem modelCheck_eq (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc)
    (checker : EmptinessChecker (SysState × BAState))
    {st : ExpandState α S} (hcg : createGraph (φ.toNNF false) = some st) :
    modelCheck (S := S) φ sysInit sysSucc sysLabel sysFR checker =
      let ba := (constructGBA (φ.toNNF false) st).degeneralize
      let hbawf := degeneralize_wellFormed_any (constructGBA (φ.toNNF false) st)
        (constructGBA_wellFormed hcg)
      checker.check (Product.getSuccessors ba sysSucc sysLabel)
        (Product.initialStates ba sysInit)
        (Product.finiteReach ba hbawf sysSucc sysLabel sysInit sysFR)
        (Product.isAccepting ba) := by
  unfold modelCheck
  dsimp only
  split
  next st' hcg' =>
    obtain rfl : st' = st := Option.some.inj (hcg'.symm.trans hcg)
    rfl
  next hcg' => exact absurd (hcg'.symm.trans hcg) (by simp)

/-! ## Soundness -/

omit [LawfulHashable SysState] in
/-- If `modelCheck` finds no counterexample, then every real run of the caller's system satisfies `φ`. -/
theorem modelCheck_empty_unsat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc)
    (checker : EmptinessChecker (SysState × BAState)) {n : Nat}
    (h : modelCheck (S := S) φ sysInit sysSucc sysLabel sysFR checker = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  intro τ hτ
  by_contra hviolate
  obtain ⟨st, hcg, _⟩ := createGraph_term (S := S) (φ.toNNF false)
  rw [modelCheck_eq φ sysInit sysSucc sysLabel sysFR checker hcg] at h
  set gba := constructGBA (φ.toNNF false) st with hgba
  set ba := gba.degeneralize with hba
  have hwf := constructGBA_wellFormed hcg
  have hbawf := degeneralize_wellFormed_any gba hwf
  have hgba_acc : gba.toSpec.accepts (fun i a => a ∈ sysLabel (τ i)) :=
    (constructGBA_correct hcg _).mpr ((Formula.toNNF_correct_neg _ φ).mp hviolate)
  have hba_acc : ba.toSpec.accepts (fun i a => a ∈ sysLabel (τ i)) :=
    (degeneralize_accepts_any gba hwf _).mpr hgba_acc
  obtain ⟨r, _, hrrun, hracc⟩ := Product.gsp_correct2 ba sysSucc sysLabel sysInit hτ hba_acc
  have hcyc : ∃ _ac : AcceptingCycle (Product.initialStates ba sysInit)
      (Product.getSuccessors ba sysSucc sysLabel) (Product.isAccepting ba), True :=
    exists_acceptingCycle_of_run (Product.finiteReach ba hbawf sysSucc sysLabel sysInit sysFR)
      hrrun.1 hrrun.2
      (fun N => by
        obtain ⟨j, hj⟩ := hracc ⟨0, Nat.one_pos⟩ N
        exact ⟨N + j, by omega, hj⟩)
  exact checker.empty_no_cycle h hcyc

/-! ## Completeness -/

omit [LawfulHashable SysState] in
/-- If `modelCheck` finds a counterexample, there's a concrete witness run of `sys` violating `φ`. -/
theorem modelCheck_nonEmpty_sat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc)
    (checker : EmptinessChecker (SysState × BAState))
    {stem loop : List (SysState × BAState)}
    (h : modelCheck (S := S) φ sysInit sysSucc sysLabel sysFR checker = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  obtain ⟨st, hcg, _⟩ := createGraph_term (S := S) (φ.toNNF false)
  rw [modelCheck_eq φ sysInit sysSucc sysLabel sysFR checker hcg] at h
  set gba := constructGBA (φ.toNNF false) st with hgba
  set ba := gba.degeneralize with hba
  have hwf := constructGBA_wellFormed hcg
  have hbawf := degeneralize_wellFormed_any gba hwf
  obtain ⟨ac, _, _⟩ := checker.nonEmpty_valid h
  have hrrun := ac.toValidLassoProduct.run_isRun
  have hracc := ac.toValidLassoProduct.run_isAccepting
  obtain ⟨hτrun, hlang⟩ := Product.gsp_correct1 ba sysSucc sysLabel sysInit ⟨hrrun, hracc⟩
  refine ⟨Prod.fst ∘ ac.toValidLassoProduct.run, hτrun, fun hsat => ?_⟩
  obtain ⟨σ, hσrun, hσcompat, hσacc⟩ := hlang
  have hgba_acc : gba.toSpec.accepts (fun n a => a ∈ sysLabel (ac.toValidLassoProduct.run n).1) :=
    (degeneralize_accepts_any gba hwf _).mp ⟨σ, hσrun, hσcompat, hσacc⟩
  exact (Formula.toNNF_correct_neg _ φ).mpr ((constructGBA_correct hcg _).mp hgba_acc) hsat

end LTLLib
