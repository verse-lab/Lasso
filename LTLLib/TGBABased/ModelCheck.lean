/-
  One entry point per search mode, `sys ⊨ φ` or `sys ⊨ (fair → φ)` with the fairness assumption hoisted out of the
  property. Each mode names a search defined elsewhere and restates its soundness and completeness. Every mode
  translates with `ltl3ba` (`LTLtoTGBA/Pipeline.lean`).

  Defines:
  - `modelCheckNDFS`: transition-based Nested DFS on the degeneralized TGBA product (`modelCheckTBA` in `NDFSCheck.lean`),
    no fairness
  - `modelCheckDijkstra`: Dijkstra's SCC-based search on the TGBA product (`modelCheckTGBA` in `DijkstraCheck.lean`), no
    fairness
  - `modelCheckFairDirect`: hoists only the conjuncts that are syntactically `□◇p`/`◇□p` over state predicates, and
    Boolean combinations of them, and translates the rest (`modelCheckUnderFairnessFlat` in `Fairness/FairRouter.lean`). This is
    exactly what TLC's `classifyExpr`, PAT's classifier and NuSMV's `JUSTICE`/`COMPASSION` recognise, so the gap to
    `modelCheckFairFNFPrune` measures, from inside our own pipeline, what those tools leave on the table. It exists for
    the ablation study.
  - `modelCheckFairFNFCross`: every fairness conjunct hoisted through its fair normal form, re-hoisted after rewriting,
    and crossed into one Dijkstra check per disjunct (`modelCheckUnderFairnessRehoistCross` in
    `Fairness/FairPipeline.lean`)
  - `modelCheckFairFNFPrune`: the same split, decided per SCC by the Streett prune instead of crossed
    (`modelCheckUnderFairnessRehoistPrune`)
  - `modelCheckFair`: the default and fastest, the prune with disjunctive hoisting, a kept conjunct `ψ ∨ γ` with a flattenable
    fairness `γ` decided by one prune run per choice of side (`modelCheckUnderFairnessDisjunctiveHoist`)

  Proves, for each mode `m`:
  - `m_empty_unsat`: (Soundness) an `.empty` result means every run of `sys` satisfies `φ`
  - `m_nonEmpty_sat`: (Completeness) a `.nonEmpty` result yields a run of `sys` violating `φ`

  Sections:
  - Nested DFS
  - Dijkstra
  - Fairness, flat conjuncts only
  - Fairness, fair normal form crossed
  - Fairness, fair normal form pruned
  - Fairness, default
-/
import LTLLib.TGBABased.DijkstraCheck
import LTLLib.TGBABased.Fairness.FairPipeline
import LTLLib.TGBABased.Fairness.FairRouter
import LTLLib.TGBABased.NDFSCheck

namespace LTLLib

variable {α : Type u} {SysState : Type v} [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
  [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α]

/-! ## Nested DFS -/

/-- Transition-based Nested DFS on the degeneralized TGBA product: `sys ⊨ φ`, no fairness.

Like `modelCheckDijkstra`, this reads a *labelled* system, so an edge atom such as `taken(a)` is supported
at no cost in product states. A system with no edge atoms is passed as `LSys.unlabelled sysSucc`. -/
def modelCheckNDFS (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) : EmptinessResult (SysState × TBAState) :=
  modelCheckTBA φ sysInit sysSucc sysLabel sysFR

/-- An `.empty` result means every real run of `sys` satisfies `φ`, the letter at each position being the
source state's atoms together with the step's own. -/
theorem modelCheckNDFS_empty_unsat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {n : Nat}
    (h : modelCheckNDFS φ sysInit sysSucc sysLabel sysFR = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ :=
  modelCheckTBA_empty_unsat φ sysInit sysSucc sysLabel sysFR h

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckNDFS_nonEmpty_sat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {stem loop : List (SysState × TBAState)}
    (h : modelCheckNDFS φ sysInit sysSucc sysLabel sysFR = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ :=
  modelCheckTBA_nonEmpty_sat φ sysInit sysSucc sysLabel sysFR h

variable [Inhabited SysState]

/-! ## Dijkstra -/

/-- Dijkstra's SCC-based search on the TGBA product: `sys ⊨ φ`, no fairness.

This mode reads a *labelled* system (`TGBABased/LabelledSys.lean`): each step carries the atoms it itself
contributes, so an edge atom such as `taken(a)` is supported at no cost in product states. A system with no
edge atoms is passed as `LSys.unlabelled sysSucc`; `LSys.toSpec_isRun_ofRun` and `LSys.valuation_unlabelled`
read the statements below back as statements about `Sys.toSpec`. -/
def modelCheckDijkstra (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) : EmptinessResult (SysState × Nat) :=
  modelCheckTGBA φ sysInit sysSucc sysLabel sysFR

/-- An `.empty` result means every real run of `sys` satisfies `φ`, the letter at each position being the
source state's atoms together with the step's own. -/
theorem modelCheckDijkstra_empty_unsat [LawfulHashable SysState] (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {n : Nat}
    (h : modelCheckDijkstra φ sysInit sysSucc sysLabel sysFR = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ :=
  modelCheckTGBA_empty_unsat φ sysInit sysSucc sysLabel sysFR dijkstraTChecker h

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckDijkstra_nonEmpty_sat [LawfulHashable SysState] (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {stem loop : List (SysState × Nat)}
    (h : modelCheckDijkstra φ sysInit sysSucc sysLabel sysFR = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ :=
  modelCheckTGBA_nonEmpty_sat φ sysInit sysSucc sysLabel sysFR dijkstraTChecker h

/-! ## Fairness, flat conjuncts only -/

/-- Only flat fairness hoisted and decided per SCC, everything else translated: `sys ⊨ φ`. -/
def modelCheckFairDirect (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α) :
    EmptinessResult (SysState × Nat) :=
  modelCheckUnderFairnessFlat φ sysInit sysSucc sysLabel

/-- An `.empty` result means every real run of `sys` satisfies `φ`. -/
theorem modelCheckFairDirect_empty_unsat [LawfulHashable SysState] (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {n : Nat}
    (h : modelCheckFairDirect φ sysInit sysSucc sysLabel = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ :=
  modelCheckUnderFairnessFlat_empty_unsat φ sysInit sysSucc sysLabel sysFR h

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckFairDirect_nonEmpty_sat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (hstate : ∀ ds ∈ (hoistFlat (φ.toNNF false).splitConj).1,
      ∀ d ∈ ds, LSys.StateOnly sysSucc sysLabel d.1.eval)
    {stem loop : List (SysState × Nat)}
    (h : modelCheckFairDirect φ sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ :=
  modelCheckUnderFairnessFlat_nonEmpty_sat φ sysInit sysSucc sysLabel hstate h

/-! ## Fairness, fair normal form crossed -/

/-- Every fairness conjunct hoisted through its fair normal form and crossed, one Dijkstra check per disjunct:
`sys ⊨ φ`.

Like `modelCheckDijkstra` and `modelCheckNDFS` this reads a *labelled* system, so a hoisted fairness may
mention an edge atom such as `taken(a)` — the crossing's region and marks are both decided on the letter
each step contributes. A system with no edge atoms is passed as `LSys.unlabelled sysSucc`. The three prune
routes below are not there yet; see `EdgeLabels.md` §11. -/
def modelCheckFairFNFCross (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) : EmptinessResult ((SysState × Nat) × Bool) :=
  modelCheckUnderFairnessRehoistCross φ sysInit sysSucc sysLabel sysFR

/-- An `.empty` result means every real run of `sys` satisfies `φ`, the letter at each position being the
source state's atoms together with the step's own. -/
theorem modelCheckFairFNFCross_empty_unsat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {n : Nat}
    (h : modelCheckFairFNFCross φ sysInit sysSucc sysLabel sysFR = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ :=
  modelCheckUnderFairnessRehoistCross_empty_unsat φ sysInit sysSucc sysLabel sysFR dijkstraTChecker dijkstraTChecker h

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckFairFNFCross_nonEmpty_sat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {stem loop : List ((SysState × Nat) × Bool)}
    (h : modelCheckFairFNFCross φ sysInit sysSucc sysLabel sysFR = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ :=
  modelCheckUnderFairnessRehoistCross_nonEmpty_sat φ sysInit sysSucc sysLabel sysFR dijkstraTChecker
    dijkstraTChecker h

/-! ## Fairness, fair normal form pruned -/

/-- Every fairness conjunct hoisted through its fair normal form and decided per SCC: `sys ⊨ φ`. -/
def modelCheckFairFNFPrune (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α) :
    EmptinessResult (SysState × Nat) :=
  modelCheckUnderFairnessRehoistPrune φ sysInit sysSucc sysLabel

/-- An `.empty` result means every real run of `sys` satisfies `φ`. -/
theorem modelCheckFairFNFPrune_empty_unsat [LawfulHashable SysState] (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {n : Nat}
    (h : modelCheckFairFNFPrune φ sysInit sysSucc sysLabel = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ :=
  modelCheckUnderFairnessRehoistPrune_empty_unsat φ sysInit sysSucc sysLabel sysFR h

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckFairFNFPrune_nonEmpty_sat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (hstate : ∀ ds ∈ (hoistFairness (φ.toNNF false).splitConj).1 ++
        (rehoist (hoistFairness (φ.toNNF false).splitConj).2).1,
      ∀ d ∈ ds, LSys.StateOnly sysSucc sysLabel d.1.eval)
    {stem loop : List (SysState × Nat)}
    (h : modelCheckFairFNFPrune φ sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ :=
  modelCheckUnderFairnessRehoistPrune_nonEmpty_sat φ sysInit sysSucc sysLabel hstate h

/-! ## Fairness, default -/

/-- The default: every fairness conjunct hoisted and decided per SCC, and every kept conjunct with a hoistable
fairness side crossed on its sides: `sys ⊨ φ`. -/
def modelCheckFair (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α) :
    EmptinessResult (SysState × Nat) :=
  modelCheckUnderFairnessDisjunctiveHoist φ sysInit sysSucc sysLabel

/-- An `.empty` result means every real run of `sys` satisfies `φ`. -/
theorem modelCheckFair_empty_unsat [LawfulHashable SysState] (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {n : Nat}
    (h : modelCheckFair φ sysInit sysSucc sysLabel = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ :=
  modelCheckUnderFairnessDisjunctiveHoist_empty_unsat φ sysInit sysSucc sysLabel sysFR h

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckFair_nonEmpty_sat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (hstate : ∀ b ∈ branches (rehoist (hoistFairness (φ.toNNF false).splitConj).2).2,
      ∀ ds ∈ (hoistFairness (φ.toNNF false).splitConj).1 ++
          (rehoist (hoistFairness (φ.toNNF false).splitConj).2).1 ++ b.1,
      ∀ d ∈ ds, LSys.StateOnly sysSucc sysLabel d.1.eval)
    {stem loop : List (SysState × Nat)}
    (h : modelCheckFair φ sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ :=
  modelCheckUnderFairnessDisjunctiveHoist_nonEmpty_sat φ sysInit sysSucc sysLabel hstate h


/-! ## The fused entry points

Each takes `LSys.StepFn` — a state's steps and its atoms from **one** call — where the route above takes
`sysSucc` and `sysLabel` separately. The two are the same term: Lean's definitional eta for structures
makes `fun s => ((f s).1, (f s).2)` and `f` interchangeable, so every bridge is `rfl` and every soundness
theorem transfers by applying the existing one. Nothing above is restated or reproved.

This exists so that "one walk of the system per state" is a property of the *type* rather than of a memo
installed behind `@[implemented_by]`. Veil's `tr` is expensive enough that computing it twice per state
dominated the run (`EdgeLabels.md` §12.12), and the memo that fixed it was `unsafe` code the kernel never
checked and that `#print axioms` never mentioned. §15. -/

section OfStep

variable (φ : Formula α) (sysInit : List SysState) (sysStep : LSys.StepFn α SysState)

/-- `modelCheckFair` over one system callback. -/
def modelCheckFairOfStep : EmptinessResult (SysState × Nat) :=
  modelCheckUnderFairnessDisjunctiveHoistOfStep φ sysInit sysStep

theorem modelCheckFairOfStep_eq (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) :
    modelCheckFairOfStep φ sysInit (fun s => (sysSucc s, sysLabel s))
      = modelCheckFair φ sysInit sysSucc sysLabel := rfl

/-- An `.empty` result means every real run of `sys` satisfies `φ`. -/
theorem modelCheckFairOfStep_empty_unsat [LawfulHashable SysState]
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) {n : Nat}
    (h : modelCheckFairOfStep φ sysInit sysStep = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ →
      Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ :=
  modelCheckFair_empty_unsat φ sysInit _ _ sysFR h

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckFairOfStep_nonEmpty_sat [LawfulHashable SysState]
    {stem loop : List (SysState × Nat)}
    (hstate : ∀ b ∈ branches (rehoist (hoistFairness (φ.toNNF false).splitConj).2).2,
      ∀ ds ∈ (hoistFairness (φ.toNNF false).splitConj).1 ++
          (rehoist (hoistFairness (φ.toNNF false).splitConj).2).1 ++ b.1,
      ∀ d ∈ ds, LSys.StateOnly (fun s => (sysStep s).1) (fun s => (sysStep s).2) d.1.eval)
    (h : modelCheckFairOfStep φ sysInit sysStep = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ :=
  modelCheckFair_nonEmpty_sat φ sysInit _ _ hstate h

/-- `modelCheckFairFNFPrune` over one system callback. -/
def modelCheckFairFNFPruneOfStep : EmptinessResult (SysState × Nat) :=
  modelCheckUnderFairnessRehoistPruneOfStep φ sysInit sysStep

theorem modelCheckFairFNFPruneOfStep_eq (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) :
    modelCheckFairFNFPruneOfStep φ sysInit (fun s => (sysSucc s, sysLabel s))
      = modelCheckFairFNFPrune φ sysInit sysSucc sysLabel := rfl

theorem modelCheckFairFNFPruneOfStep_empty_unsat [LawfulHashable SysState]
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) {n : Nat}
    (h : modelCheckFairFNFPruneOfStep φ sysInit sysStep = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ →
      Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ :=
  modelCheckFairFNFPrune_empty_unsat φ sysInit _ _ sysFR h

theorem modelCheckFairFNFPruneOfStep_nonEmpty_sat
    {stem loop : List (SysState × Nat)}
    (hstate : ∀ ds ∈ (hoistFairness (φ.toNNF false).splitConj).1 ++
        (rehoist (hoistFairness (φ.toNNF false).splitConj).2).1,
      ∀ d ∈ ds, LSys.StateOnly (fun s => (sysStep s).1) (fun s => (sysStep s).2) d.1.eval)
    (h : modelCheckFairFNFPruneOfStep φ sysInit sysStep = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ :=
  modelCheckFairFNFPrune_nonEmpty_sat φ sysInit _ _ hstate h


/-- `modelCheckFairDirect` (the PAT-style flat route) over one system callback. -/
def modelCheckFairDirectOfStep : EmptinessResult (SysState × Nat) :=
  modelCheckUnderFairnessFlatOfStep φ sysInit sysStep

theorem modelCheckFairDirectOfStep_eq (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) :
    modelCheckFairDirectOfStep φ sysInit (fun s => (sysSucc s, sysLabel s))
      = modelCheckFairDirect φ sysInit sysSucc sysLabel := rfl

theorem modelCheckFairDirectOfStep_empty_unsat [LawfulHashable SysState]
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) {n : Nat}
    (h : modelCheckFairDirectOfStep φ sysInit sysStep = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ →
      Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ :=
  modelCheckFairDirect_empty_unsat φ sysInit _ _ sysFR h

theorem modelCheckFairDirectOfStep_nonEmpty_sat {stem loop : List (SysState × Nat)}
    (hstate : ∀ ds ∈ (hoistFlat (φ.toNNF false).splitConj).1,
      ∀ d ∈ ds, LSys.StateOnly (fun s => (sysStep s).1) (fun s => (sysStep s).2) d.1.eval)
    (h : modelCheckFairDirectOfStep φ sysInit sysStep = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ :=
  modelCheckFairDirect_nonEmpty_sat φ sysInit _ _ hstate h

/-- `modelCheckDijkstra` over one system callback. -/
def modelCheckDijkstraOfStep
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) :
    EmptinessResult (SysState × Nat) :=
  modelCheckTGBAOfStep φ sysInit sysStep sysFR

theorem modelCheckDijkstraOfStep_eq (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) :
    modelCheckDijkstraOfStep φ sysInit (fun s => (sysSucc s, sysLabel s)) sysFR
      = modelCheckDijkstra φ sysInit sysSucc sysLabel sysFR := rfl

theorem modelCheckDijkstraOfStep_empty_unsat [LawfulHashable SysState]
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) {n : Nat}
    (h : modelCheckDijkstraOfStep φ sysInit sysStep sysFR = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ →
      Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ :=
  modelCheckDijkstra_empty_unsat φ sysInit _ _ sysFR h

theorem modelCheckDijkstraOfStep_nonEmpty_sat [LawfulHashable SysState]
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1))
    {stem loop : List (SysState × Nat)}
    (h : modelCheckDijkstraOfStep φ sysInit sysStep sysFR = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ :=
  modelCheckDijkstra_nonEmpty_sat φ sysInit _ _ sysFR h

/-- `modelCheckNDFS` over one system callback. -/
def modelCheckNDFSOfStep
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) :
    EmptinessResult (SysState × TBAState) :=
  modelCheckTBAOfStep φ sysInit sysStep sysFR

theorem modelCheckNDFSOfStep_eq (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) :
    modelCheckNDFSOfStep φ sysInit (fun s => (sysSucc s, sysLabel s)) sysFR
      = modelCheckNDFS φ sysInit sysSucc sysLabel sysFR := rfl

theorem modelCheckNDFSOfStep_empty_unsat
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) {n : Nat}
    (h : modelCheckNDFSOfStep φ sysInit sysStep sysFR = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ →
      Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ :=
  modelCheckNDFS_empty_unsat φ sysInit _ _ sysFR h


/-- `modelCheckFairFNFCross` (the crossing) over one system callback. -/
def modelCheckFairFNFCrossOfStep
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  modelCheckUnderFairnessRehoistCrossOfStep φ sysInit sysStep sysFR

theorem modelCheckFairFNFCrossOfStep_eq (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) :
    modelCheckFairFNFCrossOfStep φ sysInit (fun s => (sysSucc s, sysLabel s)) sysFR
      = modelCheckFairFNFCross φ sysInit sysSucc sysLabel sysFR := rfl

theorem modelCheckFairFNFCrossOfStep_nonEmpty_sat
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1))
    {stem loop : List ((SysState × Nat) × Bool)}
    (h : modelCheckFairFNFCrossOfStep φ sysInit sysStep sysFR = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ :=
  modelCheckFairFNFCross_nonEmpty_sat φ sysInit _ _ sysFR h

theorem modelCheckFairFNFCrossOfStep_empty_unsat
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) {n : Nat}
    (h : modelCheckFairFNFCrossOfStep φ sysInit sysStep sysFR = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ →
      Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ :=
  modelCheckFairFNFCross_empty_unsat φ sysInit _ _ sysFR h

end OfStep

end LTLLib
