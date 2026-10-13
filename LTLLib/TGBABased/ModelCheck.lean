module

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
  - `modelCheckFairRoutedOfStep`: `modelCheckFair` with the fallback to `modelCheckFairFNFCross` made for the caller,
    which supplies only the predicate marking the atoms a step may contribute (`pruneApplicable` in
    `Fairness/FairPipeline.lean`). This is the entry point a front end should call.

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
  - The fused entry points
  - Fairness, routed
-/
public import LTLLib.TGBABased.DijkstraCheck
public import LTLLib.TGBABased.Fairness.FairPipeline
public import LTLLib.TGBABased.Fairness.FairRouter
public import LTLLib.TGBABased.NDFSCheck

public section

namespace LTLLib

variable {α : Type u} {SysState : Type v} [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
  [BEq α] [Hashable α]

section Modes

variable [LawfulBEq α] [LawfulHashable α] [DecidableEq α]

/-! ## Nested DFS -/

/-- Transition-based Nested DFS on the degeneralized TGBA product: `sys ⊨ φ`, no fairness.

Like `modelCheckDijkstra`, this reads a *labelled* system, so an edge atom such as `taken(a)` is supported
at no cost in product states. A system with no edge atoms is passed as `LSys.unlabelled sysSucc`. -/
@[expose] def modelCheckNDFS (φ : Formula α) (sysInit : List SysState)
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
@[expose] def modelCheckDijkstra (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α) :
    EmptinessResult (SysState × Nat) :=
  modelCheckTGBA φ sysInit sysSucc sysLabel

/-- An `.empty` result means every real run of `sys` satisfies `φ`, the letter at each position being the
source state's atoms together with the step's own. -/
theorem modelCheckDijkstra_empty_unsat [LawfulHashable SysState] (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {n : Nat}
    (h : modelCheckDijkstra φ sysInit sysSucc sysLabel = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ :=
  modelCheckTGBA_empty_unsat φ sysInit sysSucc sysLabel sysFR dijkstraTChecker h

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckDijkstra_nonEmpty_sat [LawfulHashable SysState] (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {stem loop : List (SysState × Nat)}
    (h : modelCheckDijkstra φ sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ :=
  modelCheckTGBA_nonEmpty_sat φ sysInit sysSucc sysLabel sysFR dijkstraTChecker h

/-! ## Fairness, flat conjuncts only -/

/-- Only flat fairness hoisted and decided per SCC, everything else translated: `sys ⊨ φ`. -/
@[expose] def modelCheckFairDirect (φ : Formula α) (sysInit : List SysState)
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
@[expose] def modelCheckFairFNFCross (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  modelCheckUnderFairnessRehoistCross φ sysInit sysSucc sysLabel

/-- An `.empty` result means every real run of `sys` satisfies `φ`, the letter at each position being the
source state's atoms together with the step's own. -/
theorem modelCheckFairFNFCross_empty_unsat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {n : Nat}
    (h : modelCheckFairFNFCross φ sysInit sysSucc sysLabel = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ :=
  modelCheckUnderFairnessRehoistCross_empty_unsat φ sysInit sysSucc sysLabel sysFR dijkstraTChecker dijkstraTChecker h

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckFairFNFCross_nonEmpty_sat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {stem loop : List ((SysState × Nat) × Bool)}
    (h : modelCheckFairFNFCross φ sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ ∧
      (∀ n, (lassoAt stem loop.tail n).map (·.1.1) = some (ρ n).1) :=
  modelCheckUnderFairnessRehoistCross_nonEmpty_sat φ sysInit sysSucc sysLabel sysFR dijkstraTChecker
    dijkstraTChecker h

/-! ## Fairness, fair normal form pruned -/

/-- Every fairness conjunct hoisted through its fair normal form and decided per SCC: `sys ⊨ φ`. -/
@[expose] def modelCheckFairFNFPrune (φ : Formula α) (sysInit : List SysState)
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
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ ∧
      (∀ n, (lassoAt stem loop.tail n).map Prod.fst = some (ρ n).1) :=
  modelCheckUnderFairnessRehoistPrune_nonEmpty_sat φ sysInit sysSucc sysLabel hstate h

/-! ## Fairness, default -/

/-- The default: every fairness conjunct hoisted and decided per SCC, and every kept conjunct with a hoistable
fairness side crossed on its sides: `sys ⊨ φ`. -/
@[expose] def modelCheckFair (φ : Formula α) (sysInit : List SysState)
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
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ ∧
      (∀ n, (lassoAt stem loop.tail n).map Prod.fst = some (ρ n).1) :=
  modelCheckUnderFairnessDisjunctiveHoist_nonEmpty_sat φ sysInit sysSucc sysLabel hstate h

end Modes


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

section Fair

variable [Inhabited SysState] [DecidableEq α]

/-- `modelCheckFair` over one system callback. -/
@[expose] def modelCheckFairOfStep : EmptinessResult (SysState × Nat) :=
  modelCheckUnderFairnessDisjunctiveHoistOfStep φ sysInit sysStep

theorem modelCheckFairOfStep_eq (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) :
    modelCheckFairOfStep φ sysInit (fun s => (sysSucc s, sysLabel s))
      = modelCheckFair φ sysInit sysSucc sysLabel := rfl

variable [LawfulBEq α] [LawfulHashable α]

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
      ¬ Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ ∧
      (∀ n, (lassoAt stem loop.tail n).map Prod.fst = some (ρ n).1) :=
  modelCheckFair_nonEmpty_sat φ sysInit _ _ hstate h

end Fair

section FairFNFPrune

variable [Inhabited SysState] [DecidableEq α]

/-- `modelCheckFairFNFPrune` over one system callback. -/
@[expose] def modelCheckFairFNFPruneOfStep : EmptinessResult (SysState × Nat) :=
  modelCheckUnderFairnessRehoistPruneOfStep φ sysInit sysStep

theorem modelCheckFairFNFPruneOfStep_eq (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) :
    modelCheckFairFNFPruneOfStep φ sysInit (fun s => (sysSucc s, sysLabel s))
      = modelCheckFairFNFPrune φ sysInit sysSucc sysLabel := rfl

variable [LawfulBEq α] [LawfulHashable α]

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
      ¬ Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ ∧
      (∀ n, (lassoAt stem loop.tail n).map Prod.fst = some (ρ n).1) :=
  modelCheckFairFNFPrune_nonEmpty_sat φ sysInit _ _ hstate h

end FairFNFPrune

section FairDirect

variable [Inhabited SysState] [DecidableEq α]

/-- `modelCheckFairDirect` (the PAT-style flat route) over one system callback. -/
@[expose] def modelCheckFairDirectOfStep : EmptinessResult (SysState × Nat) :=
  modelCheckUnderFairnessFlatOfStep φ sysInit sysStep

theorem modelCheckFairDirectOfStep_eq (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) :
    modelCheckFairDirectOfStep φ sysInit (fun s => (sysSucc s, sysLabel s))
      = modelCheckFairDirect φ sysInit sysSucc sysLabel := rfl

variable [LawfulBEq α] [LawfulHashable α]

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

end FairDirect

section Dijkstra

variable [Inhabited SysState]

/-- `modelCheckDijkstra` over one system callback. -/
@[expose] def modelCheckDijkstraOfStep : EmptinessResult (SysState × Nat) :=
  modelCheckTGBAOfStep φ sysInit sysStep

theorem modelCheckDijkstraOfStep_eq (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) :
    modelCheckDijkstraOfStep φ sysInit (fun s => (sysSucc s, sysLabel s))
      = modelCheckDijkstra φ sysInit sysSucc sysLabel := rfl

variable [LawfulBEq α] [LawfulHashable α] [DecidableEq α]

theorem modelCheckDijkstraOfStep_empty_unsat [LawfulHashable SysState]
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) {n : Nat}
    (h : modelCheckDijkstraOfStep φ sysInit sysStep = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ →
      Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ :=
  modelCheckDijkstra_empty_unsat φ sysInit _ _ sysFR h

theorem modelCheckDijkstraOfStep_nonEmpty_sat [LawfulHashable SysState]
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1))
    {stem loop : List (SysState × Nat)}
    (h : modelCheckDijkstraOfStep φ sysInit sysStep = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ :=
  modelCheckDijkstra_nonEmpty_sat φ sysInit _ _ sysFR h

end Dijkstra

section NDFS

variable [LawfulBEq α] [LawfulHashable α]

/-- `modelCheckNDFS` over one system callback. -/
@[expose] def modelCheckNDFSOfStep
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) :
    EmptinessResult (SysState × TBAState) :=
  modelCheckTBAOfStep φ sysInit sysStep sysFR

theorem modelCheckNDFSOfStep_eq (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) :
    modelCheckNDFSOfStep φ sysInit (fun s => (sysSucc s, sysLabel s)) sysFR
      = modelCheckNDFS φ sysInit sysSucc sysLabel sysFR := rfl

variable [DecidableEq α]

theorem modelCheckNDFSOfStep_empty_unsat
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) {n : Nat}
    (h : modelCheckNDFSOfStep φ sysInit sysStep sysFR = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ →
      Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ :=
  modelCheckNDFS_empty_unsat φ sysInit _ _ sysFR h

end NDFS

section FairFNFCross

variable [Inhabited SysState] [DecidableEq α]

/-- `modelCheckFairFNFCross` (the crossing) over one system callback. -/
@[expose] def modelCheckFairFNFCrossOfStep : EmptinessResult ((SysState × Nat) × Bool) :=
  modelCheckUnderFairnessRehoistCrossOfStep φ sysInit sysStep

theorem modelCheckFairFNFCrossOfStep_eq (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) :
    modelCheckFairFNFCrossOfStep φ sysInit (fun s => (sysSucc s, sysLabel s))
      = modelCheckFairFNFCross φ sysInit sysSucc sysLabel := rfl

variable [LawfulBEq α] [LawfulHashable α]

theorem modelCheckFairFNFCrossOfStep_nonEmpty_sat
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1))
    {stem loop : List ((SysState × Nat) × Bool)}
    (h : modelCheckFairFNFCrossOfStep φ sysInit sysStep = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ ∧
      (∀ n, (lassoAt stem loop.tail n).map (·.1.1) = some (ρ n).1) :=
  modelCheckFairFNFCross_nonEmpty_sat φ sysInit _ _ sysFR h

theorem modelCheckFairFNFCrossOfStep_empty_unsat
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) {n : Nat}
    (h : modelCheckFairFNFCrossOfStep φ sysInit sysStep = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ →
      Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ :=
  modelCheckFairFNFCross_empty_unsat φ sysInit _ _ sysFR h

end FairFNFCross

section FairRouted

variable [Inhabited SysState] [DecidableEq α]

/-- **The default entry point under fairness, with the route chosen for the caller.**

`modelCheckFairOfStep` (the prune) is the faster route but its witness contract needs every hoisted
region to be decidable from the source state. `edgeAtom` marks the atoms a *step* may contribute, which is
all a caller has to supply: `pruneApplicable` then tests the regions each branch of the prune actually
receives, and a property that puts one of those atoms inside a hoisted `◇□` falls back to
`modelCheckFairFNFCrossOfStep` (the crossing), which decides such a region by latching it into the product.
A system with no edge atoms passes `fun _ => false` and always takes the prune.

Both routes answer the same question in different products — the crossing's state carries the latch — so
the latch is projected away and both report in `SysState × Nat`. -/
@[expose] def modelCheckFairRoutedOfStep (edgeAtom : α → Bool) : EmptinessResult (SysState × Nat) :=
  if pruneApplicable edgeAtom φ then
    modelCheckFairOfStep φ sysInit sysStep
  else
    (modelCheckFairFNFCrossOfStep φ sysInit sysStep).map Prod.fst

variable [LawfulBEq α] [LawfulHashable α]

/-- An `.empty` result means every real run of `sys` satisfies `φ`, whichever route ran. Soundness needs
nothing of `edgeAtom`: the prune's `.empty` verdict is sound unconditionally (`modelCheckPruneSplit`). -/
theorem modelCheckFairRoutedOfStep_empty_unsat [LawfulHashable SysState] (edgeAtom : α → Bool)
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) {n : Nat}
    (h : modelCheckFairRoutedOfStep φ sysInit sysStep edgeAtom = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ →
      Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ := by
  rw [modelCheckFairRoutedOfStep] at h
  split at h
  · exact modelCheckFairOfStep_empty_unsat φ sysInit sysStep sysFR h
  · exact modelCheckFairFNFCrossOfStep_empty_unsat φ sysInit sysStep sysFR
      (EmptinessResult.map_eq_empty h)

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`, whichever route ran. This is the
half that needs `edgeAtom` to be honest about the system: `hsteps` says every atom a step contributes is
one `edgeAtom` marks, which is what makes the prune branch's guard meaningful.

`sysFR` is owed **only if the route falls back**. The prune validates a reported lasso with
`streettCheck_nonEmpty_valid`, which has no finiteness hypothesis, so `modelCheckFairOfStep_nonEmpty_sat`
needs none either; the crossing validates through `TEmptinessChecker.nonEmpty_valid`, whose `FiniteReach`
is a field of the contract. Stating the certificate as a consequence of `pruneApplicable … = false` keeps
this theorem exactly as strong as the prune's on every property the prune decides, which is the common
case; a caller holding an unconditional certificate passes `fun _ => sysFR`. -/
theorem modelCheckFairRoutedOfStep_nonEmpty_sat [LawfulHashable SysState] (edgeAtom : α → Bool)
    (hsteps : ∀ s, ∀ st ∈ LSys.totalize (fun s => (sysStep s).1) s, ∀ a ∈ st.1, edgeAtom a = true)
    (sysFR : pruneApplicable edgeAtom φ = false →
      FiniteReach sysInit (LSys.targets fun s => (sysStep s).1))
    {stem loop : List (SysState × Nat)}
    (h : modelCheckFairRoutedOfStep φ sysInit sysStep edgeAtom = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState,
      (LSys.toSpec (fun s => (sysStep s).1) sysInit (fun s => (sysStep s).2)).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation (fun s => (sysStep s).2) ρ) φ ∧
      (∀ n, (lassoAt stem loop.tail n).map Prod.fst = some (ρ n).1) := by
  rw [modelCheckFairRoutedOfStep] at h
  split at h
  · rename_i hprune
    exact modelCheckFairOfStep_nonEmpty_sat φ sysInit sysStep
      (stateOnly_of_pruneApplicable hsteps hprune) h
  · rename_i hcross
    obtain ⟨stem', loop', hx⟩ := EmptinessResult.map_eq_nonEmpty h
    obtain ⟨ρ, hρ, hviol, hstates⟩ := modelCheckFairFNFCrossOfStep_nonEmpty_sat φ sysInit sysStep
      (sysFR (by simpa using hcross)) hx
    -- the reported lists are the crossing's with the latch bit dropped
    rw [hx] at h
    simp only [EmptinessResult.map, EmptinessResult.nonEmpty.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨ρ, hρ, hviol, fun n => ?_⟩
    rw [← List.map_tail, lassoAt_map, Option.map_map]
    exact hstates n

end FairRouted

end OfStep

end LTLLib
