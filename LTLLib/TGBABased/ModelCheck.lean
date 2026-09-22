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
    (hstate : ∀ ds ∈ (hoistFairness (φ.toNNF false).splitConj).1 ++ (rehoist (hoistFairness (φ.toNNF false).splitConj).2).1,
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

end LTLLib
