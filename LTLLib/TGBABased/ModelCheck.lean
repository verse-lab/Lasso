/-
  One entry point per search mode: `sys ⊨ φ`, or `sys ⊨ (fair → φ)` with the fairness assumption hoisted out of
  the property. Every mode's real logic and both directions of proof live where the mode was developed, this
  file only names each mode and restates its soundness and completeness against that name.

  - `modelCheckNDFS`: Nested DFS (`LTLLib.modelCheck`, single-acceptance-set), no fairness support yet, see the
    note below.
  - `modelCheckDijkstra`: Dijkstra's SCC-based search on the TGBA product (`DijkstraCheck.lean`), no fairness.
  - `modelCheckFairCrossed`: the fairness assumption hoisted and crossed into one check per disjunct
    (`FairRouter.lean`'s `modelCheckUnderFairness`).
  - `modelCheckFairPruned`: the same assumption decided per SCC instead of crossed
    (`FairRouter.lean`'s `modelCheckUnderFairnessPrune`).

  `modelCheckNDFS` cannot sit on the same TGBA product as the other three today, `nestedDFSChecker` is an
  `EmptinessChecker` (one acceptance set) and the other three need a `TEmptinessChecker` (marks per edge), so it
  runs on the older, degeneralized product instead and carries no fairness. TODO: once a dedicated LTL-to-TGBA
  translation replaces the current GBA-then-`toTGBA` route, degeneralize a TGBA to one acceptance set so NDFS can
  run on the same product as the other three, fairness included. See `tmp/MODELCHECK_NOTES.md`.

  Sections:
  - Nested DFS
  - Dijkstra
  - Fairness crossed
  - Fairness pruned
-/
import LTLLib.ModelCheck
import LTLLib.TGBABased.DijkstraCheck
import LTLLib.TGBABased.FairRouter

namespace LTLLib

/-! ## Nested DFS -/

section NDFS

variable {α : Type u} {S : Type w} [FSet (NNF α) S]
  {SysState : Type v} [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [LawfulHashable SysState]
  [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α]

/-- Nested DFS: `sys ⊨ φ`, on the degeneralized single-acceptance-set automaton, no fairness support yet, see
the file header. -/
def modelCheckNDFS (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc) : EmptinessResult (SysState × BAState) :=
  modelCheck (S := S) φ sysInit sysSucc sysLabel sysFR

omit [LawfulHashable SysState] in
/-- An `.empty` result means every real run of `sys` satisfies `φ`. -/
theorem modelCheckNDFS_empty_unsat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc) {n : Nat}
    (h : modelCheckNDFS (S := S) φ sysInit sysSucc sysLabel sysFR = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ :=
  modelCheck_empty_unsat φ sysInit sysSucc sysLabel sysFR nestedDFSChecker h

omit [LawfulHashable SysState] in
/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckNDFS_nonEmpty_sat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc) {stem loop : List (SysState × BAState)}
    (h : modelCheckNDFS (S := S) φ sysInit sysSucc sysLabel sysFR = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ :=
  modelCheck_nonEmpty_sat φ sysInit sysSucc sysLabel sysFR nestedDFSChecker h

end NDFS

/-! ## Dijkstra -/

section Dijkstra

variable {α : Type u} {S : Type w} [FSet (NNF α) S]
  {SysState : Type v} [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [Inhabited SysState]
  [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α]

/-- Dijkstra's SCC-based search on the TGBA product: `sys ⊨ φ`, no fairness. -/
def modelCheckDijkstra (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc) : EmptinessResult (SysState × Nat) :=
  modelCheckTGBA (S := S) φ sysInit sysSucc sysLabel sysFR

/-- An `.empty` result means every real run of `sys` satisfies `φ`. -/
theorem modelCheckDijkstra_empty_unsat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc) {n : Nat}
    (h : modelCheckDijkstra (S := S) φ sysInit sysSucc sysLabel sysFR = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ :=
  modelCheckTGBA_empty_unsat φ sysInit sysSucc sysLabel sysFR dijkstraTChecker h

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckDijkstra_nonEmpty_sat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc) {stem loop : List (SysState × Nat)}
    (h : modelCheckDijkstra (S := S) φ sysInit sysSucc sysLabel sysFR = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ :=
  modelCheckTGBA_nonEmpty_sat φ sysInit sysSucc sysLabel sysFR dijkstraTChecker h

end Dijkstra

/-! ## Fairness crossed -/

section FairCrossed

variable {α : Type u} {S : Type w} [FSet (NNF α) S]
  {SysState : Type v} [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [Inhabited SysState]
  [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α]

/-- The fairness assumption hoisted out of `φ` and crossed into one check per disjunct, `sys ⊨ φ`. -/
def modelCheckFairCrossed (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc) : EmptinessResult ((SysState × Nat) × Bool) :=
  modelCheckUnderFairness (S := S) φ sysInit sysSucc sysLabel sysFR

/-- An `.empty` result means every real run of `sys` satisfies `φ`. -/
theorem modelCheckFairCrossed_empty_unsat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc) {n : Nat}
    (h : modelCheckFairCrossed (S := S) φ sysInit sysSucc sysLabel sysFR = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ :=
  modelCheckUnderFairness_empty_unsat φ sysInit sysSucc sysLabel sysFR dijkstraTChecker
    dijkstraTChecker h

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckFairCrossed_nonEmpty_sat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc) {stem loop : List ((SysState × Nat) × Bool)}
    (h : modelCheckFairCrossed (S := S) φ sysInit sysSucc sysLabel sysFR = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ :=
  modelCheckUnderFairness_nonEmpty_sat φ sysInit sysSucc sysLabel sysFR dijkstraTChecker
    dijkstraTChecker h

end FairCrossed

/-! ## Fairness pruned -/

section FairPruned

variable {α : Type u} {S : Type w} [FSet (NNF α) S]
  {SysState : Type v} [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [Inhabited SysState]
  [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α]

/-- The fairness assumption hoisted out of `φ` and decided per SCC instead of crossed, `sys ⊨ φ`. -/
def modelCheckFairPruned (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α) :
    EmptinessResult (SysState × Nat) :=
  modelCheckUnderFairnessPrune (S := S) φ sysInit sysSucc sysLabel

/-- An `.empty` result means every real run of `sys` satisfies `φ`. -/
theorem modelCheckFairPruned_empty_unsat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc) {n : Nat}
    (h : modelCheckFairPruned (S := S) φ sysInit sysSucc sysLabel = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ :=
  modelCheckUnderFairnessPrune_empty_unsat φ sysInit sysSucc sysLabel sysFR h

/-- A `.nonEmpty` result yields a concrete run of `sys` violating `φ`. -/
theorem modelCheckFairPruned_nonEmpty_sat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    {stem loop : List (SysState × Nat)}
    (h : modelCheckFairPruned (S := S) φ sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ :=
  modelCheckUnderFairnessPrune_nonEmpty_sat φ sysInit sysSucc sysLabel h

end FairPruned

end LTLLib
