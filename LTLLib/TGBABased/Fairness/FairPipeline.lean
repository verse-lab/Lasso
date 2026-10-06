module

/-
  The fairness routes built on `FairRouter.lean`'s split-level searches (`modelCheckCrossSplit`, `modelCheckPruneSplit`)
  with re-hoisting and disjunctive hoisting. The negated property is split and hoisted as `FairRouter.lean` does, `rehoist`
  (`Rehoist.lean`) runs on what is left, and the final kept property goes to `ltl3ba`.

  Defines:
  - `firstNonEmpty`: decide a list of runs, stopping at the first counterexample
  - `modelCheckUnderFairnessRehoistCross`: hoist, re-hoist, then one latched check per crossed disjunct
  - `modelCheckUnderFairnessRehoistPrune`: hoist, re-hoist, then the hoisted conjuncts decided per SCC
  - `modelCheckUnderFairnessDisjunctiveHoist`: the prune route with disjunctive hoisting, one prune run per combination
    of sides of the kept mixed conjuncts

  Proves:
  - `firstNonEmpty_empty`, `firstNonEmpty_nonEmpty`: what an exhausted and a stopped fold say about the runs
  - `…_empty_unsat` (Soundness) and `…_nonEmpty_sat` (Completeness) for each route: an `.empty` result means every run
    satisfies `φ`, a `.nonEmpty` result yields a run violating `φ`

  Sections:
  - Deciding a list of runs
  - Re-hoisting routes
  - Crossing the sides of mixed conjuncts
-/
public import LTLLib.AbstractSpec.EmptinessCheck
public import LTLLib.LTL.FairNormalForm
public import LTLLib.LTL.Propositional
public import LTLLib.LTL.Semantics
public import LTLLib.Product
public import LTLLib.TGBABased.AbstractSpec.StreettSCC
public import LTLLib.TGBABased.Fairness.DisjunctiveHoist
public import LTLLib.TGBABased.Fairness.FairProduct
public import LTLLib.TGBABased.Fairness.FairRouter
public import LTLLib.TGBABased.Fairness.Rehoist
public import LTLLib.TGBABased.LTLtoTGBA.Pipeline
public import LTLLib.TGBABased.Product
public import LTLLib.TGBABased.SCC.StreettPrune

public section

namespace LTLLib

variable {α : Type u} {SysState : Type v} [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
  [Inhabited SysState] [BEq α] [Hashable α]

/-! ## Deciding a list of runs -/

section FirstNonEmpty

variable {β : Type w} {P : Type w'}

/-- Decide every item, stopping at the first counterexample, and sum the explored-state counts of an exhausted list. -/
def firstNonEmpty (f : β → EmptinessResult P) : List β → EmptinessResult P
  | [] => .empty 0
  | b :: bs =>
    match f b with
    | .nonEmpty stem loop => .nonEmpty stem loop
    | .empty n =>
      match firstNonEmpty f bs with
      | .nonEmpty stem loop => .nonEmpty stem loop
      | .empty m => .empty (n + m)

theorem firstNonEmpty_empty {f : β → EmptinessResult P} :
    ∀ {bs : List β} {n : Nat}, firstNonEmpty f bs = .empty n → ∀ b ∈ bs, ∃ m, f b = .empty m := by
  intro bs
  induction bs with
  | nil => simp
  | cons b bs ih =>
    intro n h e he
    rw [firstNonEmpty] at h
    split at h
    · simp at h
    · next n' hfb =>
      split at h
      · simp at h
      · next m hrec =>
        rcases List.mem_cons.mp he with rfl | hm
        · exact ⟨n', hfb⟩
        · exact ih hrec e hm

theorem firstNonEmpty_nonEmpty {f : β → EmptinessResult P} :
    ∀ {bs : List β} {stem loop : List P},
      firstNonEmpty f bs = .nonEmpty stem loop → ∃ b ∈ bs, f b = .nonEmpty stem loop := by
  intro bs
  induction bs with
  | nil => simp [firstNonEmpty]
  | cons b bs ih =>
    intro stem loop h
    rw [firstNonEmpty] at h
    split at h
    · next s l hfb =>
      cases h
      exact ⟨b, by simp, hfb⟩
    · next n' hfb =>
      split at h
      · next s l hrec =>
        cases h
        obtain ⟨e, he, hfe⟩ := ih hrec
        exact ⟨e, by simp [he], hfe⟩
      · simp at h

end FirstNonEmpty

variable [DecidableEq α]

/-! ## Re-hoisting routes -/

/-- Does `sys` satisfy `φ` on every run? The negated property is split and hoisted exactly as
`modelCheckUnderFairnessPrune`, `rehoist` runs on what is left before it reaches `ltl3ba`. -/
@[expose] def modelCheckUnderFairnessRehoistPrune (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) : EmptinessResult (SysState × Nat) :=
  let split := hoistFairness (φ.toNNF false).splitConj
  let rehoisted := rehoist split.2
  modelCheckPruneSplit (keptProperty rehoisted.2) (split.1 ++ rehoisted.1) sysInit sysSucc sysLabel

section Correctness

variable [LawfulBEq α] [LawfulHashable α]

/-- Soundness: an `.empty` result means every run of `sys` satisfies `φ`. -/
theorem modelCheckUnderFairnessRehoistPrune_empty_unsat [LawfulHashable SysState] (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    {n : Nat} (h : modelCheckUnderFairnessRehoistPrune φ sysInit sysSucc sysLabel = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  intro ρ hρ
  by_contra hviol
  obtain ⟨hdss, hkept⟩ :=
    (hoistFairness_correct (LSys.valuation sysLabel ρ) (φ.toNNF false).splitConj).mp
      ((NNF.satisfies_splitConj _ _).mp ((Formula.toNNF_correct_neg _ φ).mp hviol))
  obtain ⟨hdss', hkept'⟩ := (rehoist_correct _ _).mp hkept
  exact (directSatisfies_keptProperty _ _).mp
    (modelCheckPruneSplit_empty_unsat _ _ sysInit sysSucc sysLabel sysFR h ρ hρ
      fun ds hds => (List.mem_append.mp hds).elim (hdss ds) (hdss' ds)) hkept'

/-- Completeness: a `.nonEmpty` result yields one run of `sys` that violates `φ`. -/
theorem modelCheckUnderFairnessRehoistPrune_nonEmpty_sat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α)
    (hstate : ∀ ds ∈ (hoistFairness (φ.toNNF false).splitConj).1 ++
        (rehoist (hoistFairness (φ.toNNF false).splitConj).2).1,
      ∀ d ∈ ds, LSys.StateOnly sysSucc sysLabel d.1.eval)
    {stem loop : List (SysState × Nat)}
    (h : modelCheckUnderFairnessRehoistPrune φ sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  obtain ⟨ρ, hτ, hdss, hviol⟩ :=
    modelCheckPruneSplit_nonEmpty_sat _ _ sysInit sysSucc sysLabel hstate h
  -- the violated goal is the kept conjuncts negated, so they all hold on this run
  have hkept := Classical.not_not.mp (fun hno => hviol ((directSatisfies_keptProperty _ _).mpr hno))
  refine ⟨ρ, hτ, (Formula.toNNF_correct_neg _ φ).mpr ((NNF.satisfies_splitConj _ _).mpr
    ((hoistFairness_correct _ (φ.toNNF false).splitConj).mpr
      ⟨fun ds hds => hdss ds (List.mem_append_left _ hds), (rehoist_correct _ _).mpr
        ⟨fun ds hds => hdss ds (List.mem_append_right _ hds), hkept⟩⟩))⟩

end Correctness

/-- The crossing on the same split as `modelCheckUnderFairnessRehoistPrune`: hoisted, re-hoisted, and then one
latched check per crossed disjunct instead of the prune.

Reads a *labelled* system, so a hoisted fairness may mention an edge atom. A system with no edge atoms is
passed as `LSys.unlabelled sysSucc`. -/
@[expose] def modelCheckUnderFairnessRehoistCross (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool) := dijkstraTChecker)
    (sysChecker : TEmptinessChecker (SysState × Bool) := dijkstraTChecker) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  let split := hoistFairness (φ.toNNF false).splitConj
  let rehoisted := rehoist split.2
  modelCheckCrossSplit (keptProperty rehoisted.2) (split.1 ++ rehoisted.1) sysInit sysSucc sysLabel checker
    sysChecker

/-- `modelCheckUnderFairnessRehoistCross` over one system callback. -/
@[expose] def modelCheckUnderFairnessRehoistCrossOfStep (φ : Formula α)
    (sysInit : List SysState) (sysStep : LSys.StepFn α SysState)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool) := dijkstraTChecker)
    (sysChecker : TEmptinessChecker (SysState × Bool) := dijkstraTChecker) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  let split := hoistFairness (φ.toNNF false).splitConj
  let rehoisted := rehoist split.2
  modelCheckCrossSplitOfStep (keptProperty rehoisted.2) (split.1 ++ rehoisted.1) sysInit sysStep
    checker sysChecker

theorem modelCheckUnderFairnessRehoistCrossOfStep_eq (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool)) :
    modelCheckUnderFairnessRehoistCrossOfStep φ sysInit (fun s => (sysSucc s, sysLabel s)) checker sysChecker
      = modelCheckUnderFairnessRehoistCross φ sysInit sysSucc sysLabel checker sysChecker :=
  rfl

section Correctness

variable [LawfulBEq α] [LawfulHashable α]

/-- Soundness of the re-hoisting crossing: an `.empty` result means every run of `sys` satisfies `φ`. -/
theorem modelCheckUnderFairnessRehoistCross_empty_unsat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    (checker : TEmptinessChecker ((SysState × Nat) × Bool)) (sysChecker : TEmptinessChecker (SysState × Bool))
    {n : Nat} (h : modelCheckUnderFairnessRehoistCross φ sysInit sysSucc sysLabel checker sysChecker = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  intro ρ hρ
  by_contra hviol
  obtain ⟨hdss, hkept⟩ :=
    (hoistFairness_correct (LSys.valuation sysLabel ρ) (φ.toNNF false).splitConj).mp
      ((NNF.satisfies_splitConj _ _).mp ((Formula.toNNF_correct_neg _ φ).mp hviol))
  obtain ⟨hdss', hkept'⟩ := (rehoist_correct _ _).mp hkept
  exact (directSatisfies_keptProperty _ _).mp
    (modelCheckCrossSplit_empty_unsat _ _ sysInit sysSucc sysLabel sysFR checker sysChecker h ρ hρ
      fun ds hds => (List.mem_append.mp hds).elim (hdss ds) (hdss' ds)) hkept'

/-- Completeness of the re-hoisting crossing: a `.nonEmpty` result yields one run of `sys` that violates `φ`. -/
theorem modelCheckUnderFairnessRehoistCross_nonEmpty_sat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    (checker : TEmptinessChecker ((SysState × Nat) × Bool)) (sysChecker : TEmptinessChecker (SysState × Bool))
    {stem loop : List ((SysState × Nat) × Bool)}
    (h : modelCheckUnderFairnessRehoistCross φ sysInit sysSucc sysLabel checker sysChecker
      = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  obtain ⟨ρ, hρ, hdss, hviol⟩ :=
    modelCheckCrossSplit_nonEmpty_sat _ _ sysInit sysSucc sysLabel sysFR checker sysChecker h
  have hkept := Classical.not_not.mp (fun hno => hviol ((directSatisfies_keptProperty _ _).mpr hno))
  refine ⟨ρ, hρ, (Formula.toNNF_correct_neg _ φ).mpr ((NNF.satisfies_splitConj _ _).mpr
    ((hoistFairness_correct _ (φ.toNNF false).splitConj).mpr
      ⟨fun ds hds => hdss ds (List.mem_append_left _ hds), (rehoist_correct _ _).mpr
        ⟨fun ds hds => hdss ds (List.mem_append_right _ hds), hkept⟩⟩))⟩

end Correctness

/-! ## Crossing the sides of mixed conjuncts -/

/-- `modelCheckUnderFairnessRehoistPrune` with disjunctive hoisting: every combination of sides of the kept mixed
conjuncts (`branches`) is one prune run, and the first counterexample of any run is the answer. -/
@[expose] def modelCheckUnderFairnessDisjunctiveHoist (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) : EmptinessResult (SysState × Nat) :=
  let split := hoistFairness (φ.toNNF false).splitConj
  let rehoisted := rehoist split.2
  firstNonEmpty (fun b => modelCheckPruneSplit (keptProperty b.2) (split.1 ++ rehoisted.1 ++ b.1)
    sysInit sysSucc sysLabel) (branches rehoisted.2)

section Correctness

variable [LawfulBEq α] [LawfulHashable α]

/-- Soundness: an `.empty` result means every run of `sys` satisfies `φ`. -/
theorem modelCheckUnderFairnessDisjunctiveHoist_empty_unsat [LawfulHashable SysState] (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    {n : Nat} (h : modelCheckUnderFairnessDisjunctiveHoist φ sysInit sysSucc sysLabel = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  intro ρ hτ
  by_contra hviol
  obtain ⟨hdss, hkept⟩ :=
    (hoistFairness_correct (LSys.valuation sysLabel ρ) (φ.toNNF false).splitConj).mp
      ((NNF.satisfies_splitConj _ _).mp ((Formula.toNNF_correct_neg _ φ).mp hviol))
  obtain ⟨hdss', hkept'⟩ := (rehoist_correct _ _).mp hkept
  obtain ⟨b, hb, hbds, hbkept⟩ := (branches_correct _ _).mp hkept'
  obtain ⟨m, hm⟩ := firstNonEmpty_empty h b hb
  exact (directSatisfies_keptProperty _ _).mp
    (modelCheckPruneSplit_empty_unsat _ _ sysInit sysSucc sysLabel sysFR hm ρ hτ fun ds hds => by
      rcases List.mem_append.mp hds with hds | hds
      · exact (List.mem_append.mp hds).elim (hdss ds) (hdss' ds)
      · exact hbds ds hds) hbkept

/-- Completeness: a `.nonEmpty` result yields one run of `sys` that violates `φ`. -/
theorem modelCheckUnderFairnessDisjunctiveHoist_nonEmpty_sat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α)
    -- Quantified over every branch, since which one reports is not known until the search runs.
    -- Disjunctive hoisting *adds* options after the first split, so the hypothesis is stated against
    -- the regions each branch actually hands the prune — `EdgeLabels.md` §12.6 step 6, §17.
    (hstate : ∀ b ∈ branches (rehoist (hoistFairness (φ.toNNF false).splitConj).2).2,
      ∀ ds ∈ (hoistFairness (φ.toNNF false).splitConj).1 ++
          (rehoist (hoistFairness (φ.toNNF false).splitConj).2).1 ++ b.1,
      ∀ d ∈ ds, LSys.StateOnly sysSucc sysLabel d.1.eval)
    {stem loop : List (SysState × Nat)}
    (h : modelCheckUnderFairnessDisjunctiveHoist φ sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  obtain ⟨b, hb, hfb⟩ := firstNonEmpty_nonEmpty h
  obtain ⟨τ, hτ, hdss, hviol⟩ :=
    modelCheckPruneSplit_nonEmpty_sat _ _ sysInit sysSucc sysLabel (hstate b hb) hfb
  -- the violated goal is the branch's kept conjuncts negated, so they all hold on this run
  have hkept := Classical.not_not.mp (fun hno => hviol ((directSatisfies_keptProperty _ _).mpr hno))
  have hkept' := (branches_correct _ _).mpr
    ⟨b, hb, fun ds hds => hdss ds (List.mem_append_right _ hds), hkept⟩
  refine ⟨τ, hτ, (Formula.toNNF_correct_neg _ φ).mpr ((NNF.satisfies_splitConj _ _).mpr
    ((hoistFairness_correct _ (φ.toNNF false).splitConj).mpr
      ⟨fun ds hds => hdss ds (List.mem_append_left _ (List.mem_append_left _ hds)), (rehoist_correct _ _).mpr
        ⟨fun ds hds => hdss ds (List.mem_append_left _ (List.mem_append_right _ hds)), hkept'⟩⟩))⟩

end Correctness

/-! ## The same pipelines, from one system callback

`LSys.StepFn` in place of the `sysSucc`/`sysLabel` pair, so the product computes a state's transitions
once. Each body is the two-callback one with the pair replaced, so each bridge is `rfl` and no soundness
theorem above is restated — the fused entry points in `ModelCheck.lean` derive theirs by rewriting.
`EdgeLabels.md` §15. -/

@[expose] def modelCheckUnderFairnessRehoistPruneOfStep (φ : Formula α)
    (sysInit : List SysState) (sysStep : LSys.StepFn α SysState) :
    EmptinessResult (SysState × Nat) :=
  let split := hoistFairness (φ.toNNF false).splitConj
  let rehoisted := rehoist split.2
  modelCheckPruneSplitOfStep (keptProperty rehoisted.2) (split.1 ++ rehoisted.1) sysInit sysStep

theorem modelCheckUnderFairnessRehoistPruneOfStep_eq (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α) :
    modelCheckUnderFairnessRehoistPruneOfStep φ sysInit (fun s => (sysSucc s, sysLabel s))
      = modelCheckUnderFairnessRehoistPrune φ sysInit sysSucc sysLabel := rfl

@[expose] def modelCheckUnderFairnessDisjunctiveHoistOfStep (φ : Formula α)
    (sysInit : List SysState) (sysStep : LSys.StepFn α SysState) :
    EmptinessResult (SysState × Nat) :=
  let split := hoistFairness (φ.toNNF false).splitConj
  let rehoisted := rehoist split.2
  firstNonEmpty (fun b => modelCheckPruneSplitOfStep (keptProperty b.2)
    (split.1 ++ rehoisted.1 ++ b.1) sysInit sysStep) (branches rehoisted.2)

theorem modelCheckUnderFairnessDisjunctiveHoistOfStep_eq (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α) :
    modelCheckUnderFairnessDisjunctiveHoistOfStep φ sysInit (fun s => (sysSucc s, sysLabel s))
      = modelCheckUnderFairnessDisjunctiveHoist φ sysInit sysSucc sysLabel := rfl

end LTLLib
