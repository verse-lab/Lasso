/-
  Model checking against one fair-normal-form disjunct `FG l ∧ ⋀ⱼ GF lⱼ` with propositional `l` and `lⱼ`. The `GF` parts
  are marks on the product (`FairProduct.lean`) and the `FG` part is a region restriction applied by the latch
  (`AbstractSpec/RegionLatch.lean`), so one call to an unmodified `TEmptinessChecker` decides the disjunct.

  A disjunct for which the system alone admits no run is rejected by `disjunctFeasible`, the same latched check on the
  system graph rather than on the product.

  Defines:
  - `modelCheckTGBADisjunct`: one latched checker call for one disjunct
  - `sysFairMarks`, `disjunctFeasible`: the system-level fail-fast, one latched pass carrying the `GF` parts
  - `modelCheckTGBADisjunctFast`: the same behind the fail-fast

  Proves:
  - `modelCheckTGBADisjunct_empty_unsat`: (Soundness) an `.empty` result rules out every run of `sys` that satisfies the
    disjunct and violates `φ`
  - `modelCheckTGBADisjunct_nonEmpty_sat`: (Completeness) a `.nonEmpty` result yields such a run
  - `modelCheckTGBADisjunctFast_empty_unsat`, `modelCheckTGBADisjunctFast_nonEmpty_sat`: the same two for the fail-fast
    version

  Sections:
  - Region and checker obligations
  - Model checking one disjunct
  - Soundness
  - Completeness
  - Feasibility fail-fast
-/
import LTLLib.TGBABased.AbstractSpec.RegionLatch
import LTLLib.TGBABased.DijkstraCheck
import LTLLib.TGBABased.Fairness.FairProduct

namespace LTLLib

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]

/-! ## Region and checker obligations -/

open TGBAProduct (fgRegion)

section Search

variable [LawfulBEq α] [LawfulHashable α]

/-- Every latched mark is below `numAcceptSets + gfs.length + 1`, the region mark being the last one. -/
theorem modelCheckTGBADisjunct_marksBound (φ : Formula α) (sysLabel : SysState → Std.HashSet α)
    (gfs : List (BoolFormula α)) {tgba : TGBA α} (htg : ltl3ba (φ.toNNF false) = some tgba)
    (p q : (SysState × Nat) × Bool) (m : Nat)
    (hm : m ∈ latchMarks (TGBAProduct.edgeMarksFair tgba sysLabel gfs) (tgba.numAcceptSets + gfs.length) p q) :
    m < tgba.numAcceptSets + gfs.length + 1 :=
  latchMarks_lt (fun _ _ m hm => modelCheckTGBAFair_marksBound φ sysLabel gfs htg _ _ m hm) p q m hm

variable [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [Inhabited SysState]

/-! ## Model checking one disjunct -/

/-- Does `sys` satisfy `φ` on every run that satisfies `◇□fg` and every `□◇ b` for `b` in `gfs`? The `gfs`
become marks and `fg` becomes the latch's region, so neither reaches the translator. -/
def modelCheckTGBADisjunct (φ : Formula α) (fg : BoolFormula α) (gfs : List (BoolFormula α))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool) := dijkstraTChecker) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  match htg : ltl3ba (φ.toNNF false) with
  | some tgba =>
    let region := fgRegion fg sysLabel
    checker.check
      (latchSuccs (TGBAProduct.getSuccessors tgba sysSucc sysLabel) region)
      (latchInit (TGBAProduct.initialStates tgba sysInit) region fg.isTrue)
      (latch_finiteReach region fg.isTrue
        (modelCheckTGBA_finiteReach φ sysInit sysSucc sysLabel sysFR htg))
      (latchMarks (TGBAProduct.edgeMarksFair tgba sysLabel gfs) (tgba.numAcceptSets + gfs.length))
      (tgba.numAcceptSets + gfs.length + 1)
  | none => .empty 0

theorem modelCheckTGBADisjunct_eq (φ : Formula α) (fg : BoolFormula α) (gfs : List (BoolFormula α))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    {tgba : TGBA α} (htg : ltl3ba (φ.toNNF false) = some tgba) :
    modelCheckTGBADisjunct φ fg gfs sysInit sysSucc sysLabel sysFR checker =
      checker.check
        (latchSuccs (TGBAProduct.getSuccessors tgba sysSucc sysLabel) (fgRegion fg sysLabel))
        (latchInit (TGBAProduct.initialStates tgba sysInit) (fgRegion fg sysLabel) fg.isTrue)
        (latch_finiteReach (fgRegion fg sysLabel) fg.isTrue
          (modelCheckTGBA_finiteReach φ sysInit sysSucc sysLabel sysFR htg))
        (latchMarks (TGBAProduct.edgeMarksFair tgba sysLabel gfs) (tgba.numAcceptSets + gfs.length))
        (tgba.numAcceptSets + gfs.length + 1) := by
  unfold modelCheckTGBADisjunct
  split
  next tgba' htg' =>
    obtain rfl : tgba' = tgba := Option.some.inj (htg'.symm.trans htg)
    rfl
  next htg' => exact absurd (htg'.symm.trans htg) (by simp)

/-! ## Soundness -/

/-- An `.empty` result means every run of `sys` satisfying the disjunct satisfies `φ`. -/
theorem modelCheckTGBADisjunct_empty_unsat [DecidableEq α] (φ : Formula α) (fg : BoolFormula α)
    (gfs : List (BoolFormula α)) (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool)) {n : Nat}
    (h : modelCheckTGBADisjunct φ fg gfs sysInit sysSucc sysLabel sysFR checker = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      (BoolFormula.eventuallyAlways fg).satisfies (fun i a => a ∈ sysLabel (τ i)) →
      (∀ b ∈ gfs, (BoolFormula.alwaysEventually b).satisfies (fun i a => a ∈ sysLabel (τ i))) →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  intro τ hτ hfg hgf
  by_contra hviolate
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome (φ.toNNF false))
  rw [modelCheckTGBADisjunct_eq φ fg gfs sysInit sysSucc sysLabel sysFR checker htg] at h
  have hacc0 : tgba.toSpec.accepts (fun i a => a ∈ sysLabel (τ i)) :=
    (ltl3ba_accepts _ htg _).mpr ((Formula.toNNF_correct_neg _ φ).mp hviolate)
  obtain ⟨N, hN⟩ := (TGBAProduct.eventuallyAlways_iff_indexed fg sysLabel τ).mp hfg
  obtain ⟨σ, hproj, hrun, hacc⟩ := TGBAProduct.gsp_correct2Fair _ sysSucc sysLabel sysInit gfs hτ hacc0
    ((TGBAProduct.fair_iff_indexed gfs sysLabel τ).mp hgf)
  subst hproj
  exact checker.empty_no_cycle
    (fun p q m hm => modelCheckTGBADisjunct_marksBound φ sysLabel gfs htg p q m hm) h
    (by
      cases htop : fg.isTrue
      · exact latch_complete
          (latch_finiteReach (fgRegion fg sysLabel) false
            (modelCheckTGBA_finiteReach φ sysInit sysSucc sysLabel sysFR htg))
          hrun.1 (TGBAProduct.acceptingRunFair_step _ sysSucc sysLabel sysInit gfs hrun)
          (N := N) (fun n hn => hN n hn)
          (fun m hm K => TGBAProduct.acceptingRunFair_marks _ sysSucc sysLabel sysInit gfs hrun hacc m hm K)
      · exact latch_complete_total
          (latch_finiteReach (fgRegion fg sysLabel) true
            (modelCheckTGBA_finiteReach φ sysInit sysSucc sysLabel sysFR htg))
          hrun.1 (TGBAProduct.acceptingRunFair_step _ sysSucc sysLabel sysInit gfs hrun)
          (fun p => BoolFormula.eval_of_isTrue htop _)
          (fun m hm K => TGBAProduct.acceptingRunFair_marks _ sysSucc sysLabel sysInit gfs hrun hacc m hm K))

/-! ## Completeness -/

/-- A `.nonEmpty` result yields one run of `sys` that satisfies the disjunct and violates `φ`. -/
theorem modelCheckTGBADisjunct_nonEmpty_sat [DecidableEq α] (φ : Formula α) (fg : BoolFormula α)
    (gfs : List (BoolFormula α)) (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    {stem loop : List ((SysState × Nat) × Bool)}
    (h : modelCheckTGBADisjunct φ fg gfs sysInit sysSucc sysLabel sysFR checker
      = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      (BoolFormula.eventuallyAlways fg).satisfies (fun i a => a ∈ sysLabel (τ i)) ∧
      (∀ b ∈ gfs, (BoolFormula.alwaysEventually b).satisfies (fun i a => a ∈ sysLabel (τ i))) ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome (φ.toNNF false))
  rw [modelCheckTGBADisjunct_eq φ fg gfs sysInit sysSucc sysLabel sysFR checker htg] at h
  obtain ⟨ac, -, -⟩ := checker.nonEmpty_valid
    (fun p q m hm => modelCheckTGBADisjunct_marksBound φ sysLabel gfs htg p q m hm) h
  obtain ⟨τ, hτrun, hlang, hfair, hregion⟩ := TGBAProduct.exists_run_of_TRegionCycle _ sysSucc
    sysLabel sysInit gfs fg (ltl3ba_marks_lt _ htg)
    (latch_sound (fun _ _ m hm => modelCheckTGBAFair_marksBound φ sysLabel gfs htg _ _ m hm) ac)
  refine ⟨τ, hτrun, (TGBAProduct.eventuallyAlways_iff_indexed fg sysLabel τ).mpr hregion,
    (TGBAProduct.fair_iff_indexed gfs sysLabel τ).mpr hfair, fun hsat => ?_⟩
  exact (Formula.toNNF_correct_neg _ φ).mpr ((ltl3ba_accepts _ htg _).mp hlang) hsat

end Search

/-! ## Feasibility fail-fast -/

/-- The `GF` parts as marks on the system graph, read at the edge source exactly as the product reads them. -/
def sysFairMarks (gfs : List (BoolFormula α)) (sysLabel : SysState → Std.HashSet α) :
    SysState → SysState → Std.HashSet Nat :=
  fun s _ => TGBAProduct.fairMarks 0 gfs (sysLabel s)

theorem sysFairMarks_lt (gfs : List (BoolFormula α)) (sysLabel : SysState → Std.HashSet α)
    (s t : SysState) (m : Nat) (hm : m ∈ sysFairMarks gfs sysLabel s t) : m < gfs.length := by
  obtain ⟨i, hi, rfl, -⟩ := (TGBAProduct.mem_fairMarks_iff 0 gfs (sysLabel s) m).mp hm
  omega

section Feasible

variable [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [Inhabited SysState]

/-- Does the system alone admit a run satisfying the disjunct? The same latch as the full check on the system graph,
the region and the `GF` parts read off the system label. -/
def disjunctFeasible (fg : BoolFormula α) (gfs : List (BoolFormula α)) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc)
    (sysChecker : TEmptinessChecker (SysState × Bool) := dijkstraTChecker) : Bool :=
  match sysChecker.check
      (latchSuccs (Product.totalizeSucc sysSucc) (fun s => fg.eval (sysLabel s)))
      (latchInit sysInit (fun s => fg.eval (sysLabel s)) fg.isTrue)
      (latch_finiteReach _ fg.isTrue (Product.finiteReach_totalizeSucc sysInit sysSucc sysFR))
      (latchMarks (sysFairMarks gfs sysLabel) gfs.length) (gfs.length + 1) with
  | .empty _ => false
  | .nonEmpty _ _ => true

variable [LawfulBEq α]

/-- An infeasible disjunct rules out every run of `sys`, whatever the property is. -/
theorem no_run_of_disjunctFeasible_false (fg : BoolFormula α) (gfs : List (BoolFormula α))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (sysChecker : TEmptinessChecker (SysState × Bool))
    (h : disjunctFeasible fg gfs sysInit sysSucc sysLabel sysFR sysChecker = false)
    (τ : Nat → SysState) (hτ : (Sys.toSpec sysSucc sysInit sysLabel).isRun τ)
    (hfg : (BoolFormula.eventuallyAlways fg).satisfies (fun i a => a ∈ sysLabel (τ i)))
    (hgf : ∀ b ∈ gfs, (BoolFormula.alwaysEventually b).satisfies (fun i a => a ∈ sysLabel (τ i))) :
    False := by
  obtain ⟨N, hN⟩ := (TGBAProduct.eventuallyAlways_iff_indexed fg sysLabel τ).mp hfg
  have hindexed := (TGBAProduct.fair_iff_indexed gfs sysLabel τ).mp hgf
  have hmarks : ∀ m, m < gfs.length →
      ∀ K, ∃ n ≥ K, m ∈ sysFairMarks gfs sysLabel (τ n) (τ (n + 1)) := by
    intro m hm K
    obtain ⟨j, hj⟩ := hindexed m hm K
    exact ⟨K + j, by omega,
      (TGBAProduct.mem_fairMarks_iff 0 gfs (sysLabel (τ (K + j))) m).mpr ⟨m, hm, by omega, hj⟩⟩
  obtain ⟨ac, -⟩ : ∃ _ac : TAcceptingCycle
      (latchInit sysInit (fun s => fg.eval (sysLabel s)) fg.isTrue)
      (latchSuccs (Product.totalizeSucc sysSucc) (fun s => fg.eval (sysLabel s)))
      (latchMarks (sysFairMarks gfs sysLabel) gfs.length) (gfs.length + 1), True := by
    cases htop : fg.isTrue
    · exact latch_complete
        (latch_finiteReach (fun s => fg.eval (sysLabel s)) false
          (Product.finiteReach_totalizeSucc sysInit sysSucc sysFR))
        hτ.1 hτ.2 (N := N) hN hmarks
    · exact latch_complete_total
        (latch_finiteReach (fun s => fg.eval (sysLabel s)) true
          (Product.finiteReach_totalizeSucc sysInit sysSucc sysFR))
        hτ.1 hτ.2 (fun s => BoolFormula.eval_of_isTrue htop _) hmarks
  rw [disjunctFeasible] at h
  split at h
  · next hempty =>
    exact sysChecker.empty_no_cycle
      (fun s t m hm => latchMarks_lt (sysFairMarks_lt gfs sysLabel) s t m hm) hempty ⟨ac, trivial⟩
  · exact absurd h (by simp)

variable [LawfulHashable α]

/-- One disjunct behind the fail-fast, which answers `.empty` without touching the product when the disjunct is
infeasible. -/
def modelCheckTGBADisjunctFast (φ : Formula α) (fg : BoolFormula α) (gfs : List (BoolFormula α))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool) := dijkstraTChecker)
    (sysChecker : TEmptinessChecker (SysState × Bool) := dijkstraTChecker) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  if disjunctFeasible fg gfs sysInit sysSucc sysLabel sysFR sysChecker then
    modelCheckTGBADisjunct φ fg gfs sysInit sysSucc sysLabel sysFR checker
  else .empty 0

/-- An `.empty` result means every run of `sys` satisfying the disjunct satisfies `φ`. -/
theorem modelCheckTGBADisjunctFast_empty_unsat [DecidableEq α] (φ : Formula α) (fg : BoolFormula α)
    (gfs : List (BoolFormula α)) (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool)) {n : Nat}
    (h : modelCheckTGBADisjunctFast φ fg gfs sysInit sysSucc sysLabel sysFR checker
      sysChecker = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      (BoolFormula.eventuallyAlways fg).satisfies (fun i a => a ∈ sysLabel (τ i)) →
      (∀ b ∈ gfs, (BoolFormula.alwaysEventually b).satisfies (fun i a => a ∈ sysLabel (τ i))) →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  intro τ hτ hfg hgf
  rw [modelCheckTGBADisjunctFast] at h
  split at h
  · exact modelCheckTGBADisjunct_empty_unsat φ fg gfs sysInit sysSucc sysLabel sysFR
      checker h τ hτ hfg hgf
  · next hfree =>
    exact absurd hgf (fun _ => no_run_of_disjunctFeasible_false fg gfs sysInit sysSucc sysLabel
      sysFR sysChecker (by simpa using hfree) τ hτ hfg hgf)

/-- A `.nonEmpty` result yields one run of `sys` that satisfies the disjunct and violates `φ`. -/
theorem modelCheckTGBADisjunctFast_nonEmpty_sat [DecidableEq α] (φ : Formula α) (fg : BoolFormula α)
    (gfs : List (BoolFormula α)) (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool))
    {stem loop : List ((SysState × Nat) × Bool)}
    (h : modelCheckTGBADisjunctFast φ fg gfs sysInit sysSucc sysLabel sysFR checker
      sysChecker = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      (BoolFormula.eventuallyAlways fg).satisfies (fun i a => a ∈ sysLabel (τ i)) ∧
      (∀ b ∈ gfs, (BoolFormula.alwaysEventually b).satisfies (fun i a => a ∈ sysLabel (τ i))) ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  rw [modelCheckTGBADisjunctFast] at h
  split at h
  · exact modelCheckTGBADisjunct_nonEmpty_sat φ fg gfs sysInit sysSucc sysLabel sysFR
      checker h
  · exact absurd h (by simp)

end Feasible

end LTLLib
