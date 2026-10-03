module

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
  - Model checking one disjunct
  - Region and checker obligations
  - Soundness
  - Completeness
  - Feasibility fail-fast
  - The same crossing, from one system callback
-/
public import LTLLib.TGBABased.AbstractSpec.RegionLatch
public import LTLLib.TGBABased.DijkstraCheck
public import LTLLib.TGBABased.Fairness.FairProduct

public section

namespace LTLLib

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]

section Search

variable [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [Inhabited SysState]

/-! ## Model checking one disjunct -/

/-- Does `sys` satisfy `φ` on every run that satisfies `◇□fg` and every `□◇ b` for `b` in `gfs`? The `gfs`
become marks and `fg` becomes the latch's region, so neither reaches the translator.

The system is *labelled* (`TGBABased/LabelledSys.lean`): both the marks and the region are read off the
letter each step contributes, so a hoisted `◇□ψ` or `□◇ψ` may mention an edge atom such as `taken(a)`. A
system with no edge atoms is passed as `LSys.unlabelled sysSucc`. -/
@[expose] def modelCheckTGBADisjunct (φ : Formula α) (fg : BoolFormula α) (gfs : List (BoolFormula α))
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool) := dijkstraTChecker) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  match ltl3ba (φ.toNNF false) with
  | some tgba =>
    checker.check
      (latchSuccs (TGBAProduct.getSuccessors tgba sysSucc sysLabel)
        (TGBAProduct.keptSuccs tgba sysSucc sysLabel fg.eval))
      (latchInit (TGBAProduct.initialStates tgba sysInit) fg.isTrue)
      (latchMarks (TGBAProduct.edgeMarksFair tgba sysSucc sysLabel gfs)
        (TGBAProduct.keptEdgeMarksFair tgba sysSucc sysLabel fg.eval gfs)
        (tgba.numAcceptSets + gfs.length))
      (latchExpand (TGBAProduct.expandFair tgba sysSucc sysLabel gfs)
        (TGBAProduct.keptExpandFair tgba sysSucc sysLabel fg.eval gfs)
        (tgba.numAcceptSets + gfs.length))
      (tgba.numAcceptSets + gfs.length + 1)
  | none => .empty 0

/-- `modelCheckTGBADisjunct` over one system callback. -/
@[expose] def modelCheckTGBADisjunctOfStep (φ : Formula α) (fg : BoolFormula α) (gfs : List (BoolFormula α))
    (sysInit : List SysState) (sysStep : LSys.StepFn α SysState)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool) := dijkstraTChecker) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  match ltl3ba (φ.toNNF false) with
  | some tgba =>
    checker.check
      (latchSuccs (TGBAProduct.getSuccessorsOfStep tgba sysStep)
        (TGBAProduct.keptSuccsOfStep tgba sysStep fg.eval))
      (latchInit (TGBAProduct.initialStates tgba sysInit) fg.isTrue)
      (latchMarks (TGBAProduct.edgeMarksFairOfStep tgba sysStep gfs)
        (TGBAProduct.keptEdgeMarksFairOfStep tgba sysStep fg.eval gfs)
        (tgba.numAcceptSets + gfs.length))
      (latchExpand (TGBAProduct.expandFairOfStep tgba sysStep gfs)
        (TGBAProduct.keptExpandFairOfStep tgba sysStep fg.eval gfs)
        (tgba.numAcceptSets + gfs.length))
      (tgba.numAcceptSets + gfs.length + 1)
  | none => .empty 0

theorem modelCheckTGBADisjunctOfStep_eq (φ : Formula α) (fg : BoolFormula α)
    (gfs : List (BoolFormula α)) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool)) :
    modelCheckTGBADisjunctOfStep φ fg gfs sysInit (fun s => (sysSucc s, sysLabel s)) checker
      = modelCheckTGBADisjunct φ fg gfs sysInit sysSucc sysLabel checker := rfl

theorem modelCheckTGBADisjunct_eq (φ : Formula α) (fg : BoolFormula α) (gfs : List (BoolFormula α))
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    {tgba : TGBA α} (htg : ltl3ba (φ.toNNF false) = some tgba) :
    modelCheckTGBADisjunct φ fg gfs sysInit sysSucc sysLabel checker =
      checker.check
      (latchSuccs (TGBAProduct.getSuccessors tgba sysSucc sysLabel)
          (TGBAProduct.keptSuccs tgba sysSucc sysLabel fg.eval))
        (latchInit (TGBAProduct.initialStates tgba sysInit) fg.isTrue)
        (latchMarks (TGBAProduct.edgeMarksFair tgba sysSucc sysLabel gfs)
          (TGBAProduct.keptEdgeMarksFair tgba sysSucc sysLabel fg.eval gfs)
          (tgba.numAcceptSets + gfs.length))
        (latchExpand (TGBAProduct.expandFair tgba sysSucc sysLabel gfs)
          (TGBAProduct.keptExpandFair tgba sysSucc sysLabel fg.eval gfs)
          (tgba.numAcceptSets + gfs.length))
        (tgba.numAcceptSets + gfs.length + 1) := by
  unfold modelCheckTGBADisjunct
  split
  next tgba' htg' =>
    obtain rfl : tgba' = tgba := Option.some.inj (htg'.symm.trans htg)
    rfl
  next htg' => exact absurd (htg'.symm.trans htg) (by simp)

end Search

/-! ## Region and checker obligations -/

-- The `FG` conjunct enters as a *letter* restriction `fg.eval`, not as a state predicate: the latch's
-- restricted graph keeps a step exactly when the letter it reads satisfies `fg`. For a state-labelled
-- system the letter is the source state's label, so this is the old state region (`keptSteps_unlabelled`);
-- for a labelled system it also constrains edge atoms, which is what lets `◇□ψ` mention `taken(a)`.

section Correctness

variable [LawfulBEq α] [LawfulHashable α]

/-- Every latched mark is below `numAcceptSets + gfs.length + 1`, the region mark being the last one. -/
theorem modelCheckTGBADisjunct_marksBound [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (φ : Formula α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (gfs : List (BoolFormula α)) {tgba : TGBA α} (htg : ltl3ba (φ.toNNF false) = some tgba)
    (p q : (SysState × Nat) × Bool) (m : Nat)
    (keep : Std.HashSet α → Bool)
    (hm : m ∈ latchMarks (TGBAProduct.edgeMarksFair tgba sysSucc sysLabel gfs)
      (TGBAProduct.keptEdgeMarksFair tgba sysSucc sysLabel keep gfs)
      (tgba.numAcceptSets + gfs.length) p q) :
    m < tgba.numAcceptSets + gfs.length + 1 :=
  latchMarks_lt
    (fun _ _ m hm => modelCheckTGBAFair_marksBound φ sysSucc sysLabel gfs htg _ _ m hm)
    (fun _ _ m hm => TGBAProduct.keptEdgeMarksFair_lt tgba sysSucc sysLabel
      (ltl3ba_marks_lt _ htg) keep gfs _ _ m hm) p q m hm

variable [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [Inhabited SysState]

/-! ## Soundness -/

set_option maxHeartbeats 1000000 in
/-- An `.empty` result means every run of `sys` satisfying the disjunct satisfies `φ`. -/
theorem modelCheckTGBADisjunct_empty_unsat [DecidableEq α] (φ : Formula α) (fg : BoolFormula α)
    (gfs : List (BoolFormula α)) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    (checker : TEmptinessChecker ((SysState × Nat) × Bool)) {n : Nat}
    (h : modelCheckTGBADisjunct φ fg gfs sysInit sysSucc sysLabel checker = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      (BoolFormula.eventuallyAlways fg).satisfies (LSys.valuation sysLabel ρ) →
      (∀ b ∈ gfs, (BoolFormula.alwaysEventually b).satisfies (LSys.valuation sysLabel ρ)) →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  intro ρ hρ hfg hgf
  by_contra hviolate
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome (φ.toNNF false))
  rw [modelCheckTGBADisjunct_eq φ fg gfs sysInit sysSucc sysLabel checker htg] at h
  have hacc0 : tgba.toSpec.accepts (LSys.valuation sysLabel ρ) :=
    (ltl3ba_accepts _ htg _).mpr ((Formula.toNNF_correct_neg _ φ).mp hviolate)
  obtain ⟨N, hN⟩ := (TGBAProduct.eventuallyAlways_iff_indexed_run fg sysLabel ρ).mp hfg
  obtain ⟨σ, hproj, hrun, hacc⟩ := TGBAProduct.gsp_correct2Fair _ sysSucc sysLabel sysInit gfs hρ
    hacc0 ((TGBAProduct.fair_iff_indexed_run gfs sysLabel ρ).mp hgf)
  -- the projection is onto the labelled run, so read the region hypothesis through it: past `N` the run's
  -- own step reads a letter `fg` admits, which is what the restricted graph and marks are built from
  have hρσ : ∀ n, ρ n = ((σ n).1, (σ n).2.1) := fun n => congrFun hproj n
  have hN' : ∀ n, N ≤ n → fg.eval (LSys.letter (sysLabel (σ n).1) (σ n).2.1.1) = true := by
    intro n hn
    have h := hN n hn
    rwa [hρσ n] at h
  have hstep := TGBAProduct.acceptingRunFair_step _ sysSucc sysLabel sysInit gfs hrun
  have hfrbase := modelCheckTGBA_finiteReach φ sysInit sysSucc sysLabel sysFR htg
  -- Hoisted with an explicit type: leaving the latch's two graphs and two mark functions to be
  -- recovered by unification from `empty_no_cycle`'s argument blows the elaboration budget.
  have hac : ∃ _ac : TAcceptingCycle
      (latchInit (TGBAProduct.initialStates tgba sysInit) fg.isTrue)
      (latchSuccs (TGBAProduct.getSuccessors tgba sysSucc sysLabel)
        (TGBAProduct.keptSuccs tgba sysSucc sysLabel fg.eval))
      (latchMarks (TGBAProduct.edgeMarksFair tgba sysSucc sysLabel gfs)
        (TGBAProduct.keptEdgeMarksFair tgba sysSucc sysLabel fg.eval gfs)
        (tgba.numAcceptSets + gfs.length))
      (tgba.numAcceptSets + gfs.length + 1), True := by
    cases htop : fg.isTrue
    · refine latch_complete
        (latch_finiteReach
          (TGBAProduct.keptSuccs_sub tgba sysSucc sysLabel fg.eval) false hfrbase)
        hrun.1 hstep (N := N) (fun n hn => ?_) (fun m hm K => ?_)
      · exact TGBAProduct.acceptingRunFair_keptStep tgba sysSucc sysLabel sysInit gfs hrun
          fg.eval n (hN' n hn)
      · exact TGBAProduct.acceptingRunFair_keptMarks tgba sysSucc sysLabel sysInit gfs hrun hacc
          fg.eval hN' m hm K
    · -- `latch_complete_total` reads the run off `hregion` alone, so name it before `hinit`
      have htot : ∀ n, fg.eval (LSys.letter (sysLabel (σ n).1) (σ n).2.1.1) = true :=
        fun n => BoolFormula.eval_of_isTrue htop _
      refine latch_complete_total (σ := fun n => ((σ n).1, (σ n).2.2.1))
        (latch_finiteReach
          (TGBAProduct.keptSuccs_sub tgba sysSucc sysLabel fg.eval) true hfrbase)
        hrun.1 (fun n => ?_) (fun m hm K => ?_)
      · exact TGBAProduct.acceptingRunFair_keptStep tgba sysSucc sysLabel sysInit gfs hrun
          fg.eval n (htot n)
      · obtain ⟨k, hkK, -, hmm⟩ := TGBAProduct.acceptingRunFair_keptMarks tgba sysSucc sysLabel
          sysInit gfs hrun hacc fg.eval (N := 0) (fun n _ => htot n) m hm K
        exact ⟨k, hkK, hmm⟩
  exact checker.empty_no_cycle
    (latch_finiteReach (TGBAProduct.keptSuccs_sub tgba sysSucc sysLabel fg.eval) fg.isTrue hfrbase)
    (latchExpand_coherent (TGBAProduct.expandFair_coherent tgba sysSucc sysLabel gfs)
      (TGBAProduct.keptExpandFair_coherent tgba sysSucc sysLabel fg.eval gfs)
      (tgba.numAcceptSets + gfs.length))
    (fun p q m hm =>
      modelCheckTGBADisjunct_marksBound φ sysSucc sysLabel gfs htg p q m fg.eval hm)
    h hac

/-! ## Completeness -/

set_option maxHeartbeats 1000000 in
/-- A `.nonEmpty` result yields one run of `sys` that satisfies the disjunct and violates `φ`. -/
theorem modelCheckTGBADisjunct_nonEmpty_sat [DecidableEq α] (φ : Formula α) (fg : BoolFormula α)
    (gfs : List (BoolFormula α)) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    {stem loop : List ((SysState × Nat) × Bool)}
    (h : modelCheckTGBADisjunct φ fg gfs sysInit sysSucc sysLabel checker
      = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      (BoolFormula.eventuallyAlways fg).satisfies (LSys.valuation sysLabel ρ) ∧
      (∀ b ∈ gfs, (BoolFormula.alwaysEventually b).satisfies (LSys.valuation sysLabel ρ)) ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome (φ.toNNF false))
  rw [modelCheckTGBADisjunct_eq φ fg gfs sysInit sysSucc sysLabel checker htg] at h
  obtain ⟨ac, -, -⟩ := checker.nonEmpty_valid
    (latch_finiteReach (TGBAProduct.keptSuccs_sub tgba sysSucc sysLabel fg.eval) fg.isTrue
      (modelCheckTGBA_finiteReach φ sysInit sysSucc sysLabel sysFR htg))
    (latchExpand_coherent (TGBAProduct.expandFair_coherent tgba sysSucc sysLabel gfs)
      (TGBAProduct.keptExpandFair_coherent tgba sysSucc sysLabel fg.eval gfs)
      (tgba.numAcceptSets + gfs.length))
    (fun p q m hm =>
      modelCheckTGBADisjunct_marksBound φ sysSucc sysLabel gfs htg p q m fg.eval hm) h
  obtain ⟨ρ, hρrun, hlang, hfair, hregion⟩ := TGBAProduct.exists_run_of_TRegionCycle _
    sysSucc sysLabel sysInit gfs fg.eval (ltl3ba_marks_lt _ htg)
    (latch_sound (TGBAProduct.keptSuccs_sub tgba sysSucc sysLabel fg.eval)
      (fun _ _ m hm =>
        modelCheckTGBAFair_marksBound φ sysSucc sysLabel gfs htg _ _ m hm)
      (fun _ _ m hm => TGBAProduct.keptEdgeMarksFair_lt tgba sysSucc sysLabel
        (ltl3ba_marks_lt _ htg) fg.eval gfs _ _ m hm) ac)
  -- both halves of the disjunct are already stated on the letters the run reads, which is its valuation
  exact ⟨ρ, hρrun, (TGBAProduct.eventuallyAlways_iff_indexed_run fg sysLabel ρ).mpr hregion,
    (TGBAProduct.fair_iff_indexed_run gfs sysLabel ρ).mpr hfair,
    fun hsat => (Formula.toNNF_correct_neg _ φ).mpr ((ltl3ba_accepts _ htg _).mp hlang) hsat⟩

end Correctness

/-! ## Feasibility fail-fast

The system-level pre-pass runs the same latch on the system graph. Its obligation runs the *other way* from
the product's: `disjunctFeasible` is only ever allowed to reject, so it must not lose a run, and a coarser
graph or a coarser mark set can only keep more. That is why both may be over-approximated across the steps
realizing a system edge — the opposite of the region rule in `EdgeLabels.md` §6.3, where the answer has to
be exact and over-approximating a region is unsound. -/

/-- The `GF` parts as marks on the system graph: conjunct `i` marks every edge out of `s` as soon as *some*
step out of `s` reads a letter satisfying it. Depending only on the source is what keeps `sysFairExpand`
at one computation per state, and over-approximating across an edge's realizations is sound here (see the
section note). -/
@[expose] def sysFairMarks (gfs : List (BoolFormula α)) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) : SysState → SysState → Std.HashSet Nat :=
  fun s _ =>
    -- PERF: `steps` and `base` are hoisted out of the conjunct loop deliberately. Written inline they are
    -- recomputed once per conjunct, and `sysSucc` is a `tr` call on the Veil side. This was one of three
    -- causes that together made the fail-fast 2.2x slower than the state-labelled one on
    -- `MCDijkstraPerf`'s `p4`; see `EdgeLabels.md` §11 item 2 for the other two and the measurements.
    let steps := LSys.totalize sysSucc s
    let base := sysLabel s
    Std.HashSet.ofList ((List.range gfs.length).filter fun i =>
      steps.any fun st => (TGBAProduct.fairConj gfs i).eval (LSys.letter base st.1))

theorem mem_sysFairMarks_iff (gfs : List (BoolFormula α))
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (s t : SysState) (m : Nat) :
    m ∈ sysFairMarks gfs sysSucc sysLabel s t ↔
      m < gfs.length ∧ ∃ st ∈ LSys.totalize sysSucc s,
        (TGBAProduct.fairConj gfs m).eval (LSys.letter (sysLabel s) st.1) = true := by
  simp only [sysFairMarks, Std.HashSet.mem_ofList, List.contains_iff_mem, List.mem_filter,
    List.mem_range, Array.any_eq_true, Array.mem_iff_getElem]
  constructor
  · rintro ⟨hm, i, hi, hev⟩
    exact ⟨hm, _, ⟨i, hi, rfl⟩, hev⟩
  · rintro ⟨hm, st, ⟨i, hi, rfl⟩, hev⟩
    exact ⟨hm, i, hi, hev⟩

theorem sysFairMarks_lt (gfs : List (BoolFormula α))
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (s t : SysState) (m : Nat) (hm : m ∈ sysFairMarks gfs sysSucc sysLabel s t) : m < gfs.length :=
  ((mem_sysFairMarks_iff gfs sysSucc sysLabel s t m).mp hm).1

section Feasible

variable [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [Inhabited SysState]

/-- The fused expansion for the system-level feasibility latch.

PERF: one pass over `s`'s steps serves the targets *and* every outgoing edge's marks, which is why the
body is written out rather than calling `LSys.targets` and `sysFairMarks`. A labelled system's graph is
*derived* from its step list, so anything wanting both pays two derivations unless they are shared here,
and on the Veil side each derivation is a `tr` call — the dominant cost. Sharing them is what keeps this
fail-fast close to what the state-labelled one cost; the price is that `ExpandCoherent` no longer holds by
`rfl`, since `LSys.targets (LSys.totalize …)` and `Product.totalizeSucc (LSys.targets …)` agree only
propositionally (`LSys.targets_totalize`). -/
@[expose] def sysFairExpand (gfs : List (BoolFormula α)) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) : SysState → Array SysState × Array (Std.HashSet Nat) × Array Nat :=
  fun s =>
    let steps := LSys.totalize sysSucc s
    let base := sysLabel s
    let ss := steps.map Prod.snd
    let m := Std.HashSet.ofList ((List.range gfs.length).filter fun i =>
      steps.any fun st => (TGBAProduct.fairConj gfs i).eval (LSys.letter base st.1))
    (ss, ss.map fun _ => m, #[])

theorem sysFairExpand_coherent (gfs : List (BoolFormula α))
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α) :
    ExpandCoherent (Product.totalizeSucc (LSys.targets sysSucc)) (sysFairMarks gfs sysSucc sysLabel)
      (sysFairExpand gfs sysSucc sysLabel) := by
  intro s
  have h : Array.map Prod.snd (LSys.totalize sysSucc s)
      = Product.totalizeSucc (LSys.targets sysSucc) s :=
    congrFun (LSys.targets_totalize sysSucc) s
  refine Prod.ext h ?_
  show Array.map _ (Array.map Prod.snd (LSys.totalize sysSucc s)) = _
  rw [h]
  rfl

/-- The system graph restricted to the edges some step realizes with a letter satisfying the `FG` conjunct:
`keptSteps`' shadow on the system graph. For a state-labelled system every step out of `s` reads `sysLabel s`,
so this keeps all of `s`'s steps or none, which is the state region the latch used to take. -/
@[expose] def sysKeptSuccs (fg : BoolFormula α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) : SysState → Array SysState :=
  LSys.targets (TGBAProduct.keptSteps sysSucc sysLabel fg.eval)

theorem mem_sysKeptSuccs_iff (fg : BoolFormula α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (s t : SysState) :
    t ∈ sysKeptSuccs fg sysSucc sysLabel s ↔
      ∃ st ∈ LSys.totalize sysSucc s,
        fg.eval (LSys.letter (sysLabel s) st.1) = true ∧ st.2 = t := by
  simp only [sysKeptSuccs, LSys.targets, Array.mem_map, TGBAProduct.mem_keptSteps]
  constructor
  · rintro ⟨st, ⟨hst, he⟩, rfl⟩; exact ⟨st, hst, he, rfl⟩
  · rintro ⟨st, hst, he, rfl⟩; exact ⟨st, ⟨hst, he⟩, rfl⟩

theorem sysKeptSuccs_sub (fg : BoolFormula α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) :
    ∀ s t, t ∈ sysKeptSuccs fg sysSucc sysLabel s →
      t ∈ Product.totalizeSucc (LSys.targets sysSucc) s := by
  intro s t h
  obtain ⟨st, hst, -, rfl⟩ := (mem_sysKeptSuccs_iff fg sysSucc sysLabel s t).mp h
  rw [← LSys.targets_totalize]
  exact Array.mem_map.mpr ⟨st, hst, rfl⟩

/-- The fused expansion for the restricted system graph, sharing one step array the same way. Here the
restricted targets *are* `keptSteps`' projection, so this one is still `rfl`. -/
@[expose] def sysFairExpandR (fg : BoolFormula α) (gfs : List (BoolFormula α))
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α) :
    SysState → Array SysState × Array (Std.HashSet Nat) × Array Nat :=
  fun s =>
    let steps := LSys.totalize sysSucc s
    let base := sysLabel s
    let ss := (steps.filter fun st => fg.eval (LSys.letter base st.1)).map Prod.snd
    let m := Std.HashSet.ofList ((List.range gfs.length).filter fun i =>
      steps.any fun st => (TGBAProduct.fairConj gfs i).eval (LSys.letter base st.1))
    (ss, ss.map fun _ => m, #[])

theorem sysFairExpandR_coherent (fg : BoolFormula α) (gfs : List (BoolFormula α))
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α) :
    ExpandCoherent (sysKeptSuccs fg sysSucc sysLabel) (sysFairMarks gfs sysSucc sysLabel)
      (sysFairExpandR fg gfs sysSucc sysLabel) := fun _ => rfl

/-- Does the system alone admit a run satisfying the disjunct? The same latch as the full check on the system graph,
the region and the `GF` parts read off the letters the system's steps contribute. -/
@[expose] def disjunctFeasible (fg : BoolFormula α) (gfs : List (BoolFormula α)) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysChecker : TEmptinessChecker (SysState × Bool) := dijkstraTChecker) : Bool :=
  match sysChecker.check
      (latchSuccs (Product.totalizeSucc (LSys.targets sysSucc)) (sysKeptSuccs fg sysSucc sysLabel))
      (latchInit sysInit fg.isTrue)
      (latchMarks (sysFairMarks gfs sysSucc sysLabel) (sysFairMarks gfs sysSucc sysLabel) gfs.length)
      (latchExpand (sysFairExpand gfs sysSucc sysLabel) (sysFairExpandR fg gfs sysSucc sysLabel)
        gfs.length) (gfs.length + 1) with
  | .empty _ => false
  | .nonEmpty _ _ => true

/-- One disjunct behind the fail-fast, which answers `.empty` without touching the product when the disjunct is
infeasible. -/
@[expose] def modelCheckTGBADisjunctFast (φ : Formula α) (fg : BoolFormula α) (gfs : List (BoolFormula α))
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool) := dijkstraTChecker)
    (sysChecker : TEmptinessChecker (SysState × Bool) := dijkstraTChecker) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  if disjunctFeasible fg gfs sysInit sysSucc sysLabel sysChecker then
    modelCheckTGBADisjunct φ fg gfs sysInit sysSucc sysLabel checker
  else .empty 0

section Correctness

variable [LawfulBEq α]

/-- An infeasible disjunct rules out every run of `sys`, whatever the property is. -/
theorem no_run_of_disjunctFeasible_false (fg : BoolFormula α) (gfs : List (BoolFormula α))
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    (sysChecker : TEmptinessChecker (SysState × Bool))
    (h : disjunctFeasible fg gfs sysInit sysSucc sysLabel sysChecker = false)
    (ρ : Nat → LSys.Edge α SysState) (hρ : (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ)
    (hfg : (BoolFormula.eventuallyAlways fg).satisfies (LSys.valuation sysLabel ρ))
    (hgf : ∀ b ∈ gfs, (BoolFormula.alwaysEventually b).satisfies (LSys.valuation sysLabel ρ)) :
    False := by
  obtain ⟨N, hN⟩ := (TGBAProduct.eventuallyAlways_iff_indexed_run fg sysLabel ρ).mp hfg
  have hindexed := (TGBAProduct.fair_iff_indexed_run gfs sysLabel ρ).mp hgf
  -- the run's own step at `n` is a member of `totalize sysSucc (ρ n).1` reading the letter in question,
  -- so it witnesses both the region and the marks at the projected system edge
  have hregion : ∀ n, N ≤ n → (ρ (n + 1)).1 ∈ sysKeptSuccs fg sysSucc sysLabel (ρ n).1 := fun n hn =>
    (mem_sysKeptSuccs_iff fg sysSucc sysLabel _ _).mpr
      ⟨(ρ n).2, (hρ.2 n).1, hN n hn, (hρ.2 n).2⟩
  have hmarks : ∀ m, m < gfs.length →
      ∀ K, ∃ n ≥ K, m ∈ sysFairMarks gfs sysSucc sysLabel (ρ n).1 (ρ (n + 1)).1 := by
    intro m hm K
    obtain ⟨j, hj⟩ := hindexed m hm K
    exact ⟨K + j, by omega,
      (mem_sysFairMarks_iff gfs sysSucc sysLabel _ _ m).mpr ⟨hm, (ρ (K + j)).2, (hρ.2 _).1, hj⟩⟩
  obtain ⟨ac, -⟩ : ∃ _ac : TAcceptingCycle
      (latchInit sysInit fg.isTrue)
      (latchSuccs (Product.totalizeSucc (LSys.targets sysSucc)) (sysKeptSuccs fg sysSucc sysLabel))
      (latchMarks (sysFairMarks gfs sysSucc sysLabel) (sysFairMarks gfs sysSucc sysLabel) gfs.length)
      (gfs.length + 1), True := by
    cases htop : fg.isTrue
    · refine latch_complete
        (latch_finiteReach (sysKeptSuccs_sub fg sysSucc sysLabel) false
          (Product.finiteReach_totalizeSucc sysInit (LSys.targets sysSucc) sysFR))
        hρ.1 (fun n => LSys.targets_of_isRun hρ n) (N := N) hregion (fun m hm K => ?_)
      · obtain ⟨n, hnK, hmm⟩ := hmarks m hm (max K N)
        exact ⟨n, Nat.le_trans (Nat.le_max_left _ _) hnK, Nat.le_trans (Nat.le_max_right _ _) hnK, hmm⟩
    · refine latch_complete_total
        (latch_finiteReach (sysKeptSuccs_sub fg sysSucc sysLabel) true
          (Product.finiteReach_totalizeSucc sysInit (LSys.targets sysSucc) sysFR))
        hρ.1 (fun n => ?_) (fun m hm K => hmarks m hm K)
      · exact (mem_sysKeptSuccs_iff fg sysSucc sysLabel _ _).mpr
          ⟨(ρ n).2, (hρ.2 n).1, BoolFormula.eval_of_isTrue htop _, (hρ.2 n).2⟩
  rw [disjunctFeasible] at h
  split at h
  · next hempty =>
    exact sysChecker.empty_no_cycle
      (latch_finiteReach (sysKeptSuccs_sub fg sysSucc sysLabel) fg.isTrue
        (Product.finiteReach_totalizeSucc sysInit (LSys.targets sysSucc) sysFR))
      (latchExpand_coherent (sysFairExpand_coherent gfs sysSucc sysLabel)
        (sysFairExpandR_coherent fg gfs sysSucc sysLabel) gfs.length)
      (fun s t m hm => latchMarks_lt (sysFairMarks_lt gfs sysSucc sysLabel)
        (sysFairMarks_lt gfs sysSucc sysLabel) s t m hm) hempty ⟨ac, trivial⟩
  · exact absurd h (by simp)

variable [LawfulHashable α]

/-- An `.empty` result means every run of `sys` satisfying the disjunct satisfies `φ`. -/
theorem modelCheckTGBADisjunctFast_empty_unsat [DecidableEq α] (φ : Formula α) (fg : BoolFormula α)
    (gfs : List (BoolFormula α)) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool)) {n : Nat}
    (h : modelCheckTGBADisjunctFast φ fg gfs sysInit sysSucc sysLabel checker
      sysChecker = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      (BoolFormula.eventuallyAlways fg).satisfies (LSys.valuation sysLabel ρ) →
      (∀ b ∈ gfs, (BoolFormula.alwaysEventually b).satisfies (LSys.valuation sysLabel ρ)) →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  intro ρ hρ hfg hgf
  rw [modelCheckTGBADisjunctFast] at h
  split at h
  · exact modelCheckTGBADisjunct_empty_unsat φ fg gfs sysInit sysSucc sysLabel sysFR
      checker h ρ hρ hfg hgf
  · next hfree =>
    exact absurd hgf (fun _ => no_run_of_disjunctFeasible_false fg gfs sysInit sysSucc sysLabel
      sysFR sysChecker (by simpa using hfree) ρ hρ hfg hgf)

/-- A `.nonEmpty` result yields one run of `sys` that satisfies the disjunct and violates `φ`. -/
theorem modelCheckTGBADisjunctFast_nonEmpty_sat [DecidableEq α] (φ : Formula α) (fg : BoolFormula α)
    (gfs : List (BoolFormula α)) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool))
    {stem loop : List ((SysState × Nat) × Bool)}
    (h : modelCheckTGBADisjunctFast φ fg gfs sysInit sysSucc sysLabel checker
      sysChecker = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      (BoolFormula.eventuallyAlways fg).satisfies (LSys.valuation sysLabel ρ) ∧
      (∀ b ∈ gfs, (BoolFormula.alwaysEventually b).satisfies (LSys.valuation sysLabel ρ)) ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  rw [modelCheckTGBADisjunctFast] at h
  split at h
  · exact modelCheckTGBADisjunct_nonEmpty_sat φ fg gfs sysInit sysSucc sysLabel sysFR
      checker h
  · exact absurd h (by simp)

end Correctness

/-! ## The same crossing, from one system callback

`LSys.StepFn` in place of the `sysSucc`/`sysLabel` pair, so a state's transitions are computed once on
the system-level feasibility check as well as on the product. Bodies are repeated rather than refactored;
the `rfl` bridges are what guarantee the repeat is faithful. `EdgeLabels.md` §15. -/

section OfStep

variable (sysStep : LSys.StepFn α SysState)

@[expose] def sysFairMarksOfStep (gfs : List (BoolFormula α)) : SysState → SysState → Std.HashSet Nat :=
  fun s _ =>
    let r := sysStep s
    let steps := LSys.totalizeAt r.1 s
    let base := r.2
    Std.HashSet.ofList ((List.range gfs.length).filter fun i =>
      steps.any fun st => (TGBAProduct.fairConj gfs i).eval (LSys.letter base st.1))

@[expose] def sysFairExpandOfStep (gfs : List (BoolFormula α)) :
    SysState → Array SysState × Array (Std.HashSet Nat) × Array Nat :=
  fun s =>
    let r := sysStep s
    let steps := LSys.totalizeAt r.1 s
    let base := r.2
    let ss := steps.map Prod.snd
    let m := Std.HashSet.ofList ((List.range gfs.length).filter fun i =>
      steps.any fun st => (TGBAProduct.fairConj gfs i).eval (LSys.letter base st.1))
    (ss, ss.map fun _ => m, #[])

@[expose] def sysKeptSuccsOfStep (fg : BoolFormula α) : SysState → Array SysState :=
  LSys.targets (TGBAProduct.keptStepsOfStep sysStep fg.eval)

@[expose] def sysFairExpandROfStep (fg : BoolFormula α) (gfs : List (BoolFormula α)) :
    SysState → Array SysState × Array (Std.HashSet Nat) × Array Nat :=
  fun s =>
    let r := sysStep s
    let steps := LSys.totalizeAt r.1 s
    let base := r.2
    let ss := (steps.filter fun st => fg.eval (LSys.letter base st.1)).map Prod.snd
    let m := Std.HashSet.ofList ((List.range gfs.length).filter fun i =>
      steps.any fun st => (TGBAProduct.fairConj gfs i).eval (LSys.letter base st.1))
    (ss, ss.map fun _ => m, #[])

theorem sysFairMarksOfStep_eq' (gfs : List (BoolFormula α)) :
    sysFairMarksOfStep sysStep gfs
      = sysFairMarks gfs (fun s => (sysStep s).1) (fun s => (sysStep s).2) := rfl

theorem sysFairExpandOfStep_eq' (gfs : List (BoolFormula α)) :
    sysFairExpandOfStep sysStep gfs
      = sysFairExpand gfs (fun s => (sysStep s).1) (fun s => (sysStep s).2) := rfl

theorem sysKeptSuccsOfStep_eq' (fg : BoolFormula α) :
    sysKeptSuccsOfStep sysStep fg
      = sysKeptSuccs fg (fun s => (sysStep s).1) (fun s => (sysStep s).2) := rfl

theorem sysFairExpandROfStep_eq' (fg : BoolFormula α) (gfs : List (BoolFormula α)) :
    sysFairExpandROfStep sysStep fg gfs
      = sysFairExpandR fg gfs (fun s => (sysStep s).1) (fun s => (sysStep s).2) := rfl

end OfStep

/-- `disjunctFeasible` over one system callback. -/
@[expose] def disjunctFeasibleOfStep (fg : BoolFormula α) (gfs : List (BoolFormula α))
    (sysInit : List SysState) (sysStep : LSys.StepFn α SysState)
    (sysChecker : TEmptinessChecker (SysState × Bool) := dijkstraTChecker) : Bool :=
  match sysChecker.check
      (latchSuccs (Product.totalizeSucc (LSys.targets fun s => (sysStep s).1))
        (sysKeptSuccsOfStep sysStep fg))
      (latchInit sysInit fg.isTrue)
      (latchMarks (sysFairMarksOfStep sysStep gfs) (sysFairMarksOfStep sysStep gfs) gfs.length)
      (latchExpand (sysFairExpandOfStep sysStep gfs) (sysFairExpandROfStep sysStep fg gfs)
        gfs.length) (gfs.length + 1) with
  | .empty _ => false
  | .nonEmpty _ _ => true

theorem disjunctFeasibleOfStep_eq (fg : BoolFormula α) (gfs : List (BoolFormula α))
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α)
    (sysChecker : TEmptinessChecker (SysState × Bool)) :
    disjunctFeasibleOfStep fg gfs sysInit (fun s => (sysSucc s, sysLabel s)) sysChecker
      = disjunctFeasible fg gfs sysInit sysSucc sysLabel sysChecker := rfl

/-- `modelCheckTGBADisjunctFast` over one system callback. -/
@[expose] def modelCheckTGBADisjunctFastOfStep (φ : Formula α) (fg : BoolFormula α)
    (gfs : List (BoolFormula α)) (sysInit : List SysState) (sysStep : LSys.StepFn α SysState)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool) := dijkstraTChecker)
    (sysChecker : TEmptinessChecker (SysState × Bool) := dijkstraTChecker) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  if disjunctFeasibleOfStep fg gfs sysInit sysStep sysChecker then
    modelCheckTGBADisjunctOfStep φ fg gfs sysInit sysStep checker
  else .empty 0

theorem modelCheckTGBADisjunctFastOfStep_eq (φ : Formula α) (fg : BoolFormula α)
    (gfs : List (BoolFormula α)) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool)) :
    modelCheckTGBADisjunctFastOfStep φ fg gfs sysInit (fun s => (sysSucc s, sysLabel s)) checker sysChecker
      = modelCheckTGBADisjunctFast φ fg gfs sysInit sysSucc sysLabel checker sysChecker := rfl

end Feasible

end LTLLib
