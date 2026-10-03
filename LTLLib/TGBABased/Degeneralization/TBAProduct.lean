module

/-
  On-the-fly product of an external system with a `TBA`, the construction of `TGBABased/Product.lean` with
  `TBAState` in place of `Nat` states. `TGBA.degeneralize` needs a materialized `TGBA`, so the system is
  crossed with the already degeneralized `TBA`.

  Both sides are transition-based: a `TBA.Transition` carries its own label, and a system step carries its
  own letter (`TGBABased/LabelledSys.lean`), so the compatibility gate is checked per (system step,
  automaton transition) pair. The product's state set is `SysState × TBAState` either way — an edge atom
  such as `taken(a)` costs no states. See `EdgeLabels.md`.

  Defines:
  - `initialStates`, `getSuccessors`, `realizations`, `edgeMarks`, `expand`: the product graph and its marks
  - `toSpec`: the product as an abstract `TOASpec`
  - `edgeWitness`: a concrete product edge for every product step and every mark on it

  Proves:
  - `run_decompose`, `run_combine`: a product run splits into a TBA edge-run and a system run, and back
  - `gsp_correct1`, `gsp_correct2`: the two directions of the product's own correctness
  - `expand_coherent`: the fused expansion agrees with the two callbacks
  - `exists_TAcceptingCycle_of_acceptingRun`: an accepting product run yields a lasso witness
  - `exists_run_of_TAcceptingCycle`: a lasso witness yields a system run
-/
public import LTLLib.Product
public import LTLLib.TGBABased.Degeneralization.TBA
public import LTLLib.TGBABased.LabelledSys

public section

namespace LTLLib

namespace TBAProduct

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]

/-! ## Product construction -/

@[expose] def initialStates (tba : TBA α) (sysInit : List SysState) :
    List (SysState × TBAState) :=
  sysInit.flatMap fun s => tba.initialStates.toList.map fun q => (s, q)

/-- Does `valuation` satisfy `t`'s own positive/negative propositional constraint? -/
@[expose] def transCompatible (t : TBA.Transition α) (valuation : Std.HashSet α) : Bool :=
  t.positiveProps.all valuation.contains && !t.negativeProps.any valuation.contains

/-- From `(s, q)`, every system step out of `s` paired with every `q`-transition compatible with the letter
*that step* reads. The system step is chosen first because it is what fixes the letter; in a state-labelled
product the two loops are nested the other way round. -/
@[expose] def succsFrom (tba : TBA α) (q : TBAState) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) : Array (SysState × TBAState) :=
  let ts := tba.getSuccessors q
  if steps.all (·.1.isEmpty) then
    -- PERF: every step reads `base`, so compatibility is a property of the transition alone and is
    -- tested once per transition rather than once per (step, transition). See
    -- `TGBAProduct.succsFrom` and `EdgeLabels.md` §12.10 — this route feels it most, since the nested
    -- DFS walks each edge more than once.
    let ok := ts.filter fun t => transCompatible t base
    steps.flatMap fun st => ok.map fun t => (st.2, t.target)
  else
    steps.flatMap fun st =>
      let lbl := LSys.letter base st.1
      ts.filterMap fun t =>
        if transCompatible t lbl then some (st.2, t.target) else none

@[expose] def getSuccessors (tba : TBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) :
    (SysState × TBAState) → Array (SysState × TBAState) :=
  fun (s, q) => succsFrom tba q (sysLabel s) (LSys.totalize sysSucc s)

/-! ## Realizations of a product step

A product step `(s, q) → (s', q')` is realized by a pair: a system step `s → s'` and a `q → q'` transition
compatible with that step's letter. Parallel system steps make several pairs realize the same product step,
which is why the marks are collected over all of them and why `edgeWitness` has to name one. -/

/-- Every realization of a product step out of a source whose letter and steps are already in hand. -/
@[expose] def realizationsFrom [BEq SysState] [Hashable SysState] (tba : TBA α) (q : TBAState) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) (p' : SysState × TBAState) :
    Array (LStep α SysState × TBA.Transition α) :=
  (steps.filter fun st => st.2 == p'.1).flatMap fun st =>
    ((tba.getSuccessors q).filter fun t =>
      t.target == p'.2 && transCompatible t (LSys.letter base st.1)).map (st, ·)

/-- Every (system step, automaton transition) pair realizing the product step `p → p'`. -/
@[expose] def realizations [BEq SysState] [Hashable SysState] (tba : TBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (p p' : SysState × TBAState) :
    Array (LStep α SysState × TBA.Transition α) :=
  realizationsFrom tba p.2 (sysLabel p.1) (LSys.totalize sysSucc p.1) p'

theorem mem_realizations_iff [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (tba : TBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (p p' : SysState × TBAState) (r : LStep α SysState × TBA.Transition α) :
    r ∈ realizations tba sysSucc sysLabel p p' ↔
      (r.1 ∈ LSys.totalize sysSucc p.1 ∧ r.1.2 = p'.1) ∧
      (r.2 ∈ tba.getSuccessors p.2 ∧ r.2.target = p'.2 ∧
        transCompatible r.2 (LSys.letter (sysLabel p.1) r.1.1) = true) := by
  simp only [realizations, realizationsFrom, Array.mem_flatMap, Array.mem_filter, Array.mem_map,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨st, ⟨hst, hst2⟩, t, ⟨ht, htgt, hc⟩, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
    exact ⟨⟨hst, hst2⟩, ht, htgt, hc⟩
  · rintro ⟨⟨hst, hst2⟩, ht, htgt, hc⟩
    exact ⟨r.1, ⟨hst, hst2⟩, r.2, ⟨ht, htgt, hc⟩, rfl⟩

/-- Marks on a product edge `(s, q) → (s', q')`: the union over every realization of the step. Unioning
across realizations over-approximates a single step; it is sound because TGBA acceptance asks for each mark
infinitely often and `edgeWitness.markEdge` names a realization carrying the mark, so pumping the cycle
realizes them one at a time. A *region* may not be over-approximated this way — see `EdgeLabels.md` §6.3. -/
@[expose] def edgeMarksFrom [BEq SysState] [Hashable SysState] (tba : TBA α) (q : TBAState) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) (p' : SysState × TBAState) : Std.HashSet Nat :=
  (realizationsFrom tba q base steps p').foldl
    (init := Std.HashSet.emptyWithCapacity 0) fun acc r => acc.union r.2.acceptMarks

-- PERF: `edgeMarks` is the *spec* form, one edge at a time; the search does not call it. `expand` above is
-- what the search walks with, fusing this and `getSuccessors` so a caller's per-source cost is paid once per
-- product state. Do not try to make this one cache its own per-source work by returning a closure: Lean
-- eta-expands a function-returning definition into its full arity, so `edgeMarks tba sysSucc sysLabel p` is
-- a partial application whose body never runs. That was measured. `expand` returns a pair of arrays, which
-- is not a function and so is saturated at `p`. See `EdgeLabels.md` §9.
@[expose] def edgeMarks [BEq SysState] [Hashable SysState] (tba : TBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (p : SysState × TBAState) :
    (SysState × TBAState) → Std.HashSet Nat :=
  let base := sysLabel p.1
  let steps := LSys.totalize sysSucc p.1
  fun p' => edgeMarksFrom tba p.2 base steps p'

/-- Successors of a product state together with the marks of each, from one pass over the source. The
result type is a *pair of arrays*, not a function, so the compiler cannot eta-expand it: the body runs once
per call and `sysLabel`/`sysSucc` are entered once per product state. -/
@[expose] def expand [BEq SysState] [Hashable SysState] (tba : TBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (p : SysState × TBAState) :
    Array (SysState × TBAState) × Array (Std.HashSet Nat) × Array Nat :=
  let base := sysLabel p.1
  let steps := LSys.totalize sysSucc p.1
  let out := succsFrom tba p.2 base steps
  -- no options on this route, so the third array stays empty: §13.17's payload costs the nested DFS
  -- nothing, neither an allocation per edge nor an array of zeros
  (out, out.map fun p' => edgeMarksFrom tba p.2 base steps p', #[])

/-! ## The same product, from one system callback

`LSys.StepFn` in place of the `sysSucc`/`sysLabel` pair, so a source's transitions are computed once.
Mirrors `TGBAProduct`'s `OfStep` section; see `EdgeLabels.md` §15. -/

section OfStep

variable (tba : TBA α) (sysStep : LSys.StepFn α SysState)

@[expose] def getSuccessorsOfStep : (SysState × TBAState) → Array (SysState × TBAState) :=
  fun p => let r := sysStep p.1; succsFrom tba p.2 r.2 (LSys.totalizeAt r.1 p.1)

variable [BEq SysState] [Hashable SysState]

@[expose] def edgeMarksOfStep (p : SysState × TBAState) : (SysState × TBAState) → Std.HashSet Nat :=
  let r := sysStep p.1
  fun p' => edgeMarksFrom tba p.2 r.2 (LSys.totalizeAt r.1 p.1) p'

@[expose] def expandOfStep (p : SysState × TBAState) :
    Array (SysState × TBAState) × Array (Std.HashSet Nat) × Array Nat :=
  let r := sysStep p.1
  let base := r.2
  let steps := LSys.totalizeAt r.1 p.1
  let out := succsFrom tba p.2 base steps
  (out, out.map fun p' => edgeMarksFrom tba p.2 base steps p', #[])

theorem getSuccessorsOfStep_eq' :
    getSuccessorsOfStep tba sysStep
      = getSuccessors tba (fun s => (sysStep s).1) (fun s => (sysStep s).2) := by
  funext p; obtain ⟨s, q⟩ := p; rfl

theorem edgeMarksOfStep_eq' :
    edgeMarksOfStep tba sysStep
      = edgeMarks tba (fun s => (sysStep s).1) (fun s => (sysStep s).2) := rfl

theorem expandOfStep_eq' :
    expandOfStep tba sysStep
      = expand tba (fun s => (sysStep s).1) (fun s => (sysStep s).2) := rfl

end OfStep

/-- `expand` is the fused form of `getSuccessors` and `edgeMarks`: one call per product state. Coherence is
definitional, because `expand` is literally the two of them sharing their per-source work. -/
theorem expand_coherent [BEq SysState] [Hashable SysState] (tba : TBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α) :
    ExpandCoherent (getSuccessors tba sysSucc sysLabel) (edgeMarks tba sysSucc sysLabel)
      (expand tba sysSucc sysLabel) := fun _ => rfl

/-! ## Proof-level bridge -/

abbrev Edge (SysState : Type v) (α : Type u) [BEq α] [Hashable α] :=
  SysState × LStep α SysState × TBA.Edge α

/-- Convert the computational product to an abstract `TOASpec`. -/
@[expose] def toSpec (tba : TBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    TOASpec (SysState × TBAState) (Edge SysState α) α tba.numAcceptSets where
  src e := (e.1, e.2.2.1)
  dst e := (e.2.1.2, e.2.2.2.target)
  valid e := e.2.2.2 ∈ tba.getSuccessors e.2.2.1 ∧
    transCompatible e.2.2.2 (LSys.letter (sysLabel e.1) e.2.1.1) = true ∧
    e.2.1 ∈ LSys.totalize sysSucc e.1
  initial p := p ∈ initialStates tba sysInit
  labelCompat e v := ∀ a, v a ↔ a ∈ LSys.letter (sysLabel e.1) e.2.1.1
  acceptMark i e := e.2.2.2.acceptMarks.contains i.val

/-- Stand-in for the `find?`-missed branches below, never actually selected. -/
private def junkTransition (q : TBAState) : TBA.Transition α :=
  { target := q, positiveProps := Std.HashSet.emptyWithCapacity 0,
    negativeProps := Std.HashSet.emptyWithCapacity 0,
    acceptMarks := Std.HashSet.emptyWithCapacity 0 }

/-! ## Product run decomposition + acceptance transfer -/

/-- A product step is exactly a system step out of `p.1` paired with an automaton transition compatible with
that step's letter. -/
theorem getSuccessors_mem_iff (tba : TBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) {p p' : SysState × TBAState} :
    p' ∈ getSuccessors tba sysSucc sysLabel p ↔
      ∃ st ∈ LSys.totalize sysSucc p.1, ∃ t ∈ tba.getSuccessors p.2,
        transCompatible t (LSys.letter (sysLabel p.1) st.1) = true ∧ st.2 = p'.1 ∧ t.target = p'.2 := by
  obtain ⟨s, q⟩ := p
  obtain ⟨s', q'⟩ := p'
  show _ ∈ succsFrom tba q (sysLabel s) (LSys.totalize sysSucc s) ↔ _
  unfold succsFrom
  dsimp only
  split
  · -- the shared-letter branch: `LSys.letter base st.1 = base` for every step, by the guard
    next hall =>
      have hbase : ∀ st ∈ LSys.totalize sysSucc s, LSys.letter (sysLabel s) st.1 = sysLabel s :=
        fun st hst => by
          rw [LSys.letter, if_pos (by simpa using Array.all_eq_true'.mp hall st hst)]
      simp only [Array.mem_flatMap, Array.mem_map, Array.mem_filter]
      constructor
      · rintro ⟨st, hst, t, ⟨ht, hc⟩, heq⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
        exact ⟨st, hst, t, ht, by rw [hbase st hst]; exact hc, rfl, rfl⟩
      · rintro ⟨st, hst, t, ht, hc, rfl, rfl⟩
        rw [hbase st hst] at hc
        exact ⟨st, hst, t, ⟨ht, hc⟩, rfl⟩
  · simp only [Array.mem_flatMap, Array.mem_filterMap]
    constructor
    · rintro ⟨st, hst, t, ht, hopt⟩
      by_cases hc : transCompatible t (LSys.letter (sysLabel s) st.1) = true
      · rw [if_pos hc] at hopt
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp (Option.some.inj hopt)
        exact ⟨st, hst, t, ht, hc, rfl, rfl⟩
      · rw [if_neg hc] at hopt; exact absurd hopt (by simp)
    · rintro ⟨st, hst, t, ht, hc, rfl, rfl⟩
      exact ⟨st, hst, t, ht, by rw [if_pos hc]⟩

private theorem reachable_imp (tba : TBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    ∀ {p : SysState × TBAState},
      Reachable (initialStates tba sysInit) (getSuccessors tba sysSucc sysLabel) p →
      Reachable sysInit (Product.totalizeSucc (LSys.targets sysSucc)) p.1 ∧
        Reachable tba.initialStates.toList tba.succStates p.2 := by
  intro p h
  induction h with
  | base hi =>
    simp only [initialStates, List.mem_flatMap, List.mem_map] at hi
    obtain ⟨s, hs_mem, q, hq_mem, heq⟩ := hi
    subst heq
    exact ⟨.base hs_mem, .base hq_mem⟩
  | step hprev hmem ih =>
    rename_i prev cur
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨st, hst, t, ht, -, hst2, htgt⟩ := (getSuccessors_mem_iff tba sysSucc sysLabel).mp hmem
    refine ⟨.step ih1 ?_, .step ih2 (htgt ▸ Array.mem_map.mpr ⟨t, ht, rfl⟩)⟩
    rw [← LSys.targets_totalize]
    exact hst2 ▸ Array.mem_map.mpr ⟨st, hst, rfl⟩

/-- The product's own `FiniteReach` witness, from the caller's system-side one and `TBA.WellFormed`. -/
def finiteReach (tba : TBA α) (htwf : tba.WellFormed)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState) (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) :
    FiniteReach (initialStates tba sysInit) (getSuccessors tba sysSucc sysLabel) :=
  ((Product.finiteReach_totalizeSucc sysInit (LSys.targets sysSucc) sysFR).prod
      (tba.finiteReach htwf)).subset
    (fun _ hp => reachable_imp tba sysSucc sysLabel sysInit hp)

/-- A product run splits into a TGBA edge-run and an `LSys.toSpec` run that stay compatible at every step. -/
theorem run_decompose (tba : TBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : Lentil.exec (Edge SysState α)} (hrun : (toSpec tba sysSucc sysLabel sysInit).isRun σ) :
    tba.toSpec.isRun (fun n => (σ n).2.2) ∧
    (LSys.toSpec sysSucc sysInit sysLabel).isRun (fun n => ((σ n).1, (σ n).2.1)) ∧
    ∀ n, transCompatible (σ n).2.2.2 (LSys.letter (sysLabel (σ n).1) (σ n).2.1.1) = true := by
  obtain ⟨hinit, hstep⟩ := hrun
  simp only [toSpec, initialStates, List.mem_flatMap, List.mem_map] at hinit
  obtain ⟨s, hs_mem, q, hq_mem, heq⟩ := hinit
  obtain ⟨hs0, hq0⟩ := Prod.mk.injEq .. |>.mp heq
  refine ⟨⟨?_, fun n => ⟨(hstep n).1.1, ?_⟩⟩, ⟨?_, fun n => ⟨(hstep n).1.2.2, ?_⟩⟩,
    fun n => (hstep n).1.2.1⟩
  · show tba.isInitial (σ 0).2.2.1 = true
    rw [← hq0]
    exact Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hq_mem)
  · exact congrArg Prod.snd (hstep n).2
  · show (σ 0).1 ∈ sysInit
    rw [← hs0]; exact hs_mem
  · exact congrArg Prod.fst (hstep n).2

/-- A TGBA edge-run and a labelled system run that agree step by step combine into a genuine product run. -/
theorem run_combine (tba : TBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : Lentil.exec (TBA.Edge α)} {ρ : Lentil.exec (LSys.Edge α SysState)}
    (htba : tba.toSpec.isRun σ) (hsys : (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ)
    (hcompat : ∀ n, transCompatible (σ n).2 (LSys.letter (sysLabel (ρ n).1) (ρ n).2.1) = true) :
    (toSpec tba sysSucc sysLabel sysInit).isRun (fun n => ((ρ n).1, (ρ n).2, σ n)) := by
  obtain ⟨htba_init, htba_step⟩ := htba
  obtain ⟨hsys_init, hsys_step⟩ := hsys
  refine ⟨?_, fun n => ⟨⟨(htba_step n).1, hcompat n, (hsys_step n).1⟩, ?_⟩⟩
  · show ((ρ 0).1, (σ 0).1) ∈ initialStates tba sysInit
    simp only [initialStates, List.mem_flatMap, List.mem_map]
    exact ⟨(ρ 0).1, hsys_init, (σ 0).1,
      Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr htba_init), rfl⟩
  · have h1 : (ρ n).2.2 = (ρ (n + 1)).1 := (hsys_step n).2
    have h2 : (σ n).2.target = (σ (n + 1)).1 := (htba_step n).2
    show ((ρ n).2.2, (σ n).2.target) = ((ρ (n + 1)).1, (σ (n + 1)).1)
    rw [h1, h2]

private theorem transCompatible_iff_labelCompat [LawfulBEq α] (tba : TBA α)
    (e : TBA.Edge α) (valuation : Std.HashSet α) :
    transCompatible e.2 valuation = true ↔ tba.toSpec.labelCompat e (fun a => a ∈ valuation) := by
  unfold transCompatible TBA.toSpec
  simp only [Bool.and_eq_true, Bool.not_eq_true', Std.HashSet.all_eq_true_iff_forall_mem,
    Std.HashSet.any_eq_false_iff_forall_mem, Std.HashSet.mem_iff_contains, Bool.not_eq_true]

/-- An accepting product run decomposes into a labelled system run and a TGBA-language membership witness for
the letters that run reads. -/
theorem gsp_correct1 [LawfulBEq α] (tba : TBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState) {σ : Lentil.exec (Edge SysState α)}
    (hacc : (toSpec tba sysSucc sysLabel sysInit).isRun σ ∧
            (toSpec tba sysSucc sysLabel sysInit).isAcceptingRun σ) :
    (LSys.toSpec sysSucc sysInit sysLabel).isRun (fun n => ((σ n).1, (σ n).2.1)) ∧
    tba.toSpec.accepts (LSys.valuation sysLabel (fun n => ((σ n).1, (σ n).2.1))) := by
  obtain ⟨hrun, hacc⟩ := hacc
  obtain ⟨htbarun, hsysrun, hcompat⟩ := run_decompose tba sysSucc sysLabel sysInit hrun
  exact ⟨hsysrun, fun n => (σ n).2.2, htbarun,
    fun n => (transCompatible_iff_labelCompat tba (σ n).2.2
      (LSys.letter (sysLabel (σ n).1) (σ n).2.1.1)).mp (hcompat n),
    hacc⟩

/-- A genuine labelled system run whose letters lie in the TGBA's language lifts to an accepting product run
projecting back down to it. -/
theorem gsp_correct2 [LawfulBEq α] (tba : TBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState) {ρ : Lentil.exec (LSys.Edge α SysState)}
    (hsys : (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ)
    (hlang : tba.toSpec.accepts (LSys.valuation sysLabel ρ)) :
    ∃ σ : Lentil.exec (Edge SysState α), ρ = (fun n => ((σ n).1, (σ n).2.1)) ∧
      (toSpec tba sysSucc sysLabel sysInit).isRun σ ∧
      (toSpec tba sysSucc sysLabel sysInit).isAcceptingRun σ := by
  obtain ⟨σ, hrun, hcompat, hacc⟩ := hlang
  exact ⟨fun n => ((ρ n).1, (ρ n).2, σ n), rfl,
    run_combine tba sysSucc sysLabel sysInit hrun hsys
      (fun n => (transCompatible_iff_labelCompat tba (σ n)
        (LSys.letter (sysLabel (ρ n).1) (ρ n).2.1)).mpr (hcompat n)),
    hacc⟩

/-! ## Edge witness -/

private theorem foldl_union_contains {β : Type w} (m : Nat) (f : β → Std.HashSet Nat) :
    ∀ (l : List β) (init : Std.HashSet Nat),
      (l.foldl (fun acc b => acc.union (f b)) init).contains m ↔
        init.contains m ∨ ∃ b ∈ l, (f b).contains m := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro init
    rw [List.foldl_cons, ih, Std.HashSet.union_eq, Std.HashSet.contains_union]
    simp only [Bool.or_eq_true, List.mem_cons]
    constructor
    · rintro ((h1 | h2) | ⟨b, hb, hbm⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨a, Or.inl rfl, h2⟩
      · exact Or.inr ⟨b, Or.inr hb, hbm⟩
    · rintro (h | ⟨b, rfl | hb, hbm⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr hbm)
      · exact Or.inr ⟨b, hb, hbm⟩

/-- A product edge's marks are exactly those of the transitions of its realizations. -/
theorem mem_edgeMarks_iff [BEq SysState] [Hashable SysState] (tba : TBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (p p' : SysState × TBAState) (m : Nat) :
    (edgeMarks tba sysSucc sysLabel p p').contains m ↔
      ∃ r ∈ realizations tba sysSucc sysLabel p p', r.2.acceptMarks.contains m := by
  show (edgeMarksFrom tba p.2 (sysLabel p.1) (LSys.totalize sysSucc p.1) p').contains m ↔ _
  rw [edgeMarksFrom, ← Array.foldl_toList,
    foldl_union_contains m (fun r : LStep α SysState × TBA.Transition α => r.2.acceptMarks),
    Std.HashSet.contains_emptyWithCapacity]
  simp only [Bool.false_eq_true, false_or, ← Array.mem_def, realizations]

/-- A product edge's marks are exactly some automaton transition's, so any per-transition bound transfers. -/
theorem edgeMarks_lt [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (tba : TBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (hbound : ∀ q t, t ∈ tba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tba.numAcceptSets)
    (p p' : SysState × TBAState) (m : Nat) (hm : m ∈ edgeMarks tba sysSucc sysLabel p p') :
    m < tba.numAcceptSets := by
  obtain ⟨r, hr, hrm⟩ :=
    (mem_edgeMarks_iff tba sysSucc sysLabel p p' m).mp (Std.HashSet.mem_iff_contains.mp hm)
  obtain ⟨-, ht, -, -⟩ := (mem_realizations_iff tba sysSucc sysLabel p p' r).mp hr
  exact hbound _ _ ht m (Std.HashSet.mem_iff_contains.mpr hrm)

/-- The product step `p → p'` has a realization exactly when it is a step at all. -/
theorem exists_realization_iff [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (tba : TBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (p p' : SysState × TBAState) :
    (∃ r, r ∈ realizations tba sysSucc sysLabel p p') ↔
      p' ∈ getSuccessors tba sysSucc sysLabel p := by
  rw [getSuccessors_mem_iff]
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨⟨hst, hst2⟩, ht, htgt, hc⟩ := (mem_realizations_iff tba sysSucc sysLabel p p' r).mp hr
    exact ⟨r.1, hst, r.2, ht, hc, hst2, htgt⟩
  · rintro ⟨st, hst, t, ht, hc, hst2, htgt⟩
    exact ⟨(st, t), (mem_realizations_iff tba sysSucc sysLabel p p' (st, t)).mpr
      ⟨⟨hst, hst2⟩, ht, htgt, hc⟩⟩

variable [BEq SysState] [Hashable SysState] [LawfulBEq SysState]

/-- The realization the witness picks for a step, or for a step carrying a given mark. -/
private def pick (tba : TBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (p p' : SysState × TBAState)
    (extra : LStep α SysState × TBA.Transition α → Bool) :
    LStep α SysState × TBA.Transition α :=
  ((realizations tba sysSucc sysLabel p p').find? extra).getD
    (((∅ : Std.HashSet α), p'.1), junkTransition p'.2)

private theorem pick_spec (tba : TBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (p p' : SysState × TBAState)
    (extra : LStep α SysState × TBA.Transition α → Bool)
    (hex : ∃ r ∈ realizations tba sysSucc sysLabel p p', extra r = true) :
    (pick tba sysSucc sysLabel p p' extra) ∈ realizations tba sysSucc sysLabel p p' ∧
      extra (pick tba sysSucc sysLabel p p' extra) = true := by
  obtain ⟨r, hr, hextra⟩ := hex
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Array.find?_isSome.mpr ⟨r, hr, hextra⟩)
  rw [pick, ha, Option.getD_some]
  exact ⟨Array.mem_of_find?_eq_some ha, Array.find?_some ha⟩

/-- Realize any product step or `edgeMarks`-witnessed mark as a concrete product `Edge`, by picking a
realization of matching shape. -/
def edgeWitness (tba : TBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    TEdgeWitness (toSpec tba sysSucc sysLabel sysInit)
      (getSuccessors tba sysSucc sysLabel) (edgeMarks tba sysSucc sysLabel) where
  stepEdge p p' :=
    let r := pick tba sysSucc sysLabel p p' (fun _ => true)
    (p.1, r.1, ⟨p.2, r.2⟩)
  stepEdge_spec := by
    intro p p' hp'
    obtain ⟨r, hr⟩ := (exists_realization_iff tba sysSucc sysLabel p p').mpr hp'
    obtain ⟨hmem, -⟩ := pick_spec tba sysSucc sysLabel p p' (fun _ => true) ⟨r, hr, rfl⟩
    obtain ⟨⟨hst, hst2⟩, ht, htgt, hc⟩ :=
      (mem_realizations_iff tba sysSucc sysLabel p p' _).mp hmem
    exact ⟨⟨ht, hc, hst⟩, rfl, by simp only [toSpec, hst2, htgt]⟩
  markEdge p p' m :=
    let r := pick tba sysSucc sysLabel p p' (fun r => r.2.acceptMarks.contains m)
    (p.1, r.1, ⟨p.2, r.2⟩)
  markEdge_spec := by
    intro p p' m _ _ hm
    obtain ⟨r, hr, hrm⟩ :=
      (mem_edgeMarks_iff tba sysSucc sysLabel p p' m).mp (Std.HashSet.mem_iff_contains.mp hm)
    obtain ⟨hmem, hextra⟩ := pick_spec tba sysSucc sysLabel p p'
      (fun r => r.2.acceptMarks.contains m) ⟨r, hr, hrm⟩
    obtain ⟨⟨hst, hst2⟩, ht, htgt, hc⟩ :=
      (mem_realizations_iff tba sysSucc sysLabel p p' _).mp hmem
    exact ⟨⟨ht, hc, hst⟩, rfl, by simp only [toSpec, hst2, htgt], hextra⟩

/-! ## From an accepting run to a lasso -/

/-- The product-state sequence an accepting product run walks starts initial, steps along `getSuccessors`, and
carries every mark infinitely often. -/
theorem acceptingRun_states (tba : TBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : Lentil.exec (Edge SysState α)}
    (hrun : (toSpec tba sysSucc sysLabel sysInit).isRun σ)
    (hacc : (toSpec tba sysSucc sysLabel sysInit).isAcceptingRun σ) :
    ((σ 0).1, (σ 0).2.2.1) ∈ initialStates tba sysInit ∧
    (∀ n, ((σ (n + 1)).1, (σ (n + 1)).2.2.1) ∈
      getSuccessors tba sysSucc sysLabel ((σ n).1, (σ n).2.2.1)) ∧
    ∀ m, m < tba.numAcceptSets → ∀ N, ∃ n ≥ N, m ∈ edgeMarks tba sysSucc sysLabel
      ((σ n).1, (σ n).2.2.1) ((σ (n + 1)).1, (σ (n + 1)).2.2.1) := by
  obtain ⟨hinit, hstep⟩ := hrun
  refine ⟨hinit, fun n => ?_, fun m hm N => ?_⟩
  · obtain ⟨⟨ht, hc, hsys⟩, hlink⟩ := hstep n
    have h1 : (σ n).2.1.2 = (σ (n + 1)).1 := congrArg Prod.fst hlink
    have h2 : (σ n).2.2.2.target = (σ (n + 1)).2.2.1 := congrArg Prod.snd hlink
    exact (getSuccessors_mem_iff tba sysSucc sysLabel).mpr
      ⟨(σ n).2.1, hsys, (σ n).2.2.2, ht, hc, h1, h2⟩
  · obtain ⟨j, hj⟩ := hacc ⟨m, hm⟩ N
    obtain ⟨⟨ht, hc, hsys⟩, hlink⟩ := hstep (N + j)
    have h1 : (σ (N + j)).2.1.2 = (σ (N + j + 1)).1 := congrArg Prod.fst hlink
    have h2 : (σ (N + j)).2.2.2.target = (σ (N + j + 1)).2.2.1 := congrArg Prod.snd hlink
    refine ⟨N + j, by omega, Std.HashSet.mem_iff_contains.mpr
      ((mem_edgeMarks_iff tba sysSucc sysLabel _ _ m).mpr
        ⟨((σ (N + j)).2.1, (σ (N + j)).2.2.2), ?_, hj⟩)⟩
    exact (mem_realizations_iff tba sysSucc sysLabel _ _ _).mpr ⟨⟨hsys, h1⟩, ht, h2, hc⟩

theorem exists_TAcceptingCycle_of_acceptingRun (tba : TBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState)
    (fr : FiniteReach (initialStates tba sysInit) (getSuccessors tba sysSucc sysLabel))
    {σ : Lentil.exec (Edge SysState α)}
    (hrun : (toSpec tba sysSucc sysLabel sysInit).isRun σ)
    (hacc : (toSpec tba sysSucc sysLabel sysInit).isAcceptingRun σ) :
    ∃ _ac : TAcceptingCycle (initialStates tba sysInit) (getSuccessors tba sysSucc sysLabel)
      (edgeMarks tba sysSucc sysLabel) tba.numAcceptSets, True :=
  have h := acceptingRun_states tba sysSucc sysLabel sysInit hrun hacc
  exists_TAcceptingCycle_of_run fr (σ := fun n => ((σ n).1, (σ n).2.2.1)) h.1 h.2.1 h.2.2

end TBAProduct

/-! ## Lasso witness -/

/-- The `TBAProduct.toSpec` specialization of `TAcceptingCycle.toTValidLassoOf`. -/
theorem TAcceptingCycle.toTValidLassoTBAProduct {α : Type u} {SysState : Type v} [BEq α] [Hashable α]
    [BEq SysState] [Hashable SysState] [LawfulBEq SysState] {tba : TBA α}
    {sysSucc : SysState → Array (LStep α SysState)} {sysLabel : SysState → Std.HashSet α}
    {sysInit : List SysState}
    (ac : TAcceptingCycle (TBAProduct.initialStates tba sysInit)
      (TBAProduct.getSuccessors tba sysSucc sysLabel)
      (TBAProduct.edgeMarks tba sysSucc sysLabel) tba.numAcceptSets) :
    TValidLasso (TBAProduct.toSpec tba sysSucc sysLabel sysInit)
      (stemEdges (TBAProduct.edgeWitness tba sysSucc sysLabel sysInit).stepEdge ac.stem)
      (ac.cycleE (TBAProduct.edgeWitness tba sysSucc sysLabel sysInit)) :=
  ac.toTValidLassoOf (TBAProduct.edgeWitness tba sysSucc sysLabel sysInit) (fun hs => hs)

namespace TBAProduct

/-- The counterexample a product cycle describes: one labelled system run whose letters the automaton accepts.
A predicate holding at every cycle state holds past the stem, and one holding at some cycle state infinitely
often. -/
theorem exists_run_of_TAcceptingCycle {α : Type u} {SysState : Type v} [BEq α] [Hashable α]
    [LawfulBEq α] [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (tba : TBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState)
    (ac : TAcceptingCycle (initialStates tba sysInit) (getSuccessors tba sysSucc sysLabel)
      (edgeMarks tba sysSucc sysLabel) tba.numAcceptSets) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      tba.toSpec.accepts (LSys.valuation sysLabel ρ) ∧
      (∀ P : SysState → Prop, (∀ p ∈ ac.cycle, P p.1) → ∃ N, ∀ n, N ≤ n → P (ρ n).1) ∧
      (∀ P : SysState → Prop, (∃ p ∈ ac.cycle, P p.1) → ∀ n, ∃ j, P (ρ (n + j)).1) := by
  obtain ⟨hρrun, hlang⟩ := gsp_correct1 tba sysSucc sysLabel sysInit
    ⟨ac.toTValidLassoTBAProduct.run_isRun, ac.toTValidLassoTBAProduct.run_isAccepting⟩
  refine ⟨fun n => ((ac.toTValidLassoTBAProduct.run n).1, (ac.toTValidLassoTBAProduct.run n).2.1),
    hρrun, hlang, fun P hP => ?_, fun P hP n => ?_⟩
  · refine ⟨(stemEdges (edgeWitness tba sysSucc sysLabel sysInit).stepEdge ac.stem).length,
      fun n hn => ?_⟩
    obtain ⟨i, hi, hsrc⟩ := TValidLasso.run_src_mem_cycle
      (edgeWitness tba sysSucc sysLabel sysInit) ac ac.toTValidLassoTBAProduct n (by omega)
    have hPi := hP _ (List.getElem_mem hi)
    rw [← hsrc] at hPi
    exact hPi
  · obtain ⟨p, hp, hPp⟩ := hP
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
    obtain ⟨t, ht⟩ := TValidLasso.run_src_hits_cycle (edgeWitness tba sysSucc sysLabel sysInit)
      ac ac.toTValidLassoTBAProduct i hi n
    rw [← ht] at hPp
    exact ⟨t, hPp⟩

end TBAProduct

end LTLLib
