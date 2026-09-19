/-
  On-the-fly product of an external system with a `TBA`, the construction of `TGBABased/Product.lean` with `TBAState`
  in place of `Nat` states. `TGBA.degeneralize` needs a materialized `TGBA`, so the system is crossed with the already
  degeneralized `TBA`.

  Defines:
  - `TBAProduct.getSuccessors`, `TBAProduct.edgeMarks`: the product's successors and edge marks
  - `TBAProduct.toSpec`: the product as a `TOASpec`
  - `TBAProduct.edgeWitness`: concrete product edges realizing steps and marks

  Proves:
  - `run_decompose`/`run_combine`: a product run splits into a TBA edge-run and a system run, and back
  - `gsp_correct1`/`gsp_correct2`: accepting product runs are exactly system runs whose labeling the TBA accepts
  - `exists_TAcceptingCycle_of_acceptingRun`: an accepting product run yields a lasso witness
  - `exists_run_of_TAcceptingCycle`: a lasso witness yields a system run, carrying a per-cycle predicate onto the run's tail
    and a per-state one onto infinitely many positions

  Sections:
  - Product construction
  - Proof-level bridge
  - Product run decomposition + acceptance transfer
  - Edge witness
  - From an accepting run to a lasso
  - Lasso witness
-/
import LTLLib.Product
import LTLLib.TGBABased.Degeneralization.TBA

namespace LTLLib

namespace TBAProduct

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]

/-! ## Product construction -/

def initialStates (tba : TBA α) (sysInit : List SysState) :
    List (SysState × TBAState) :=
  sysInit.flatMap fun s => tba.initialStates.toList.map fun q => (s, q)

/-- Does `valuation` satisfy `t`'s own positive/negative propositional constraint? -/
def transCompatible (t : TBA.Transition α) (valuation : Std.HashSet α) : Bool :=
  t.positiveProps.all valuation.contains && !t.negativeProps.any valuation.contains

/-- From `(s, q)`, every `q`-transition compatible with `s`'s label, paired with every totalized system successor of `s`. -/
def getSuccessors (tba : TBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) :
    (SysState × TBAState) → Array (SysState × TBAState) :=
  fun (s, q) =>
    let lbl := sysLabel s
    let sysSuccs := Product.totalizeSucc sysSucc s
    (tba.getSuccessors q).flatMap fun t =>
      if transCompatible t lbl then sysSuccs.map fun s' => (s', t.target) else #[]

/-- Marks on a product edge `(s, q) → (s', q')`: the union over every `q → q'` transition compatible with `s`'s label. -/
def edgeMarks (tba : TBA α) (sysLabel : SysState → Std.HashSet α) :
    (SysState × TBAState) → (SysState × TBAState) → Std.HashSet Nat :=
  fun (s, q) (_, q') =>
    let lbl := sysLabel s
    ((tba.getSuccessors q).filter fun t => t.target == q' && transCompatible t lbl)
      |>.foldl (init := Std.HashSet.emptyWithCapacity 0) fun acc t => acc.union t.acceptMarks

/-! ## Proof-level bridge -/

abbrev Edge (SysState : Type v) (α : Type u) [BEq α] [Hashable α] :=
  SysState × SysState × TBA.Edge α

/-- Convert the computational product to an abstract `TOASpec`. -/
def toSpec (tba : TBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    TOASpec (SysState × TBAState) (Edge SysState α) α tba.numAcceptSets where
  src e := (e.1, e.2.2.1)
  dst e := (e.2.1, e.2.2.2.target)
  valid e := e.2.2.2 ∈ tba.getSuccessors e.2.2.1 ∧
    transCompatible e.2.2.2 (sysLabel e.1) = true ∧ e.2.1 ∈ Product.totalizeSucc sysSucc e.1
  initial p := p ∈ initialStates tba sysInit
  labelCompat e v := ∀ a, v a ↔ a ∈ sysLabel e.1
  acceptMark i e := e.2.2.2.acceptMarks.contains i.val

/-- Stand-in for the `find?`-missed branches below, never actually selected. -/
private def junkTransition (q : TBAState) : TBA.Transition α :=
  { target := q, positiveProps := Std.HashSet.emptyWithCapacity 0,
    negativeProps := Std.HashSet.emptyWithCapacity 0,
    acceptMarks := Std.HashSet.emptyWithCapacity 0 }

/-! ## Product run decomposition + acceptance transfer -/

/-- A product step is exactly a compatible automaton transition paired with a totalized system successor. -/
theorem getSuccessors_mem_iff (tba : TBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) {p p' : SysState × TBAState} :
    p' ∈ getSuccessors tba sysSucc sysLabel p ↔
      ∃ t ∈ tba.getSuccessors p.2, transCompatible t (sysLabel p.1) = true ∧
        p'.1 ∈ Product.totalizeSucc sysSucc p.1 ∧ t.target = p'.2 := by
  obtain ⟨s, q⟩ := p
  obtain ⟨s', q'⟩ := p'
  unfold getSuccessors
  simp only [Array.mem_flatMap]
  constructor
  · rintro ⟨t, ht, hmem⟩
    by_cases hc : transCompatible t (sysLabel s) = true
    · rw [if_pos hc] at hmem
      obtain ⟨s'', hs'', heq⟩ := Array.mem_map.mp hmem
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
      exact ⟨t, ht, hc, hs'', rfl⟩
    · rw [if_neg hc] at hmem; simp at hmem
  · rintro ⟨t, ht, hc, hs', rfl⟩
    exact ⟨t, ht, by rw [if_pos hc]; exact Array.mem_map.mpr ⟨s', hs', rfl⟩⟩

private theorem reachable_imp (tba : TBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    ∀ {p : SysState × TBAState},
      Reachable (initialStates tba sysInit) (getSuccessors tba sysSucc sysLabel) p →
      Reachable sysInit (Product.totalizeSucc sysSucc) p.1 ∧
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
    obtain ⟨t, ht, _, hsys, htgt⟩ := (getSuccessors_mem_iff tba sysSucc sysLabel).mp hmem
    exact ⟨.step ih1 hsys, .step ih2 (htgt ▸ Array.mem_map.mpr ⟨t, ht, rfl⟩)⟩

/-- The product has finitely many reachable states if the system does and the `TBA` is well-formed. -/
def finiteReach (tba : TBA α) (htwf : tba.WellFormed) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (sysFR : FiniteReach sysInit sysSucc) :
    FiniteReach (initialStates tba sysInit) (getSuccessors tba sysSucc sysLabel) :=
  ((Product.finiteReach_totalizeSucc sysInit sysSucc sysFR).prod (tba.finiteReach htwf)).subset
    (fun _ hp => reachable_imp tba sysSucc sysLabel sysInit hp)

/-- A product run splits into a TBA edge-run and a `Sys.toSpec` run that stay compatible at every step. -/
theorem run_decompose (tba : TBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : TLA.exec (Edge SysState α)} (hrun : (toSpec tba sysSucc sysLabel sysInit).isRun σ) :
    tba.toSpec.isRun (fun n => (σ n).2.2) ∧
    (Sys.toSpec sysSucc sysInit sysLabel).isRun (fun n => (σ n).1) ∧
    ∀ n, transCompatible (σ n).2.2.2 (sysLabel (σ n).1) = true := by
  obtain ⟨hinit, hstep⟩ := hrun
  simp only [toSpec, initialStates, List.mem_flatMap, List.mem_map] at hinit
  obtain ⟨s, hs_mem, q, hq_mem, heq⟩ := hinit
  obtain ⟨hs0, hq0⟩ := Prod.mk.injEq .. |>.mp heq
  refine ⟨⟨?_, fun n => ⟨(hstep n).1.1, ?_⟩⟩, ⟨?_, fun n => ?_⟩, fun n => (hstep n).1.2.1⟩
  · show tba.isInitial (σ 0).2.2.1 = true
    rw [← hq0]
    exact Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hq_mem)
  · exact congrArg Prod.snd (hstep n).2
  · show (σ 0).1 ∈ sysInit
    rw [← hs0]; exact hs_mem
  · show (σ (n + 1)).1 ∈ Product.totalizeSucc sysSucc ((σ n).1)
    have h2 : (σ n).2.1 = (σ (n + 1)).1 := congrArg Prod.fst (hstep n).2
    rw [← h2]
    exact (hstep n).1.2.2

/-- A TBA edge-run and a system run that agree step by step combine into a genuine product run. -/
theorem run_combine (tba : TBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : TLA.exec (TBA.Edge α)} {τ : TLA.exec SysState}
    (htba : tba.toSpec.isRun σ) (hsys : (Sys.toSpec sysSucc sysInit sysLabel).isRun τ)
    (hcompat : ∀ n, transCompatible (σ n).2 (sysLabel (τ n)) = true) :
    (toSpec tba sysSucc sysLabel sysInit).isRun (fun n => (τ n, τ (n + 1), σ n)) := by
  obtain ⟨htba_init, htba_step⟩ := htba
  obtain ⟨hsys_init, hsys_step⟩ := hsys
  refine ⟨?_, fun n => ⟨⟨(htba_step n).1, hcompat n, hsys_step n⟩, ?_⟩⟩
  · show (τ 0, (σ 0).1) ∈ initialStates tba sysInit
    simp only [initialStates, List.mem_flatMap, List.mem_map]
    exact ⟨τ 0, hsys_init, (σ 0).1,
      Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr htba_init), rfl⟩
  · have h2 : (σ n).2.target = (σ (n + 1)).1 := (htba_step n).2
    show ((τ (n + 1)), (σ n).2.target) = ((τ (n + 1)), (σ (n + 1)).1)
    rw [h2]

private theorem transCompatible_iff_labelCompat [LawfulBEq α] (tba : TBA α)
    (e : TBA.Edge α) (valuation : Std.HashSet α) :
    transCompatible e.2 valuation = true ↔ tba.toSpec.labelCompat e (fun a => a ∈ valuation) := by
  unfold transCompatible TBA.toSpec
  simp only [Bool.and_eq_true, Bool.not_eq_true', Std.HashSet.all_eq_true_iff_forall_mem,
    Std.HashSet.any_eq_false_iff_forall_mem, Std.HashSet.mem_iff_contains, Bool.not_eq_true]

/-- An accepting product run projects to a system run whose labeling the TBA accepts. -/
theorem gsp_correct1 [LawfulBEq α] (tba : TBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : TLA.exec (Edge SysState α)}
    (hacc : (toSpec tba sysSucc sysLabel sysInit).isRun σ ∧
            (toSpec tba sysSucc sysLabel sysInit).isAcceptingRun σ) :
    (Sys.toSpec sysSucc sysInit sysLabel).isRun (fun n => (σ n).1) ∧
    tba.toSpec.accepts (fun n a => a ∈ sysLabel (σ n).1) := by
  obtain ⟨hrun, hacc⟩ := hacc
  obtain ⟨htbarun, hsysrun, hcompat⟩ := run_decompose tba sysSucc sysLabel sysInit hrun
  exact ⟨hsysrun, fun n => (σ n).2.2, htbarun,
    fun n => (transCompatible_iff_labelCompat tba (σ n).2.2 (sysLabel (σ n).1)).mp (hcompat n),
    hacc⟩

/-- A system run whose labeling the TBA accepts lifts to an accepting product run projecting to it. -/
theorem gsp_correct2 [LawfulBEq α] (tba : TBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {τ : TLA.exec SysState} (hsys : (Sys.toSpec sysSucc sysInit sysLabel).isRun τ)
    (hlang : tba.toSpec.accepts (fun n a => a ∈ sysLabel (τ n))) :
    ∃ σ : TLA.exec (Edge SysState α), τ = (fun n => (σ n).1) ∧
      (toSpec tba sysSucc sysLabel sysInit).isRun σ ∧
      (toSpec tba sysSucc sysLabel sysInit).isAcceptingRun σ := by
  obtain ⟨σ, hrun, hcompat, hacc⟩ := hlang
  exact ⟨fun n => (τ n, τ (n + 1), σ n), rfl,
    run_combine tba sysSucc sysLabel sysInit hrun hsys
      (fun n => (transCompatible_iff_labelCompat tba (σ n) (sysLabel (τ n))).mpr (hcompat n)),
    hacc⟩

/-! ## Edge witness -/

private theorem foldl_union_contains (m : Nat) :
    ∀ (l : List (TBA.Transition α)) (init : Std.HashSet Nat),
      (l.foldl (fun acc t => acc.union t.acceptMarks) init).contains m ↔
        init.contains m ∨ ∃ t ∈ l, t.acceptMarks.contains m := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro init
    rw [List.foldl_cons, ih, Std.HashSet.union_eq, Std.HashSet.contains_union]
    simp only [Bool.or_eq_true, List.mem_cons]
    constructor
    · rintro ((h1 | h2) | ⟨t, ht, htm⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨a, Or.inl rfl, h2⟩
      · exact Or.inr ⟨t, Or.inr ht, htm⟩
    · rintro (h | ⟨t, rfl | ht, htm⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr htm)
      · exact Or.inr ⟨t, ht, htm⟩

/-- A product edge's marks are exactly those of the compatible automaton transitions realizing it. -/
theorem mem_edgeMarks_iff (tba : TBA α) (sysLabel : SysState → Std.HashSet α)
    (p p' : SysState × TBAState) (m : Nat) :
    (edgeMarks tba sysLabel p p').contains m ↔
      ∃ t ∈ tba.getSuccessors p.2, t.target = p'.2 ∧
        transCompatible t (sysLabel p.1) = true ∧ t.acceptMarks.contains m := by
  obtain ⟨s, q⟩ := p
  obtain ⟨s', q'⟩ := p'
  rw [edgeMarks, ← Array.foldl_toList, foldl_union_contains m,
    Std.HashSet.contains_emptyWithCapacity]
  simp only [Bool.false_eq_true, false_or, ← Array.mem_def, Array.mem_filter, Bool.and_eq_true,
    beq_iff_eq]
  tauto

/-- Product edge marks inherit any bound on the automaton's transition marks. -/
theorem edgeMarks_lt (tba : TBA α) (sysLabel : SysState → Std.HashSet α)
    (hbound : ∀ q t, t ∈ tba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tba.numAcceptSets)
    (p p' : SysState × TBAState) (m : Nat) (hm : m ∈ edgeMarks tba sysLabel p p') :
    m < tba.numAcceptSets := by
  obtain ⟨t, ht, -, -, htm⟩ :=
    (mem_edgeMarks_iff tba sysLabel p p' m).mp (Std.HashSet.mem_iff_contains.mp hm)
  exact hbound _ _ ht m (Std.HashSet.mem_iff_contains.mpr htm)

/-- Realize any product step or `edgeMarks`-witnessed mark as a concrete product `Edge` by picking a matching transition. -/
def edgeWitness (tba : TBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    TEdgeWitness (toSpec tba sysSucc sysLabel sysInit)
      (getSuccessors tba sysSucc sysLabel) (edgeMarks tba sysLabel) where
  stepEdge p p' :=
    let lbl := sysLabel p.1
    (p.1, p'.1, ⟨p.2, ((tba.getSuccessors p.2).find?
      (fun t => t.target == p'.2 && transCompatible t lbl)).getD (junkTransition p'.2)⟩)
  stepEdge_spec := by
    intro p p' hp'
    obtain ⟨t, ht, hc, hsys, htgt⟩ := (getSuccessors_mem_iff tba sysSucc sysLabel).mp hp'
    have hex : ∃ x, x ∈ tba.getSuccessors p.2 ∧ (x.target == p'.2 && transCompatible x (sysLabel p.1)) :=
      ⟨t, ht, by simp [htgt, hc]⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Array.find?_isSome.mpr hex)
    have hp := Array.find?_some ha
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hmem : a ∈ tba.getSuccessors p.2 := Array.mem_of_find?_eq_some ha
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · simpa only [toSpec, ha, Option.getD_some] using hmem
    · simpa only [toSpec, ha, Option.getD_some] using hp.2
    · simpa only [toSpec, ha, Option.getD_some] using hsys
    · simp only [toSpec, ha, Option.getD_some]
    · simp only [toSpec, ha, Option.getD_some, hp.1]
  markEdge p p' m :=
    let lbl := sysLabel p.1
    (p.1, p'.1, ⟨p.2, ((tba.getSuccessors p.2).find?
      (fun t => t.target == p'.2 && transCompatible t lbl &&
        t.acceptMarks.contains m)).getD (junkTransition p'.2)⟩)
  markEdge_spec := by
    intro p p' m _ hstep hm
    have hsys : p'.1 ∈ Product.totalizeSucc sysSucc p.1 := by
      obtain ⟨-, -, -, h, -⟩ := (getSuccessors_mem_iff tba sysSucc sysLabel).mp hstep
      exact h
    obtain ⟨t, ht, htgt, hc, htm⟩ :=
      (mem_edgeMarks_iff tba sysLabel p p' m).mp (Std.HashSet.mem_iff_contains.mp hm)
    have hex : ∃ x, x ∈ tba.getSuccessors p.2 ∧
        (x.target == p'.2 && transCompatible x (sysLabel p.1) && x.acceptMarks.contains m) :=
      ⟨t, ht, by simp [htgt, hc, htm]⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Array.find?_isSome.mpr hex)
    have hp := Array.find?_some ha
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hmem : a ∈ tba.getSuccessors p.2 := Array.mem_of_find?_eq_some ha
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simpa only [toSpec, ha, Option.getD_some] using hmem
    · simpa only [toSpec, ha, Option.getD_some] using hp.1.2
    · simpa only [toSpec, ha, Option.getD_some] using hsys
    · simp only [toSpec, ha, Option.getD_some]
    · simp only [toSpec, ha, Option.getD_some, hp.1.1]
    · simpa only [toSpec, ha, Option.getD_some] using hp.2

/-! ## From an accepting run to a lasso -/

/-- The product states of an accepting product run start initial, follow `getSuccessors`, and carry every mark infinitely often. -/
theorem acceptingRun_states (tba : TBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : TLA.exec (Edge SysState α)}
    (hrun : (toSpec tba sysSucc sysLabel sysInit).isRun σ)
    (hacc : (toSpec tba sysSucc sysLabel sysInit).isAcceptingRun σ) :
    ((σ 0).1, (σ 0).2.2.1) ∈ initialStates tba sysInit ∧
    (∀ n, ((σ (n + 1)).1, (σ (n + 1)).2.2.1) ∈
      getSuccessors tba sysSucc sysLabel ((σ n).1, (σ n).2.2.1)) ∧
    ∀ m, m < tba.numAcceptSets → ∀ N, ∃ n ≥ N, m ∈ edgeMarks tba sysLabel
      ((σ n).1, (σ n).2.2.1) ((σ (n + 1)).1, (σ (n + 1)).2.2.1) := by
  obtain ⟨hinit, hstep⟩ := hrun
  refine ⟨hinit, fun n => ?_, fun m hm N => ?_⟩
  · obtain ⟨⟨ht, hc, hsys⟩, hlink⟩ := hstep n
    have h1 : (σ n).2.1 = (σ (n + 1)).1 := congrArg Prod.fst hlink
    have h2 : (σ n).2.2.2.target = (σ (n + 1)).2.2.1 := congrArg Prod.snd hlink
    exact (getSuccessors_mem_iff tba sysSucc sysLabel).mpr ⟨(σ n).2.2.2, ht, hc, h1 ▸ hsys, h2⟩
  · obtain ⟨j, hj⟩ := hacc ⟨m, hm⟩ N
    obtain ⟨⟨ht, hc, -⟩, hlink⟩ := hstep (N + j)
    have h2 : (σ (N + j)).2.2.2.target = (σ (N + j + 1)).2.2.1 := congrArg Prod.snd hlink
    exact ⟨N + j, by omega, Std.HashSet.mem_iff_contains.mpr
      ((mem_edgeMarks_iff tba sysLabel _ _ m).mpr ⟨(σ (N + j)).2.2.2, ht, h2, hc, hj⟩)⟩

theorem exists_TAcceptingCycle_of_acceptingRun (tba : TBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (fr : FiniteReach (initialStates tba sysInit) (getSuccessors tba sysSucc sysLabel))
    {σ : TLA.exec (Edge SysState α)}
    (hrun : (toSpec tba sysSucc sysLabel sysInit).isRun σ)
    (hacc : (toSpec tba sysSucc sysLabel sysInit).isAcceptingRun σ) :
    ∃ _ac : TAcceptingCycle (initialStates tba sysInit) (getSuccessors tba sysSucc sysLabel)
      (edgeMarks tba sysLabel) tba.numAcceptSets, True :=
  have h := acceptingRun_states tba sysSucc sysLabel sysInit hrun hacc
  exists_TAcceptingCycle_of_run fr (σ := fun n => ((σ n).1, (σ n).2.2.1)) h.1 h.2.1 h.2.2

end TBAProduct

/-! ## Lasso witness -/

/-- The `TBAProduct.toSpec` specialization of `TAcceptingCycle.toTValidLassoOf`. -/
def TAcceptingCycle.toTValidLassoTBAProduct {α : Type u} {SysState : Type v} [BEq α] [Hashable α]
    {tba : TBA α} {sysSucc : SysState → Array SysState}
    {sysLabel : SysState → Std.HashSet α} {sysInit : List SysState}
    (ac : TAcceptingCycle (TBAProduct.initialStates tba sysInit)
      (TBAProduct.getSuccessors tba sysSucc sysLabel)
      (TBAProduct.edgeMarks tba sysLabel) tba.numAcceptSets) :
    TValidLasso (TBAProduct.toSpec tba sysSucc sysLabel sysInit)
      (stemEdges (TBAProduct.edgeWitness tba sysSucc sysLabel sysInit).stepEdge ac.stem)
      (ac.cycleE (TBAProduct.edgeWitness tba sysSucc sysLabel sysInit)) :=
  ac.toTValidLassoOf (TBAProduct.edgeWitness tba sysSucc sysLabel sysInit) (fun hs => hs)

namespace TBAProduct

/-- A product cycle yields a system run whose labeling the TBA accepts. A predicate holding at every cycle state holds
from the stem on, and one holding at some cycle state holds infinitely often. -/
theorem exists_run_of_TAcceptingCycle {α : Type u} {SysState : Type v} [BEq α] [Hashable α]
    [LawfulBEq α] (tba : TBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (ac : TAcceptingCycle (initialStates tba sysInit) (getSuccessors tba sysSucc sysLabel)
      (edgeMarks tba sysLabel) tba.numAcceptSets) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      tba.toSpec.accepts (fun n a => a ∈ sysLabel (τ n)) ∧
      (∀ P : SysState → Prop, (∀ p ∈ ac.cycle, P p.1) → ∃ N, ∀ n, N ≤ n → P (τ n)) ∧
      (∀ P : SysState → Prop, (∃ p ∈ ac.cycle, P p.1) → ∀ n, ∃ j, P (τ (n + j))) := by
  obtain ⟨hτrun, hlang⟩ := gsp_correct1 tba sysSucc sysLabel sysInit
    ⟨ac.toTValidLassoTBAProduct.run_isRun, ac.toTValidLassoTBAProduct.run_isAccepting⟩
  refine ⟨fun n => (ac.toTValidLassoTBAProduct.run n).1, hτrun, hlang, fun P hP => ?_, fun P hP n => ?_⟩
  · refine ⟨(stemEdges (edgeWitness tba sysSucc sysLabel sysInit).stepEdge ac.stem).length,
      fun n hn => ?_⟩
    obtain ⟨i, hi, hsrc⟩ := TValidLasso.run_src_mem_cycle (edgeWitness tba sysSucc sysLabel sysInit)
      ac ac.toTValidLassoTBAProduct n (by omega)
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
