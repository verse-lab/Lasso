/-
  On-the-fly product construction between an external system and a `TGBA`.

  A `TGBA.Transition` carries its own label, so the compatibility gate is checked per transition rather than
  once per source state, correct even for heterogeneously-labeled outgoing transitions.

  Key theorems:
  - `run_decompose`/`run_combine`: a product run splits into a TGBA edge-run and a system run, and back
  - `gsp_correct1`/`gsp_correct2`: the two directions of the product's own correctness
  - `exists_TAcceptingCycle_of_acceptingRun`: an accepting product run yields a lasso witness

  Sections:
  - Product construction
  - Proof-level bridge
  - Product run decomposition + acceptance transfer
  - Edge witness
  - From an accepting run to a lasso
  - Lasso witness
-/
import LTLLib.Product
import LTLLib.TGBABased.AbstractSpec.Pumping
import LTLLib.TGBABased.LTLtoTGBA.GBAToTGBA

namespace LTLLib

namespace TGBAProduct

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]

/-! ## Product construction -/

def initialStates (tgba : TGBA α) (sysInit : List SysState) :
    List (SysState × Nat) :=
  sysInit.flatMap fun s => tgba.initialStates.toList.map fun q => (s, q)

/-- Does `valuation` satisfy `t`'s own positive/negative propositional constraint? -/
def transCompatible (t : TGBA.Transition α) (valuation : Std.HashSet α) : Bool :=
  t.positiveProps.all valuation.contains && !t.negativeProps.any valuation.contains

/-- From `(s, q)`, every `q`-transition compatible with `s`'s label, paired with every totalized system successor of `s`. -/
def getSuccessors (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) :
    (SysState × Nat) → Array (SysState × Nat) :=
  fun (s, q) =>
    let lbl := sysLabel s
    let sysSuccs := Product.totalizeSucc sysSucc s
    (tgba.getSuccessors q).flatMap fun t =>
      if transCompatible t lbl then sysSuccs.map fun s' => (s', t.target) else #[]

/-- Marks on a product edge `(s, q) → (s', q')`: the union over every `q → q'` transition compatible with `s`'s label. -/
def edgeMarks (tgba : TGBA α) (sysLabel : SysState → Std.HashSet α) :
    (SysState × Nat) → (SysState × Nat) → Std.HashSet Nat :=
  fun (s, q) (_, q') =>
    let lbl := sysLabel s
    ((tgba.getSuccessors q).filter fun t => t.target == q' && transCompatible t lbl)
      |>.foldl (init := Std.HashSet.emptyWithCapacity 0) fun acc t => acc.union t.acceptMarks

/-! ## Proof-level bridge -/

abbrev Edge (SysState : Type v) (α : Type u) [BEq α] [Hashable α] :=
  SysState × SysState × TGBA.Edge α

/-- Convert the computational product to an abstract `TOASpec`. -/
def toSpec (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    TOASpec (SysState × Nat) (Edge SysState α) α tgba.numAcceptSets where
  src e := (e.1, e.2.2.1)
  dst e := (e.2.1, e.2.2.2.target)
  valid e := e.2.2.2 ∈ tgba.getSuccessors e.2.2.1 ∧
    transCompatible e.2.2.2 (sysLabel e.1) = true ∧ e.2.1 ∈ Product.totalizeSucc sysSucc e.1
  initial p := p ∈ initialStates tgba sysInit
  labelCompat e v := ∀ a, v a ↔ a ∈ sysLabel e.1
  acceptMark i e := e.2.2.2.acceptMarks.contains i.val

/-- Stand-in for the `find?`-missed branches below, never actually selected. -/
private def junkTransition (q : Nat) : TGBA.Transition α :=
  { target := q, positiveProps := Std.HashSet.emptyWithCapacity 0,
    negativeProps := Std.HashSet.emptyWithCapacity 0,
    acceptMarks := Std.HashSet.emptyWithCapacity 0 }

/-! ## Product run decomposition + acceptance transfer -/

private theorem getSuccessors_mem_iff (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) {p p' : SysState × Nat} :
    p' ∈ getSuccessors tgba sysSucc sysLabel p ↔
      ∃ t ∈ tgba.getSuccessors p.2, transCompatible t (sysLabel p.1) = true ∧
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

private theorem reachable_imp (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    ∀ {p : SysState × Nat},
      Reachable (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel) p →
      Reachable sysInit (Product.totalizeSucc sysSucc) p.1 ∧
        Reachable tgba.initialStates.toList tgba.succStates p.2 := by
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
    obtain ⟨t, ht, _, hsys, htgt⟩ := (getSuccessors_mem_iff tgba sysSucc sysLabel).mp hmem
    exact ⟨.step ih1 hsys, .step ih2 (htgt ▸ Array.mem_map.mpr ⟨t, ht, rfl⟩)⟩

/-- The product's own `FiniteReach` witness, from the caller's system-side one and `TGBA.WellFormed`. -/
def finiteReach (tgba : TGBA α) (htwf : tgba.WellFormed) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (sysFR : FiniteReach sysInit sysSucc) :
    FiniteReach (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel) :=
  ((Product.finiteReach_totalizeSucc sysInit sysSucc sysFR).prod (tgba.finiteReach htwf)).subset
    (fun _ hp => reachable_imp tgba sysSucc sysLabel sysInit hp)

/-- A product run splits into a TGBA edge-run and a `Sys.toSpec` run that stay compatible at every step. -/
theorem run_decompose (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : TLA.exec (Edge SysState α)} (hrun : (toSpec tgba sysSucc sysLabel sysInit).isRun σ) :
    tgba.toSpec.isRun (fun n => (σ n).2.2) ∧
    (Sys.toSpec sysSucc sysInit sysLabel).isRun (fun n => (σ n).1) ∧
    ∀ n, transCompatible (σ n).2.2.2 (sysLabel (σ n).1) = true := by
  obtain ⟨hinit, hstep⟩ := hrun
  simp only [toSpec, initialStates, List.mem_flatMap, List.mem_map] at hinit
  obtain ⟨s, hs_mem, q, hq_mem, heq⟩ := hinit
  obtain ⟨hs0, hq0⟩ := Prod.mk.injEq .. |>.mp heq
  refine ⟨⟨?_, fun n => ⟨(hstep n).1.1, ?_⟩⟩, ⟨?_, fun n => ?_⟩, fun n => (hstep n).1.2.1⟩
  · show tgba.isInitial (σ 0).2.2.1 = true
    rw [← hq0]
    exact Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hq_mem)
  · exact congrArg Prod.snd (hstep n).2
  · show (σ 0).1 ∈ sysInit
    rw [← hs0]; exact hs_mem
  · show (σ (n + 1)).1 ∈ Product.totalizeSucc sysSucc ((σ n).1)
    have h2 : (σ n).2.1 = (σ (n + 1)).1 := congrArg Prod.fst (hstep n).2
    rw [← h2]
    exact (hstep n).1.2.2

/-- A TGBA edge-run and a system run that agree step by step combine into a genuine product run. -/
theorem run_combine (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : TLA.exec (TGBA.Edge α)} {τ : TLA.exec SysState}
    (htgba : tgba.toSpec.isRun σ) (hsys : (Sys.toSpec sysSucc sysInit sysLabel).isRun τ)
    (hcompat : ∀ n, transCompatible (σ n).2 (sysLabel (τ n)) = true) :
    (toSpec tgba sysSucc sysLabel sysInit).isRun (fun n => (τ n, τ (n + 1), σ n)) := by
  obtain ⟨htgba_init, htgba_step⟩ := htgba
  obtain ⟨hsys_init, hsys_step⟩ := hsys
  refine ⟨?_, fun n => ⟨⟨(htgba_step n).1, hcompat n, hsys_step n⟩, ?_⟩⟩
  · show (τ 0, (σ 0).1) ∈ initialStates tgba sysInit
    simp only [initialStates, List.mem_flatMap, List.mem_map]
    exact ⟨τ 0, hsys_init, (σ 0).1,
      Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr htgba_init), rfl⟩
  · have h2 : (σ n).2.target = (σ (n + 1)).1 := (htgba_step n).2
    show ((τ (n + 1)), (σ n).2.target) = ((τ (n + 1)), (σ (n + 1)).1)
    rw [h2]

private theorem transCompatible_iff_labelCompat [LawfulBEq α] (tgba : TGBA α)
    (e : TGBA.Edge α) (valuation : Std.HashSet α) :
    transCompatible e.2 valuation = true ↔ tgba.toSpec.labelCompat e (fun a => a ∈ valuation) := by
  unfold transCompatible TGBA.toSpec
  simp only [Bool.and_eq_true, Bool.not_eq_true', Std.HashSet.all_eq_true_iff_forall_mem,
    Std.HashSet.any_eq_false_iff_forall_mem, Std.HashSet.mem_iff_contains, Bool.not_eq_true]

/-- An accepting product run decomposes into a system run and a TGBA-language membership witness for the system's own labeling. -/
theorem gsp_correct1 [LawfulBEq α] (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : TLA.exec (Edge SysState α)}
    (hacc : (toSpec tgba sysSucc sysLabel sysInit).isRun σ ∧
            (toSpec tgba sysSucc sysLabel sysInit).isAcceptingRun σ) :
    (Sys.toSpec sysSucc sysInit sysLabel).isRun (fun n => (σ n).1) ∧
    tgba.toSpec.accepts (fun n a => a ∈ sysLabel (σ n).1) := by
  obtain ⟨hrun, hacc⟩ := hacc
  obtain ⟨htgbarun, hsysrun, hcompat⟩ := run_decompose tgba sysSucc sysLabel sysInit hrun
  exact ⟨hsysrun, fun n => (σ n).2.2, htgbarun,
    fun n => (transCompatible_iff_labelCompat tgba (σ n).2.2 (sysLabel (σ n).1)).mp (hcompat n),
    hacc⟩

/-- A genuine system run whose own labeling lies in the TGBA's language lifts to an accepting product run projecting back down to it. -/
theorem gsp_correct2 [LawfulBEq α] (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {τ : TLA.exec SysState} (hsys : (Sys.toSpec sysSucc sysInit sysLabel).isRun τ)
    (hlang : tgba.toSpec.accepts (fun n a => a ∈ sysLabel (τ n))) :
    ∃ σ : TLA.exec (Edge SysState α), τ = (fun n => (σ n).1) ∧
      (toSpec tgba sysSucc sysLabel sysInit).isRun σ ∧
      (toSpec tgba sysSucc sysLabel sysInit).isAcceptingRun σ := by
  obtain ⟨σ, hrun, hcompat, hacc⟩ := hlang
  exact ⟨fun n => (τ n, τ (n + 1), σ n), rfl,
    run_combine tgba sysSucc sysLabel sysInit hrun hsys
      (fun n => (transCompatible_iff_labelCompat tgba (σ n) (sysLabel (τ n))).mpr (hcompat n)),
    hacc⟩

/-! ## Edge witness -/

private theorem foldl_union_contains (m : Nat) :
    ∀ (l : List (TGBA.Transition α)) (init : Std.HashSet Nat),
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

private theorem mem_edgeMarks_iff (tgba : TGBA α) (sysLabel : SysState → Std.HashSet α)
    (p p' : SysState × Nat) (m : Nat) :
    (edgeMarks tgba sysLabel p p').contains m ↔
      ∃ t ∈ tgba.getSuccessors p.2, t.target = p'.2 ∧
        transCompatible t (sysLabel p.1) = true ∧ t.acceptMarks.contains m := by
  obtain ⟨s, q⟩ := p
  obtain ⟨s', q'⟩ := p'
  rw [edgeMarks, ← Array.foldl_toList, foldl_union_contains m,
    Std.HashSet.contains_emptyWithCapacity]
  simp only [Bool.false_eq_true, false_or, ← Array.mem_def, Array.mem_filter, Bool.and_eq_true,
    beq_iff_eq]
  tauto

/-- A product edge's marks are exactly some automaton transition's, so any per-transition bound transfers. -/
theorem edgeMarks_lt (tgba : TGBA α) (sysLabel : SysState → Std.HashSet α)
    (hbound : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets)
    (p p' : SysState × Nat) (m : Nat) (hm : m ∈ edgeMarks tgba sysLabel p p') :
    m < tgba.numAcceptSets := by
  obtain ⟨t, ht, -, -, htm⟩ :=
    (mem_edgeMarks_iff tgba sysLabel p p' m).mp (Std.HashSet.mem_iff_contains.mp hm)
  exact hbound _ _ ht m (Std.HashSet.mem_iff_contains.mpr htm)

/-- Realize any product step or `edgeMarks`-witnessed mark as a concrete product `Edge`, by picking any
transition of matching shape (existence off `getSuccessors_mem_iff`/`mem_edgeMarks_iff`). -/
def edgeWitness (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    TEdgeWitness (toSpec tgba sysSucc sysLabel sysInit)
      (getSuccessors tgba sysSucc sysLabel) (edgeMarks tgba sysLabel) where
  stepEdge p p' :=
    let lbl := sysLabel p.1
    (p.1, p'.1, ⟨p.2, ((tgba.getSuccessors p.2).find?
      (fun t => t.target == p'.2 && transCompatible t lbl)).getD (junkTransition p'.2)⟩)
  stepEdge_spec := by
    intro p p' hp'
    obtain ⟨t, ht, hc, hsys, htgt⟩ := (getSuccessors_mem_iff tgba sysSucc sysLabel).mp hp'
    have hex : ∃ x, x ∈ tgba.getSuccessors p.2 ∧ (x.target == p'.2 && transCompatible x (sysLabel p.1)) :=
      ⟨t, ht, by simp [htgt, hc]⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Array.find?_isSome.mpr hex)
    have hp := Array.find?_some ha
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hmem : a ∈ tgba.getSuccessors p.2 := Array.mem_of_find?_eq_some ha
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · simpa only [toSpec, ha, Option.getD_some] using hmem
    · simpa only [toSpec, ha, Option.getD_some] using hp.2
    · simpa only [toSpec, ha, Option.getD_some] using hsys
    · simp only [toSpec, ha, Option.getD_some]
    · simp only [toSpec, ha, Option.getD_some, hp.1]
  markEdge p p' m :=
    let lbl := sysLabel p.1
    (p.1, p'.1, ⟨p.2, ((tgba.getSuccessors p.2).find?
      (fun t => t.target == p'.2 && transCompatible t lbl &&
        t.acceptMarks.contains m)).getD (junkTransition p'.2)⟩)
  markEdge_spec := by
    intro p p' m _ hstep hm
    have hsys : p'.1 ∈ Product.totalizeSucc sysSucc p.1 := by
      obtain ⟨-, -, -, h, -⟩ := (getSuccessors_mem_iff tgba sysSucc sysLabel).mp hstep
      exact h
    obtain ⟨t, ht, htgt, hc, htm⟩ :=
      (mem_edgeMarks_iff tgba sysLabel p p' m).mp (Std.HashSet.mem_iff_contains.mp hm)
    have hex : ∃ x, x ∈ tgba.getSuccessors p.2 ∧
        (x.target == p'.2 && transCompatible x (sysLabel p.1) && x.acceptMarks.contains m) :=
      ⟨t, ht, by simp [htgt, hc, htm]⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Array.find?_isSome.mpr hex)
    have hp := Array.find?_some ha
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hmem : a ∈ tgba.getSuccessors p.2 := Array.mem_of_find?_eq_some ha
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simpa only [toSpec, ha, Option.getD_some] using hmem
    · simpa only [toSpec, ha, Option.getD_some] using hp.1.2
    · simpa only [toSpec, ha, Option.getD_some] using hsys
    · simp only [toSpec, ha, Option.getD_some]
    · simp only [toSpec, ha, Option.getD_some, hp.1.1]
    · simpa only [toSpec, ha, Option.getD_some] using hp.2

/-! ## From an accepting run to a lasso -/

theorem exists_TAcceptingCycle_of_acceptingRun (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (fr : FiniteReach (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel))
    {σ : TLA.exec (Edge SysState α)}
    (hrun : (toSpec tgba sysSucc sysLabel sysInit).isRun σ)
    (hacc : (toSpec tgba sysSucc sysLabel sysInit).isAcceptingRun σ) :
    ∃ _ac : TAcceptingCycle (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel)
      (edgeMarks tgba sysLabel) tgba.numAcceptSets, True := by
  obtain ⟨hinit, hstep⟩ := hrun
  refine exists_TAcceptingCycle_of_run fr (σ := fun n => ((σ n).1, (σ n).2.2.1)) hinit ?_ ?_
  · intro n
    obtain ⟨⟨ht, hc, hsys⟩, hlink⟩ := hstep n
    have h1 : (σ n).2.1 = (σ (n + 1)).1 := congrArg Prod.fst hlink
    have h2 : (σ n).2.2.2.target = (σ (n + 1)).2.2.1 := congrArg Prod.snd hlink
    exact (getSuccessors_mem_iff tgba sysSucc sysLabel).mpr ⟨(σ n).2.2.2, ht, hc, h1 ▸ hsys, h2⟩
  · intro m hm N
    obtain ⟨j, hj⟩ := hacc ⟨m, hm⟩ N
    obtain ⟨⟨ht, hc, -⟩, hlink⟩ := hstep (N + j)
    have h2 : (σ (N + j)).2.2.2.target = (σ (N + j + 1)).2.2.1 := congrArg Prod.snd hlink
    exact ⟨N + j, by omega, Std.HashSet.mem_iff_contains.mpr
      ((mem_edgeMarks_iff tgba sysLabel _ _ m).mpr ⟨(σ (N + j)).2.2.2, ht, h2, hc, hj⟩)⟩

end TGBAProduct

/-! ## Lasso witness -/

/-- The `TGBAProduct.toSpec` specialization of `TAcceptingCycle.toTValidLassoOf`. -/
def TAcceptingCycle.toTValidLassoProduct {α : Type u} {SysState : Type v} [BEq α] [Hashable α]
    {tgba : TGBA α} {sysSucc : SysState → Array SysState}
    {sysLabel : SysState → Std.HashSet α} {sysInit : List SysState}
    (ac : TAcceptingCycle (TGBAProduct.initialStates tgba sysInit)
      (TGBAProduct.getSuccessors tgba sysSucc sysLabel)
      (TGBAProduct.edgeMarks tgba sysLabel) tgba.numAcceptSets) :
    TValidLasso (TGBAProduct.toSpec tgba sysSucc sysLabel sysInit)
      (stemEdges (TGBAProduct.edgeWitness tgba sysSucc sysLabel sysInit).stepEdge ac.stem)
      (ac.cycleE (TGBAProduct.edgeWitness tgba sysSucc sysLabel sysInit)) :=
  ac.toTValidLassoOf (TGBAProduct.edgeWitness tgba sysSucc sysLabel sysInit) (fun hs => hs)

end LTLLib
