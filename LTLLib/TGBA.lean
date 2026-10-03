module

/-
  Transition-based generalized Büchi automata (TGBA), with labels and acceptance marks attached to transitions rather
  than states. A GBA converts to a TGBA by pushing its acceptance marks onto all outgoing transitions. `consistentPart`
  drops the transitions no valuation takes, so that an emptiness check reading only the graph decides the language.

  Defines:
  - `TGBA.Transition`, `TGBA`: a labeled, marked transition and the automaton
  - `TGBA.edgeMarks`, `TGBA.cachedEdgeMarks`: the marks on an edge, the second backed by a precomputed table
  - `TGBA.WellFormed`, `TGBA.finiteReach`: well-formedness and the `FiniteReach` witness it gives
  - `TGBA.toSpec`: the automaton as an abstract `TOASpec`
  - `TGBA.edgeWitness`, `TAcceptingCycle.toTValidLasso`: the lasso bridge for `toSpec`
  - `TGBA.consistentPart`: the automaton without the transitions no valuation takes

  Proves:
  - `TGBA.cachedEdgeMarks_contains_iff`: `cachedEdgeMarks` agrees with `edgeMarks`
  - `TGBA.exists_TAcceptingCycle_of_acceptingRun`: an accepting run of `toSpec` yields a `TAcceptingCycle`
  - `TAcceptingCycle.run_states_mem`: every state of the lasso run lies in a well-formed TGBA's state set
  - `TGBA.consistentPart_accepts`: dropping the transitions no valuation takes keeps the language
  - `TGBA.accepts_of_consistentPart_cycle`: an accepting cycle of the consistent part is read by some word

  Sections:
  - The automaton
  - Proof-level bridge
  - Lasso witness
  - Lasso states of a well-formed TGBA
  - From an accepting run to a lasso
  - Transitions some valuation takes
-/

public import Std
public import LTLLib.TGBABased.AbstractSpec.Acceptance
public import LTLLib.TGBABased.AbstractSpec.EmptinessCheck
public import LTLLib.TGBABased.AbstractSpec.Lasso
public import LTLLib.TGBABased.AbstractSpec.Pumping
public import LTLLib.AbstractSpec.GraphPaths

public section

namespace LTLLib

/-! ## The automaton -/

/-- A single labeled, marked transition. -/
structure TGBA.Transition (α : Type u) [BEq α] [Hashable α] where
  target : Nat
  positiveProps : Std.HashSet α  -- propositions required true by the label
  negativeProps : Std.HashSet α  -- propositions required false by the label
  acceptMarks : Std.HashSet Nat  -- indices of the acceptance sets this transition belongs to

/-- A Transition-based Generalized Büchi Automaton -/
structure TGBA (α : Type u) [BEq α] [Hashable α] where
  states : Std.HashSet Nat
  initialStates : Std.HashSet Nat
  successors : Std.HashMap Nat (Array (TGBA.Transition α))  -- keyed by source state
  numAcceptSets : Nat

namespace TGBA

variable {α} [BEq α] [Hashable α]

/-- Number of states in the TGBA. -/
@[expose] def numStates (tgba : TGBA α) : Nat := tgba.states.size

/-- Outgoing transitions of a state. -/
@[expose] def getSuccessors (tgba : TGBA α) (state : Nat) : Array (Transition α) :=
  tgba.successors[state]?.getD #[]

/-- Check if a state is initial. -/
@[expose] def isInitial (tgba : TGBA α) (state : Nat) : Bool :=
  tgba.initialStates.contains state

/-- Check if a transition carries a given acceptance mark. -/
@[expose] def Transition.isAccepting (t : Transition α) (setIdx : Nat) : Bool :=
  t.acceptMarks.contains setIdx

@[expose] def succStates (tgba : TGBA α) (q : Nat) : Array Nat :=
  (tgba.getSuccessors q).map (·.target)

/-- Union of marks over every `q → q'` transition (there may be several parallel ones). -/
@[expose] def edgeMarks (tgba : TGBA α) (q q' : Nat) : Std.HashSet Nat :=
  ((tgba.getSuccessors q).filter (·.target == q')).foldl
    (init := Std.HashSet.emptyWithCapacity 0) fun acc t => acc.union t.acceptMarks

/-- Precomputed `(source, target) → marks` lookup, one pass over every transition. -/
@[expose] def edgeMarksTable (tgba : TGBA α) : Std.HashMap (Nat × Nat) (Std.HashSet Nat) :=
  (tgba.successors.toList.flatMap fun qts => qts.2.toList.map fun t => ((qts.1, t.target), t.acceptMarks)).foldl
    (init := {}) fun m kv => m.insert kv.1 ((m.getD kv.1 (Std.HashSet.emptyWithCapacity 0)).union kv.2)

/-- `edgeMarks` as a constant-time lookup in `edgeMarksTable`. -/
@[expose] def cachedEdgeMarks (tgba : TGBA α) (q q' : Nat) : Std.HashSet Nat :=
  tgba.edgeMarksTable.getD (q, q') (Std.HashSet.emptyWithCapacity 0)

structure WellFormed (tgba : TGBA α) : Prop where
  initial_mem : ∀ q, tgba.isInitial q → tgba.states.contains q
  succ_mem : ∀ q t, tgba.states.contains q → t ∈ tgba.getSuccessors q →
    tgba.states.contains t.target
  -- Acceptance marks are within range
  marks_range : ∀ q t, tgba.states.contains q → t ∈ tgba.getSuccessors q →
    ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets

/-- The `FiniteReach` witness of a well-formed `TGBA`, its state set bounding the reachable set. -/
theorem finiteReach (tgba : TGBA α) (hwf : tgba.WellFormed) :
    FiniteReach tgba.initialStates.toList tgba.succStates := by
  refine ⟨tgba.states.toList, fun q hq => Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr ?_)⟩
  induction hq with
  | base hi =>
    exact hwf.initial_mem _ (by
      show tgba.isInitial _ = true
      exact Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hi))
  | step _ hmem ih =>
    rename_i prev cur
    obtain ⟨t, ht, rfl⟩ := Array.mem_map.mp hmem
    exact hwf.succ_mem _ _ ih ht

/-! ## Proof-level bridge -/

/-- An edge of a TGBA: the source state together with one of its outgoing transitions. -/
abbrev Edge (α : Type u) [BEq α] [Hashable α] := (_q : Nat) × TGBA.Transition α

/-- Convert a computational `TGBA` to an abstract `TOASpec`. Edges are source-state/transition pairs,
label and acceptance marks are read directly off the one transition committed to. -/
@[expose] def toSpec (tgba : TGBA α) : TOASpec Nat (Edge α) α tgba.numAcceptSets where
  src e := e.1
  dst e := e.2.target
  valid e := e.2 ∈ tgba.getSuccessors e.1
  initial q := tgba.isInitial q
  labelCompat e v := (∀ a, e.2.positiveProps.contains a → v a) ∧
    (∀ a, e.2.negativeProps.contains a → ¬ v a)
  acceptMark i e := e.2.acceptMarks.contains i.val

end TGBA

/-! ## Lasso witness -/

variable {α : Type u} [BEq α] [Hashable α]

/-- Stand-in for the `find?` branches below that never fire. -/
private def TGBA.junkTransition (q : Nat) : TGBA.Transition α :=
  { target := q, positiveProps := Std.HashSet.emptyWithCapacity 0,
    negativeProps := Std.HashSet.emptyWithCapacity 0, acceptMarks := Std.HashSet.emptyWithCapacity 0 }

private theorem TGBA.mem_edgeMarks_iff (tgba : TGBA α) (q q' m : Nat) :
    (tgba.edgeMarks q q').contains m ↔
      ∃ t ∈ tgba.getSuccessors q, t.target = q' ∧ t.acceptMarks.contains m := by
  have hfold : ∀ (l : List (Transition α)) (init : Std.HashSet Nat),
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
  rw [TGBA.edgeMarks, ← Array.foldl_toList, hfold, Std.HashSet.contains_emptyWithCapacity]
  simp only [Bool.false_eq_true, false_or, ← Array.mem_def, Array.mem_filter, beq_iff_eq]
  grind

private theorem TGBA.mem_edgeMarksTable_iff (tgba : TGBA α) (q q' m : Nat) :
    (tgba.edgeMarksTable.getD (q, q') (Std.HashSet.emptyWithCapacity 0)).contains m ↔
      ∃ t ∈ tgba.getSuccessors q, t.target = q' ∧ t.acceptMarks.contains m := by
  have hfold : ∀ (l : List ((Nat × Nat) × Std.HashSet Nat))
      (init : Std.HashMap (Nat × Nat) (Std.HashSet Nat)),
      ((l.foldl (fun m kv => m.insert kv.1 ((m.getD kv.1 (Std.HashSet.emptyWithCapacity 0)).union kv.2))
        init).getD (q, q') (Std.HashSet.emptyWithCapacity 0)).contains m ↔
        (init.getD (q, q') (Std.HashSet.emptyWithCapacity 0)).contains m ∨
          ∃ kv ∈ l, kv.1 = (q, q') ∧ kv.2.contains m := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro init
      rw [List.foldl_cons, ih]
      by_cases hkey : a.1 = (q, q')
      · rw [hkey, Std.HashMap.getD_insert_self, Std.HashSet.union_eq, Std.HashSet.contains_union]
        simp only [Bool.or_eq_true, List.mem_cons]
        constructor
        · rintro ((h1 | h2) | h3)
          · exact Or.inl h1
          · exact Or.inr ⟨a, Or.inl rfl, hkey, h2⟩
          · obtain ⟨kv, hkv, hkv1, hkv2⟩ := h3
            exact Or.inr ⟨kv, Or.inr hkv, hkv1, hkv2⟩
        · rintro (h | ⟨kv, rfl | hkv, hkv1, hkv2⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr hkv2)
          · exact Or.inr ⟨kv, hkv, hkv1, hkv2⟩
      · have hbeq : (a.1 == (q, q')) = false := by simpa using hkey
        rw [Std.HashMap.getD_insert, if_neg (by simpa using hbeq)]
        simp only [List.mem_cons]
        constructor
        · rintro (h | ⟨kv, hkv, hkv1, hkv2⟩)
          · exact Or.inl h
          · exact Or.inr ⟨kv, Or.inr hkv, hkv1, hkv2⟩
        · rintro (h | ⟨kv, rfl | hkv, hkv1, hkv2⟩)
          · exact Or.inl h
          · exact absurd hkv1 hkey
          · exact Or.inr ⟨kv, hkv, hkv1, hkv2⟩
  rw [TGBA.edgeMarksTable, hfold, Std.HashMap.getD_empty, Std.HashSet.contains_emptyWithCapacity]
  simp only [Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨kv, hkv, hkv1, hkv2⟩
    obtain ⟨qts, hqts, hkveq⟩ := List.mem_flatMap.mp hkv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hkveq
    simp only [Prod.mk.injEq] at hkv1
    obtain ⟨hq, hq'⟩ := hkv1
    subst hq
    have hget : tgba.successors[qts.1]? = some qts.2 :=
      Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hqts
    have hsucc : tgba.getSuccessors qts.1 = qts.2 := by simp [TGBA.getSuccessors, hget]
    exact ⟨t, hsucc ▸ Array.mem_def.mpr ht, hq', hkv2⟩
  · rintro ⟨t, ht, ht', htm⟩
    have hex : tgba.successors[q]? = some (tgba.getSuccessors q) := by
      rcases hopt : tgba.successors[q]? with _ | ts
      · exact absurd ht (by simp [TGBA.getSuccessors, hopt])
      · simp [TGBA.getSuccessors, hopt]
    exact ⟨((q, t.target), t.acceptMarks), List.mem_flatMap.mpr
      ⟨(q, tgba.getSuccessors q), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hex,
        List.mem_map.mpr ⟨t, Array.mem_def.mp ht, rfl⟩⟩, by simp [ht'], htm⟩

/-- `cachedEdgeMarks` agrees with `edgeMarks` on every mark. -/
theorem TGBA.cachedEdgeMarks_contains_iff (tgba : TGBA α) (q q' m : Nat) :
    (tgba.cachedEdgeMarks q q').contains m ↔ (tgba.edgeMarks q q').contains m := by
  rw [TGBA.cachedEdgeMarks, TGBA.mem_edgeMarksTable_iff, TGBA.mem_edgeMarks_iff]

/-- Realize any `tgba.succStates`-step or `tgba.edgeMarks`-witnessed mark as a concrete `TGBA.Edge`, by picking any
transition of matching shape. -/
def TGBA.edgeWitness (tgba : TGBA α) : TEdgeWitness tgba.toSpec tgba.succStates tgba.edgeMarks where
  stepEdge s s' := ⟨s, ((tgba.getSuccessors s).find? (·.target == s')).getD (junkTransition s')⟩
  stepEdge_spec := by
    intro s s' hs'
    obtain ⟨t, ht, hteq⟩ := Array.mem_map.mp hs'
    have hex : ∃ x, x ∈ tgba.getSuccessors s ∧ x.target == s' := ⟨t, ht, by simp [hteq]⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Array.find?_isSome.mpr hex)
    have htgt : a.target = s' := by simpa using Array.find?_some ha
    have hmem : a ∈ tgba.getSuccessors s := Array.mem_of_find?_eq_some ha
    refine ⟨?_, ?_, ?_⟩ <;> simp [TGBA.toSpec, ha, hmem, htgt]
  markEdge s s' m := ⟨s, ((tgba.getSuccessors s).find?
    (fun t => t.target == s' && t.acceptMarks.contains m)).getD (junkTransition s')⟩
  markEdge_spec := by
    intro s s' m hm _ hm'
    obtain ⟨t, ht, hteq, htm⟩ :=
      (TGBA.mem_edgeMarks_iff tgba s s' m).mp (Std.HashSet.mem_iff_contains.mp hm')
    have hex : ∃ x, x ∈ tgba.getSuccessors s ∧ (x.target == s' && x.acceptMarks.contains m) :=
      ⟨t, ht, by simp [hteq, htm]⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Array.find?_isSome.mpr hex)
    have hp := Array.find?_some ha
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hmem : a ∈ tgba.getSuccessors s := Array.mem_of_find?_eq_some ha
    refine ⟨?_, rfl, ?_, ?_⟩ <;> simp only [TGBA.toSpec, ha, Option.getD_some] <;>
      first | exact hmem | exact hp.1 | exact hp.2

/-- The `TGBA.toSpec` specialization of `TAcceptingCycle.toTValidLassoOf`. -/
theorem TAcceptingCycle.toTValidLasso {tgba : TGBA α}
    (ac : TAcceptingCycle tgba.initialStates.toList tgba.succStates tgba.edgeMarks tgba.numAcceptSets) :
    TValidLasso tgba.toSpec (stemEdges tgba.edgeWitness.stepEdge ac.stem) (ac.cycleE tgba.edgeWitness) :=
  ac.toTValidLassoOf tgba.edgeWitness
    (fun hs => Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hs))

/-- Canonical valuation read directly off a transition's own positive atoms. -/
def TGBA.canonicalTransLabel (t : TGBA.Transition α) : α → Prop :=
  fun a => t.positiveProps.contains a

/-- `canonicalTransLabel` satisfies a transition's label-compatibility constraint,
given its positive/negative atom sets are disjoint. -/
theorem TGBA.canonicalTransLabel_compat (t : TGBA.Transition α)
    (hdisjoint : ∀ a, t.positiveProps.contains a → t.negativeProps.contains a → False) :
    (∀ a, t.positiveProps.contains a → TGBA.canonicalTransLabel t a) ∧
    (∀ a, t.negativeProps.contains a → ¬ TGBA.canonicalTransLabel t a) :=
  ⟨fun _ ha => ha, fun a ha hpos => hdisjoint a hpos ha⟩

/-! ## Lasso states of a well-formed TGBA -/

/-- A `succs`-successor state of a well-formed TGBA's state also lies in its state set. -/
private theorem TGBA.WellFormed.succState_mem {tgba : TGBA α} (hwf : tgba.WellFormed) {q q' : Nat}
    (hq : tgba.states.contains q = true) (hsucc : q' ∈ tgba.succStates q) :
    tgba.states.contains q' = true := by
  obtain ⟨t, ht, rfl⟩ := Array.mem_map.mp hsucc
  exact hwf.succ_mem q t hq ht

/-- Every stem state of a `TAcceptingCycle` lies in a well-formed TGBA's state set. -/
theorem TAcceptingCycle.stem_states_mem {tgba : TGBA α} (hwf : tgba.WellFormed)
    (ac : TAcceptingCycle tgba.initialStates.toList tgba.succStates tgba.edgeMarks tgba.numAcceptSets) :
    ∀ (i : Nat) (hi : i < ac.stem.length), tgba.states.contains (ac.stem[i]'hi) = true :=
  chain_closure ac.stem (List.ne_nil_of_length_pos (by have := ac.stem_nonempty; omega))
    (hwf.initial_mem _ (Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp ac.stem_head_initial)))
    ac.stem_chain (fun _ _ hs ht => hwf.succState_mem hs ht)

/-- Every cycle state of a `TAcceptingCycle` lies in a well-formed TGBA's state set. -/
theorem TAcceptingCycle.cycle_states_mem {tgba : TGBA α} (hwf : tgba.WellFormed)
    (ac : TAcceptingCycle tgba.initialStates.toList tgba.succStates tgba.edgeMarks tgba.numAcceptSets) :
    ∀ (i : Nat) (hi : i < ac.cycle.length), tgba.states.contains (ac.cycle[i]'hi) = true := by
  have hsn := ac.stem_nonempty
  have hcn := ac.cycle_nonempty
  have hhead : tgba.states.contains (ac.cycle.head (List.ne_nil_of_length_pos (by omega))) = true := by
    rw [← ac.overlap]
    have hlast : ac.stem[ac.stem.length - 1]'(by omega) =
        ac.stem.getLast (List.ne_nil_of_length_pos (by omega)) := by
      rw [List.getLast_eq_getElem]
    rw [← hlast]
    exact ac.stem_states_mem hwf (ac.stem.length - 1) (by omega)
  exact chain_closure ac.cycle (List.ne_nil_of_length_pos (by omega)) hhead ac.cycle_chain
    (fun _ _ hs ht => hwf.succState_mem hs ht)

/-- Every edge of the lasso-derived run has both endpoints inside a well-formed TGBA's state set. -/
theorem TAcceptingCycle.run_states_mem {tgba : TGBA α} (hwf : tgba.WellFormed)
    (ac : TAcceptingCycle tgba.initialStates.toList tgba.succStates tgba.edgeMarks tgba.numAcceptSets)
    (n : Nat) :
    tgba.states.contains (tgba.toSpec.src (ac.toTValidLasso.run n)) = true ∧
    tgba.states.contains (tgba.toSpec.dst (ac.toTValidLasso.run n)) = true := by
  have hL := tgba.edgeWitness
  by_cases hs : n < (stemEdges tgba.edgeWitness.stepEdge ac.stem).length
  · have heq := TValidLasso.run_eq_stem ac.toTValidLasso n hs
    have hn1 : n + 1 < ac.stem.length := by
      have := stemEdges_length tgba.edgeWitness.stepEdge ac.stem; omega
    have hn : n < ac.stem.length := by omega
    rw [stemEdges_getElem tgba.edgeWitness.stepEdge ac.stem n hn1 hs] at heq
    rw [heq, (tgba.edgeWitness.stepEdge_spec (ac.stem_chain n hn1)).2.1,
      (tgba.edgeWitness.stepEdge_spec (ac.stem_chain n hn1)).2.2]
    exact ⟨ac.stem_states_mem hwf n hn, ac.stem_states_mem hwf (n + 1) hn1⟩
  · have heq := TValidLasso.run_eq_cycle ac.toTValidLasso n hs
    have hcnn : (ac.cycleE tgba.edgeWitness).length ≥ 1 := ac.toTValidLasso.cycle_nonempty
    have hcne : ac.cycleE tgba.edgeWitness ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hcov : ((ac.cycleE tgba.edgeWitness)[(n - (stemEdges tgba.edgeWitness.stepEdge ac.stem).length) %
        (ac.cycleE tgba.edgeWitness).length]'
        (Nat.mod_lt _ (by omega))) ∈ ac.cycleE tgba.edgeWitness :=
      List.getElem_mem _
    rw [heq]
    obtain ⟨i, hi, hsrc, hdst⟩ := cycleE_endpoints_mem tgba.edgeWitness ac hcov
    rw [hsrc, hdst]
    exact ⟨ac.cycle_states_mem hwf i hi,
      ac.cycle_states_mem hwf _ (Nat.mod_lt _ (by have := ac.cycle_nonempty; omega))⟩

/-! ## From an accepting run to a lasso -/

/-- The converse of `TAcceptingCycle.toTValidLasso`: an accepting run of `tgba.toSpec` yields a `TAcceptingCycle`. -/
theorem TGBA.exists_TAcceptingCycle_of_acceptingRun (tgba : TGBA α) (hwf : tgba.WellFormed)
    {σ : Lentil.exec (TGBA.Edge α)} (hrun : tgba.toSpec.isRun σ) (hacc : tgba.toSpec.isAcceptingRun σ) :
    ∃ _ac : TAcceptingCycle tgba.initialStates.toList tgba.succStates tgba.edgeMarks tgba.numAcceptSets,
      True := by
  obtain ⟨hinit, hstep⟩ := hrun
  refine exists_TAcceptingCycle_of_run (tgba.finiteReach hwf) (σ := fun n => (σ n).1) ?_ ?_ ?_
  · exact Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hinit)
  · intro n
    have hlink : (σ n).2.target = (σ (n + 1)).1 := (hstep n).2
    show (σ (n + 1)).1 ∈ tgba.succStates (σ n).1
    rw [← hlink]
    exact Array.mem_map.mpr ⟨(σ n).2, (hstep n).1, rfl⟩
  · intro m hm N
    obtain ⟨j, hj⟩ := hacc ⟨m, hm⟩ N
    exact ⟨N + j, by omega, Std.HashSet.mem_iff_contains.mpr
      ((TGBA.mem_edgeMarks_iff tgba _ _ m).mpr
        ⟨(σ (N + j)).2, (hstep (N + j)).1, (hstep (N + j)).2, hj⟩)⟩

/-- Every mark on an edge is one its witnessing transition carries, so a per-transition bound transfers. -/
theorem TGBA.edgeMarks_lt (tgba : TGBA α)
    (hbound : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets)
    (q q' m : Nat) (hm : m ∈ tgba.edgeMarks q q') : m < tgba.numAcceptSets := by
  obtain ⟨t, ht, -, htm⟩ := (TGBA.mem_edgeMarks_iff tgba q q' m).mp (Std.HashSet.mem_iff_contains.mp hm)
  exact hbound q t ht m (Std.HashSet.mem_iff_contains.mpr htm)

/-! ## Transitions some valuation takes -/

namespace TGBA

/-- No atom is required both true and false, so some valuation takes the transition. -/
def Transition.isConsistent (t : Transition α) : Bool :=
  !t.positiveProps.any t.negativeProps.contains

/-- The same automaton without the transitions no valuation takes. -/
@[expose] def consistentPart (tgba : TGBA α) : TGBA α :=
  { tgba with successors := tgba.successors.map fun _ ts => ts.filter (·.isConsistent) }

theorem getSuccessors_consistentPart (tgba : TGBA α) (q : Nat) :
    tgba.consistentPart.getSuccessors q = (tgba.getSuccessors q).filter (·.isConsistent) := by
  unfold consistentPart getSuccessors
  rw [Std.HashMap.getElem?_map]
  cases tgba.successors[q]? <;> simp

theorem consistentPart_wellFormed {tgba : TGBA α} (hwf : tgba.WellFormed) : tgba.consistentPart.WellFormed where
  initial_mem := hwf.initial_mem
  succ_mem q t hq ht := by
    rw [getSuccessors_consistentPart] at ht
    exact hwf.succ_mem q t hq (Array.mem_filter.mp ht).1
  marks_range q t hq ht := by
    rw [getSuccessors_consistentPart] at ht
    exact hwf.marks_range q t hq (Array.mem_filter.mp ht).1

variable [LawfulBEq α]

theorem Transition.disjoint_of_isConsistent {t : Transition α} (h : t.isConsistent = true) :
    ∀ a, t.positiveProps.contains a → t.negativeProps.contains a → False := by
  intro a hp hn
  simp only [Transition.isConsistent, Bool.not_eq_eq_eq_not, Bool.not_true,
    Std.HashSet.any_eq_false_iff_forall_mem] at h
  have := h a (Std.HashSet.mem_iff_contains.mpr hp)
  simp_all

theorem Transition.isConsistent_of_labelCompat {t : Transition α} {v : α → Prop}
    (h : (∀ a, t.positiveProps.contains a → v a) ∧ (∀ a, t.negativeProps.contains a → ¬ v a)) :
    t.isConsistent = true := by
  simp only [Transition.isConsistent, Bool.not_eq_eq_eq_not, Bool.not_true,
    Std.HashSet.any_eq_false_iff_forall_mem]
  intro a ha
  cases hn : t.negativeProps.contains a
  · rfl
  · exact absurd (h.1 a (Std.HashSet.mem_iff_contains.mp ha)) (h.2 a hn)

/-- Dropping the transitions no valuation takes changes the accepted language not at all. -/
theorem consistentPart_accepts (tgba : TGBA α) (ξ : OmegaWord α) :
    tgba.consistentPart.toSpec.accepts ξ ↔ tgba.toSpec.accepts ξ := by
  constructor
  · rintro ⟨σ, ⟨hinit, hstep⟩, hcompat, hacc⟩
    refine ⟨σ, ⟨hinit, fun n => ⟨?_, (hstep n).2⟩⟩, hcompat, hacc⟩
    have hv : (σ n).2 ∈ tgba.consistentPart.getSuccessors (σ n).1 := (hstep n).1
    rw [getSuccessors_consistentPart] at hv
    exact (Array.mem_filter.mp hv).1
  · rintro ⟨σ, ⟨hinit, hstep⟩, hcompat, hacc⟩
    refine ⟨σ, ⟨hinit, fun n => ⟨?_, (hstep n).2⟩⟩, hcompat, hacc⟩
    show (σ n).2 ∈ tgba.consistentPart.getSuccessors (σ n).1
    rw [getSuccessors_consistentPart]
    exact Array.mem_filter.mpr ⟨(hstep n).1, Transition.isConsistent_of_labelCompat (hcompat n)⟩

/-- An accepting cycle of the consistent part is read by the word taking each run transition's positive atoms. -/
theorem accepts_of_consistentPart_cycle (tgba : TGBA α)
    (ac : TAcceptingCycle tgba.consistentPart.initialStates.toList tgba.consistentPart.succStates
      tgba.consistentPart.edgeMarks tgba.consistentPart.numAcceptSets) :
    ∃ ξ, tgba.toSpec.accepts ξ := by
  refine ⟨fun n => canonicalTransLabel (ac.toTValidLasso.run n).2,
    (consistentPart_accepts tgba _).mp (ac.toTValidLasso.accepts_of_validLasso fun n => ?_)⟩
  have hv : (ac.toTValidLasso.run n).2 ∈ tgba.consistentPart.getSuccessors (ac.toTValidLasso.run n).1 :=
    ac.toTValidLasso.run_valid n
  rw [getSuccessors_consistentPart] at hv
  exact canonicalTransLabel_compat _ (Transition.disjoint_of_isConsistent (Array.mem_filter.mp hv).2)

end TGBA

end LTLLib
