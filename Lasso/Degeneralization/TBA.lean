module

/-
  Single-mark Transition-based Büchi Automaton (`TBA`) and the degeneralization of a TGBA into one.

  An acceptance counter tracks which mark to satisfy next, and acceptance stays on edges throughout, only the number of
  marks collapses to one. The state space is |TGBA| × max(1, k) for k marks.

  Defines:
  - `TBAState`: a TGBA state paired with an acceptance counter
  - `TBA`: the single-mark automaton, `TBA.toSpec` its `TOASpec`
  - `TBA.cachedEdgeMarks`: `edgeMarks` as a lookup in a precomputed table
  - `TGBA.degeneralize`: the degeneralization

  Proves:
  - `TBA.cachedEdgeMarks_contains_iff`: `cachedEdgeMarks` and `edgeMarks` contain the same marks

  References:
  - Baier, Katoen. Principles of Model Checking, Section 4.3.3.

  Sections:
  - Degeneralized state
  - Standard transition-based Büchi Automaton
  - Cached edge marks
  - Degeneralization
-/
public import Lasso.TGBA

public section

namespace Lasso

/-! ## Degeneralized state -/

/-- A `TBA` state after degeneralization: a TGBA state paired with an acceptance counter. -/
structure TBAState where
  tgbaState : Nat  -- Original TGBA state identifier.
  acceptIdx : Nat  -- Acceptance mark we're waiting to see next, in `[0, k)`.
deriving BEq, Hashable, Repr, Inhabited, DecidableEq

private theorem TBAState.beq_def (x y : TBAState) :
    (x == y) = (x.tgbaState == y.tgbaState && x.acceptIdx == y.acceptIdx) := rfl

instance : LawfulBEq TBAState where
  eq_of_beq {x y} h := by
    rw [TBAState.beq_def] at h
    simp [Bool.and_eq_true, beq_iff_eq] at h
    exact TBAState.mk.injEq .. |>.mpr h
  rfl {a} := by rw [TBAState.beq_def]; simp

instance : LawfulHashable TBAState where
  hash_eq {a b} h := by have := eq_of_beq h; subst this; rfl

instance : ToString TBAState where
  toString s := s!"({s.tgbaState}, {s.acceptIdx})"

/-! ## Standard transition-based Büchi Automaton -/

/-- A single labeled, marked transition of a `TBA`. -/
structure TBA.Transition (α : Type u) [BEq α] [Hashable α] where
  target : TBAState
  positiveProps : Std.HashSet α  -- propositions required true by the label
  negativeProps : Std.HashSet α  -- propositions required false by the label
  acceptMarks : Std.HashSet Nat  -- `⊆ {0}`, the single surviving mark after degeneralization

/-- A single-mark Transition-based Büchi Automaton, produced by degeneralizing a `TGBA`. -/
structure TBA (α : Type u) [BEq α] [Hashable α] where
  states : Std.HashSet TBAState
  initialStates : Std.HashSet TBAState
  successors : Std.HashMap TBAState (Array (TBA.Transition α))  -- keyed by source state
  numAcceptSets : Nat  -- always 1

namespace TBA

variable {α} [BEq α] [Hashable α]

@[expose] def numStates (tba : TBA α) : Nat := tba.states.size

/-- Outgoing transitions of a state. -/
@[expose] def getSuccessors (tba : TBA α) (s : TBAState) : Array (Transition α) :=
  tba.successors[s]?.getD #[]

@[expose] def isInitial (tba : TBA α) (s : TBAState) : Bool :=
  tba.initialStates.contains s

@[expose] def succStates (tba : TBA α) (s : TBAState) : Array TBAState :=
  (tba.getSuccessors s).map (·.target)

/-- Union of marks over every `s → s'` transition (there may be several parallel ones). -/
@[expose] def edgeMarks (tba : TBA α) (s s' : TBAState) : Std.HashSet Nat :=
  ((tba.getSuccessors s).filter (·.target == s')).foldl
    (init := Std.HashSet.emptyWithCapacity 0) fun acc t => acc.union t.acceptMarks

/-- Precomputed `(source, target) → marks` lookup over every transition. -/
@[expose] def edgeMarksTable (tba : TBA α) : Std.HashMap (TBAState × TBAState) (Std.HashSet Nat) :=
  (tba.successors.toList.flatMap fun sts => sts.2.toList.map fun t => ((sts.1, t.target), t.acceptMarks)).foldl
    (init := {}) fun m kv => m.insert kv.1 ((m.getD kv.1 (Std.HashSet.emptyWithCapacity 0)).union kv.2)

/-- `edgeMarks` as an O(1) lookup in `edgeMarksTable`. -/
@[expose] def cachedEdgeMarks (tba : TBA α) (s s' : TBAState) : Std.HashSet Nat :=
  tba.edgeMarksTable.getD (s, s') (Std.HashSet.emptyWithCapacity 0)

structure WellFormed (tba : TBA α) : Prop where
  initial_mem : ∀ s, tba.isInitial s → tba.states.contains s
  succ_mem : ∀ s t, tba.states.contains s → t ∈ tba.getSuccessors s → tba.states.contains t.target
  marks_range : ∀ s t, tba.states.contains s → t ∈ tba.getSuccessors s → ∀ m ∈ t.acceptMarks, m < tba.numAcceptSets

/-- A well-formed `TBA` has finitely many reachable states, bounded by its state set. -/
theorem finiteReach (tba : TBA α) (hwf : tba.WellFormed) :
    FiniteReach tba.initialStates.toList tba.succStates := by
  refine ⟨tba.states.toList, fun s hs => Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr ?_)⟩
  induction hs with
  | base hi =>
    exact hwf.initial_mem _ (by
      show tba.isInitial _ = true
      exact Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hi))
  | step _ hmem ih =>
    rename_i prev cur
    obtain ⟨t, ht, rfl⟩ := Array.mem_map.mp hmem
    exact hwf.succ_mem _ _ ih ht

/-- An edge of a `TBA`: the source state together with one of its outgoing transitions. -/
abbrev Edge (α : Type u) [BEq α] [Hashable α] := (_s : TBAState) × TBA.Transition α

/-- Convert a computational `TBA` to an abstract `TOASpec`. -/
@[expose] def toSpec (tba : TBA α) : TOASpec TBAState (Edge α) α tba.numAcceptSets where
  src e := e.1
  dst e := e.2.target
  valid e := e.2 ∈ tba.getSuccessors e.1
  initial s := tba.isInitial s
  labelCompat e v := (∀ a, e.2.positiveProps.contains a → v a) ∧
    (∀ a, e.2.negativeProps.contains a → ¬ v a)
  acceptMark i e := e.2.acceptMarks.contains i.val

end TBA

/-! ## Cached edge marks -/

private theorem TBA.mem_edgeMarks_iff {α : Type u} [BEq α] [Hashable α] (tba : TBA α) (s s' : TBAState) (m : Nat) :
    (tba.edgeMarks s s').contains m ↔
      ∃ t ∈ tba.getSuccessors s, t.target = s' ∧ t.acceptMarks.contains m := by
  have hfold : ∀ (l : List (TBA.Transition α)) (init : Std.HashSet Nat),
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
  rw [TBA.edgeMarks, ← Array.foldl_toList, hfold, Std.HashSet.contains_emptyWithCapacity]
  simp only [Bool.false_eq_true, false_or, ← Array.mem_def, Array.mem_filter, beq_iff_eq]
  grind

private theorem TBA.mem_edgeMarksTable_iff {α : Type u} [BEq α] [Hashable α]
    (tba : TBA α) (s s' : TBAState) (m : Nat) :
    (tba.edgeMarksTable.getD (s, s') (Std.HashSet.emptyWithCapacity 0)).contains m ↔
      ∃ t ∈ tba.getSuccessors s, t.target = s' ∧ t.acceptMarks.contains m := by
  have hfold : ∀ (l : List ((TBAState × TBAState) × Std.HashSet Nat))
      (init : Std.HashMap (TBAState × TBAState) (Std.HashSet Nat)),
      ((l.foldl (fun m kv => m.insert kv.1 ((m.getD kv.1 (Std.HashSet.emptyWithCapacity 0)).union kv.2))
        init).getD (s, s') (Std.HashSet.emptyWithCapacity 0)).contains m ↔
        (init.getD (s, s') (Std.HashSet.emptyWithCapacity 0)).contains m ∨
          ∃ kv ∈ l, kv.1 = (s, s') ∧ kv.2.contains m := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro init
      rw [List.foldl_cons, ih]
      by_cases hkey : a.1 = (s, s')
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
      · have hbeq : (a.1 == (s, s')) = false := by simpa using hkey
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
  rw [TBA.edgeMarksTable, hfold, Std.HashMap.getD_empty, Std.HashSet.contains_emptyWithCapacity]
  simp only [Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨kv, hkv, hkv1, hkv2⟩
    obtain ⟨sts, hsts, hkveq⟩ := List.mem_flatMap.mp hkv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hkveq
    simp only [Prod.mk.injEq] at hkv1
    obtain ⟨hs, hs'⟩ := hkv1
    subst hs
    have hget : tba.successors[sts.1]? = some sts.2 :=
      Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hsts
    have hsucc : tba.getSuccessors sts.1 = sts.2 := by simp [TBA.getSuccessors, hget]
    exact ⟨t, hsucc ▸ Array.mem_def.mpr ht, hs', hkv2⟩
  · rintro ⟨t, ht, ht', htm⟩
    have hex : tba.successors[s]? = some (tba.getSuccessors s) := by
      rcases hopt : tba.successors[s]? with _ | ts
      · exact absurd ht (by simp [TBA.getSuccessors, hopt])
      · simp [TBA.getSuccessors, hopt]
    exact ⟨((s, t.target), t.acceptMarks), List.mem_flatMap.mpr
      ⟨(s, tba.getSuccessors s), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hex,
        List.mem_map.mpr ⟨t, Array.mem_def.mp ht, rfl⟩⟩, by simp [ht'], htm⟩

/-- `cachedEdgeMarks` and `edgeMarks` contain the same marks. -/
theorem TBA.cachedEdgeMarks_contains_iff {α : Type u} [BEq α] [Hashable α]
    (tba : TBA α) (s s' : TBAState) (m : Nat) :
    (tba.cachedEdgeMarks s s').contains m ↔ (tba.edgeMarks s s').contains m := by
  rw [TBA.cachedEdgeMarks, TBA.mem_edgeMarksTable_iff, TBA.mem_edgeMarks_iff]

/-! ## Degeneralization -/

namespace TGBA

variable {α} [BEq α] [Hashable α]

/-- Degeneralize a TGBA to a single-mark `TBA` (Baier and Katoen, Section 4.3.3, transposed onto edges):
- States: `{(q, i) | q ∈ TGBA.states, 0 ≤ i < k}` where `k = max(1, numAcceptSets)`
- Initial: `{(q, 0) | q ∈ TGBA.initialStates}`
- Transitions: `(q, i) → (q', i')` for each `q →[marks] q'` in the TGBA, with `i' = (i + 1) % k` if `i ∈ marks`, else `i' = i`
- Accepting: the new edge carries the mark iff `i = 0` and the original carries mark `0`, or the TGBA has no marks at all -/
@[expose] def degeneralize (tgba : TGBA α) : TBA α :=
  let k := if tgba.numAcceptSets == 0 then 1 else tgba.numAcceptSets
  let totalStates := tgba.states.size * k

  -- Build all states
  let allStates := tgba.states.fold
    (init := Std.HashSet.emptyWithCapacity totalStates) fun acc q =>
      (List.range k).foldl (init := acc) fun acc i =>
        acc.insert { tgbaState := q, acceptIdx := i }

  -- Build initial states
  let initStates := tgba.initialStates.fold
    (init := Std.HashSet.emptyWithCapacity tgba.initialStates.size) fun acc q =>
      acc.insert { tgbaState := q, acceptIdx := 0 }

  -- Build transitions
  let succMap := tgba.states.fold
    (init := Std.HashMap.emptyWithCapacity totalStates) fun succMap q =>
      let qTrans := tgba.getSuccessors q
      (List.range k).foldl (init := succMap) fun succMap i =>
        let baState : TBAState := { tgbaState := q, acceptIdx := i }
        -- Compute next acceptance index, and whether this edge carries the single surviving mark
        let baTrans := qTrans.map fun t =>
          -- `(i + 1) % k` is `0` when `k = 1`, which covers `numAcceptSets = 0`
          let nextIdx := if t.acceptMarks.contains i then (i + 1) % k else i
          let marks := if tgba.numAcceptSets == 0 || (i == 0 && t.acceptMarks.contains 0)
            then Std.HashSet.emptyWithCapacity 1 |>.insert 0 else Std.HashSet.emptyWithCapacity 0
          ({ target := { tgbaState := t.target, acceptIdx := nextIdx },
             positiveProps := t.positiveProps, negativeProps := t.negativeProps,
             acceptMarks := marks } : TBA.Transition α)
        succMap.insert baState baTrans

  { states := allStates, initialStates := initStates, successors := succMap, numAcceptSets := 1 }

end TGBA

end Lasso
