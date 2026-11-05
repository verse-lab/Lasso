module

/-
  Bridge between the computational `TGBA.degeneralize` and the abstract `TOASpec.degeneralize`, giving
  `TBA.toSpec accepts ξ ↔ TGBA.toSpec accepts ξ`.

  Lemmas are stated over the clamped mark count `degK tgba` that `TGBA.degeneralize` uses. Only the composition with
  `TOASpec.degeneralize`, which needs `k > 0`, splits on `tgba.numAcceptSets = 0`.

  Proves:
  - `TGBA.degeneralize_states_contains`, `TGBA.degeneralize_initialStates_contains`: the (initial) states of the `TBA`
  - `TGBA.degeneralize_getSuccessors_mem`: the `TBA`'s transitions lift the TGBA's, with the counter and mark updated
  - `TGBA.degeneralize_wellFormed`: degeneralizing a well-formed TGBA yields a well-formed TBA
  - `TGBA.degeneralize_bridge`: for `numAcceptSets > 0`, the `TBA` and `TOASpec.degeneralize` accept the same words
  - `TGBA.degeneralize_accepts_zero`: for `numAcceptSets = 0`, the `TBA` and the `TGBA` accept the same words
  - `TGBA.degeneralize_accepts_any`: the `TBA` and the `TGBA` it comes from accept the same words

  Sections:
  - Generic fold helpers
  - The clamped mark count
  - Initial states characterization
  - States characterization
  - Successor characterization
  - Well-formedness is preserved by degeneralize
  - Main bridge
  - The `numAcceptSets = 0` case
  - Unconditional wrappers
-/
public import Lasso.Degeneralization.TAcceptance
public import Lasso.Degeneralization.TBA

public section

namespace Lasso

variable {α : Type u} [BEq α] [Hashable α]

/-! ## Generic fold helpers -/

private theorem HashSet_foldl_cond_insert_contains
    [BEq γ] [Hashable γ] [LawfulBEq γ] [LawfulHashable γ]
    (l : List β) (p : β → Bool) (f : β → γ) (init : Std.HashSet γ) (q : γ) :
    (l.foldl (fun acc x => if p x then acc.insert (f x) else acc) init).contains q =
      (init.contains q || l.any (fun x => p x && (f x == q))) := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.any_cons]
    split
    · next hp =>
      rw [ih]; simp only [Std.HashSet.contains_insert, hp, Bool.true_and]; ac_rfl
    · next hp =>
      rw [ih]; simp only [Bool.not_eq_true] at hp; simp [hp]

private theorem HashSet_foldl_map_insert_contains
    [BEq γ] [Hashable γ] [LawfulBEq γ] [LawfulHashable γ]
    (l : List β) (f : β → γ) (init : Std.HashSet γ) (q : γ) :
    (l.foldl (fun acc x => acc.insert (f x)) init).contains q =
      (init.contains q || l.any (fun x => f x == q)) := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih]; simp only [Std.HashSet.contains_insert]; ac_rfl

private theorem HashMap_foldl_insert_preserves
    [BEq γ] [Hashable γ] [LawfulBEq γ] [LawfulHashable γ]
    {β : Type w} (l : List β) (key : β → γ) (val : β → ε)
    (init : Std.HashMap γ ε) (q : γ)
    (h_no_key : ∀ x ∈ l, (key x == q) = false) :
    (l.foldl (fun acc x => acc.insert (key x) (val x)) init)[q]? = init[q]? := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun x hx => h_no_key x (List.mem_cons_of_mem _ hx)),
        Std.HashMap.getElem?_insert]
    simp [h_no_key hd List.mem_cons_self]

private theorem HashMap_foldl_insert_of_mem
    [BEq γ] [Hashable γ] [LawfulBEq γ] [LawfulHashable γ]
    {β : Type w} (l : List β) (key : β → γ) (val : β → ε)
    (init : Std.HashMap γ ε) (x : β)
    (hmem : x ∈ l) (hkey : key x = q)
    (h_distinct : l.Pairwise (fun a b => (key a == key b) = false)) :
    (l.foldl (fun acc y => acc.insert (key y) (val y)) init)[q]? = some (val x) := by
  subst hkey
  induction l generalizing init with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    obtain ⟨h_all, h_pw_tl⟩ := List.pairwise_cons.mp h_distinct
    cases hmem with
    | head =>
      rw [HashMap_foldl_insert_preserves tl key val _ (key x)
        (fun y hy => by rw [BEq.comm]; exact h_all y hy)]
      rw [Std.HashMap.getElem?_insert]; simp
    | tail _ hmem_tl =>
      exact ih _ hmem_tl h_pw_tl

/-! ## The clamped mark count -/

/-- The mark count `max(1, numAcceptSets)` that `TGBA.degeneralize` clamps to. -/
def degK (tgba : TGBA α) : Nat := if tgba.numAcceptSets == 0 then 1 else tgba.numAcceptSets

private theorem degK_pos (tgba : TGBA α) : 0 < degK tgba := by
  unfold degK
  split
  · exact Nat.one_pos
  · next h => exact Nat.pos_of_ne_zero (by simpa using h)

private theorem degK_eq_of_pos {tgba : TGBA α} (hk : tgba.numAcceptSets > 0) :
    degK tgba = tgba.numAcceptSets := by
  have : (tgba.numAcceptSets == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  simp [degK, this]

/-! ## Initial states characterization -/

-- A degeneralized state is initial iff its `tgbaState` is initial in `tgba` and its counter is 0.
theorem TGBA.degeneralize_initialStates_contains (tgba : TGBA α) (s : TBAState) :
    (tgba.degeneralize).initialStates.contains s ↔
      tgba.initialStates.contains s.tgbaState ∧ s.acceptIdx = 0 := by
  simp only [TGBA.degeneralize, Std.HashSet.fold_eq_foldl_toList]
  rw [HashSet_foldl_map_insert_contains]
  simp only [Std.HashSet.contains_emptyWithCapacity, Bool.false_or]
  rw [List.any_eq_true]
  constructor
  · rintro ⟨q, hq, heq⟩
    rw [beq_iff_eq] at heq
    have h1 : s.tgbaState = q := by rw [← heq]
    have h2 : s.acceptIdx = 0 := by rw [← heq]
    exact ⟨h1 ▸ (Std.HashSet.mem_toList.mp hq |> Std.HashSet.mem_iff_contains.mp), h2⟩
  · rintro ⟨hmem, hidx⟩
    exact ⟨s.tgbaState,
      Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hmem),
      by rw [beq_iff_eq]; cases s; simp_all⟩

/-! ## States characterization -/

/-- The fold building `allStates` contains `s` iff `init` did or `s.tgbaState ∈ l` with `s.acceptIdx < k`. -/
private theorem outer_fold_states_mem
    (k : Nat) (l : List Nat) (init : Std.HashSet TBAState) (s : TBAState) :
    (l.foldl (init := init) fun acc tgbaState =>
      (List.range k).foldl (init := acc) fun acc i =>
        acc.insert ({ tgbaState, acceptIdx := i } : TBAState)).contains s = true ↔
      init.contains s = true ∨ (s.tgbaState ∈ l ∧ s.acceptIdx < k) := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    have hinner : ((List.range k).foldl (init := init) fun acc i =>
        acc.insert ({ tgbaState := hd, acceptIdx := i } : TBAState)).contains s = true ↔
        init.contains s = true ∨ (hd = s.tgbaState ∧ s.acceptIdx < k) := by
      rw [HashSet_foldl_map_insert_contains]
      simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range]
      constructor
      · rintro (h | ⟨i, hi, heq⟩)
        · exact Or.inl h
        · rw [beq_iff_eq] at heq
          exact Or.inr ⟨(TBAState.mk.inj heq).1, heq ▸ hi⟩
      · rintro (h | ⟨heq, hi⟩)
        · exact Or.inl h
        · exact Or.inr ⟨s.acceptIdx, hi, by rw [beq_iff_eq]; cases s; simp_all⟩
    rw [hinner]; grind

/-- `(tgba.degeneralize).states` contains `s` iff `s.tgbaState ∈ tgba.states` and `s.acceptIdx` is within range. -/
theorem TGBA.degeneralize_states_contains (tgba : TGBA α) (s : TBAState) :
    (tgba.degeneralize).states.contains s = true ↔
      tgba.states.contains s.tgbaState = true ∧ s.acceptIdx < degK tgba := by
  simp only [TGBA.degeneralize, Std.HashSet.fold_eq_foldl_toList]
  rw [outer_fold_states_mem]
  simp only [Std.HashSet.contains_emptyWithCapacity, Bool.false_eq_true, false_or]
  rw [show s.tgbaState ∈ tgba.states.toList ↔ tgba.states.contains s.tgbaState = true from
    ⟨fun h => Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp h),
     fun h => Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr h)⟩]
  rfl

/-! ## Successor characterization -/

/-- Keys produced by the inner fold are pairwise distinct (same tgbaState, different acceptIdx). -/
private theorem range_keys_pairwise_distinct (tgbaState : Nat) (k : Nat) :
    (List.range k).Pairwise (fun a b =>
      (({ tgbaState, acceptIdx := a } : TBAState) ==
       { tgbaState, acceptIdx := b }) = false) := by
  exact List.nodup_range.imp (fun {a b} (h : a ≠ b) => by
    simp only [beq_eq_false_iff_ne]; intro heq; exact h (TBAState.mk.inj heq).2)

/-- Keys from different tgbaStates are never equal to a key with a given tgbaState. -/
private theorem key_ne_of_tgbaState_ne (tgbaState : Nat) (i : Nat) (s : TBAState)
    (hne : s.tgbaState ≠ tgbaState) :
    (({ tgbaState, acceptIdx := i } : TBAState) == s) = false := by
  simp only [beq_eq_false_iff_ne]
  intro h; exact hne (h ▸ rfl)

/-- Compute the successor transition array for a single (tgbaState, i) pair. -/
private def computeTBASuccs (tgba : TGBA α) (q i k : Nat) : Array (TBA.Transition α) :=
  (tgba.getSuccessors q).map fun t =>
    let nextIdx := if t.acceptMarks.contains i then (i + 1) % k else i
    let marks := if tgba.numAcceptSets == 0 || (i == 0 && t.acceptMarks.contains 0)
      then Std.HashSet.emptyWithCapacity 1 |>.insert 0 else Std.HashSet.emptyWithCapacity 0
    ({ target := { tgbaState := t.target, acceptIdx := nextIdx },
       positiveProps := t.positiveProps, negativeProps := t.negativeProps,
       acceptMarks := marks } : TBA.Transition α)

/-- Membership in `computeTBASuccs` characterized in terms of TGBA transitions and counter update. -/
private theorem mem_computeTBASuccs (tgba : TGBA α) (q i k : Nat) (t' : TBA.Transition α) :
    t' ∈ computeTBASuccs tgba q i k ↔
      ∃ t ∈ tgba.getSuccessors q,
        t'.target = ({ tgbaState := t.target, acceptIdx :=
          if t.acceptMarks.contains i then (i + 1) % k else i } : TBAState) ∧
        t'.positiveProps = t.positiveProps ∧ t'.negativeProps = t.negativeProps ∧
        t'.acceptMarks = (if tgba.numAcceptSets == 0 || (i == 0 && t.acceptMarks.contains 0)
          then Std.HashSet.emptyWithCapacity 1 |>.insert 0 else Std.HashSet.emptyWithCapacity 0) := by
  simp only [computeTBASuccs, Array.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl, rfl, rfl, rfl⟩
  · rintro ⟨t, ht, h1, h2, h3, h4⟩
    refine ⟨t, ht, ?_⟩
    cases t'
    simp_all

/-- The inner fold over `List.range k` inserts an entry per counter value of `q` and preserves every other key. -/
private theorem inner_range_fold
    (tgba : TGBA α) (q : Nat) (k : Nat)
    (succMap : Std.HashMap TBAState (Array (TBA.Transition α)))
    (s : TBAState) :
    let succMap' := (List.range k).foldl (init := succMap) fun succMap i =>
      succMap.insert { tgbaState := q, acceptIdx := i } (computeTBASuccs tgba q i k)
    (s.tgbaState ≠ q → succMap'[s]? = succMap[s]?) ∧
    (s.tgbaState = q → s.acceptIdx < k →
      succMap'[s]? = some (computeTBASuccs tgba q s.acceptIdx k)) ∧
    (s.tgbaState = q → ¬(s.acceptIdx < k) → succMap'[s]? = succMap[s]?) := by
  refine ⟨fun hne => ?_, fun heq hi => ?_, fun heq hni => ?_⟩
  · exact HashMap_foldl_insert_preserves (List.range k)
      (fun i => { tgbaState := q, acceptIdx := i })
      (fun i => computeTBASuccs tgba q i k)
      succMap s
      (fun i _ => key_ne_of_tgbaState_ne q i s hne)
  · have hmem : s.acceptIdx ∈ List.range k := List.mem_range.mpr hi
    have hkey : ({ tgbaState := q, acceptIdx := s.acceptIdx } : TBAState) = s := by
      cases s; simp_all
    exact HashMap_foldl_insert_of_mem (List.range k)
      (fun i => { tgbaState := q, acceptIdx := i })
      (fun i => computeTBASuccs tgba q i k)
      succMap s.acceptIdx hmem hkey
      (range_keys_pairwise_distinct q k)
  · exact HashMap_foldl_insert_preserves (List.range k)
      (fun i => { tgbaState := q, acceptIdx := i })
      (fun i => computeTBASuccs tgba q i k)
      succMap s
      (fun i hi_mem => by
        simp only [beq_eq_false_iff_ne]
        intro h; exact hni (by rw [← (TBAState.mk.inj h).2]; exact List.mem_range.mp hi_mem))

/-- The double fold maps `⟨q, i⟩` with `q ∈ l` and `i < k` to its computed successors, and keeps every other key. -/
private theorem outer_fold_successors
    (tgba : TGBA α) (k : Nat) (l : List Nat) (init : Std.HashMap TBAState (Array (TBA.Transition α)))
    (s : TBAState)
    (h_distinct : l.Pairwise (· ≠ ·)) :
    let succMap := l.foldl (init := init) fun succMap q =>
      (List.range k).foldl (init := succMap) fun succMap i =>
        succMap.insert ⟨q, i⟩ (computeTBASuccs tgba q i k)
    (s.tgbaState ∈ l → s.acceptIdx < k →
      succMap[s]? = some (computeTBASuccs tgba s.tgbaState s.acceptIdx k)) ∧
    (s.tgbaState ∉ l → succMap[s]? = init[s]?) ∧
    (s.tgbaState ∈ l → ¬(s.acceptIdx < k) → succMap[s]? = init[s]?) := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨h_all, h_pw_tl⟩ := List.pairwise_cons.mp h_distinct
    have inner := inner_range_fold tgba hd k init s
    let init' := (List.range k).foldl (init := init) fun succMap i =>
      succMap.insert ({ tgbaState := hd, acceptIdx := i } : TBAState)
        (computeTBASuccs tgba hd i k)
    have ih_inst := ih init' h_pw_tl
    simp only [List.foldl_cons, List.mem_cons] at *
    refine ⟨fun h hi => ?_, fun hni => ?_, fun h hni => ?_⟩
    · rcases h with rfl | hmem_tl
      · have hni : s.tgbaState ∉ tl := fun h => absurd rfl (h_all s.tgbaState h)
        rw [ih_inst.2.1 hni]
        exact inner.2.1 rfl hi
      · exact ih_inst.1 hmem_tl hi
    · simp only [_root_.not_or] at hni
      rw [ih_inst.2.1 hni.2, inner.1 hni.1]
    · rcases h with rfl | hmem_tl
      · have hni_tl : s.tgbaState ∉ tl := fun h => absurd rfl (h_all s.tgbaState h)
        rw [ih_inst.2.1 hni_tl, inner.2.2 rfl hni]
      · have hne : s.tgbaState ≠ hd := Ne.symm (h_all s.tgbaState hmem_tl)
        rw [ih_inst.2.2 hmem_tl hni, inner.1 hne]

/-- `tgba.degeneralize`'s successors HashMap unfolds to the double fold above. -/
private theorem degeneralize_successors_eq (tgba : TGBA α) :
    (tgba.degeneralize).successors =
      tgba.states.toList.foldl (init := Std.HashMap.emptyWithCapacity (tgba.states.size * degK tgba))
        fun succMap q =>
          (List.range (degK tgba)).foldl (init := succMap) fun succMap i =>
            succMap.insert ⟨q, i⟩ (computeTBASuccs tgba q i (degK tgba)) := by
  simp only [TGBA.degeneralize, degK, computeTBASuccs, Std.HashSet.fold_eq_foldl_toList]

/-- `t'` leaves `s` in the `TBA` iff `s` is a state and `t'` lifts a TGBA transition, with counter and mark updated. -/
theorem TGBA.degeneralize_getSuccessors_mem (tgba : TGBA α) (s : TBAState) (t' : TBA.Transition α) :
    t' ∈ (tgba.degeneralize).getSuccessors s ↔
      tgba.states.contains s.tgbaState ∧ s.acceptIdx < degK tgba ∧
      ∃ t ∈ tgba.getSuccessors s.tgbaState,
        t'.target = ({ tgbaState := t.target, acceptIdx :=
          if t.acceptMarks.contains s.acceptIdx
            then (s.acceptIdx + 1) % degK tgba else s.acceptIdx } : TBAState) ∧
        t'.positiveProps = t.positiveProps ∧ t'.negativeProps = t.negativeProps ∧
        t'.acceptMarks = (if tgba.numAcceptSets == 0 || (s.acceptIdx == 0 && t.acceptMarks.contains 0)
          then Std.HashSet.emptyWithCapacity 1 |>.insert 0 else Std.HashSet.emptyWithCapacity 0) := by
  simp only [TBA.getSuccessors]
  rw [degeneralize_successors_eq]
  have h_distinct : tgba.states.toList.Pairwise (· ≠ ·) :=
    (Std.HashSet.distinct_toList (m := tgba.states)).imp
      (fun h => by simp [beq_eq_false_iff_ne] at h; exact h)
  have h_fold := outer_fold_successors tgba (degK tgba) tgba.states.toList
    (Std.HashMap.emptyWithCapacity (tgba.states.size * degK tgba)) s h_distinct
  have mem_iff : tgba.states.contains s.tgbaState ↔ s.tgbaState ∈ tgba.states.toList :=
    ⟨fun h => Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr h),
     fun h => Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp h)⟩
  by_cases hmem : tgba.states.contains s.tgbaState <;>
    by_cases hidx : s.acceptIdx < degK tgba
  · rw [h_fold.1 (mem_iff.mp hmem) hidx]
    simp only [Option.getD_some]
    rw [mem_computeTBASuccs]
    constructor
    · rintro ⟨t, ht, h1, h2, h3, h4⟩; exact ⟨hmem, hidx, t, ht, h1, h2, h3, h4⟩
    · rintro ⟨_, _, t, ht, h1, h2, h3, h4⟩; exact ⟨t, ht, h1, h2, h3, h4⟩
  · rw [h_fold.2.2 (mem_iff.mp hmem) hidx]
    simp only [Std.HashMap.getElem?_emptyWithCapacity, Option.getD_none,
               Array.not_mem_empty, false_iff, not_and]
    intro _ h; exact absurd h hidx
  · rw [h_fold.2.1 (fun h => hmem (mem_iff.mpr h))]
    simp only [Std.HashMap.getElem?_emptyWithCapacity, Option.getD_none,
               Array.not_mem_empty, false_iff, not_and]
    intro h; exact absurd h hmem
  · rw [h_fold.2.1 (fun h => hmem (mem_iff.mpr h))]
    simp only [Std.HashMap.getElem?_emptyWithCapacity, Option.getD_none,
               Array.not_mem_empty, false_iff, not_and]
    intro h; exact absurd h hmem

/-! ## Well-formedness is preserved by degeneralize -/

/-- Degeneralizing a well-formed TGBA yields a well-formed TBA. -/
theorem TGBA.degeneralize_wellFormed (tgba : TGBA α) (hwf : tgba.WellFormed) : (tgba.degeneralize).WellFormed where
  initial_mem s hs := by
    obtain ⟨h1, h2⟩ := (TGBA.degeneralize_initialStates_contains tgba s).mp hs
    exact (TGBA.degeneralize_states_contains tgba s).mpr ⟨hwf.initial_mem s.tgbaState h1, h2 ▸ degK_pos tgba⟩
  succ_mem s t' hs hsucc := by
    obtain ⟨h1, h2⟩ := (TGBA.degeneralize_states_contains tgba s).mp hs
    obtain ⟨_, _, t, ht, htarget, _, _, _⟩ := (TGBA.degeneralize_getSuccessors_mem tgba s t').mp hsucc
    refine (TGBA.degeneralize_states_contains tgba t'.target).mpr ⟨?_, ?_⟩
    · rw [htarget]; exact hwf.succ_mem s.tgbaState t h1 ht
    · rw [htarget]; split
      · exact Nat.mod_lt _ (degK_pos tgba)
      · exact h2
  marks_range s t' hs hsucc m hm := by
    obtain ⟨_, _, t, ht, _, _, _, hmarks⟩ := (TGBA.degeneralize_getSuccessors_mem tgba s t').mp hsucc
    rw [hmarks] at hm
    split at hm
    · have h0 : 0 = m := by simpa using hm
      show m < 1
      omega
    · simp at hm

/-! ## Main bridge -/

/-- `TGBA.degeneralize_getSuccessors_mem` for `numAcceptSets > 0`, stated over `numAcceptSets` instead of `degK`. -/
private theorem degeneralize_getSuccessors_mem' (tgba : TGBA α) (hk : tgba.numAcceptSets > 0)
    (s : TBAState) (t' : TBA.Transition α) :
    t' ∈ (tgba.degeneralize).getSuccessors s ↔
      tgba.states.contains s.tgbaState ∧ s.acceptIdx < tgba.numAcceptSets ∧
      ∃ t ∈ tgba.getSuccessors s.tgbaState,
        t'.target = ({ tgbaState := t.target, acceptIdx :=
          if t.acceptMarks.contains s.acceptIdx
            then (s.acceptIdx + 1) % tgba.numAcceptSets else s.acceptIdx } : TBAState) ∧
        t'.positiveProps = t.positiveProps ∧ t'.negativeProps = t.negativeProps ∧
        t'.acceptMarks = (if s.acceptIdx == 0 && t.acceptMarks.contains 0
          then Std.HashSet.emptyWithCapacity 1 |>.insert 0 else Std.HashSet.emptyWithCapacity 0) := by
  have hne : (tgba.numAcceptSets == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  rw [TGBA.degeneralize_getSuccessors_mem, degK_eq_of_pos hk]
  simp only [hne, Bool.false_or]

-- Every state visited by an abstract run of `tgba.toSpec.degeneralize hk` has its TGBA component in `tgba.states`.
private theorem run_states_mem (tgba : TGBA α) (hwf : tgba.WellFormed)
    (σ' : Nat → TGBA.Edge α × Fin tgba.numAcceptSets)
    (hinit : tgba.isInitial (σ' 0).1.1)
    (hstep : ∀ n, (σ' n).1.2 ∈ tgba.getSuccessors (σ' n).1.1 ∧ (σ' n).1.2.target = (σ' (n + 1)).1.1) :
    ∀ n, tgba.states.contains (σ' n).1.1 := by
  intro n
  induction n with
  | zero => exact hwf.initial_mem _ hinit
  | succ n ih =>
    have := hwf.succ_mem _ _ ih (hstep n).1
    rwa [(hstep n).2] at this

/-- The computational `TBA` and the abstract degeneralized automaton accept the same ω-words. -/
theorem TGBA.degeneralize_bridge [LawfulBEq α] [LawfulHashable α]
    (tgba : TGBA α) (hk : tgba.numAcceptSets > 0) (hwf : tgba.WellFormed) (ξ : OmegaWord α) :
    (tgba.degeneralize).toSpec.accepts ξ ↔ (tgba.toSpec.degeneralize hk).accepts ξ := by
  constructor
  · -- Forward: TBA.toSpec accepts → TOASpec.degeneralize accepts
    rintro ⟨σ, ⟨hinit, hstep⟩, hcompat, hacc⟩
    simp only [TBA.toSpec, TOASpec.runCompatible, TOASpec.isAcceptingRun] at hinit hstep hcompat hacc
    have hchar := fun n => (degeneralize_getSuccessors_mem' tgba hk (σ n).1 (σ n).2).mp (hstep n).1
    let t : Nat → TGBA.Transition α := fun n => Classical.choose (hchar n).2.2
    have ht_mem : ∀ n, t n ∈ tgba.getSuccessors (σ n).1.tgbaState := fun n => (Classical.choose_spec (hchar n).2.2).1
    have ht_target : ∀ n, (σ n).2.target = ({ tgbaState := (t n).target, acceptIdx := if (t n).acceptMarks.contains (σ n).1.acceptIdx then ((σ n).1.acceptIdx + 1) % tgba.numAcceptSets else (σ n).1.acceptIdx } : TBAState) :=
      fun n => (Classical.choose_spec (hchar n).2.2).2.1
    have ht_pos : ∀ n, (σ n).2.positiveProps = (t n).positiveProps :=
      fun n => (Classical.choose_spec (hchar n).2.2).2.2.1
    have ht_neg : ∀ n, (σ n).2.negativeProps = (t n).negativeProps :=
      fun n => (Classical.choose_spec (hchar n).2.2).2.2.2.1
    have ht_marks : ∀ n, (σ n).2.acceptMarks = (if (σ n).1.acceptIdx == 0 && (t n).acceptMarks.contains 0
        then Std.HashSet.emptyWithCapacity 1 |>.insert 0 else Std.HashSet.emptyWithCapacity 0) :=
      fun n => (Classical.choose_spec (hchar n).2.2).2.2.2.2
    have hidx_next : ∀ n, (σ (n + 1)).1.tgbaState = (t n).target ∧
        (σ (n + 1)).1.acceptIdx = (if (t n).acceptMarks.contains (σ n).1.acceptIdx
          then ((σ n).1.acceptIdx + 1) % tgba.numAcceptSets else (σ n).1.acceptIdx) := by
      intro n
      have heq : (σ n).2.target = (σ (n + 1)).1 := (hstep n).2
      rw [ht_target n] at heq
      exact ⟨congrArg TBAState.tgbaState heq |>.symm, congrArg TBAState.acceptIdx heq |>.symm⟩
    have hidx_bound : ∀ n, (σ n).1.acceptIdx < tgba.numAcceptSets := fun n => (hchar n).2.1
    refine ⟨fun n => (⟨(σ n).1.tgbaState, t n⟩, ⟨(σ n).1.acceptIdx, hidx_bound n⟩), ⟨?_, ?_⟩, ?_, ?_⟩
    · -- Initial
      simp only [TOASpec.degeneralize, TGBA.toSpec]
      obtain ⟨hi, hz⟩ := (TGBA.degeneralize_initialStates_contains tgba (σ 0).1).mp hinit
      exact ⟨hi, Fin.ext hz⟩
    · -- Transitions
      intro n
      simp only [TOASpec.degeneralize, TGBA.toSpec, TOASpec.counterStep]
      obtain ⟨h1, h2⟩ := hidx_next n
      refine ⟨ht_mem n, Prod.ext h1.symm (Fin.ext ?_)⟩
      dsimp only
      -- The abstract counter and executable transition use different Decidable instances.
      by_cases hc : (t n).acceptMarks.contains (σ n).1.acceptIdx = true
      · rw (transparency := .default) [ite_eq_left hc] at h2 ⊢
        exact h2.symm
      · rw (transparency := .default) [ite_eq_right hc] at h2 ⊢
        exact h2.symm
    · -- Compatibility
      intro n
      simp only [TOASpec.degeneralize, TGBA.toSpec]
      rw [← ht_pos n, ← ht_neg n]
      exact hcompat n
    · -- Accepting
      intro i n
      obtain ⟨j, hj⟩ := hacc ⟨0, Nat.one_pos⟩ n
      rw [ht_marks (n + j)] at hj
      simp only [TOASpec.degeneralize, TGBA.toSpec]
      by_cases hcase : (σ (n + j)).1.acceptIdx == 0 && (t (n + j)).acceptMarks.contains 0
      · simp only [Bool.and_eq_true, beq_iff_eq] at hcase
        exact ⟨j, Fin.ext hcase.1, hcase.2⟩
      · simp [hcase] at hj
  · -- Backward: TOASpec.degeneralize accepts → TBA.toSpec accepts
    rintro ⟨σ', ⟨hinit', hstep'⟩, hcompat', hacc'⟩
    simp only [TOASpec.degeneralize, TGBA.toSpec, TOASpec.counterStep, TOASpec.runCompatible,
      TOASpec.isAcceptingRun] at hinit' hstep' hcompat' hacc'
    have hinit0 : tgba.isInitial (σ' 0).1.1 := hinit'.1
    have hstep0 : ∀ n, (σ' n).1.2 ∈ tgba.getSuccessors (σ' n).1.1 ∧ (σ' n).1.2.target = (σ' (n + 1)).1.1 :=
      fun n => ⟨(hstep' n).1, congrArg Prod.fst (hstep' n).2⟩
    have h_in := run_states_mem tgba hwf σ' hinit0 hstep0
    let σ : Nat → TBA.Edge α := fun n => ⟨{ tgbaState := (σ' n).1.1, acceptIdx := (σ' n).2.val },
      { target := { tgbaState := (σ' n).1.2.target, acceptIdx :=
          if (σ' n).1.2.acceptMarks.contains (σ' n).2.val then ((σ' n).2.val + 1) % tgba.numAcceptSets
          else (σ' n).2.val },
        positiveProps := (σ' n).1.2.positiveProps, negativeProps := (σ' n).1.2.negativeProps,
        acceptMarks := if (σ' n).2.val == 0 && (σ' n).1.2.acceptMarks.contains 0
          then Std.HashSet.emptyWithCapacity 1 |>.insert 0 else Std.HashSet.emptyWithCapacity 0 }⟩
    refine ⟨σ, ⟨?_, ?_⟩, ?_, ?_⟩
    · -- Initial
      simp only [TBA.toSpec, TBA.isInitial]
      rw [show (σ 0).1 = ({ tgbaState := (σ' 0).1.1, acceptIdx := (σ' 0).2.val } : TBAState) from rfl,
        TGBA.degeneralize_initialStates_contains]
      exact ⟨hinit0, congrArg Fin.val hinit'.2⟩
    · -- Transitions
      intro n
      simp only [TBA.toSpec]
      refine ⟨?_, ?_⟩
      · rw [degeneralize_getSuccessors_mem' tgba hk]
        exact ⟨h_in n, (σ' n).2.isLt, (σ' n).1.2, (hstep' n).1, rfl, rfl, rfl, rfl⟩
      · have h2 := (hstep' n).2
        rw [Prod.mk.injEq] at h2
        obtain ⟨h1, hc2⟩ := h2
        show ({ tgbaState := (σ' n).1.2.target, acceptIdx :=
            if (σ' n).1.2.acceptMarks.contains (σ' n).2.val then ((σ' n).2.val + 1) % tgba.numAcceptSets
            else (σ' n).2.val } : TBAState) =
          { tgbaState := (σ' (n + 1)).1.1, acceptIdx := (σ' (n + 1)).2.val }
        rw [h1]
        congr 1
        have hc := congrArg Fin.val hc2
        by_cases hm : (σ' n).1.2.acceptMarks.contains (σ' n).2.val = true
        · rw (transparency := .default) [ite_eq_left hm] at hc ⊢
          exact hc
        · rw (transparency := .default) [ite_eq_right hm] at hc ⊢
          exact hc
    · -- Compatibility
      intro n
      simp only [TBA.toSpec]
      exact hcompat' n
    · -- Accepting
      intro i n
      have hi0 : i.val = 0 := by have h : i.val < 1 := i.isLt; omega
      obtain ⟨j, hj⟩ := hacc' ⟨0, Nat.one_pos⟩ n
      refine ⟨j, ?_⟩
      simp only [TBA.toSpec, hi0]
      have hc0 : (σ' (n + j)).2.val = 0 := congrArg Fin.val hj.1
      have hm0 : (σ' (n + j)).1.2.acceptMarks.contains 0 = true := hj.2
      show (0 : Nat) ∈ (if (σ' (n + j)).2.val == 0 && (σ' (n + j)).1.2.acceptMarks.contains 0
        then Std.HashSet.emptyWithCapacity 1 |>.insert 0 else Std.HashSet.emptyWithCapacity 0)
      rw [hc0, hm0]
      simp

/-! ## The `numAcceptSets = 0` case -/

/-- For `numAcceptSets = 0`, where both acceptance conditions are trivial, the `TBA` and the `TGBA` accept the same ω-words. -/
theorem TGBA.degeneralize_accepts_zero [LawfulBEq α] [LawfulHashable α] (tgba : TGBA α) (h0 : tgba.numAcceptSets = 0)
    (hwf : tgba.WellFormed) (ξ : OmegaWord α) :
    (tgba.degeneralize).toSpec.accepts ξ ↔ tgba.toSpec.accepts ξ := by
  have hdegK : degK tgba = 1 := by simp [degK, h0]
  constructor
  · rintro ⟨σ, ⟨hinit, hstep⟩, hcompat, -⟩
    simp only [TBA.toSpec] at hinit hstep hcompat
    have hchar := fun n => (TGBA.degeneralize_getSuccessors_mem tgba (σ n).1 (σ n).2).mp (hstep n).1
    let t : Nat → TGBA.Transition α := fun n => Classical.choose (hchar n).2.2
    have ht_mem : ∀ n, t n ∈ tgba.getSuccessors (σ n).1.tgbaState := fun n => (Classical.choose_spec (hchar n).2.2).1
    have ht_target : ∀ n, (σ n).2.target = ({ tgbaState := (t n).target, acceptIdx := if (t n).acceptMarks.contains (σ n).1.acceptIdx then ((σ n).1.acceptIdx + 1) % degK tgba else (σ n).1.acceptIdx } : TBAState) :=
      fun n => (Classical.choose_spec (hchar n).2.2).2.1
    have ht_pos : ∀ n, (σ n).2.positiveProps = (t n).positiveProps :=
      fun n => (Classical.choose_spec (hchar n).2.2).2.2.1
    have ht_neg : ∀ n, (σ n).2.negativeProps = (t n).negativeProps :=
      fun n => (Classical.choose_spec (hchar n).2.2).2.2.2.1
    have hidx_next : ∀ n, (σ (n + 1)).1.tgbaState = (t n).target := by
      intro n
      have heq : (σ n).2.target = (σ (n + 1)).1 := (hstep n).2
      rw [ht_target n] at heq
      exact (congrArg TBAState.tgbaState heq).symm
    have hinit2 : tgba.isInitial (σ 0).1.tgbaState ∧ (σ 0).1.acceptIdx = 0 :=
      (TGBA.degeneralize_initialStates_contains tgba (σ 0).1).mp hinit
    refine ⟨fun n => ⟨(σ n).1.tgbaState, t n⟩, ⟨hinit2.1, ?_⟩, ?_, ?_⟩
    · intro n
      simp only [TGBA.toSpec]
      exact ⟨ht_mem n, (hidx_next n).symm⟩
    · intro n
      simp only [TGBA.toSpec]
      rw [← ht_pos n, ← ht_neg n]
      exact hcompat n
    · intro i
      exact absurd i.isLt (by omega)
  · rintro ⟨σ, ⟨hinit, hstep⟩, hcompat, -⟩
    simp only [TGBA.toSpec] at hinit hstep hcompat
    have hmem : ∀ n, tgba.states.contains (σ n).1 = true := by
      intro n
      induction n with
      | zero => exact hwf.initial_mem _ hinit
      | succ n ih =>
        have := hwf.succ_mem _ _ ih (hstep n).1
        rwa [(hstep n).2] at this
    let σ_tba : Nat → TBA.Edge α := fun n =>
      ⟨{ tgbaState := (σ n).1, acceptIdx := 0 },
        { target := { tgbaState := (σ n).2.target, acceptIdx := 0 },
          positiveProps := (σ n).2.positiveProps, negativeProps := (σ n).2.negativeProps,
          acceptMarks := Std.HashSet.emptyWithCapacity 1 |>.insert 0 }⟩
    refine ⟨σ_tba, ⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [TBA.toSpec, TBA.isInitial]
      rw [TGBA.degeneralize_initialStates_contains]
      exact ⟨hinit, rfl⟩
    · intro n
      simp only [TBA.toSpec]
      refine ⟨?_, ?_⟩
      · rw [TGBA.degeneralize_getSuccessors_mem]
        have hs0 : (σ_tba n).1.acceptIdx = 0 := rfl
        refine ⟨hmem n, ?_, (σ n).2, (hstep n).1, ?_, rfl, rfl, ?_⟩
        · rw [hs0, hdegK]; omega
        · show ({ tgbaState := (σ n).2.target, acceptIdx := 0 } : TBAState) =
            { tgbaState := (σ n).2.target, acceptIdx :=
              if (σ n).2.acceptMarks.contains 0 then (0 + 1) % degK tgba else 0 }
          rw [hdegK]; split <;> rfl
        · show (Std.HashSet.emptyWithCapacity 1 |>.insert 0 : Std.HashSet Nat) =
            (if tgba.numAcceptSets == 0 || (0 == 0 && (σ n).2.acceptMarks.contains 0)
              then Std.HashSet.emptyWithCapacity 1 |>.insert 0 else Std.HashSet.emptyWithCapacity 0)
          simp [h0]
      · show ({ tgbaState := (σ n).2.target, acceptIdx := 0 } : TBAState) =
          { tgbaState := (σ (n + 1)).1, acceptIdx := 0 }
        congr 1
        exact (hstep n).2
    · intro n
      simp only [TBA.toSpec]
      exact hcompat n
    · intro i n
      have hi0 : i.val = 0 := by have h : i.val < 1 := i.isLt; omega
      refine ⟨0, ?_⟩
      simp only [TBA.toSpec, hi0]
      show (0 : Nat) ∈ (Std.HashSet.emptyWithCapacity 1 |>.insert 0)
      simp

/-! ## Unconditional wrappers -/

/-- The `TBA` and the `TGBA` it was degeneralized from accept the same ω-words, regardless of `numAcceptSets`. -/
theorem TGBA.degeneralize_accepts_any [LawfulBEq α] [LawfulHashable α] (tgba : TGBA α) (hwf : tgba.WellFormed)
    (ξ : OmegaWord α) : (tgba.degeneralize).toSpec.accepts ξ ↔ tgba.toSpec.accepts ξ :=
  if h0 : tgba.numAcceptSets = 0 then
    TGBA.degeneralize_accepts_zero tgba h0 hwf ξ
  else by
    have hk : tgba.numAcceptSets > 0 := by omega
    rw [TGBA.degeneralize_bridge tgba hk hwf ξ]
    exact TOASpec.degeneralize_correct tgba.toSpec hk ξ

end Lasso
