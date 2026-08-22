/-
  Bridge between computational `GBA.degeneralize` and abstract `OASpec.degeneralize`.

  Shows that the computational BA (from `GBA.degeneralize`) and the abstract
  degeneralized automaton (`OASpec.degeneralize`) accept the same ω-words,
  completing the chain:

    GBA.toSpec accepts ξ ↔ ξ ⊨ φ               (constructGBA_correct)
    OASpec.degeneralize accepts ξ ↔ OASpec accepts ξ  (degeneralize_correct)
    BA.toSpec accepts ξ ↔ OASpec.degeneralize accepts ξ   (THIS FILE)
-/

import LTLLib.AbstractSpec.Acceptance
import LTLLib.GBA
import LTLLib.BA

namespace LTLLib

variable {α : Type u} [BEq α] [Hashable α]

/-! ### Generic fold helpers -/

/-- Folding conditional inserts into a HashSet with a mapping function. -/
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

/-- Folding unconditional inserts into a HashSet with a mapping function. -/
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

/-- Folding inserts into a HashMap preserves keys not touched by the fold. -/
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

/-- Folding inserts with pairwise distinct keys: element x maps to val x. -/
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

/-! ### Simplification: k > 0 implies the `if` in degeneralize simplifies -/

private theorem degeneralize_k_eq {gba : GBA α}
    (hk : gba.numAcceptSets > 0) :
    (if gba.acceptSets.size == 0 then 1 else gba.acceptSets.size) =
      gba.acceptSets.size := by
  simp only [GBA.numAcceptSets] at hk
  have : (gba.acceptSets.size == 0) = false := by
    simp only [beq_eq_false_iff_ne]; omega
  simp [this]

private theorem degeneralize_k_pos {gba : GBA α}
    (hk : gba.numAcceptSets > 0) :
    0 < (if gba.acceptSets.size == 0 then 1 else gba.acceptSets.size) := by
  rw [degeneralize_k_eq hk]; exact hk

/-! ### Labeling is preserved -/

theorem degeneralize_labeling (gba : GBA α) :
    (gba.degeneralize).labeling = gba.labeling := by
  simp [GBA.degeneralize]

theorem degeneralize_canonicalLabel_compat (gba : GBA α) (s : BAState)
    (h : gba.toSpec.labelCompat s.gbaState (canonicalLabel gba.labeling s.gbaState)) :
    (gba.degeneralize).toSpec.labelCompat s
      (canonicalLabel (gba.degeneralize).labeling s.gbaState) := by
  rw [degeneralize_labeling]
  show (BA.toSpec (gba.degeneralize)).labelCompat s _
  simp only [BA.toSpec]
  simpa only [GBA.toSpec] using h

/-! ### Initial states characterization -/

theorem degeneralize_initialStates_contains (gba : GBA α) (s : BAState) :
    (gba.degeneralize).initialStates.contains s ↔
      gba.initialStates.contains s.gbaState ∧ s.acceptIdx = 0 := by
  simp only [GBA.degeneralize, Std.HashSet.fold_eq_foldl_toList]
  rw [HashSet_foldl_map_insert_contains]
  simp only [Std.HashSet.contains_emptyWithCapacity, Bool.false_or]
  rw [List.any_eq_true]
  constructor
  · rintro ⟨q, hq, heq⟩
    rw [beq_iff_eq] at heq
    have h1 : s.gbaState = q := by rw [← heq]
    have h2 : s.acceptIdx = 0 := by rw [← heq]
    exact ⟨h1 ▸ (Std.HashSet.mem_toList.mp hq |> Std.HashSet.mem_iff_contains.mp), h2⟩
  · rintro ⟨hmem, hidx⟩
    exact ⟨s.gbaState,
      Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hmem),
      by rw [beq_iff_eq]; cases s; simp_all⟩

/-! ### Accepting states characterization -/

theorem degeneralize_isAccepting (gba : GBA α) (s : BAState) :
    (gba.degeneralize).isAccepting s ↔
      gba.states.contains s.gbaState ∧
        (gba.isAccepting 0 s.gbaState) = true ∧
        s.acceptIdx = 0 := by
  simp only [BA.isAccepting, GBA.degeneralize, Std.HashSet.fold_eq_foldl_toList]
  rw [HashSet_foldl_cond_insert_contains]
  simp only [Std.HashSet.contains_emptyWithCapacity, Bool.false_or]
  rw [List.any_eq_true]
  constructor
  · rintro ⟨q, hq, h_and⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h_and
    have h1 : s.gbaState = q := by rw [← h_and.2]
    have h2 : s.acceptIdx = 0 := by rw [← h_and.2]
    exact ⟨h1 ▸ (Std.HashSet.mem_toList.mp hq |> Std.HashSet.mem_iff_contains.mp),
           h1 ▸ h_and.1, h2⟩
  · rintro ⟨hmem, hacc, hidx⟩
    exact ⟨s.gbaState,
      Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hmem),
      by simp [beq_iff_eq, hacc]; cases s; simp_all⟩

/-! ### Successor characterization

The `GBA.degeneralize` successors are built by a double fold:
outer over `gba.states`, inner over `List.range k`.

Strategy: characterize the inner fold using `HashMap_foldl_insert_of_mem`,
then compose via the outer fold.
-/

/-- Keys produced by the inner fold are pairwise distinct
(same gbaState, different acceptIdx from List.range k). -/
private theorem range_keys_pairwise_distinct (gbaState : Nat) (k : Nat) :
    (List.range k).Pairwise (fun a b =>
      (({ gbaState, acceptIdx := a } : BAState) ==
       { gbaState, acceptIdx := b }) = false) := by
  exact List.nodup_range.imp (fun {a b} (h : a ≠ b) => by
    simp only [beq_eq_false_iff_ne]; intro heq; exact h (BAState.mk.inj heq).2)

/-- Keys from different gbaStates are never equal to a key with a given gbaState. -/
private theorem key_ne_of_gbaState_ne (gbaState : Nat) (i : Nat) (s : BAState)
    (hne : s.gbaState ≠ gbaState) :
    (({ gbaState, acceptIdx := i } : BAState) == s) = false := by
  simp only [beq_eq_false_iff_ne]
  intro h; exact hne (h ▸ rfl)

/-- Compute the successor array for a single (gbaState, i) pair. -/
private def computeBASuccs (gba : GBA α) (gbaState : Nat) (i k : Nat)
    : Array BAState :=
  (gba.getSuccessors gbaState).map fun q =>
    { gbaState := q,
      acceptIdx := if gba.acceptSets.size == 0 then 0
                   else if gba.isAccepting i gbaState then (i + 1) % k
                   else i }

/-- Inner fold: for a fixed gbaState, the fold over `List.range k` inserts
entries for each counter value and preserves other entries. -/
private theorem inner_range_fold
    (gba : GBA α) (gbaState : Nat) (k : Nat)
    (succMap : Std.HashMap BAState (Array BAState))
    (s : BAState) :
    let succMap' := (List.range k).foldl (init := succMap) fun succMap i =>
      succMap.insert { gbaState, acceptIdx := i } (computeBASuccs gba gbaState i k)
    (s.gbaState ≠ gbaState → succMap'[s]? = succMap[s]?) ∧
    (s.gbaState = gbaState → s.acceptIdx < k →
      succMap'[s]? = some (computeBASuccs gba gbaState s.acceptIdx k)) ∧
    (s.gbaState = gbaState → ¬(s.acceptIdx < k) → succMap'[s]? = succMap[s]?) := by
  refine ⟨fun hne => ?_, fun heq hi => ?_, fun heq hni => ?_⟩
  · exact HashMap_foldl_insert_preserves (List.range k)
      (fun i => { gbaState, acceptIdx := i })
      (fun i => computeBASuccs gba gbaState i k)
      succMap s
      (fun i _ => key_ne_of_gbaState_ne gbaState i s hne)
  · have hmem : s.acceptIdx ∈ List.range k := List.mem_range.mpr hi
    have hkey : ({ gbaState, acceptIdx := s.acceptIdx } : BAState) = s := by
      cases s; simp_all
    exact HashMap_foldl_insert_of_mem (List.range k)
      (fun i => { gbaState, acceptIdx := i })
      (fun i => computeBASuccs gba gbaState i k)
      succMap s.acceptIdx hmem hkey
      (range_keys_pairwise_distinct gbaState k)
  · exact HashMap_foldl_insert_preserves (List.range k)
      (fun i => { gbaState, acceptIdx := i })
      (fun i => computeBASuccs gba gbaState i k)
      succMap s
      (fun i hi_mem => by
        simp only [beq_eq_false_iff_ne]
        intro h; exact hni (by rw [← (BAState.mk.inj h).2]; exact List.mem_range.mp hi_mem))

/-- The full double fold: for q ∈ gba.states and i < k, the entry at ⟨q, i⟩
has the computed successors. For q ∉ gba.states, no entry. -/
private theorem outer_fold_successors
    (gba : GBA α) (k : Nat) (l : List Nat) (init : Std.HashMap BAState (Array BAState))
    (s : BAState)
    (h_distinct : l.Pairwise (· ≠ ·)) :
    let succMap := l.foldl (init := init) fun succMap q =>
      (List.range k).foldl (init := succMap) fun succMap i =>
        succMap.insert ⟨q, i⟩ (computeBASuccs gba q i k)
    (s.gbaState ∈ l → s.acceptIdx < k →
      succMap[s]? = some (computeBASuccs gba s.gbaState s.acceptIdx k)) ∧
    (s.gbaState ∉ l → succMap[s]? = init[s]?) ∧
    (s.gbaState ∈ l → ¬(s.acceptIdx < k) → succMap[s]? = init[s]?) := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨h_all, h_pw_tl⟩ := List.pairwise_cons.mp h_distinct
    have inner := inner_range_fold gba hd k init s
    let init' := (List.range k).foldl (init := init) fun succMap i =>
      succMap.insert ({ gbaState := hd, acceptIdx := i } : BAState)
        (computeBASuccs gba hd i k)
    have ih_inst := ih init' h_pw_tl
    simp only [List.foldl_cons, List.mem_cons] at *
    refine ⟨fun h hi => ?_, fun hni => ?_, fun h hni => ?_⟩
    · rcases h with rfl | hmem_tl
      · have hni : s.gbaState ∉ tl := fun h => absurd rfl (h_all s.gbaState h)
        rw [ih_inst.2.1 hni]
        exact inner.2.1 rfl hi
      · exact ih_inst.1 hmem_tl hi
    · push_neg at hni
      rw [ih_inst.2.1 hni.2, inner.1 hni.1]
    · rcases h with rfl | hmem_tl
      · have hni_tl : s.gbaState ∉ tl := fun h => absurd rfl (h_all s.gbaState h)
        rw [ih_inst.2.1 hni_tl, inner.2.2 rfl hni]
      · have hne : s.gbaState ≠ hd := Ne.symm (h_all s.gbaState hmem_tl)
        rw [ih_inst.2.2 hmem_tl hni, inner.1 hne]

/-- Membership in `computeBASuccs` characterized in terms of GBA transitions
and counter update. -/
private theorem mem_computeBASuccs (gba : GBA α)
    (hk : gba.numAcceptSets > 0) (gbaState i : Nat) (s' : BAState) :
    s' ∈ computeBASuccs gba gbaState i gba.numAcceptSets ↔
      s'.gbaState ∈ gba.getSuccessors gbaState ∧
      s'.acceptIdx = (if gba.isAccepting i gbaState
                      then (i + 1) % gba.numAcceptSets
                      else i) := by
  simp only [computeBASuccs, Array.mem_map]
  have hsize : (gba.acceptSets.size == 0) = false := by
    simp only [GBA.numAcceptSets] at hk; simp only [beq_eq_false_iff_ne]; omega
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq, by simp [hsize, GBA.numAcceptSets]⟩
  · rintro ⟨h_succ, h_idx⟩
    exact ⟨s'.gbaState, h_succ, by
      cases s'; simp_all [GBA.numAcceptSets]⟩

/-- The successors HashMap of `gba.degeneralize` has the double-fold structure
expected by `outer_fold_successors`. -/
private theorem degeneralize_successors_eq (gba : GBA α)
    (hk : gba.numAcceptSets > 0) :
    let k := gba.numAcceptSets
    (gba.degeneralize).successors =
      gba.states.toList.foldl (init := Std.HashMap.emptyWithCapacity (gba.states.size * k))
        fun succMap q =>
          (List.range k).foldl (init := succMap) fun succMap i =>
            succMap.insert ⟨q, i⟩ (computeBASuccs gba q i k) := by
  simp only [GBA.degeneralize, Std.HashSet.fold_eq_foldl_toList, degeneralize_k_eq hk]
  congr 1

/-- Final successor characterization: `s' ∈ ba.getSuccessors s` iff
the GBA transition holds and the counter is updated correctly. -/
theorem degeneralize_getSuccessors_mem (gba : GBA α)
    (hk : gba.numAcceptSets > 0) (s s' : BAState) :
    s' ∈ (gba.degeneralize).getSuccessors s ↔
      gba.states.contains s.gbaState ∧
      s.acceptIdx < gba.numAcceptSets ∧
      s'.gbaState ∈ gba.getSuccessors s.gbaState ∧
      s'.acceptIdx = (if gba.isAccepting s.acceptIdx s.gbaState
                      then (s.acceptIdx + 1) % gba.numAcceptSets
                      else s.acceptIdx) := by
  simp only [BA.getSuccessors]
  rw [degeneralize_successors_eq gba hk]
  have h_distinct : gba.states.toList.Pairwise (· ≠ ·) :=
    (Std.HashSet.distinct_toList (m := gba.states)).imp
      (fun h => by simp [beq_eq_false_iff_ne] at h; exact h)
  have h_fold := outer_fold_successors gba gba.numAcceptSets gba.states.toList
    (Std.HashMap.emptyWithCapacity (gba.states.size * gba.numAcceptSets)) s h_distinct
  have mem_iff : gba.states.contains s.gbaState ↔ s.gbaState ∈ gba.states.toList :=
    ⟨fun h => Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr h),
     fun h => Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp h)⟩
  by_cases hmem : gba.states.contains s.gbaState <;>
    by_cases hidx : s.acceptIdx < gba.numAcceptSets
  · -- s.gbaState ∈ states, acceptIdx < k
    rw [h_fold.1 (mem_iff.mp hmem) hidx]
    simp only [Option.getD_some]
    rw [mem_computeBASuccs gba hk]
    exact ⟨fun ⟨h1, h2⟩ => ⟨hmem, hidx, h1, h2⟩,
           fun ⟨_, _, h1, h2⟩ => ⟨h1, h2⟩⟩
  · -- s.gbaState ∈ states, acceptIdx ≥ k
    rw [h_fold.2.2 (mem_iff.mp hmem) hidx]
    simp only [Std.HashMap.getElem?_emptyWithCapacity, Option.getD_none,
               Array.not_mem_empty, false_iff, not_and]
    intro _ h; exact absurd h hidx
  · -- s.gbaState ∉ states
    rw [h_fold.2.1 (fun h => hmem (mem_iff.mpr h))]
    simp only [Std.HashMap.getElem?_emptyWithCapacity, Option.getD_none,
               Array.not_mem_empty, false_iff, not_and]
    intro h; exact absurd h hmem
  · -- s.gbaState ∉ states, acceptIdx ≥ k
    rw [h_fold.2.1 (fun h => hmem (mem_iff.mpr h))]
    simp only [Std.HashMap.getElem?_emptyWithCapacity, Option.getD_none,
               Array.not_mem_empty, false_iff, not_and]
    intro h; exact absurd h hmem

/-! ### States characterization -/

/-- Double fold building `allStates`: the result contains `s` iff `init` did,
or `s.gbaState` was iterated over (`∈ l`) with `s.acceptIdx < k`. -/
private theorem outer_fold_states_mem
    (k : Nat) (l : List Nat) (init : Std.HashSet BAState) (s : BAState) :
    (l.foldl (init := init) fun acc gbaState =>
      (List.range k).foldl (init := acc) fun acc i =>
        acc.insert ({ gbaState, acceptIdx := i } : BAState)).contains s = true ↔
      init.contains s = true ∨ (s.gbaState ∈ l ∧ s.acceptIdx < k) := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    have hinner : ((List.range k).foldl (init := init) fun acc i =>
        acc.insert ({ gbaState := hd, acceptIdx := i } : BAState)).contains s = true ↔
        init.contains s = true ∨ (hd = s.gbaState ∧ s.acceptIdx < k) := by
      rw [HashSet_foldl_map_insert_contains]
      simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range]
      constructor
      · rintro (h | ⟨i, hi, heq⟩)
        · exact Or.inl h
        · rw [beq_iff_eq] at heq
          exact Or.inr ⟨(BAState.mk.inj heq).1, heq ▸ hi⟩
      · rintro (h | ⟨heq, hi⟩)
        · exact Or.inl h
        · exact Or.inr ⟨s.acceptIdx, hi, by rw [beq_iff_eq]; cases s; simp_all⟩
    rw [hinner]; grind

/-- `(gba.degeneralize).states` contains `s` iff `s.gbaState ∈ gba.states`
and `s.acceptIdx` is within range. -/
theorem degeneralize_states_contains (gba : GBA α) (hk : gba.numAcceptSets > 0)
    (s : BAState) :
    (gba.degeneralize).states.contains s = true ↔
      gba.states.contains s.gbaState = true ∧ s.acceptIdx < gba.numAcceptSets := by
  simp only [GBA.degeneralize, Std.HashSet.fold_eq_foldl_toList, degeneralize_k_eq hk]
  rw [outer_fold_states_mem]
  simp only [Std.HashSet.contains_emptyWithCapacity, Bool.false_eq_true, false_or]
  rw [show s.gbaState ∈ gba.states.toList ↔ gba.states.contains s.gbaState = true from
    ⟨fun h => Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp h),
     fun h => Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr h)⟩]
  simp only [GBA.numAcceptSets]

/-! ### Well-formedness is preserved by degeneralize -/

/-- Degeneralizing a well-formed GBA yields a well-formed BA. -/
theorem degeneralize_wellFormed (gba : GBA α) (hk : gba.numAcceptSets > 0)
    (hwf : gba.WellFormed) : (gba.degeneralize).WellFormed where
  initial_mem s hs := by
    obtain ⟨h1, h2⟩ := (degeneralize_initialStates_contains gba s).mp hs
    exact (degeneralize_states_contains gba hk s).mpr ⟨hwf.initial_mem s.gbaState h1, h2 ▸ hk⟩
  succ_mem s s' hs hsucc := by
    obtain ⟨h1, h2⟩ := (degeneralize_states_contains gba hk s).mp hs
    obtain ⟨_, _, h3, h4⟩ := (degeneralize_getSuccessors_mem gba hk s s').mp hsucc
    refine (degeneralize_states_contains gba hk s').mpr ⟨hwf.succ_mem s.gbaState s'.gbaState h1 h3, ?_⟩
    rw [h4]; split
    · exact Nat.mod_lt _ hk
    · omega

/-! ### Main bridge -/

/-- The computational BA and the abstract degeneralized automaton accept
the same ω-words. -/

-- Helper: all states in an abstract run are in gba.states
private theorem run_states_mem (gba : GBA α) (hk : gba.numAcceptSets > 0)
    (hwf : gba.WellFormed) (σ' : Nat → Nat × Fin gba.numAcceptSets)
    (hinit : ((gba.toSpec).degeneralize hk).initial (σ' 0))
    (htrans : ∀ n, ((gba.toSpec).degeneralize hk).trans (σ' n) (σ' (n + 1))) :
    ∀ n, gba.states.contains (σ' n).1 := by
  intro n
  induction n with
  | zero =>
    exact hwf.initial_mem _ (by
      have := hinit.1; simp [GBA.toSpec, GBA.isInitial] at this; exact this)
  | succ n ih =>
    exact hwf.succ_mem _ _ ih (by
      have := (htrans n).1; simp [GBA.toSpec] at this; exact this)

theorem degeneralize_bridge [LawfulBEq α] [LawfulHashable α]
    (gba : GBA α) (hk : gba.numAcceptSets > 0)
    (hwf : gba.WellFormed) (ξ : OmegaWord α) :
    (gba.degeneralize).toSpec.accepts ξ ↔
      ((gba.toSpec).degeneralize hk).accepts ξ := by
  constructor
  · -- Forward: BA.toSpec accepts → OASpec.degeneralize accepts
    rintro ⟨σ, ⟨hinit, htrans⟩, hcompat, hacc⟩
    have h_init := (degeneralize_initialStates_contains gba (σ 0)).mp hinit
    have h_trans : ∀ n, gba.states.contains (σ n).gbaState ∧
        (σ n).acceptIdx < gba.numAcceptSets ∧
        (σ (n+1)).gbaState ∈ gba.getSuccessors (σ n).gbaState ∧
        (σ (n+1)).acceptIdx = (if gba.isAccepting (σ n).acceptIdx (σ n).gbaState
          then ((σ n).acceptIdx + 1) % gba.numAcceptSets else (σ n).acceptIdx) :=
      fun n => (degeneralize_getSuccessors_mem gba hk (σ n) (σ (n+1))).mp (htrans n)
    have h_bound : ∀ n, (σ n).acceptIdx < gba.numAcceptSets :=
      fun n => (h_trans n).2.1
    refine ⟨fun n => ((σ n).gbaState, ⟨(σ n).acceptIdx, h_bound n⟩), ⟨?_, ?_⟩, ?_, ?_⟩
    · -- Initial
      simp only [OASpec.degeneralize, GBA.toSpec, GBA.isInitial]
      exact ⟨h_init.1, Fin.ext h_init.2⟩
    · -- Transitions
      intro n
      simp only [OASpec.degeneralize, GBA.toSpec, OASpec.counterStep]
      refine ⟨(h_trans n).2.2.1, Fin.ext ?_⟩
      split <;> simp_all [GBA.numAcceptSets, (h_trans n).2.2.2]
    · -- Compatibility
      intro n
      simp only [OASpec.degeneralize, GBA.toSpec]
      have := hcompat n
      simp only [BA.toSpec] at this
      rwa [degeneralize_labeling] at this
    · -- Accepting
      intro ⟨i, hi⟩ n
      have : i = 0 := by omega
      subst this
      obtain ⟨j, hj⟩ := hacc ⟨0, Nat.one_pos⟩ n
      simp only [BA.toSpec] at hj
      rw [degeneralize_isAccepting] at hj
      exact ⟨j, by simp only [OASpec.degeneralize, GBA.toSpec]; exact ⟨Fin.ext hj.2.2, hj.2.1⟩⟩
  · -- Backward: OASpec.degeneralize accepts → BA.toSpec accepts
    rintro ⟨σ', ⟨hinit', htrans'⟩, hcompat', hacc'⟩
    have h_in := run_states_mem gba hk hwf σ' hinit' htrans'
    refine ⟨fun n => ⟨(σ' n).1, (σ' n).2.val⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · -- Initial
      show (gba.degeneralize).initialStates.contains ⟨(σ' 0).1, (σ' 0).2.val⟩
      rw [degeneralize_initialStates_contains]
      simp only [OASpec.degeneralize, GBA.toSpec, GBA.isInitial] at hinit'
      exact ⟨hinit'.1, congrArg Fin.val hinit'.2⟩
    · -- Transitions
      intro n
      show (⟨(σ' (n+1)).1, (σ' (n+1)).2.val⟩ : BAState) ∈
        (gba.degeneralize).getSuccessors ⟨(σ' n).1, (σ' n).2.val⟩
      rw [degeneralize_getSuccessors_mem gba hk]
      simp only [OASpec.degeneralize, GBA.toSpec, OASpec.counterStep] at htrans'
      have h_cstep := (htrans' n).2
      refine ⟨h_in n, (σ' n).2.isLt, (htrans' n).1, ?_⟩
      split at * <;> simp_all
    · -- Compatibility
      intro n
      show (gba.degeneralize).toSpec.labelCompat ⟨(σ' n).1, (σ' n).2.val⟩ (ξ n)
      simp only [BA.toSpec]
      rw [degeneralize_labeling]
      have := hcompat' n
      simp only [OASpec.degeneralize, GBA.toSpec] at this
      exact this
    · -- Accepting
      intro ⟨i, hi⟩ n
      have : i = 0 := by omega
      subst this
      obtain ⟨j, hj⟩ := hacc' ⟨0, Nat.one_pos⟩ n
      simp only [OASpec.degeneralize, GBA.toSpec] at hj
      show ∃ j, (gba.degeneralize).isAccepting ⟨(σ' (n + j)).1, (σ' (n + j)).2.val⟩
      exact ⟨j, (degeneralize_isAccepting gba _).mpr
        ⟨h_in (n + j), hj.2, congrArg Fin.val hj.1⟩⟩

/-! ### The `numAcceptSets = 0` case

`gba.numAcceptSets = 0` for any formula with no Until-subformula.

This proves `BA.toSpec.accepts ξ ↔ GBA.toSpec.accepts ξ` *directly* for
`numAcceptSets = 0`.

With `k = 0`, `GBA.toSpec.isAcceptingRun` is vacuous (`Fin 0` is empty) and,
computationally, `GBA.degeneralize` clamps to `k = 1` with *every* state accepting.
Therefore, the BA side's acceptance condition is equally trivial. -/

private theorem mem_computeBASuccs_zero (gba : GBA α) (h0 : gba.acceptSets.size = 0)
    (gbaState i : Nat) (s' : BAState) :
    s' ∈ computeBASuccs gba gbaState i 1 ↔
      s'.gbaState ∈ gba.getSuccessors gbaState ∧ s'.acceptIdx = 0 := by
  simp only [computeBASuccs, Array.mem_map]
  have hsize : (gba.acceptSets.size == 0) = true := by simp [h0]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨hq, by simp [hsize]⟩
  · rintro ⟨h_succ, h_idx⟩
    exact ⟨s'.gbaState, h_succ, by cases s'; simp_all⟩

private theorem degeneralize_successors_eq_zero (gba : GBA α) (h0 : gba.acceptSets.size = 0) :
    (gba.degeneralize).successors =
      gba.states.toList.foldl (init := Std.HashMap.emptyWithCapacity (gba.states.size * 1))
        fun succMap q =>
          (List.range 1).foldl (init := succMap) fun succMap i =>
            succMap.insert ⟨q, i⟩ (computeBASuccs gba q i 1) := by
  simp only [GBA.degeneralize, Std.HashSet.fold_eq_foldl_toList, h0, beq_self_eq_true,
    ↓reduceIte, computeBASuccs]

theorem degeneralize_getSuccessors_mem_zero (gba : GBA α) (h0 : gba.acceptSets.size = 0)
    (s s' : BAState) :
    s' ∈ (gba.degeneralize).getSuccessors s ↔
      gba.states.contains s.gbaState ∧
      s.acceptIdx < 1 ∧
      s'.gbaState ∈ gba.getSuccessors s.gbaState ∧
      s'.acceptIdx = 0 := by
  simp only [BA.getSuccessors]
  rw [degeneralize_successors_eq_zero gba h0]
  have h_distinct : gba.states.toList.Pairwise (· ≠ ·) :=
    (Std.HashSet.distinct_toList (m := gba.states)).imp
      (fun h => by simp [beq_eq_false_iff_ne] at h; exact h)
  have h_fold := outer_fold_successors gba 1 gba.states.toList
    (Std.HashMap.emptyWithCapacity (gba.states.size * 1)) s h_distinct
  have mem_iff : gba.states.contains s.gbaState ↔ s.gbaState ∈ gba.states.toList :=
    ⟨fun h => Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr h),
     fun h => Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp h)⟩
  by_cases hmem : gba.states.contains s.gbaState <;>
    by_cases hidx : s.acceptIdx < 1
  · rw [h_fold.1 (mem_iff.mp hmem) hidx]
    simp only [Option.getD_some]
    rw [mem_computeBASuccs_zero gba h0]
    exact ⟨fun ⟨h1, h2⟩ => ⟨hmem, hidx, h1, h2⟩, fun ⟨_, _, h1, h2⟩ => ⟨h1, h2⟩⟩
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

theorem degeneralize_states_contains_zero (gba : GBA α) (h0 : gba.acceptSets.size = 0)
    (s : BAState) :
    (gba.degeneralize).states.contains s = true ↔
      gba.states.contains s.gbaState = true ∧ s.acceptIdx < 1 := by
  simp only [GBA.degeneralize, Std.HashSet.fold_eq_foldl_toList, h0, beq_self_eq_true,
    ↓reduceIte]
  rw [outer_fold_states_mem]
  simp only [Std.HashSet.contains_emptyWithCapacity, Bool.false_eq_true, false_or]
  rw [show s.gbaState ∈ gba.states.toList ↔ gba.states.contains s.gbaState = true from
    ⟨fun h => Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp h),
     fun h => Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr h)⟩]

/-- Degeneralizing a well-formed GBA with no acceptance sets still yields a
well-formed BA. -/
theorem degeneralize_wellFormed_zero (gba : GBA α) (h0 : gba.acceptSets.size = 0)
    (hwf : gba.WellFormed) : (gba.degeneralize).WellFormed where
  initial_mem s hs := by
    obtain ⟨h1, h2⟩ := (degeneralize_initialStates_contains gba s).mp hs
    exact (degeneralize_states_contains_zero gba h0 s).mpr ⟨hwf.initial_mem s.gbaState h1, by omega⟩
  succ_mem s s' hs hsucc := by
    obtain ⟨h1, _⟩ := (degeneralize_states_contains_zero gba h0 s).mp hs
    obtain ⟨_, _, h3, h4⟩ := (degeneralize_getSuccessors_mem_zero gba h0 s s').mp hsucc
    exact (degeneralize_states_contains_zero gba h0 s').mpr
      ⟨hwf.succ_mem s.gbaState s'.gbaState h1 h3, by omega⟩

/-- `gba.isAccepting 0` is vacuously true everywhere when there are no
acceptance sets (the mirror of `OASpec`'s "when `k = 0`, every
run is vacuously accepting"). -/
private theorem GBA.isAccepting_zero_of_empty (gba : GBA α) (h0 : gba.acceptSets.size = 0)
    (q : Nat) : gba.isAccepting 0 q = true := by
  simp only [GBA.isAccepting]
  rw [show gba.acceptSets[0]? = none from by
    rw [Array.getElem?_eq_none_iff]; omega]

/-- The `numAcceptSets = 0` twin of `degeneralize_bridge`. -/
theorem degeneralize_accepts_zero (gba : GBA α) (h0 : gba.acceptSets.size = 0)
    (hwf : gba.WellFormed) (ξ : OmegaWord α) :
    (gba.degeneralize).toSpec.accepts ξ ↔ gba.toSpec.accepts ξ := by
  have hnum : gba.numAcceptSets = 0 := by simp [GBA.numAcceptSets, h0]
  constructor
  · rintro ⟨σ', ⟨hinit', htrans'⟩, hcompat', _⟩
    refine ⟨fun n => (σ' n).gbaState, ⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [GBA.toSpec, GBA.isInitial]
      exact ((degeneralize_initialStates_contains gba (σ' 0)).mp hinit').1
    · intro n
      simp only [GBA.toSpec]
      exact ((degeneralize_getSuccessors_mem_zero gba h0 (σ' n) (σ' (n+1))).mp (htrans' n)).2.2.1
    · intro n
      show gba.toSpec.labelCompat (σ' n).gbaState (ξ n)
      simp only [GBA.toSpec]
      have h := hcompat' n
      simp only [BA.toSpec, degeneralize_labeling] at h
      exact h
    · intro i
      exact absurd i.isLt (by omega)
  · rintro ⟨σ, ⟨hinit, htrans⟩, hcompat, _⟩
    have hmem : ∀ n, gba.states.contains (σ n) = true := by
      intro n
      induction n with
      | zero => exact hwf.initial_mem _ hinit
      | succ n ih => exact hwf.succ_mem _ _ ih (htrans n)
    refine ⟨fun n => ⟨σ n, 0⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · exact (degeneralize_initialStates_contains gba ⟨σ 0, 0⟩).mpr ⟨hinit, rfl⟩
    · intro n
      exact (degeneralize_getSuccessors_mem_zero gba h0 ⟨σ n, 0⟩ ⟨σ (n+1), 0⟩).mpr
        ⟨hmem n, Nat.one_pos, htrans n, rfl⟩
    · intro n
      show (gba.degeneralize).toSpec.labelCompat ⟨σ n, 0⟩ (ξ n)
      simp only [BA.toSpec, degeneralize_labeling]
      exact hcompat n
    · intro ⟨i, hi⟩ n
      have : i = 0 := by omega
      subst this
      refine ⟨0, ?_⟩
      show (gba.degeneralize).isAccepting ⟨σ (n + 0), 0⟩
      exact (degeneralize_isAccepting gba _).mpr
        ⟨hmem (n + 0), GBA.isAccepting_zero_of_empty gba h0 _, rfl⟩

/-! ### Unconditional wrappers

Combine the `hk`-based (`numAcceptSets > 0`) and `h0`-based (`= 0`) halves
into single theorems that hold for *any* well-formed `GBA`. -/

/-- Degeneralizing a well-formed `GBA` always yields a well-formed `BA`,
regardless of `numAcceptSets`. -/
theorem degeneralize_wellFormed_any (gba : GBA α) (hwf : gba.WellFormed) :
    (gba.degeneralize).WellFormed :=
  if h0 : gba.acceptSets.size = 0 then
    degeneralize_wellFormed_zero gba h0 hwf
  else
    degeneralize_wellFormed gba (by simp only [GBA.numAcceptSets]; omega) hwf

/-- The `BA` and the `GBA` it was degeneralized from accept the
same ω-words, regardless of `numAcceptSets`. -/
theorem degeneralize_accepts_any [LawfulBEq α] [LawfulHashable α]
    (gba : GBA α) (hwf : gba.WellFormed) (ξ : OmegaWord α) :
    (gba.degeneralize).toSpec.accepts ξ ↔ gba.toSpec.accepts ξ :=
  if h0 : gba.acceptSets.size = 0 then
    degeneralize_accepts_zero gba h0 hwf ξ
  else by
    have hk : gba.numAcceptSets > 0 := by simp only [GBA.numAcceptSets]; omega
    rw [degeneralize_bridge gba hk hwf ξ]
    exact degeneralize_correct gba.toSpec hk ξ

/-- If `s` is a state of `gba.degeneralize`, then `s.gbaState` is a state of `gba`. -/
theorem degeneralize_states_gbaState_mem_any (gba : GBA α) (s : BAState)
    (hs : (gba.degeneralize).states.contains s = true) :
    gba.states.contains s.gbaState = true :=
  if h0 : gba.acceptSets.size = 0 then
    ((degeneralize_states_contains_zero gba h0 s).mp hs).1
  else
    ((degeneralize_states_contains gba (by simp only [GBA.numAcceptSets]; omega) s).mp hs).1

end LTLLib
