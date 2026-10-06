module

/-
  The live/dead bookkeeping shared by the SCC-based emptiness checks: a stack of live states, its position map, and the
  dead set a closed component is flushed into. The invariant and the three `LawfulDFSOps` status laws are proved once here.

  Defines:
  - `liveStatusOf`: the `DFSStatus` of a state, read off `liveIndex` and `dead` alone
  - `liveFlush`: POP's flush loop, everything above a position leaving `live` and joining `dead`
  - `LiveWF`: `liveIndex` is the exact position map of `live`

  Proves:
  - `LiveWF.push`, `liveStatusOf_insert`: PUSH preserves the invariant and marks only its target live
  - `liveFlush_spec`: the flush preserves the invariant and only ever promotes live states to dead
  - `liveFlush_size`: the flush drains `live` down to exactly the position it was given
  - `liveFlush_dead_or_old`, `liveFlush_getElem!_lt`: what the flush leaves in `dead` and what it leaves alone
  - `liveFlush_touched_mono`: a touched state stays touched

  Sections:
  - The triple
  - Well-formedness
  - PUSH
  - The flush
-/
public import Std
public import LTLLib.TGBABased.SCC.GenericDFS

public section

namespace LTLLib

variable {State : Type u} [BEq State] [Hashable State]

/-! ## The triple -/

theorem Array.getElem!_push_lt {α} [Inhabited α] {xs : Array α} {x : α} {i : Nat} (h : i < xs.size) :
    (xs.push x)[i]! = xs[i]! := by
  rw [getElem!_pos (xs.push x) i (by simpa using Nat.lt_succ_of_lt h), Array.getElem_push_lt h,
    getElem!_pos xs i h]

theorem Array.getElem!_push_eq {α} [Inhabited α] {xs : Array α} {x : α} :
    (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos (xs.push x) xs.size (by simp), Array.getElem_push_eq]

/-- The status of `q`, read off `liveIndex` and `dead` alone. -/
@[expose] def liveStatusOf (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State) (q : State) : DFSStatus :=
  if liveIndex.contains q then .live else if dead.contains q then .dead else .unknown

/-- POP's flush loop: every state above `pos` leaves `live` and joins `dead`. -/
@[expose] def liveFlush (live : Array State) (liveIndex : Std.HashMap State Nat)
    (dead : Std.HashSet State) (pos : Nat) :
    Array State × Std.HashMap State Nat × Std.HashSet State :=
  if live.size > pos then
    match live.back? with
    | none => (live, liveIndex, dead)
    | some q => liveFlush live.pop (liveIndex.erase q) (dead.insert q) pos
  else (live, liveIndex, dead)
termination_by live.size
decreasing_by simp only [Array.size_pop]; omega

/-! ## Well-formedness -/

/-- `liveIndex` is the exact position map of `live`, which also rules out duplicate `live` entries. -/
structure LiveWF [Inhabited State] (live : Array State) (liveIndex : Std.HashMap State Nat) : Prop where
  -- every `live` position maps back to itself
  fwd : ∀ i, (h : i < live.size) → liveIndex[live[i]]? = some i
  -- every `liveIndex` entry names a `live` slot holding that state
  bwd : ∀ q p, liveIndex[q]? = some p → p < live.size ∧ live[p]! = q

/-- Distinct live positions hold distinct states. -/
theorem LiveWF.inj [Inhabited State] {live : Array State} {liveIndex : Std.HashMap State Nat}
    (hwf : LiveWF live liveIndex) {a b : Nat} (ha : a < live.size) (hb : b < live.size)
    (hab : live[a] = live[b]) : a = b := by
  have h1 := hwf.fwd a ha
  rw [hab, hwf.fwd b hb] at h1
  exact (Option.some.inj h1).symm

theorem liveWF_init [Inhabited State] (n : Nat) :
    LiveWF (#[] : Array State) (Std.HashMap.emptyWithCapacity n) :=
  ⟨fun i h => by simp at h, fun q p h => by simp at h⟩

/-! ## PUSH -/

/-- PUSH of a new state preserves the invariant. -/
theorem LiveWF.push [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {live : Array State} {liveIndex : Std.HashMap State Nat} (hwf : LiveWF live liveIndex)
    {q : State} (hq : liveIndex.contains q = false) :
    LiveWF (live.push q) (liveIndex.insert q live.size) := by
  refine ⟨fun i h => ?_, fun q' p h => ?_⟩
  · simp only [Array.size_push] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · rw [Array.getElem_push_lt hlt]
      have hne : live[i] ≠ q := by
        intro heq'
        have hpos := hwf.fwd i hlt
        rw [heq'] at hpos
        simp only [Std.HashMap.contains_eq_isSome_getElem?] at hq
        simp [hpos] at hq
      rw [Std.HashMap.getElem?_insert]
      simp [Ne.symm hne]
      exact hwf.fwd i hlt
    · subst heq
      rw [Array.getElem_push_eq, Std.HashMap.getElem?_insert]
      simp
  · simp only [Std.HashMap.getElem?_insert] at h
    cases hc : q == q' with
    | true =>
      have hqeq : q' = q := (beq_iff_eq.mp hc).symm
      simp [hc] at h
      subst hqeq
      exact ⟨by simp only [Array.size_push]; omega, by rw [← h, Array.getElem!_push_eq]⟩
    | false =>
      simp [hc] at h
      obtain ⟨h', heq⟩ := hwf.bwd q' p h
      exact ⟨by simp only [Array.size_push]; omega, by rw [Array.getElem!_push_lt h', heq]⟩

/-- PUSH marks its target live regardless of prior status and leaves every other state's untouched. -/
theorem liveStatusOf_insert [LawfulBEq State] [LawfulHashable State]
    (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State) (q : State) (pos : Nat) (q' : State) :
    liveStatusOf (liveIndex.insert q pos) dead q' =
      if q' == q then .live else liveStatusOf liveIndex dead q' := by
  unfold liveStatusOf
  simp only [Std.HashMap.contains_insert]
  cases hc : q' == q with
  | true =>
    have h2 : (q == q') = true := by
      have := beq_iff_eq.mp hc; simp [this.symm]
    simp [h2]
  | false =>
    have h2 : (q == q') = false := by
      have : q' ≠ q := by simpa using hc
      simp [Ne.symm this]
    simp [h2]

/-! ## The flush -/

/-- The flush preserves the invariant, and every state's status is unchanged or promoted from live to dead. -/
theorem liveFlush_spec [Inhabited State] [LawfulBEq State] [LawfulHashable State] (pos : Nat) :
    ∀ (live : Array State) (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State),
    (∀ i, (h : i < live.size) → liveIndex[live[i]]? = some i) →
    (∀ q p, liveIndex[q]? = some p → p < live.size ∧ live[p]! = q) →
    (∀ i, (h : i < (liveFlush live liveIndex dead pos).1.size) →
      (liveFlush live liveIndex dead pos).2.1[(liveFlush live liveIndex dead pos).1[i]]? = some i) ∧
    (∀ q p, (liveFlush live liveIndex dead pos).2.1[q]? = some p →
      p < (liveFlush live liveIndex dead pos).1.size ∧
      (liveFlush live liveIndex dead pos).1[p]! = q) ∧
    (∀ q, liveStatusOf (liveFlush live liveIndex dead pos).2.1
        (liveFlush live liveIndex dead pos).2.2 q = liveStatusOf liveIndex dead q ∨
      (liveStatusOf liveIndex dead q = .live ∧
       liveStatusOf (liveFlush live liveIndex dead pos).2.1
        (liveFlush live liveIndex dead pos).2.2 q = .dead)) := by
  intro live liveIndex dead
  induction live, liveIndex, dead using liveFlush.induct (pos := pos) with
  | case1 live liveIndex dead hgt hnone =>
    have hempty : live = #[] := Array.back?_eq_none_iff.mp hnone
    simp only [hempty, Array.size_empty] at hgt
    omega
  | case2 live liveIndex dead hgt q hb ih =>
    intro hwf hbwd
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hqpos : liveIndex[q]? = some ys.size := by
      have := hwf ys.size (by simp only [Array.size_push]; omega)
      simpa using this
    have hwf' : ∀ i, (h : i < ys.size) → (liveIndex.erase q)[ys[i]]? = some i := by
      intro i h
      have hi := hwf i (by simp only [Array.size_push]; omega)
      simp only [Array.getElem_push_lt h] at hi
      have hne : ys[i] ≠ q := by
        intro heq
        rw [heq, hqpos] at hi
        simp only [Option.some.injEq] at hi
        omega
      rw [Std.HashMap.getElem?_erase]
      simp [Ne.symm hne, hi]
    have hbwd' : ∀ q' p, (liveIndex.erase q)[q']? = some p → p < ys.size ∧ ys[p]! = q' := by
      intro q' p h
      rw [Std.HashMap.getElem?_erase] at h
      by_cases hqq' : q == q'
      · simp [hqq'] at h
      · simp only [hqq', Bool.false_eq_true, if_false] at h
        obtain ⟨hp1, hp2⟩ := hbwd q' p h
        simp only [Array.size_push] at hp1
        have hqne : q' ≠ q := fun heq => by simp [heq] at hqq'
        have hpne : p ≠ ys.size := by
          intro heq
          rw [heq, Array.getElem!_push_eq] at hp2
          exact hqne hp2.symm
        exact ⟨by omega, by rw [← hp2, Array.getElem!_push_lt (by omega)]⟩
    have hpop : (ys.push q).pop = ys := by simp
    simp only [hpop] at ih
    obtain ⟨ihwf, ihbwd, ihstatus⟩ := ih hwf' hbwd'
    unfold liveFlush
    simp only [hgt, if_true, hb, hpop]
    refine ⟨ihwf, ihbwd, ?_⟩
    · intro q'
      have hstep : liveStatusOf (liveIndex.erase q) (dead.insert q) q' =
          liveStatusOf liveIndex dead q' ∨
          (liveStatusOf liveIndex dead q' = .live ∧
           liveStatusOf (liveIndex.erase q) (dead.insert q) q' = .dead) := by
        by_cases hc : q' = q
        · right
          unfold liveStatusOf
          have hcontains : liveIndex.contains q' := by
            rw [hc, Std.HashMap.contains_eq_isSome_getElem?, hqpos]; rfl
          refine ⟨by simp [hcontains], ?_⟩
          simp [hc]
        · unfold liveStatusOf
          have h1 : (liveIndex.erase q).contains q' = liveIndex.contains q' := by
            rw [Std.HashMap.contains_erase]; simp [Ne.symm hc]
          have h2 : (dead.insert q).contains q' = dead.contains q' := by
            rw [Std.HashSet.contains_insert]; simp [Ne.symm hc]
          simp [h1, h2]
      rcases ihstatus q' with ihs | ⟨ihs1, ihs2⟩ <;> rcases hstep with hs | ⟨hs1, hs2⟩
      · exact Or.inl (ihs.trans hs)
      · exact Or.inr ⟨hs1, ihs.trans hs2⟩
      · exact Or.inr ⟨hs.symm.trans ihs1, ihs2⟩
      · exact absurd (ihs1.symm.trans hs2) (by simp)
  | case3 live liveIndex dead hle =>
    intro hwf hbwd
    unfold liveFlush
    simp only [hle, if_false]
    exact ⟨hwf, hbwd, fun q => Or.inl trivial⟩

/-- The flush preserves `LiveWF`. -/
theorem LiveWF.flush [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {live : Array State} {liveIndex : Std.HashMap State Nat} {dead : Std.HashSet State} (pos : Nat)
    (hwf : LiveWF live liveIndex) :
    LiveWF (liveFlush live liveIndex dead pos).1 (liveFlush live liveIndex dead pos).2.1 :=
  let h := liveFlush_spec pos live liveIndex dead hwf.fwd hwf.bwd
  ⟨h.1, h.2.1⟩

/-- A state the flush leaves dead was already dead, or sat in the flushed part of `live`. -/
theorem liveFlush_dead_or_old [Inhabited State] [LawfulBEq State] (pos : Nat) :
    ∀ (live : Array State) (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State) (q : State),
    q ∈ (liveFlush live liveIndex dead pos).2.2 →
    q ∈ dead ∨ ∃ p, pos ≤ p ∧ p < live.size ∧ live[p]! = q := by
  intro live liveIndex dead
  induction live, liveIndex, dead using liveFlush.induct (pos := pos) with
  | case1 live liveIndex dead hgt hnone =>
    intro q hq
    unfold liveFlush at hq
    simp only [hgt, if_true, hnone] at hq
    exact Or.inl hq
  | case2 live liveIndex dead hgt q0 hb ih =>
    intro q hq
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push q0).pop = ys := by simp
    simp only [hpop] at ih
    unfold liveFlush at hq
    simp only [hgt, if_true, hb, hpop] at hq
    rcases ih q hq with hc | ⟨p, hp1, hp2, hp3⟩
    · rw [Std.HashSet.mem_insert] at hc
      rcases hc with hc | hc
      · refine Or.inr ⟨ys.size, ?_, by simp, by rw [← beq_iff_eq.mp hc, Array.getElem!_push_eq]⟩
        simp only [Array.size_push] at hgt
        omega
      · exact Or.inl hc
    · refine Or.inr ⟨p, hp1, by simp only [Array.size_push]; omega, ?_⟩
      rw [Array.getElem!_push_lt hp2]
      exact hp3
  | case3 live liveIndex dead hle =>
    intro q hq
    unfold liveFlush at hq
    simp only [hle, if_false] at hq
    exact Or.inl hq

/-- The flush only ever adds to `dead`. -/
theorem liveFlush_dead_mono [Inhabited State] [LawfulBEq State] [LawfulHashable State] (pos : Nat) :
    ∀ (live : Array State) (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State) (q : State),
    q ∈ dead → q ∈ (liveFlush live liveIndex dead pos).2.2 := by
  intro live liveIndex dead
  induction live, liveIndex, dead using liveFlush.induct (pos := pos) with
  | case1 live liveIndex dead hgt hnone =>
    intro q hq
    unfold liveFlush
    simp only [hgt, if_true, hnone]
    exact hq
  | case2 live liveIndex dead hgt q0 hb ih =>
    intro q hq
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push q0).pop = ys := by simp
    simp only [hpop] at ih
    unfold liveFlush
    simp only [hgt, if_true, hb, hpop]
    exact ih q (Std.HashSet.mem_insert.mpr (Or.inr hq))
  | case3 live liveIndex dead hle =>
    intro q hq
    unfold liveFlush
    simp only [hle, if_false]
    exact hq

/-- Everything the flush takes off the stack is dead afterwards. -/
theorem liveFlush_dead_of_ge [Inhabited State] [LawfulBEq State] [LawfulHashable State] (pos : Nat) :
    ∀ (live : Array State) (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State) (i : Nat),
    pos ≤ i → i < live.size → live[i]! ∈ (liveFlush live liveIndex dead pos).2.2 := by
  intro live liveIndex dead
  induction live, liveIndex, dead using liveFlush.induct (pos := pos) with
  | case1 live liveIndex dead hgt hnone =>
    have hempty : live = #[] := Array.back?_eq_none_iff.mp hnone
    intro i _ hi
    simp [hempty] at hi
  | case2 live liveIndex dead hgt q0 hb ih =>
    intro i hpi hi
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push q0).pop = ys := by simp
    simp only [hpop] at ih
    unfold liveFlush
    simp only [hgt, if_true, hb, hpop]
    simp only [Array.size_push] at hi
    rcases Nat.lt_or_ge i ys.size with hlt | hge
    · rw [Array.getElem!_push_lt hlt]
      exact ih i hpi hlt
    · have hie : i = ys.size := by omega
      subst hie
      rw [Array.getElem!_push_eq]
      exact liveFlush_dead_mono pos ys (liveIndex.erase q0) (dead.insert q0) q0
        (Std.HashSet.mem_insert.mpr (Or.inl (by simp)))
  | case3 live liveIndex dead hle =>
    intro i hpi hi
    omega

/-- The flush leaves everything below `pos` where it was. -/
theorem liveFlush_getElem!_lt [Inhabited State] (pos : Nat) :
    ∀ (live : Array State) (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State) (i : Nat), i < pos →
    (liveFlush live liveIndex dead pos).1[i]! = live[i]! := by
  intro live liveIndex dead
  induction live, liveIndex, dead using liveFlush.induct (pos := pos) with
  | case1 live liveIndex dead hgt hnone =>
    intro i hi
    unfold liveFlush
    simp only [hgt, if_true, hnone]
  | case2 live liveIndex dead hgt q hb ih =>
    intro i hi
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push q).pop = ys := by simp
    simp only [hpop] at ih
    unfold liveFlush
    simp only [hgt, if_true, hb, hpop]
    have hilt : i < ys.size := by
      have hgt' : (ys.push q).size > pos := hgt
      simp only [Array.size_push] at hgt'
      omega
    rw [ih i hi, Array.getElem!_push_lt hilt]
  | case3 live liveIndex dead hle =>
    intro i hi
    unfold liveFlush
    simp only [hle, if_false]

/-- A touched state is still live or has joined the dead after the flush. -/
theorem liveFlush_touched_mono [Inhabited State] [LawfulBEq State] [LawfulHashable State] (pos : Nat) :
    ∀ (live : Array State) (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State) (s : State),
    s ∈ live ∨ s ∈ dead →
      s ∈ (liveFlush live liveIndex dead pos).1 ∨ s ∈ (liveFlush live liveIndex dead pos).2.2 := by
  intro live liveIndex dead
  induction live, liveIndex, dead using liveFlush.induct (pos := pos) with
  | case1 live liveIndex dead hgt hnone =>
    have hempty : live = #[] := Array.back?_eq_none_iff.mp hnone
    simp only [hempty, Array.size_empty] at hgt
    omega
  | case2 live liveIndex dead hgt q hb ih =>
    intro s hs
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push q).pop = ys := by simp
    simp only [hpop] at ih
    unfold liveFlush
    simp only [hgt, if_true, hb, hpop]
    refine ih s ?_
    rcases hs with hs | hs
    · rcases Array.mem_push.mp hs with hs' | rfl
      · exact Or.inl hs'
      · exact Or.inr (by rw [Std.HashSet.mem_insert]; simp)
    · exact Or.inr (by rw [Std.HashSet.mem_insert]; exact Or.inr hs)
  | case3 live liveIndex dead hle =>
    intro s hs
    unfold liveFlush
    simp only [hle, if_false]
    exact hs

/-- The flush drains `live` down to exactly `pos`, given `pos ≤ live.size`. -/
theorem liveFlush_size (pos : Nat) :
    ∀ (live : Array State) (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State),
    pos ≤ live.size → (liveFlush live liveIndex dead pos).1.size = pos := by
  intro live liveIndex dead
  induction live, liveIndex, dead using liveFlush.induct (pos := pos) with
  | case1 live liveIndex dead hgt hnone =>
    intro _
    have hempty : live = #[] := Array.back?_eq_none_iff.mp hnone
    simp only [hempty, Array.size_empty] at hgt
    omega
  | case2 live liveIndex dead hgt q hb ih =>
    intro hle
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push q).pop = ys := by simp
    have hgt' : (ys.push q).size > pos := hgt
    rw [hpop] at ih
    unfold liveFlush
    simp only [hgt, if_true, hb, hpop]
    exact ih (by simp only [Array.size_push] at hgt' ⊢; omega)
  | case3 live liveIndex dead hle' =>
    intro hle
    unfold liveFlush
    simp only [hle', if_false]
    omega

end LTLLib
