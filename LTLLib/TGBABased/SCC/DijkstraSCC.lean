/-
  Algorithm 3, Dijkstra's path-based SCC emptiness check: refines `GenericDFS.lean`'s abstract operations with
  two stacks, the DFS path and the open-SCC-root candidates.

  Also proves `push`/`update` never require well-formedness for their status-transition behavior, and that `pop`
  does (`DijkstraWellFormed`, `dijkstraWellFormed_init`/`_push`/`_update`/`_pop`).

  Renault, Duret-Lutz, Kordon, Poitrenaud, "Three SCC-based Emptiness Checks for Generalized Büchi Automata"
  (LPAR-19, 2013).


  live : hstack of ⟨Q⟩
  dead : store of ⟨Q⟩
  roots : rstack of ⟨root : int, acc : 2^F⟩

  GET_STATUS(q ∈ Q) → Status
    if live.get(q) ≠ -1
      return LIVE
    else if dead.has(q)
      return DEAD
    else
      return UNKNOWN

  PUSH(q ∈ Q) → Position
    Position p ← live.size()
    live.push(q)
    roots.push_trivial(dfs.size())
    return p

  UPDATE(acc ∈ 2^F, d ∈ Q)
    dpos ← live.get(d)
    ⟨r, a⟩ ← roots.pop()
    a ← a ∪ acc
    while dpos < dfs[r].pos
      ⟨r, la⟩ ← roots.pop()
      a ← a ∪ dfs[r].acc ∪ la
    roots.push_non_trivial(a, r, dfs.size() - 1)
    if a = F
      report counterexample found

  POP(s ∈ Step)
    if dfs.size() = roots.top_root()
      -- An SCC has been found.
      roots.pop()
      while live.size() > s.pos
        q ← live.pop()
        dead.add(q)

  Verified against the `TEmptinessChecker` contract as `dijkstraTChecker`: `dijkstraCheck_nonEmpty_valid` (a
  reported stem/loop really is a `TAcceptingCycle`) and `dijkstraCheck_empty_no_cycle` (an `.empty` answer proves none exists).

  Lean encoding notes:
  - `dfs[r].pos`/`dfs[r].acc` read the generic driver's Step stack, which no `DFSOps` operation is handed.
    `DijkstraAux` keeps its own `dfsInfo` instead, extended and shrunk in lockstep with `push`/`pop`, so `dfs.size()`
    is `dfsInfo.size` and `dfs[r].pos`/`dfs[r].acc` are `(dfsInfo[r]!).1`/`.2`. `UPDATE` indexes it at an arbitrary
    dfs-depth, so the `Position` the driver hands back on `pop` would not be enough on its own.
  - `push_non_trivial` and `push_trivial` implemented just as a standard `push` for now, no roots-stack compression applied.
  - Mark sets are `Nat` bitmasks rather than `Std.HashSet Nat`, so `a = F` is an O(1) equality against the all-ones mask `(1 <<< numMarks) - 1`.

  Sections:
  - Dijkstra's search state
  - PUSH and UPDATE
  - POP
  - Well-formedness and the basic status axioms
  - Range bookkeeping and `DijkstraRootsWF`
  - The range invariant and its preservation
  - Witness extraction and the `DFSOps` instance
  - Completeness: no accepting SCC survives an empty search
  - Lifting completeness to the whole search
  - The `TEmptinessChecker` contract
-/

import Std
import LTLLib.AbstractSpec.EmptinessCheck
import LTLLib.AbstractSpec.GraphPaths
import LTLLib.TGBABased.AbstractSpec.EmptinessCheck
import LTLLib.TGBABased.AbstractSpec.SCCTheory
import LTLLib.TGBABased.SCC.GenericDFS

namespace LTLLib

variable {State : Type u} [BEq State] [Hashable State]

/-! ## Dijkstra's search state -/

/-- Dijkstra's private search state, `dfsInfo` being the paper's `dfs` and `roots`' values positions in it.

"In practice, Algorithm 3 (without the green dotted boxes) actually manages three stacks: live, the set of LIVE
states; dfs, the subset of live that are on the DFS search path, represented … by a stack of positions in live;
and roots, the stack of SCC roots, stored as positions in the dfs stack. When given two consecutive roots,
roots[i] and roots[i+1], the set of states belonging to the SCC rooted in roots[i], are the states at positions
dfs[roots[i]].pos, …, dfs[roots[i+1]].pos − 1 in live." (Renault/Duret-Lutz/Kordon/Poitrenaud, §3.2) -/
structure DijkstraAux (State : Type u) [BEq State] [Hashable State] where
  live : Array State
  liveIndex : Std.HashMap State Nat -- position of each live state, for O(1) membership
  dead : Std.HashSet State
  roots : Array (Nat × Nat)  -- (dfs-depth, merged acc bitmask)
  dfsInfo : Array (Nat × Nat)  -- (pos, incoming-edge acc bitmask), per currently-open dfs-depth

def dijkstraInitAux : DijkstraAux State where
  live := #[]
  liveIndex := Std.HashMap.emptyWithCapacity 0
  dead := Std.HashSet.emptyWithCapacity 0
  roots := #[]
  dfsInfo := #[]

/-- The bitmask representation `roots`/`dfsInfo` use for mark-sets, cheap since `numMarks` is always small. -/
private def marksToBitmask (marks : Std.HashSet Nat) : Nat :=
  marks.toList.foldl (init := 0) fun mask m => mask ||| (1 <<< m)

/-- Status read off `liveIndex`/`dead` alone, for where no full `DijkstraAux` is in scope. -/
private def dijkstraStatusOf (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State) (q : State) :
    DFSStatus :=
  if liveIndex.contains q then .live else if dead.contains q then .dead else .unknown

def dijkstraGetStatus (aux : DijkstraAux State) (q : State) : DFSStatus :=
  dijkstraStatusOf aux.liveIndex aux.dead q

/-! ## PUSH and UPDATE -/

/-- `PUSH`, line 24 (`roots.push_trivial(dfs.size())`): a newly visited state starts as a trivial SCC candidate,
non-trivial ones are only created by merging on a back-edge (Renault/Duret-Lutz/Kordon/Poitrenaud, §3.2). -/
def dijkstraPush (aux : DijkstraAux State) (q : State) (marks : Std.HashSet Nat) :
    DijkstraAux State × Nat :=
  let pos := aux.live.size
  let dfsSize := aux.dfsInfo.size
  ({ aux with
      live := aux.live.push q
      liveIndex := aux.liveIndex.insert q pos
      roots := aux.roots.push (dfsSize, 0)
      dfsInfo := aux.dfsInfo.push (pos, marksToBitmask marks) },
   pos)

/-- The merge loop of `UPDATE`, lines 20-23. `r` arrives pre-popped, so line 22 folds `dfsInfo[r]`, the abandoned entry,
never the adopted one, and the settled root's own entry marks stay out of `a`. -/
private def dijkstraMergeRoots (dfsInfo : Array (Nat × Nat)) (dpos : Nat)
    (roots : Array (Nat × Nat)) (r : Nat) (a : Nat) :
    Array (Nat × Nat) × Nat × Nat :=
  if dpos < (dfsInfo[r]!).1 then
    match h : roots.back? with
    | none => (roots, r, a)
    | some (r1, la) => dijkstraMergeRoots dfsInfo dpos roots.pop r1 (a ||| (dfsInfo[r]!).2 ||| la)
  else (roots, r, a)
termination_by roots.size
decreasing_by
  have hne : roots.size > 0 := by
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp h
    simp [hys]
  simp only [Array.size_pop]; omega

def dijkstraUpdate (numMarks : Nat) (aux : DijkstraAux State)
    (marks : Std.HashSet Nat) (d : State) : DijkstraAux State × Bool :=
  match aux.roots.back? with
  | none => (aux, false)
  | some (r0, a0) =>
    let dpos := aux.liveIndex.getD d 0
    -- Line 19 (`a ← a ∪ acc`). No entry-marks seed, the loop folds those in if it moves past the top.
    let a0' := a0 ||| marksToBitmask marks
    let (roots, r, a) := dijkstraMergeRoots aux.dfsInfo dpos aux.roots.pop r0 a0'
    -- `a = F`, O(1) against the all-ones mask
    let found := a == (1 <<< numMarks) - 1
    ({ aux with roots := roots.push (r, a) }, found)

/-! ## POP -/

/-- The flush loop of `POP`, lines 30-32. -/
private def dijkstraFlushLive (live : Array State) (liveIndex : Std.HashMap State Nat)
    (dead : Std.HashSet State) (pos : Nat) :
    Array State × Std.HashMap State Nat × Std.HashSet State :=
  if live.size > pos then
    match live.back? with
    | none => (live, liveIndex, dead)
    | some q => dijkstraFlushLive live.pop (liveIndex.erase q) (dead.insert q) pos
  else (live, liveIndex, dead)
termination_by live.size
decreasing_by simp only [Array.size_pop]; omega

/-- `POP`, lines 27-32.
Dijkstra's merge is eager, so a popped state's SCC membership is already decided and
`POP` only ever confirms a root and flushes, never reporting a counterexample itself. -/
def dijkstraPop (aux : DijkstraAux State) (pos : Nat) : DijkstraAux State × Bool :=
  let dfsInfo' := aux.dfsInfo.pop
  match aux.roots.back? with
  | none => ({ aux with dfsInfo := dfsInfo' }, false)
  | some (r, _) =>
    if dfsInfo'.size = r then
      let (live, liveIndex, dead) := dijkstraFlushLive aux.live aux.liveIndex aux.dead pos
      ({ aux with
        dfsInfo := dfsInfo'
        roots := aux.roots.pop
        live := live
        liveIndex := liveIndex
        dead := dead }, false)
    else ({ aux with dfsInfo := dfsInfo' }, false)

/-! ## Well-formedness and the basic status axioms

`LawfulDFSOps` status laws cannot hold for an arbitrary (e.g. unreachable) `aux : DijkstraAux State`.
`DijkstraWellFormed` are the relevant invariants preserved to ensure it. -/

private theorem Array.getElem!_push_lt {α} [Inhabited α] {xs : Array α} {x : α} {i : Nat} (h : i < xs.size) :
    (xs.push x)[i]! = xs[i]! := by
  rw [getElem!_pos (xs.push x) i (by simpa using Nat.lt_succ_of_lt h), Array.getElem_push_lt h,
    getElem!_pos xs i h]

private theorem Array.getElem!_push_eq {α} [Inhabited α] {xs : Array α} {x : α} :
    (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos (xs.push x) xs.size (by simp), Array.getElem_push_eq]

/-- `live` and `liveIndex` agree in both directions. -/
structure DijkstraWellFormed [Inhabited State] (aux : DijkstraAux State) : Prop where
  -- every `live` position maps back to itself, which also rules out duplicate `live` entries
  fwd : ∀ i, (h : i < aux.live.size) → aux.liveIndex[aux.live[i]]? = some i
  -- every `liveIndex` entry names a real `live` slot, so a back-edge target's recorded position is real
  bwd : ∀ q p, aux.liveIndex[q]? = some p → p < aux.live.size ∧ aux.live[p]! = q

theorem dijkstraWellFormed_init [Inhabited State] : DijkstraWellFormed (dijkstraInitAux (State := State)) :=
  ⟨fun i h => by simp [dijkstraInitAux] at h, fun q p h => by simp [dijkstraInitAux] at h⟩

theorem dijkstraWellFormed_push [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (aux : DijkstraAux State) (q : State) (marks : Std.HashSet Nat) (hwf : DijkstraWellFormed aux)
    (hq : dijkstraGetStatus aux q = .unknown) : DijkstraWellFormed (dijkstraPush aux q marks).1 := by
  refine ⟨fun i h => ?_, fun q' p h => ?_⟩
  · unfold dijkstraPush at h ⊢
    simp only [Array.size_push] at h
    simp only
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · rw [Array.getElem_push_lt hlt]
      have hne : aux.live[i] ≠ q := by
        intro heq'
        have hpos := hwf.fwd i hlt
        rw [heq'] at hpos
        unfold dijkstraGetStatus dijkstraStatusOf at hq
        simp only [Std.HashMap.contains_eq_isSome_getElem?] at hq
        simp [hpos] at hq
      rw [Std.HashMap.getElem?_insert]
      simp [Ne.symm hne]
      exact hwf.fwd i hlt
    · subst heq
      rw [Array.getElem_push_eq, Std.HashMap.getElem?_insert]
      simp
  · unfold dijkstraPush at h ⊢
    simp only [Std.HashMap.getElem?_insert] at h
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

/-- `push` marks its target live regardless of prior status and leaves every other state's untouched,
the target being new is only needed for well-formedness. -/
theorem dijkstraPush_status [LawfulBEq State] [LawfulHashable State] (aux : DijkstraAux State) (q : State)
    (marks : Std.HashSet Nat) (q' : State) :
    dijkstraGetStatus (dijkstraPush aux q marks).1 q' = if q' == q then .live else dijkstraGetStatus aux q' := by
  unfold dijkstraGetStatus dijkstraStatusOf dijkstraPush
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

/-- `dijkstraUpdate` is pure `roots`-bookkeeping, it never touches `live`/`liveIndex`/`dead`/`dfsInfo` at all. -/
theorem dijkstraUpdate_fields (numMarks : Nat) (aux : DijkstraAux State) (marks : Std.HashSet Nat) (d : State) :
    (dijkstraUpdate numMarks aux marks d).1.live = aux.live ∧
    (dijkstraUpdate numMarks aux marks d).1.liveIndex = aux.liveIndex ∧
    (dijkstraUpdate numMarks aux marks d).1.dead = aux.dead ∧
    (dijkstraUpdate numMarks aux marks d).1.dfsInfo = aux.dfsInfo := by
  unfold dijkstraUpdate
  cases aux.roots.back? with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some x => obtain ⟨r0, a0⟩ := x; exact ⟨rfl, rfl, rfl, rfl⟩

theorem dijkstraWellFormed_update [Inhabited State] (numMarks : Nat) (aux : DijkstraAux State)
    (marks : Std.HashSet Nat) (d : State) (hwf : DijkstraWellFormed aux) :
    DijkstraWellFormed (dijkstraUpdate numMarks aux marks d).1 := by
  obtain ⟨hlive, hli, _, _⟩ := dijkstraUpdate_fields numMarks aux marks d
  refine ⟨fun i h => ?_, fun q p h => ?_⟩
  · simp only [hlive] at h ⊢
    simp only [hli]
    exact hwf.fwd i h
  · simp only [hli] at h
    simp only [hlive]
    exact hwf.bwd q p h

/-- `update` is pure bookkeeping, it never changes any state's status. -/
theorem dijkstraUpdate_status (numMarks : Nat) (aux : DijkstraAux State) (marks : Std.HashSet Nat) (d q : State) :
    dijkstraGetStatus (dijkstraUpdate numMarks aux marks d).1 q = dijkstraGetStatus aux q := by
  obtain ⟨_, hli, hdead, _⟩ := dijkstraUpdate_fields numMarks aux marks d
  unfold dijkstraGetStatus
  simp only [hli, hdead]

/-- `dijkstraFlushLive` preserves well-formedness, and every state's status is unchanged or promoted from live to dead, never demoted. -/
theorem dijkstraFlushLive_spec [Inhabited State] [LawfulBEq State] [LawfulHashable State] (pos : Nat) :
    ∀ (live : Array State) (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State),
    (∀ i, (h : i < live.size) → liveIndex[live[i]]? = some i) →
    (∀ q p, liveIndex[q]? = some p → p < live.size ∧ live[p]! = q) →
    (∀ i, (h : i < (dijkstraFlushLive live liveIndex dead pos).1.size) →
      (dijkstraFlushLive live liveIndex dead pos).2.1[(dijkstraFlushLive live liveIndex dead pos).1[i]]? = some i) ∧
    (∀ q p, (dijkstraFlushLive live liveIndex dead pos).2.1[q]? = some p →
      p < (dijkstraFlushLive live liveIndex dead pos).1.size ∧
      (dijkstraFlushLive live liveIndex dead pos).1[p]! = q) ∧
    (∀ q, dijkstraStatusOf (dijkstraFlushLive live liveIndex dead pos).2.1
        (dijkstraFlushLive live liveIndex dead pos).2.2 q = dijkstraStatusOf liveIndex dead q ∨
      (dijkstraStatusOf liveIndex dead q = .live ∧
       dijkstraStatusOf (dijkstraFlushLive live liveIndex dead pos).2.1
        (dijkstraFlushLive live liveIndex dead pos).2.2 q = .dead)) := by
  intro live liveIndex dead
  induction live, liveIndex, dead using dijkstraFlushLive.induct (pos := pos) with
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
    unfold dijkstraFlushLive
    simp only [hgt, if_true, hb, hpop]
    refine ⟨ihwf, ihbwd, ?_⟩
    · intro q'
      have hstep : dijkstraStatusOf (liveIndex.erase q) (dead.insert q) q' =
          dijkstraStatusOf liveIndex dead q' ∨
          (dijkstraStatusOf liveIndex dead q' = .live ∧
           dijkstraStatusOf (liveIndex.erase q) (dead.insert q) q' = .dead) := by
        by_cases hc : q' = q
        · right
          unfold dijkstraStatusOf
          have hcontains : liveIndex.contains q' := by
            rw [hc, Std.HashMap.contains_eq_isSome_getElem?, hqpos]; rfl
          refine ⟨by simp [hcontains], ?_⟩
          simp [hc]
        · unfold dijkstraStatusOf
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
    unfold dijkstraFlushLive
    simp only [hle, if_false]
    exact ⟨hwf, hbwd, fun q => Or.inl trivial⟩

/-- `dijkstraFlushLive` drains `live` down to exactly `pos`, given `pos ≤ live.size`. -/
theorem dijkstraFlushLive_size (pos : Nat) :
    ∀ (live : Array State) (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State),
    pos ≤ live.size → (dijkstraFlushLive live liveIndex dead pos).1.size = pos := by
  intro live liveIndex dead
  induction live, liveIndex, dead using dijkstraFlushLive.induct (pos := pos) with
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
    unfold dijkstraFlushLive
    simp only [hgt, if_true, hb, hpop]
    exact ih (by simp only [Array.size_push] at hgt' ⊢; omega)
  | case3 live liveIndex dead hle' =>
    intro hle
    unfold dijkstraFlushLive
    simp only [hle', if_false]
    omega

/-- `dijkstraPop` preserves well-formedness, the non-flush branches leaving `live`/`liveIndex` untouched. -/
theorem dijkstraWellFormed_pop [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (aux : DijkstraAux State) (pos : Nat) (hwf : DijkstraWellFormed aux) :
    DijkstraWellFormed (dijkstraPop aux pos).1 := by
  unfold dijkstraPop
  cases aux.roots.back? with
  | none => exact ⟨hwf.fwd, hwf.bwd⟩
  | some x =>
    obtain ⟨r, _⟩ := x
    by_cases h : aux.dfsInfo.pop.size = r
    · simp only [h, if_true]
      obtain ⟨hfwd, hbwd, _⟩ := dijkstraFlushLive_spec pos aux.live aux.liveIndex aux.dead hwf.fwd hwf.bwd
      exact ⟨hfwd, hbwd⟩
    · simp only [h, if_false]
      exact ⟨hwf.fwd, hwf.bwd⟩

/-- `pop` only ever promotes states from live to dead, never touching an unknown or dead one.

False without well-formedness: A `live` entry `liveIndex` does not know about would be flushed straight from `.unknown`. -/
theorem dijkstraPop_status [Inhabited State] [LawfulBEq State] [LawfulHashable State] (aux : DijkstraAux State)
    (pos : Nat) (hwf : DijkstraWellFormed aux) (q : State) :
    dijkstraGetStatus (dijkstraPop aux pos).1 q = dijkstraGetStatus aux q ∨
    (dijkstraGetStatus aux q = .live ∧ dijkstraGetStatus (dijkstraPop aux pos).1 q = .dead) := by
  unfold dijkstraGetStatus dijkstraPop
  cases aux.roots.back? with
  | none => exact Or.inl rfl
  | some x =>
    obtain ⟨r, _⟩ := x
    by_cases h : aux.dfsInfo.pop.size = r
    · simp only [h, if_true]
      exact (dijkstraFlushLive_spec pos aux.live aux.liveIndex aux.dead hwf.fwd hwf.bwd).2.2 q
    · simp only [h, if_false]
      exact Or.inl trivial

theorem dijkstraGetStatus_initAux [LawfulBEq State] [LawfulHashable State] (q : State) :
    dijkstraGetStatus (dijkstraInitAux (State := State)) q = .unknown := by
  unfold dijkstraGetStatus dijkstraStatusOf dijkstraInitAux
  simp

/-! ## Range bookkeeping and `DijkstraRootsWF`

Each `roots[i]` owns a contiguous slice of `live` (Renault et al. §4.1, quoted on `DijkstraAux`). Positions and
the merge's bitmask arithmetic only, no `succs`, connectivity is `DijkstraRangeInv` in the next section. -/

/-- Position in `live` where the range rooted at `roots[i]` begins. -/
def DijkstraAux.rangeStart (aux : DijkstraAux State) (i : Nat) : Nat := (aux.dfsInfo[(aux.roots[i]!).1]!).1

/-- One past the range's last `live` position, the next range's start, or `live.size` at the top. -/
def DijkstraAux.rangeEnd (aux : DijkstraAux State) (i : Nat) : Nat :=
  if i + 1 < aux.roots.size then aux.rangeStart (i + 1) else aux.live.size

/-- The states currently in the range rooted at `roots[i]`. -/
def DijkstraAux.range (aux : DijkstraAux State) (i : Nat) : Std.HashSet State :=
  (aux.live.extract (aux.rangeStart i) (aux.rangeEnd i)).foldl
    (init := Std.HashSet.emptyWithCapacity 0) fun acc s => acc.insert s

private theorem mem_foldl_insert [LawfulBEq State] (l : List State) (init : Std.HashSet State) (x : State) :
    x ∈ l.foldl (fun acc s => acc.insert s) init ↔ x ∈ init ∨ x ∈ l := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Std.HashSet.mem_insert, List.mem_cons, beq_iff_eq]
    tauto

/-- `x` is in the range rooted at `roots[i]` iff `live` holds it between `rangeStart i` and `rangeEnd i`. -/
theorem DijkstraAux.mem_range_iff [LawfulBEq State] [Inhabited State] (aux : DijkstraAux State) (i : Nat) (x : State) :
    x ∈ aux.range i ↔
      ∃ p, aux.rangeStart i ≤ p ∧ p < min (aux.rangeEnd i) aux.live.size ∧ aux.live[p]! = x := by
  unfold DijkstraAux.range
  rw [← Array.foldl_toList, mem_foldl_insert]
  simp only [Std.HashSet.not_mem_emptyWithCapacity, false_or, Array.mem_toList_iff,
    Array.mem_extract_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨aux.rangeStart i + k, by omega, by omega, by
      rw [getElem!_pos aux.live (aux.rangeStart i + k) (by omega)]⟩
  · rintro ⟨p, hp1, hp2, hp3⟩
    refine ⟨p - aux.rangeStart i, by omega, ?_⟩
    simp only [show aux.rangeStart i + (p - aux.rangeStart i) = p from by omega]
    rw [← hp3, getElem!_pos aux.live p (by omega)]

/-- Positional bookkeeping on `roots`/`dfsInfo` alone, what lets `range` tile `live` without gaps or overlaps. -/
structure DijkstraRootsWF (aux : DijkstraAux State) : Prop where
  -- dfs-depths are in-bounds and strictly increasing
  rootsBounds : ∀ i, (h : i < aux.roots.size) → (aux.roots[i]!).1 < aux.dfsInfo.size
  rootsMono : ∀ i j, i < j → j < aux.roots.size → (aux.roots[i]!).1 < (aux.roots[j]!).1
  dfsInfoOk : aux.roots.size ≤ aux.dfsInfo.size
  -- each `dfsInfo` entry is `live.size` at its own push time, which only grows
  dfsInfoMono : ∀ i j, i < j → j < aux.dfsInfo.size → (aux.dfsInfo[i]!).1 < (aux.dfsInfo[j]!).1
  dfsInfoLt : ∀ i, i < aux.dfsInfo.size → (aux.dfsInfo[i]!).1 < aux.live.size
  -- `roots` and `dfsInfo` are simultaneously nonempty, so the driver's top frame always has a range to sit in
  rootsBase : ∀ h : 0 < aux.roots.size, (aux.roots[0]!).1 = 0
  rootsEmpty : aux.roots.size = 0 → aux.dfsInfo.size = 0
  dfsInfoBase : ∀ h : 0 < aux.dfsInfo.size, (aux.dfsInfo[0]!).1 = 0
  liveEmptyOfDfsEmpty : aux.dfsInfo.size = 0 → aux.live.size = 0

/-- A still-open driver frame always has a `roots`-range to sit inside. -/
theorem DijkstraRootsWF.roots_pos_of_dfsInfo_pos {aux : DijkstraAux State} (hwf : DijkstraRootsWF aux)
    (h : 0 < aux.dfsInfo.size) : 0 < aux.roots.size := by
  by_contra hc
  exact absurd (hwf.rootsEmpty (by omega)) (by omega)

theorem dijkstraRootsWF_init : DijkstraRootsWF (dijkstraInitAux (State := State)) :=
  ⟨fun i h => by simp [dijkstraInitAux] at h, fun i j _ hj => by simp [dijkstraInitAux] at hj,
   by simp [dijkstraInitAux], fun i j _ hj => by simp [dijkstraInitAux] at hj,
   fun i hi => by simp [dijkstraInitAux] at hi, fun h => by simp [dijkstraInitAux] at h,
   fun _ => by simp [dijkstraInitAux], fun h => by simp [dijkstraInitAux] at h, fun _ => by simp [dijkstraInitAux]⟩

private theorem Array.getElem!_push_of_size_zero {α} [Inhabited α] {xs : Array α} (a : α)
    (h : xs.size = 0) : (xs.push a)[0]! = a := by
  rw [← h]; exact Array.getElem!_push_eq

private theorem Array.getElem!_pop_lt {α} [Inhabited α] {xs : Array α} {i : Nat} (h : i < xs.pop.size) :
    xs.pop[i]! = xs[i]! := by
  rcases hb : xs.back? with _ | y
  · have hxs : xs = #[] := Array.back?_eq_none_iff.mp hb
    simp [hxs] at h
  · obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push y).pop = ys := by simp
    rw [hpop] at h ⊢
    exact (Array.getElem!_push_lt h).symm

theorem dijkstraRootsWF_push (aux : DijkstraAux State) (q : State) (marks : Std.HashSet Nat)
    (hwf : DijkstraRootsWF aux) : DijkstraRootsWF (dijkstraPush aux q marks).1 := by
  obtain ⟨hbounds, hmono, hok, hdmono, hdlt, hbase, hempty, hdbase, hlempty⟩ := hwf
  unfold dijkstraPush
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i h
    simp only [Array.size_push] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · rw [Array.getElem!_push_lt hlt]; exact (hbounds i hlt).trans (by simp)
    · subst heq; rw [Array.getElem!_push_eq]; simp
  · intro i j hij h
    simp only [Array.size_push] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hjlt | hjeq
    · rw [Array.getElem!_push_lt (hij.trans hjlt), Array.getElem!_push_lt hjlt]
      exact hmono i j hij hjlt
    · subst hjeq
      rw [Array.getElem!_push_lt hij, Array.getElem!_push_eq]
      simp; exact hbounds i hij
  · simp only [Array.size_push]; omega
  · intro i j hij h
    simp only [Array.size_push] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hjlt | hjeq
    · rw [Array.getElem!_push_lt (hij.trans hjlt), Array.getElem!_push_lt hjlt]
      exact hdmono i j hij hjlt
    · subst hjeq
      rw [Array.getElem!_push_lt hij, Array.getElem!_push_eq]
      simp; exact hdlt i hij
  · intro i h
    simp only [Array.size_push] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | heq
    · rw [Array.getElem!_push_lt hlt]; exact (hdlt i hlt).trans (by simp)
    · subst heq; rw [Array.getElem!_push_eq]; simp
  · intro _
    simp only
    by_cases hc : 0 < aux.roots.size
    · rw [Array.getElem!_push_lt hc]; exact hbase hc
    · have hempty' : aux.roots = #[] := Array.eq_empty_of_size_eq_zero (by omega)
      rw [hempty']
      have : aux.dfsInfo.size = 0 := hempty (by omega)
      simp [this]
  · simp only [Array.size_push]; omega
  · intro _
    simp only
    by_cases hc : 0 < aux.dfsInfo.size
    · rw [Array.getElem!_push_lt hc]; exact hdbase hc
    · have hz : aux.dfsInfo.size = 0 := by omega
      have hkey : (aux.dfsInfo.push (aux.live.size, marksToBitmask marks))[aux.dfsInfo.size]! =
          (aux.live.size, marksToBitmask marks) := Array.getElem!_push_eq
      rw [hz] at hkey
      rw [hkey]
      exact hlempty hz
  · simp only [Array.size_push]; omega

/-- `DijkstraRootsWF`'s `roots`-only facts, relativized to an arbitrary `bound` so the merge loop can carry them. -/
private def RootsChain (roots : Array (Nat × Nat)) (bound : Nat) : Prop :=
  (∀ i, i < roots.size → (roots[i]!).1 < bound) ∧
  (∀ i j, i < j → j < roots.size → (roots[i]!).1 < (roots[j]!).1) ∧
  (∀ h : 0 < roots.size, (roots[0]!).1 = 0) ∧
  (roots.size = 0 → bound = 0)

private theorem DijkstraRootsWF.chain_pop {aux : DijkstraAux State} (hwf : DijkstraRootsWF aux)
    {ys : Array (Nat × Nat)} {r0 a0 : Nat} (hys : aux.roots = ys.push (r0, a0)) :
    RootsChain ys r0 := by
  obtain ⟨_, hmono, _, _, _, hbase, _, _, _⟩ := hwf
  refine ⟨fun i hi => ?_, fun i j hij hj => ?_, fun hpos => ?_, fun hemp => ?_⟩
  · have := hmono i ys.size hi (by rw [hys]; simp)
    rwa [hys, Array.getElem!_push_lt hi, Array.getElem!_push_eq] at this
  · have hjb : j < aux.roots.size := by rw [hys]; simp; omega
    have := hmono i j hij hjb
    rwa [hys, Array.getElem!_push_lt (hij.trans hj), Array.getElem!_push_lt hj] at this
  · have hb0 := hbase (show 0 < aux.roots.size from by rw [hys]; simp)
    rwa [hys, Array.getElem!_push_lt hpos] at hb0
  · have hb0 := hbase (show 0 < aux.roots.size from by rw [hys]; simp)
    have hb0' : aux.roots[ys.size]!.1 = 0 := by rw [hemp]; exact hb0
    rwa [hys, Array.getElem!_push_eq] at hb0'

private theorem dijkstraMergeRoots_spec (dfsInfo : Array (Nat × Nat)) (dpos : Nat) :
    ∀ (roots : Array (Nat × Nat)) (r a : Nat), r < dfsInfo.size → RootsChain roots r →
    (dijkstraMergeRoots dfsInfo dpos roots r a).1.size ≤ roots.size ∧
    (dijkstraMergeRoots dfsInfo dpos roots r a).2.1 < dfsInfo.size ∧
    RootsChain (dijkstraMergeRoots dfsInfo dpos roots r a).1 (dijkstraMergeRoots dfsInfo dpos roots r a).2.1 ∧
    ∀ i, i < (dijkstraMergeRoots dfsInfo dpos roots r a).1.size →
      (dijkstraMergeRoots dfsInfo dpos roots r a).1[i]! = roots[i]! := by
  intro roots r a
  induction roots, r, a using dijkstraMergeRoots.induct dfsInfo dpos with
  | case1 roots r a hcond hnone =>
    intro hr hchain
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hnone]
    exact ⟨le_refl _, hr, hchain, fun i _ => rfl⟩
  | case2 roots r a hcond r1 la hb ih =>
    intro hr hchain
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    obtain ⟨hbounds, hmono, hbase0, hrzero⟩ := hchain
    have hpop : (ys.push (r1, la)).pop = ys := by simp
    have hr1 : r1 < r := by
      have := hbounds ys.size (by simp)
      rwa [Array.getElem!_push_eq] at this
    have hys' : RootsChain ys r1 := by
      refine ⟨fun i hi => ?_, fun i j hij hj => ?_, fun hpos => ?_, fun hempty => ?_⟩
      · have := hmono i ys.size hi (by simp)
        rwa [Array.getElem!_push_lt hi, Array.getElem!_push_eq] at this
      · have := hmono i j hij (hj.trans (by simp))
        rwa [Array.getElem!_push_lt (hij.trans hj), Array.getElem!_push_lt hj] at this
      · have hb0 := hbase0 (show 0 < (ys.push (r1, la)).size from by simp)
        rwa [Array.getElem!_push_lt hpos] at hb0
      · have hb0 := hbase0 (show 0 < (ys.push (r1, la)).size from by simp)
        have hb0' : (ys.push (r1, la))[ys.size]!.1 = 0 := by rw [hempty]; exact hb0
        rwa [Array.getElem!_push_eq] at hb0'
    have hihyp := ih (by omega) (by rw [hpop]; exact hys')
    rw [hpop] at hihyp
    obtain ⟨h1, h2, h3, h4⟩ := hihyp
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hb]
    dsimp only
    rw [hpop]
    refine ⟨by simp only [Array.size_push]; omega, h2, h3, fun i hi => ?_⟩
    have hilt : i < ys.size := lt_of_lt_of_le hi h1
    rw [h4 i hi, Array.getElem!_push_lt hilt]
  | case3 roots r a hcond =>
    intro hr hchain
    unfold dijkstraMergeRoots
    simp only [hcond, if_false]
    exact ⟨le_refl _, hr, hchain, fun i _ => trivial⟩

private theorem dijkstraMergeRoots_bitmask_mono (dfsInfo : Array (Nat × Nat)) (dpos m : Nat) :
    ∀ (roots : Array (Nat × Nat)) (r a : Nat), a.testBit m = true →
      (dijkstraMergeRoots dfsInfo dpos roots r a).2.2.testBit m = true := by
  intro roots r a
  induction roots, r, a using dijkstraMergeRoots.induct dfsInfo dpos with
  | case1 roots r a hcond hnone =>
    intro hm
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hnone]
    exact hm
  | case2 roots r a hcond r1 la hb ih =>
    intro hm
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hb]
    dsimp only
    exact ih (by simp [Nat.testBit_or, hm])
  | case3 roots r a hcond =>
    intro hm
    unfold dijkstraMergeRoots
    simp only [hcond, if_false]
    exact hm

private theorem dijkstraMergeRoots_bitmask_absorbs (dfsInfo : Array (Nat × Nat)) (dpos : Nat) :
    ∀ (roots : Array (Nat × Nat)) (r a : Nat) (j : Nat),
      (dijkstraMergeRoots dfsInfo dpos roots r a).1.size ≤ j → j < roots.size → ∀ m,
        (roots[j]!).2.testBit m = true → (dijkstraMergeRoots dfsInfo dpos roots r a).2.2.testBit m = true := by
  intro roots r a
  induction roots, r, a using dijkstraMergeRoots.induct dfsInfo dpos with
  | case1 roots r a hcond hnone =>
    intro j hj1 hj2 m hm
    have hempty : roots = #[] := Array.back?_eq_none_iff.mp hnone
    rw [hempty] at hj2
    simp at hj2
  | case2 roots r a hcond r1 la hb ih =>
    intro j hj1 hj2 m hm
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push (r1, la)).pop = ys := by simp
    have hj1' : (dijkstraMergeRoots dfsInfo dpos (ys.push (r1, la)).pop r1
        (a ||| (dfsInfo[r]!).2 ||| la)).1.size ≤ j := by
      unfold dijkstraMergeRoots at hj1
      simp only [hcond, if_true] at hj1
      rw [hb] at hj1
      dsimp only at hj1
      exact hj1
    by_cases hje : j < ys.size
    · have hm' : (ys[j]!).2.testBit m = true := by rwa [Array.getElem!_push_lt hje] at hm
      have hres := ih j hj1' (by rwa [hpop]) m (by rwa [hpop])
      simp only [hpop] at hres
      unfold dijkstraMergeRoots
      simp only [hcond, if_true]
      rw [hb]
      dsimp only
      simp only [hpop]
      exact hres
    · have hjeq : j = ys.size := by simp at hj2; omega
      have heq : (ys.push (r1, la))[j]! = (r1, la) := by rw [hjeq]; exact Array.getElem!_push_eq
      rw [heq] at hm
      have hfold : (a ||| (dfsInfo[r]!).2 ||| la).testBit m = true := by
        simp only [Nat.testBit_or, hm, Bool.or_true]
      have hres := dijkstraMergeRoots_bitmask_mono dfsInfo dpos m ys r1 _ hfold
      unfold dijkstraMergeRoots
      simp only [hcond, if_true]
      rw [hb]
      dsimp only
      rw [hpop]
      exact hres
  | case3 roots r a hcond =>
    intro j hj1 hj2 m hm
    unfold dijkstraMergeRoots at hj1
    simp only [hcond, if_false] at hj1
    omega

private theorem dijkstraMergeRoots_dfsInfo_absorbs_self (dfsInfo : Array (Nat × Nat)) (dpos : Nat) :
    ∀ (roots : Array (Nat × Nat)) (r a : Nat),
      (dijkstraMergeRoots dfsInfo dpos roots r a).1.size < roots.size → ∀ m,
        (dfsInfo[r]!).2.testBit m = true →
          (dijkstraMergeRoots dfsInfo dpos roots r a).2.2.testBit m = true := by
  intro roots r a
  induction roots, r, a using dijkstraMergeRoots.induct dfsInfo dpos with
  | case1 roots r a hcond hnone =>
    intro hlt m hm
    have hempty : roots = #[] := Array.back?_eq_none_iff.mp hnone
    rw [hempty] at hlt
    simp at hlt
  | case2 roots r a hcond r1 la hb _ =>
    intro _ m hm
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push (r1, la)).pop = ys := by simp
    have hfold : (a ||| (dfsInfo[r]!).2 ||| la).testBit m = true := by
      simp only [Nat.testBit_or, hm, Bool.or_true, Bool.true_or]
    have hres := dijkstraMergeRoots_bitmask_mono dfsInfo dpos m ys r1 _ hfold
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hb]
    dsimp only
    rw [hpop]
    exact hres
  | case3 roots r a hcond =>
    intro hlt m hm
    unfold dijkstraMergeRoots at hlt
    simp only [hcond, if_false] at hlt
    omega

private theorem dijkstraMergeRoots_dfsInfo_absorbs (dfsInfo : Array (Nat × Nat)) (dpos : Nat) :
    ∀ (roots : Array (Nat × Nat)) (r a : Nat) (j : Nat),
      (dijkstraMergeRoots dfsInfo dpos roots r a).1.size < j → j < roots.size → ∀ m,
        (dfsInfo[(roots[j]!).1]!).2.testBit m = true →
          (dijkstraMergeRoots dfsInfo dpos roots r a).2.2.testBit m = true := by
  intro roots r a
  induction roots, r, a using dijkstraMergeRoots.induct dfsInfo dpos with
  | case1 roots r a hcond hnone =>
    intro j hj1 hj2 m hm
    have hempty : roots = #[] := Array.back?_eq_none_iff.mp hnone
    rw [hempty] at hj2
    simp at hj2
  | case2 roots r a hcond r1 la hb ih =>
    intro j hj1 hj2 m hm
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push (r1, la)).pop = ys := by simp
    have hj1' : (dijkstraMergeRoots dfsInfo dpos (ys.push (r1, la)).pop r1
        (a ||| (dfsInfo[r]!).2 ||| la)).1.size < j := by
      unfold dijkstraMergeRoots at hj1
      simp only [hcond, if_true] at hj1
      rw [hb] at hj1
      dsimp only at hj1
      exact hj1
    by_cases hje : j < ys.size
    · have hm' : (dfsInfo[(ys[j]!).1]!).2.testBit m = true := by
        rwa [Array.getElem!_push_lt hje] at hm
      have hres := ih j hj1' (by rwa [hpop]) m (by rwa [hpop])
      simp only [hpop] at hres
      unfold dijkstraMergeRoots
      simp only [hcond, if_true]
      rw [hb]
      dsimp only
      simp only [hpop]
      exact hres
    -- `j` is the entry being stripped right now, so its own root only picks the marks up one step later,
    -- which `hj1'` guarantees actually happens.
    · have hjeq : j = ys.size := by simp at hj2; omega
      have heq : (ys.push (r1, la))[j]! = (r1, la) := by rw [hjeq]; exact Array.getElem!_push_eq
      simp only [heq] at hm
      have hres := dijkstraMergeRoots_dfsInfo_absorbs_self dfsInfo dpos ys r1
        (a ||| (dfsInfo[r]!).2 ||| la) (by rw [hpop] at hj1'; omega) m hm
      unfold dijkstraMergeRoots
      simp only [hcond, if_true]
      rw [hb]
      dsimp only
      rw [hpop]
      exact hres
  | case3 roots r a hcond =>
    intro j hj1 hj2 m hm
    unfold dijkstraMergeRoots at hj1
    simp only [hcond, if_false] at hj1
    omega

private theorem dijkstraMergeRoots_size_le (dfsInfo : Array (Nat × Nat)) (dpos : Nat) :
    ∀ (roots : Array (Nat × Nat)) (r a : Nat),
      (dijkstraMergeRoots dfsInfo dpos roots r a).1.size ≤ roots.size := by
  intro roots r a
  induction roots, r, a using dijkstraMergeRoots.induct dfsInfo dpos with
  | case1 roots r a hcond hnone =>
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hnone]
  | case2 roots r a hcond r1 la hb ih =>
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push (r1, la)).pop = ys := by simp
    simp only [hpop] at ih
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hb]
    dsimp only
    rw [hpop]
    simp only [Array.size_push]
    omega
  | case3 roots r a hcond =>
    unfold dijkstraMergeRoots
    simp only [hcond, if_false]
    exact Nat.le_refl _

private theorem dijkstraMergeRoots_bitmask_elim (dfsInfo : Array (Nat × Nat)) (dpos : Nat) (P : Nat → Prop) :
    ∀ (roots : Array (Nat × Nat)) (r a : Nat),
      (∀ m, a.testBit m = true → P m) →
      (∀ j, (dijkstraMergeRoots dfsInfo dpos roots r a).1.size ≤ j → j < roots.size →
        ∀ m, (roots[j]!).2.testBit m = true → P m) →
      ((dijkstraMergeRoots dfsInfo dpos roots r a).1.size < roots.size →
        ∀ m, (dfsInfo[r]!).2.testBit m = true → P m) →
      (∀ j, (dijkstraMergeRoots dfsInfo dpos roots r a).1.size < j → j < roots.size →
        ∀ m, (dfsInfo[(roots[j]!).1]!).2.testBit m = true → P m) →
      ∀ m, (dijkstraMergeRoots dfsInfo dpos roots r a).2.2.testBit m = true → P m := by
  intro roots r a
  induction roots, r, a using dijkstraMergeRoots.induct dfsInfo dpos with
  | case1 roots r a hcond hnone =>
    intro ha _ _ _ m hm
    refine ha m ?_
    unfold dijkstraMergeRoots at hm
    simp only [hcond, if_true] at hm
    rwa [hnone] at hm
  | case2 roots r a hcond r1 la hb ih =>
    intro ha hroots hself hdfs m hm
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push (r1, la)).pop = ys := by simp
    simp only [hpop] at ih
    have hstep : dijkstraMergeRoots dfsInfo dpos (ys.push (r1, la)) r a =
        dijkstraMergeRoots dfsInfo dpos ys r1 (a ||| (dfsInfo[r]!).2 ||| la) := by
      conv_lhs => unfold dijkstraMergeRoots
      simp only [hcond, if_true]
      rw [hb]
      dsimp only
      rw [hpop]
    rw [hstep] at hroots hself hdfs hm
    have hle := dijkstraMergeRoots_size_le dfsInfo dpos ys r1 (a ||| (dfsInfo[r]!).2 ||| la)
    have hsizelt : (dijkstraMergeRoots dfsInfo dpos ys r1 (a ||| (dfsInfo[r]!).2 ||| la)).1.size
        < (ys.push (r1, la)).size := by simp only [Array.size_push]; omega
    refine ih ?_ ?_ ?_ ?_ m hm
    -- the seed splits three ways: the old accumulator, the root being abandoned, and the entry just popped
    · intro m' hm'
      simp only [Nat.testBit_or, Bool.or_eq_true] at hm'
      rcases hm' with hm' | hm'
      · rcases hm' with hm' | hm'
        · exact ha m' hm'
        · exact hself hsizelt m' hm'
      · exact hroots ys.size hle (by simp) m'
          (by rw [Array.getElem!_push_eq]; exact hm')
    · intro j hj1 hj2 m' hm'
      exact hroots j hj1 (by simp only [Array.size_push]; omega) m'
        (by rw [Array.getElem!_push_lt hj2]; exact hm')
    · intro hlt m' hm'
      exact hdfs ys.size hlt (by simp) m' (by rw [Array.getElem!_push_eq]; exact hm')
    · intro j hj1 hj2 m' hm'
      exact hdfs j hj1 (by simp only [Array.size_push]; omega) m'
        (by rw [Array.getElem!_push_lt hj2]; exact hm')
  | case3 roots r a hcond =>
    intro ha _ _ _ m hm
    refine ha m ?_
    unfold dijkstraMergeRoots at hm
    simpa only [hcond, if_false] using hm

private theorem allOnesMask_eq (numMarks : Nat) : (1 <<< numMarks) - 1 = 2 ^ numMarks - 1 := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]

private theorem eq_allOnesMask_of_testBit_cover {a numMarks : Nat} (hbound : a < 2 ^ numMarks)
    (hcov : ∀ m, m < numMarks → a.testBit m = true) : a = (1 <<< numMarks) - 1 := by
  rw [allOnesMask_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_two_pow_sub_one]
  by_cases hi : i < numMarks
  · simp only [hi, decide_true]
    exact hcov i hi
  · simp only [hi, decide_false]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hbound (Nat.pow_le_pow_right (by omega) (by omega)))

private theorem foldl_or_lt_two_pow {numMarks : Nat} :
    ∀ (l : List Nat), (∀ m ∈ l, m < numMarks) → ∀ init, init < 2 ^ numMarks →
      l.foldl (fun mask m => mask ||| (1 <<< m)) init < 2 ^ numMarks
  | [], _, init, hinit => hinit
  | a :: t, hl, init, hinit => by
    simp only [List.foldl_cons]
    refine foldl_or_lt_two_pow t (fun m hm => hl m (List.mem_cons_of_mem _ hm)) _ ?_
    refine Nat.or_lt_two_pow hinit ?_
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by omega) (hl a (List.mem_cons_self ..))

private theorem marksToBitmask_lt {marks : Std.HashSet Nat} {numMarks : Nat}
    (hb : ∀ m ∈ marks, m < numMarks) : marksToBitmask marks < 2 ^ numMarks := by
  unfold marksToBitmask
  exact foldl_or_lt_two_pow marks.toList (fun m hm => hb m (Std.HashSet.mem_toList.mp hm)) 0 (Nat.two_pow_pos numMarks)

private theorem foldl_or_testBit :
    ∀ (l : List Nat) (init m : Nat), init.testBit m = true ∨ m ∈ l →
      (l.foldl (fun mask k => mask ||| (1 <<< k)) init).testBit m = true
  | [], _, _, h => by simpa using h
  | a :: t, init, m, h => by
    simp only [List.foldl_cons]
    refine foldl_or_testBit t _ m ?_
    rcases h with h | h
    · exact Or.inl (by simp [h])
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl (by simp [Nat.shiftLeft_eq, Nat.testBit_two_pow_self])
      · exact Or.inr h

private theorem marksToBitmask_testBit {marks : Std.HashSet Nat} {m : Nat} (hm : m ∈ marks) :
    (marksToBitmask marks).testBit m = true := by
  unfold marksToBitmask
  exact foldl_or_testBit marks.toList 0 m (Or.inr (Std.HashSet.mem_toList.mpr hm))

private theorem foldl_or_testBit_elim :
    ∀ (l : List Nat) (init m : Nat),
      (l.foldl (fun mask k => mask ||| (1 <<< k)) init).testBit m = true → init.testBit m = true ∨ m ∈ l
  | [], _, _, h => by simpa using h
  | a :: t, init, m, h => by
    simp only [List.foldl_cons] at h
    rcases foldl_or_testBit_elim t _ m h with h' | h'
    · simp only [Nat.testBit_or, Bool.or_eq_true] at h'
      rcases h' with h' | h'
      · exact Or.inl h'
      · rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow] at h'
        exact Or.inr (by simp [(of_decide_eq_true h').symm])
    · exact Or.inr (List.mem_cons_of_mem _ h')

private theorem marksToBitmask_mem {marks : Std.HashSet Nat} {m : Nat}
    (hm : (marksToBitmask marks).testBit m = true) : m ∈ marks := by
  unfold marksToBitmask at hm
  rcases foldl_or_testBit_elim marks.toList 0 m hm with h | h
  · simp at h
  · exact Std.HashSet.mem_toList.mp h

private theorem getElem!_pair_default_snd_lt (numMarks : Nat) : (default : Nat × Nat).2 < 2 ^ numMarks :=
  Nat.two_pow_pos numMarks

private theorem dijkstraMergeRoots_bitmask_bound (dfsInfo : Array (Nat × Nat)) (dpos numMarks : Nat)
    (hdfs : ∀ i : Nat, (dfsInfo[i]!).2 < 2 ^ numMarks) :
    ∀ (roots : Array (Nat × Nat)) (r a : Nat), a < 2 ^ numMarks →
      (∀ i : Nat, (roots[i]!).2 < 2 ^ numMarks) →
      (dijkstraMergeRoots dfsInfo dpos roots r a).2.2 < 2 ^ numMarks := by
  intro roots r a
  induction roots, r, a using dijkstraMergeRoots.induct dfsInfo dpos with
  | case1 roots r a hcond hnone =>
    intro ha _
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hnone]
    exact ha
  | case2 roots r a hcond r1 la hb ih =>
    intro ha hroots
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push (r1, la)).pop = ys := by simp
    simp only [hpop] at ih
    have hla : la < 2 ^ numMarks := by
      have := hroots ys.size
      rwa [Array.getElem!_push_eq] at this
    have hys' : ∀ i : Nat, (ys[i]!).2 < 2 ^ numMarks := by
      intro i
      by_cases hi : i < ys.size
      · have := hroots i; rwa [Array.getElem!_push_lt hi] at this
      · rw [getElem!_neg ys i hi]; exact getElem!_pair_default_snd_lt numMarks
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hb]
    dsimp only
    rw [hpop]
    exact ih (Nat.or_lt_two_pow (Nat.or_lt_two_pow ha (hdfs r)) hla) hys'
  | case3 roots r a hcond =>
    intro ha _
    unfold dijkstraMergeRoots
    simp only [hcond, if_false]
    exact ha

private theorem array_pop_bitmask_bound {numMarks : Nat} {xs : Array (Nat × Nat)}
    (hxs : ∀ i : Nat, (xs[i]!).2 < 2 ^ numMarks) : ∀ i : Nat, (xs.pop[i]!).2 < 2 ^ numMarks := by
  intro i
  by_cases hi : i < xs.pop.size
  · rw [Array.getElem!_pop_lt hi]; exact hxs i
  · rw [getElem!_neg xs.pop i hi]; exact getElem!_pair_default_snd_lt numMarks

private theorem dijkstraFlushLive_dead_or_old [Inhabited State] [LawfulBEq State] (pos : Nat) :
    ∀ (live : Array State) (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State) (q : State),
    q ∈ (dijkstraFlushLive live liveIndex dead pos).2.2 →
    q ∈ dead ∨ ∃ p, pos ≤ p ∧ p < live.size ∧ live[p]! = q := by
  intro live liveIndex dead
  induction live, liveIndex, dead using dijkstraFlushLive.induct (pos := pos) with
  | case1 live liveIndex dead hgt hnone =>
    intro q hq
    unfold dijkstraFlushLive at hq
    simp only [hgt, if_true, hnone] at hq
    exact Or.inl hq
  | case2 live liveIndex dead hgt q0 hb ih =>
    intro q hq
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push q0).pop = ys := by simp
    simp only [hpop] at ih
    unfold dijkstraFlushLive at hq
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
    unfold dijkstraFlushLive at hq
    simp only [hle, if_false] at hq
    exact Or.inl hq

private theorem dijkstraFlushLive_getElem!_lt [Inhabited State] (pos : Nat) :
    ∀ (live : Array State) (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State) (i : Nat), i < pos →
    (dijkstraFlushLive live liveIndex dead pos).1[i]! = live[i]! := by
  intro live liveIndex dead
  induction live, liveIndex, dead using dijkstraFlushLive.induct (pos := pos) with
  | case1 live liveIndex dead hgt hnone =>
    intro i hi
    unfold dijkstraFlushLive
    simp only [hgt, if_true, hnone]
  | case2 live liveIndex dead hgt q hb ih =>
    intro i hi
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push q).pop = ys := by simp
    simp only [hpop] at ih
    unfold dijkstraFlushLive
    simp only [hgt, if_true, hb, hpop]
    have hilt : i < ys.size := by
      have hgt' : (ys.push q).size > pos := hgt
      simp only [Array.size_push] at hgt'
      omega
    rw [ih i hi, Array.getElem!_push_lt hilt]
  | case3 live liveIndex dead hle =>
    intro i hi
    unfold dijkstraFlushLive
    simp only [hle, if_false]

private theorem dijkstraMergeRoots_locate (dfsInfo : Array (Nat × Nat)) (dpos : Nat)
    (hdbase0 : 0 < dfsInfo.size → (dfsInfo[0]!).1 = 0) :
    ∀ (full roots : Array (Nat × Nat)) (r a : Nat), r < dfsInfo.size → roots.size ≤ full.size →
    RootsChain roots r → (∀ i, i < roots.size → roots[i]! = full[i]!) → r = (full[roots.size]!).1 →
    (dijkstraMergeRoots dfsInfo dpos roots r a).2.1 =
      (full[(dijkstraMergeRoots dfsInfo dpos roots r a).1.size]!).1 ∧
    (dfsInfo[(dijkstraMergeRoots dfsInfo dpos roots r a).2.1]!).1 ≤ dpos ∧
    ((dijkstraMergeRoots dfsInfo dpos roots r a).1.size = roots.size ∨
      (dijkstraMergeRoots dfsInfo dpos roots r a).1.size < roots.size ∧
      dpos < (dfsInfo[(full[(dijkstraMergeRoots dfsInfo dpos roots r a).1.size + 1]!).1]!).1) := by
  intro full roots r a
  induction roots, r, a using dijkstraMergeRoots.induct dfsInfo dpos with
  | case1 roots r a hcond hnone =>
    intro hr hsub hchain hpre hridx
    have hrsize : roots.size = 0 := by
      have := Array.back?_eq_none_iff.mp hnone; simp [this]
    have hrzero : r = 0 := hchain.2.2.2 hrsize
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hnone]
    refine ⟨hridx, ?_, ?_⟩
    · rw [hrzero]
      simp [hdbase0 (by omega)]
    · exact Or.inl rfl
  | case2 roots r a hcond r1 la hb ih =>
    intro hr hsub hchain hpre hridx
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push (r1, la)).pop = ys := by simp
    have hr1 : r1 < r := by
      have := hchain.1 ys.size (by simp)
      rwa [Array.getElem!_push_eq] at this
    have hys' : RootsChain ys r1 := by
      obtain ⟨hbounds, hmono, hbase0, hrzero⟩ := hchain
      refine ⟨fun i hi => ?_, fun i j hij hj => ?_, fun hpos => ?_, fun hempty => ?_⟩
      · have := hmono i ys.size hi (by simp)
        rwa [Array.getElem!_push_lt hi, Array.getElem!_push_eq] at this
      · have := hmono i j hij (hj.trans (by simp))
        rwa [Array.getElem!_push_lt (hij.trans hj), Array.getElem!_push_lt hj] at this
      · have hb0 := hbase0 (show 0 < (ys.push (r1, la)).size from by simp)
        rwa [Array.getElem!_push_lt hpos] at hb0
      · have hb0 := hbase0 (show 0 < (ys.push (r1, la)).size from by simp)
        have hb0' : (ys.push (r1, la))[ys.size]!.1 = 0 := by rw [hempty]; exact hb0
        rwa [Array.getElem!_push_eq] at hb0'
    have hpre' : ∀ i, i < ys.size → ys[i]! = full[i]! := by
      intro i hi
      have := hpre i (by simp only [Array.size_push]; omega)
      rwa [Array.getElem!_push_lt hi] at this
    have hridx' : r1 = (full[ys.size]!).1 := by
      have hval := hpre ys.size (by simp)
      rw [Array.getElem!_push_eq] at hval
      rw [← hval]
    have hsub' : (ys.push (r1, la)).pop.size ≤ full.size := by
      rw [hpop]; simp only [Array.size_push] at hsub; omega
    have hychain : RootsChain (ys.push (r1, la)).pop r1 := by rw [hpop]; exact hys'
    have hypre : ∀ i, i < (ys.push (r1, la)).pop.size → (ys.push (r1, la)).pop[i]! = full[i]! := by
      rw [hpop]; exact hpre'
    have hyridx : r1 = (full[(ys.push (r1, la)).pop.size]!).1 := by rw [hpop]; exact hridx'
    have hihyp := ih (hr1.trans hr) hsub' hychain hypre hyridx
    rw [hpop] at hihyp
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hb]
    dsimp only
    rw [hpop]
    refine ⟨hihyp.1, hihyp.2.1, Or.inr ⟨by simp only [Array.size_push]; omega, ?_⟩⟩
    rcases hihyp.2.2 with heq | ⟨_, hlt⟩
    · rw [heq, show ys.size + 1 = (ys.push (r1, la)).size from by simp, ← hridx]
      exact hcond
    · exact hlt
  | case3 roots r a hcond =>
    intro hr hsub hchain hpre hridx
    unfold dijkstraMergeRoots
    simp only [hcond, if_false]
    refine ⟨hridx, by omega, ?_⟩
    exact Or.inl trivial

theorem dijkstraRootsWF_update (numMarks : Nat) (aux : DijkstraAux State) (marks : Std.HashSet Nat)
    (d : State) (hwf : DijkstraRootsWF aux) : DijkstraRootsWF (dijkstraUpdate numMarks aux marks d).1 := by
  unfold dijkstraUpdate
  cases haux : aux.roots.back? with
  | none =>
    obtain ⟨hbounds, hmono, hok, hdmono, hdlt, hbase, hempty, hdbase, hlempty⟩ := hwf
    dsimp only; exact ⟨hbounds, hmono, hok, hdmono, hdlt, hbase, hempty, hdbase, hlempty⟩
  | some x =>
    obtain ⟨r0, a0⟩ := x
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp haux
    have hpop : aux.roots.pop = ys := by rw [hys]; simp
    have hys' : RootsChain ys r0 := hwf.chain_pop hys
    obtain ⟨hbounds, hmono, hok, hdmono, hdlt, hbase, hempty, hdbase, hlempty⟩ := hwf
    have hr0 : r0 < aux.dfsInfo.size := by
      have := hbounds ys.size (by rw [hys]; simp)
      rwa [hys, Array.getElem!_push_eq] at this
    set res := dijkstraMergeRoots aux.dfsInfo (aux.liveIndex.getD d 0) ys r0
      (a0 ||| marksToBitmask marks) with hres
    have hspec := dijkstraMergeRoots_spec aux.dfsInfo (aux.liveIndex.getD d 0) ys r0
      (a0 ||| marksToBitmask marks) hr0 hys'
    rw [hpop]
    obtain ⟨hs1, hs2, ⟨hs3a, hs3b, hs3c, hs3d⟩, hs4⟩ := hspec
    refine ⟨fun i hi => ?_, fun i j hij hj => ?_, ?_, hdmono, hdlt, fun _ => ?_,
      fun h => by simp only [Array.size_push] at h; omega, hdbase, hlempty⟩
    · simp only [Array.size_push] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · rw [Array.getElem!_push_lt hlt]; exact (hs3a i hlt).trans hs2
      · subst heq; rw [Array.getElem!_push_eq]; exact hs2
    · simp only [Array.size_push] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | hjeq
      · rw [Array.getElem!_push_lt (hij.trans hjlt), Array.getElem!_push_lt hjlt]
        exact hs3b i j hij hjlt
      · subst hjeq
        rw [Array.getElem!_push_lt hij, Array.getElem!_push_eq]
        exact hs3a i hij
    · simp only [Array.size_push]
      have hroots : aux.roots.size ≤ aux.dfsInfo.size := hok
      rw [hys] at hroots
      simp only [Array.size_push] at hroots
      omega
    · -- new top-level `rootsBase`: either the merge survived (its own `roots0`) or fully collapsed (its `rZero`).
      by_cases hc : 0 < res.1.size
      · rw [Array.getElem!_push_lt hc]; exact hs3c hc
      · have hz : res.1.size = 0 := by omega
        have hkey : (res.1.push (res.2.1, res.2.2))[res.1.size]! = (res.2.1, res.2.2) :=
          Array.getElem!_push_eq
        rw [hz] at hkey
        rw [hkey]; exact hs3d hz

private theorem dijkstraUpdate_merge_locate [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (numMarks : Nat) (aux : DijkstraAux State) (marks : Std.HashSet Nat) (d : State)
    (hwf : DijkstraWellFormed aux) (hrwf : DijkstraRootsWF aux) (hroots_pos : 0 < aux.roots.size)
    (hd_contains : aux.liveIndex.contains d = true) :
    ∃ lo, lo < aux.roots.size ∧ d ∈ aux.range lo ∧
      (dijkstraUpdate numMarks aux marks d).1.roots.size = lo + 1 ∧
      (∀ i, i < lo → (dijkstraUpdate numMarks aux marks d).1.roots[i]! = aux.roots[i]!) ∧
      ((dijkstraUpdate numMarks aux marks d).1.roots[lo]!).1 = (aux.roots[lo]!).1 := by
  obtain ⟨r0, a0, hback⟩ : ∃ r0 a0, aux.roots.back? = some (r0, a0) := by
    rcases hbk : aux.roots.back? with _ | p
    · exact absurd (Array.back?_eq_none_iff.mp hbk) (by
        intro he; rw [he] at hroots_pos; simp at hroots_pos)
    · exact ⟨p.1, p.2, by simp⟩
  obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hback
  have hpop : aux.roots.pop = ys := by rw [hys]; simp
  have hys' : RootsChain ys r0 := hrwf.chain_pop hys
  have hr0 : r0 < aux.dfsInfo.size := by
    have := hrwf.rootsBounds ys.size (by rw [hys]; simp)
    rwa [hys, Array.getElem!_push_eq] at this
  have hmergePre : ∀ i, i < ys.size → ys[i]! = aux.roots[i]! := by
    intro i hi; rw [hys, Array.getElem!_push_lt hi]
  have hridx : r0 = (aux.roots[ys.size]!).1 := by rw [hys, Array.getElem!_push_eq]
  have hsub : ys.size ≤ aux.roots.size := by rw [hys]; simp
  have hrootssize : aux.roots.size = ys.size + 1 := by rw [hys]; simp
  set dpos := aux.liveIndex.getD d 0 with hdpos_def
  set a0' := a0 ||| marksToBitmask marks with ha0'_def
  have haux'roots : (dijkstraUpdate numMarks aux marks d).1.roots =
      (dijkstraMergeRoots aux.dfsInfo dpos ys r0 a0').1.push
      ((dijkstraMergeRoots aux.dfsInfo dpos ys r0 a0').2.1,
       (dijkstraMergeRoots aux.dfsInfo dpos ys r0 a0').2.2) := by
    unfold dijkstraUpdate
    rw [hback]
    dsimp only
    rw [hpop]
  have hdp_eq : aux.liveIndex[d]? = some dpos :=
    Std.HashMap.getElem?_eq_some_getD_of_contains hd_contains
  obtain ⟨hdpos_lt, hdpos_val⟩ := hwf.bwd d dpos hdp_eq
  have hlocate := dijkstraMergeRoots_locate aux.dfsInfo dpos hrwf.dfsInfoBase
    aux.roots ys r0 a0' hr0 hsub hys' hmergePre hridx
  set res := dijkstraMergeRoots aux.dfsInfo dpos ys r0 a0' with hres_def
  set lo := res.1.size with hlo_def
  have hlo_le_ys : lo ≤ ys.size := (dijkstraMergeRoots_spec aux.dfsInfo dpos ys r0 a0' hr0 hys').1
  have hlo_lt : lo < aux.roots.size := by omega
  have hd_range : d ∈ aux.range lo := by
    rw [DijkstraAux.mem_range_iff]
    refine ⟨dpos, ?_, ?_, hdpos_val⟩
    · show aux.rangeStart lo ≤ dpos
      unfold DijkstraAux.rangeStart
      rw [← hlocate.1]
      exact hlocate.2.1
    · rcases hlocate.2.2 with heq | ⟨hlt_size, hlt⟩
      · have hend : aux.rangeEnd lo = aux.live.size := by
          unfold DijkstraAux.rangeEnd
          rw [heq]
          simp only [show ¬ ys.size + 1 < aux.roots.size from by omega, if_false]
        rw [hend, min_self]; exact hdpos_lt
      · have hlo1 : lo + 1 < aux.roots.size := by omega
        have hend : aux.rangeEnd lo = aux.rangeStart (lo + 1) := by
          unfold DijkstraAux.rangeEnd
          rw [if_pos hlo1]
        have hstart_eq : aux.rangeStart (lo + 1) = (aux.dfsInfo[(aux.roots[lo + 1]!).1]!).1 := rfl
        rw [hend, hstart_eq]
        exact Nat.lt_min.mpr ⟨hlt, hdpos_lt⟩
  refine ⟨lo, hlo_lt, hd_range, ?_, ?_, ?_⟩
  · rw [haux'roots]; simp only [Array.size_push, hlo_def]
  · intro i hi
    rw [haux'roots, Array.getElem!_push_lt (show i < res.1.size from by omega)]
    exact ((dijkstraMergeRoots_spec aux.dfsInfo dpos ys r0 a0' hr0 hys').2.2.2 i (by omega)).trans
      (hmergePre i (by omega))
  · rw [haux'roots, Array.getElem!_push_eq, hlocate.1]

private theorem dijkstraUpdate_merge_bitmask [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (numMarks : Nat) (aux : DijkstraAux State) (marks : Std.HashSet Nat) (d : State)
    (hpos : 0 < aux.roots.size) :
    ∃ lo, lo + 1 = (dijkstraUpdate numMarks aux marks d).1.roots.size ∧
    (∀ m, ((aux.roots[aux.roots.size - 1]!).2 ||| marksToBitmask marks).testBit m = true →
      ((dijkstraUpdate numMarks aux marks d).1.roots[lo]!).2.testBit m = true) ∧
    (∀ k, lo ≤ k → k < aux.roots.size - 1 → ∀ m, (aux.roots[k]!).2.testBit m = true →
      ((dijkstraUpdate numMarks aux marks d).1.roots[lo]!).2.testBit m = true) ∧
    (∀ k, lo < k → k < aux.roots.size → ∀ m, (aux.dfsInfo[(aux.roots[k]!).1]!).2.testBit m = true →
      ((dijkstraUpdate numMarks aux marks d).1.roots[lo]!).2.testBit m = true) := by
  unfold dijkstraUpdate
  cases haux : aux.roots.back? with
  | none =>
    exfalso
    have := Array.back?_eq_none_iff.mp haux
    rw [this] at hpos
    simp at hpos
  | some x =>
    obtain ⟨r0, a0⟩ := x
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp haux
    have hpop : aux.roots.pop = ys := by rw [hys]; simp
    have hidx : aux.roots.size - 1 = ys.size := by rw [hys]; simp
    have hrsize : aux.roots.size = ys.size + 1 := by rw [hys]; simp
    have htop : aux.roots[aux.roots.size - 1]! = (r0, a0) := by rw [hidx, hys, Array.getElem!_push_eq]
    dsimp only
    rw [hpop]
    refine ⟨(dijkstraMergeRoots aux.dfsInfo (aux.liveIndex.getD d 0) ys r0
        (a0 ||| marksToBitmask marks)).1.size, by simp only [Array.size_push],
      fun m hm => ?_, fun k hk1 hk2 m hm => ?_, fun k hk1 hk2 m hm => ?_⟩
    · rw [htop] at hm
      dsimp only at hm
      rw [Array.getElem!_push_eq]
      exact dijkstraMergeRoots_bitmask_mono aux.dfsInfo (aux.liveIndex.getD d 0) m ys r0 _ hm
    · rw [hidx] at hk2
      have hm' : (ys[k]!).2.testBit m = true := by
        have hke : ys[k]! = aux.roots[k]! := by rw [hys, Array.getElem!_push_lt hk2]
        rw [hke]; exact hm
      rw [Array.getElem!_push_eq]
      exact dijkstraMergeRoots_bitmask_absorbs aux.dfsInfo (aux.liveIndex.getD d 0) ys r0
        (a0 ||| marksToBitmask marks) k hk1 hk2 m hm'
    · rw [Array.getElem!_push_eq]
      rcases Nat.lt_or_ge k ys.size with hklt | hkge
      · have hm' : (aux.dfsInfo[(ys[k]!).1]!).2.testBit m = true := by
          have hke : ys[k]! = aux.roots[k]! := by rw [hys, Array.getElem!_push_lt hklt]
          rw [hke]; exact hm
        exact dijkstraMergeRoots_dfsInfo_absorbs aux.dfsInfo (aux.liveIndex.getD d 0) ys r0
          (a0 ||| marksToBitmask marks) k hk1 hklt m hm'
      -- `k` is the pre-merge top itself, whose entry marks are folded as soon as the loop moves off it.
      · have hkeq : k = ys.size := by omega
        have hm' : (aux.dfsInfo[r0]!).2.testBit m = true := by
          rwa [hkeq, hys, Array.getElem!_push_eq] at hm
        exact dijkstraMergeRoots_dfsInfo_absorbs_self aux.dfsInfo (aux.liveIndex.getD d 0) ys r0
          (a0 ||| marksToBitmask marks) (by omega) m hm'

private theorem dijkstraUpdate_merge_bound [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (numMarks : Nat) (aux : DijkstraAux State) (marks : Std.HashSet Nat) (d : State)
    (hpos : 0 < aux.roots.size) (hdfsBound : ∀ i : Nat, (aux.dfsInfo[i]!).2 < 2 ^ numMarks)
    (hrootsBound : ∀ i : Nat, (aux.roots[i]!).2 < 2 ^ numMarks) (hmarksLt : marksToBitmask marks < 2 ^ numMarks) :
    ∃ lo, lo + 1 = (dijkstraUpdate numMarks aux marks d).1.roots.size ∧
      ((dijkstraUpdate numMarks aux marks d).1.roots[lo]!).2 < 2 ^ numMarks := by
  unfold dijkstraUpdate
  cases haux : aux.roots.back? with
  | none =>
    exfalso
    have := Array.back?_eq_none_iff.mp haux
    rw [this] at hpos
    simp at hpos
  | some x =>
    obtain ⟨r0, a0⟩ := x
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp haux
    have hpop : aux.roots.pop = ys := by rw [hys]; simp
    have hidx : aux.roots.size - 1 = ys.size := by rw [hys]; simp
    have ha0 : a0 < 2 ^ numMarks := by
      have := hrootsBound (aux.roots.size - 1)
      rwa [hidx, hys, Array.getElem!_push_eq] at this
    have hys' : ∀ i : Nat, (ys[i]!).2 < 2 ^ numMarks := by
      intro i
      by_cases hi : i < ys.size
      · have := hrootsBound i; rwa [hys, Array.getElem!_push_lt hi] at this
      · rw [getElem!_neg ys i hi]; exact getElem!_pair_default_snd_lt numMarks
    dsimp only
    rw [hpop]
    refine ⟨(dijkstraMergeRoots aux.dfsInfo (aux.liveIndex.getD d 0) ys r0
        (a0 ||| marksToBitmask marks)).1.size, by simp only [Array.size_push], ?_⟩
    rw [Array.getElem!_push_eq]
    exact dijkstraMergeRoots_bitmask_bound aux.dfsInfo (aux.liveIndex.getD d 0) numMarks hdfsBound ys r0 _
      (Nat.or_lt_two_pow ha0 hmarksLt) hys'

private theorem dijkstraUpdate_merge_bitmask_elim [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (numMarks : Nat) (aux : DijkstraAux State) (marks : Std.HashSet Nat) (d : State)
    (hpos : 0 < aux.roots.size) :
    ∃ lo, lo + 1 = (dijkstraUpdate numMarks aux marks d).1.roots.size ∧
      ∀ P : Nat → Prop,
        (∀ m, (marksToBitmask marks).testBit m = true → P m) →
        (∀ k, lo ≤ k → k < aux.roots.size → ∀ m, (aux.roots[k]!).2.testBit m = true → P m) →
        (∀ k, lo < k → k < aux.roots.size → ∀ m,
          (aux.dfsInfo[(aux.roots[k]!).1]!).2.testBit m = true → P m) →
        ∀ m, ((dijkstraUpdate numMarks aux marks d).1.roots[lo]!).2.testBit m = true → P m := by
  unfold dijkstraUpdate
  cases haux : aux.roots.back? with
  | none =>
    exfalso
    have := Array.back?_eq_none_iff.mp haux
    rw [this] at hpos
    simp at hpos
  | some x =>
    obtain ⟨r0, a0⟩ := x
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp haux
    have hpop : aux.roots.pop = ys := by rw [hys]; simp
    have hrsize : aux.roots.size = ys.size + 1 := by rw [hys]; simp
    have htop : aux.roots[ys.size]! = (r0, a0) := by rw [hys, Array.getElem!_push_eq]
    dsimp only
    rw [hpop]
    have hle := dijkstraMergeRoots_size_le aux.dfsInfo (aux.liveIndex.getD d 0) ys r0
      (a0 ||| marksToBitmask marks)
    refine ⟨(dijkstraMergeRoots aux.dfsInfo (aux.liveIndex.getD d 0) ys r0
        (a0 ||| marksToBitmask marks)).1.size, by simp only [Array.size_push],
      fun P hedge hrange hentry m hm => ?_⟩
    rw [Array.getElem!_push_eq] at hm
    refine dijkstraMergeRoots_bitmask_elim aux.dfsInfo (aux.liveIndex.getD d 0) P ys r0 _
      ?_ ?_ ?_ ?_ m hm
    -- the seed is the old top range's own bitmask joined with this edge's marks
    · intro m' hm'
      simp only [Nat.testBit_or, Bool.or_eq_true] at hm'
      rcases hm' with hm' | hm'
      · exact hrange ys.size hle (by omega) m' (by rw [htop]; exact hm')
      · exact hedge m' hm'
    · intro j hj1 hj2 m' hm'
      exact hrange j hj1 (by omega) m' (by rw [hys, Array.getElem!_push_lt hj2]; exact hm')
    · intro hlt m' hm'
      exact hentry ys.size hlt (by omega) m' (by rw [htop]; exact hm')
    · intro j hj1 hj2 m' hm'
      exact hentry j hj1 (by omega) m' (by rw [hys, Array.getElem!_push_lt hj2]; exact hm')

private theorem dijkstraUpdate_merge_found [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (numMarks : Nat) (aux : DijkstraAux State) (marks : Std.HashSet Nat) (d : State) (hpos : 0 < aux.roots.size) :
    ∃ lo, lo + 1 = (dijkstraUpdate numMarks aux marks d).1.roots.size ∧
      (dijkstraUpdate numMarks aux marks d).2 =
        (((dijkstraUpdate numMarks aux marks d).1.roots[lo]!).2 == (1 <<< numMarks) - 1) := by
  unfold dijkstraUpdate
  cases haux : aux.roots.back? with
  | none =>
    exfalso
    have := Array.back?_eq_none_iff.mp haux
    rw [this] at hpos
    simp at hpos
  | some x =>
    obtain ⟨r0, a0⟩ := x
    dsimp only
    refine ⟨(dijkstraMergeRoots aux.dfsInfo (aux.liveIndex.getD d 0) aux.roots.pop r0
        (a0 ||| marksToBitmask marks)).1.size, by simp only [Array.size_push], ?_⟩
    rw [Array.getElem!_push_eq]

private theorem mono_index_le {roots : Array (Nat × Nat)}
    (hmono : ∀ i j, i < j → j < roots.size → (roots[i]!).1 < (roots[j]!).1) :
    ∀ i, i < roots.size → i ≤ (roots[i]!).1 := by
  intro i
  induction i with
  | zero => intro _; omega
  | succ k ih =>
    intro hk1
    have := ih (by omega)
    have hstep := hmono k (k + 1) (by omega) hk1
    omega

theorem dijkstraRootsWF_pop (aux : DijkstraAux State) (pos : Nat) (hwf : DijkstraRootsWF aux)
    (hpos : ∀ r snd, aux.roots.back? = some (r, snd) → aux.dfsInfo.pop.size = r →
      pos = (aux.dfsInfo[r]!).1) :
    DijkstraRootsWF (dijkstraPop aux pos).1 := by
  obtain ⟨hbounds, hmono, hok, hdmono, hdlt, hbase, hzero, hdbase, hlempty⟩ := hwf
  have hdmono' : ∀ i j, i < j → j < aux.dfsInfo.pop.size →
      (aux.dfsInfo.pop[i]!).1 < (aux.dfsInfo.pop[j]!).1 := by
    intro i j hij hj
    have hjb : j < aux.dfsInfo.size := by simp only [Array.size_pop] at hj; omega
    rw [Array.getElem!_pop_lt (hij.trans hj), Array.getElem!_pop_lt hj]
    exact hdmono i j hij hjb
  have hdlt_same : ∀ i, i < aux.dfsInfo.pop.size → (aux.dfsInfo.pop[i]!).1 < aux.live.size := by
    intro i hi
    have hib : i < aux.dfsInfo.size := by simp only [Array.size_pop] at hi; omega
    rw [Array.getElem!_pop_lt hi]
    exact hdlt i hib
  have hdbase' : ∀ h : 0 < aux.dfsInfo.pop.size, (aux.dfsInfo.pop[0]!).1 = 0 := by
    intro h
    rw [Array.getElem!_pop_lt h]
    exact hdbase (by simp only [Array.size_pop] at h; omega)
  unfold dijkstraPop
  cases haux : aux.roots.back? with
  | none =>
    have hempty : aux.roots = #[] := Array.back?_eq_none_iff.mp haux
    have hdz : aux.dfsInfo.size = 0 := hzero (by rw [hempty]; simp)
    exact ⟨fun i hi => absurd hi (by rw [hempty]; simp), fun i j _ hj => absurd hj (by rw [hempty]; simp),
      by rw [hempty]; simp, hdmono', hdlt_same, fun h => absurd h (by rw [hempty]; simp),
      fun _ => by simp only [Array.size_pop]; omega, hdbase', fun _ => hlempty hdz⟩
  | some x =>
    obtain ⟨r, snd⟩ := x
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp haux
    have hpop : aux.roots.pop = ys := by rw [hys]; simp
    have hidx : ys.size ≤ r := by
      have := mono_index_le hmono ys.size (by rw [hys]; simp)
      rwa [hys, Array.getElem!_push_eq] at this
    have hrbound : r < aux.dfsInfo.size := by
      have := hbounds ys.size (by rw [hys]; simp)
      rwa [hys, Array.getElem!_push_eq] at this
    by_cases h : aux.dfsInfo.pop.size = r
    · simp only [h, if_true]
      have hb' : ∀ i, i < aux.roots.pop.size → (aux.roots.pop[i]!).1 < aux.dfsInfo.pop.size := by
        rw [hpop, h]
        intro i hi
        have := hmono i ys.size hi (by rw [hys]; simp)
        rwa [hys, Array.getElem!_push_lt hi, Array.getElem!_push_eq] at this
      have hm' : ∀ i j, i < j → j < aux.roots.pop.size → (aux.roots.pop[i]!).1 < (aux.roots.pop[j]!).1 := by
        rw [hpop]
        intro i j hij hj
        have := hmono i j hij (by rw [hys]; simp; omega)
        rwa [hys, Array.getElem!_push_lt (hij.trans hj), Array.getElem!_push_lt hj] at this
      have hd' : aux.roots.pop.size ≤ aux.dfsInfo.pop.size := by rw [hpop, h]; omega
      have hposeq : pos = (aux.dfsInfo[r]!).1 := hpos r snd haux h
      have hrlive : (aux.dfsInfo[r]!).1 < aux.live.size := hdlt r hrbound
      have hflushsize : (dijkstraFlushLive aux.live aux.liveIndex aux.dead pos).1.size = pos :=
        dijkstraFlushLive_size pos aux.live aux.liveIndex aux.dead (by rw [hposeq]; omega)
      have hdlt' : ∀ i, i < aux.dfsInfo.pop.size →
          (aux.dfsInfo.pop[i]!).1 < (dijkstraFlushLive aux.live aux.liveIndex aux.dead pos).1.size := by
        intro i hi
        rw [hflushsize, hposeq]
        rw [Array.getElem!_pop_lt hi]
        rw [h] at hi
        exact hdmono i r hi hrbound
      have hbase' : ∀ hpos' : 0 < aux.roots.pop.size, aux.roots.pop[0]!.1 = 0 := by
        rw [hpop]
        intro hpos'
        have hb0 := hbase (show 0 < aux.roots.size from by rw [hys]; simp)
        rwa [hys, Array.getElem!_push_lt hpos'] at hb0
      have hzero' : aux.roots.pop.size = 0 → aux.dfsInfo.pop.size = 0 := by
        rw [hpop]
        intro hemp
        have hb0 := hbase (show 0 < aux.roots.size from by rw [hys]; simp)
        have hb0' : aux.roots[ys.size]!.1 = 0 := by rw [hemp]; exact hb0
        rw [hys, Array.getElem!_push_eq] at hb0'
        omega
      have hlempty' : aux.dfsInfo.pop.size = 0 →
          (dijkstraFlushLive aux.live aux.liveIndex aux.dead pos).1.size = 0 := by
        intro hz
        have hrz : r = 0 := by omega
        have hpz : pos = 0 := by
          rw [hposeq, hrz]; exact hdbase (by omega)
        rw [hflushsize, hpz]
      exact ⟨hb', hm', hd', hdmono', hdlt', hbase', hzero', hdbase', hlempty'⟩
    · simp only [h, if_false]
      have hps : aux.dfsInfo.pop.size = aux.dfsInfo.size - 1 := by simp [Array.size_pop]
      have hlt : r < aux.dfsInfo.pop.size := by omega
      have hval : (aux.roots[ys.size]!).1 = r := by rw [hys, Array.getElem!_push_eq]
      have hsz : aux.roots.size = ys.size + 1 := by rw [hys]; simp
      have hb' : ∀ i, i < aux.roots.size → (aux.roots[i]!).1 < aux.dfsInfo.pop.size := by
        intro i hi
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by rw [hys] at hi; simpa using hi)) with hilt | hieq
        · have hstep := hmono i ys.size hilt (by rw [hys]; simp)
          rw [hval] at hstep
          omega
        · have hie : i = ys.size := by omega
          rw [hie, hval]
          exact hlt
      have hd' : aux.roots.size ≤ aux.dfsInfo.pop.size := by
        have hbig := mono_index_le hmono (aux.roots.size - 1) (by omega)
        have hsz' : aux.roots.size - 1 = ys.size := by omega
        rw [hsz', hval] at hbig
        omega
      have hlempty' : aux.dfsInfo.pop.size = 0 → aux.live.size = 0 := by
        intro hz
        simp only [Array.size_pop] at hz
        exact absurd (show aux.dfsInfo.pop.size = r by simp only [Array.size_pop]; omega) h
      exact ⟨hb', hmono, hd', hdmono', hdlt_same, hbase, fun hc => absurd hc (by rw [hsz]; omega), hdbase', hlempty'⟩

/-! ## The range invariant and its preservation

`DijkstraRangeInv` on every open `roots`-range: internal connectivity, tree-adjacency between consecutive ranges,
and bitmask soundness. Carried through `dfsGo`'s recursion with the stack-side `DijkstraNoInternalEdge` and `NoBackDispatch`. -/

/-- Connectivity and bitmask soundness on every currently open `roots`-range. -/
structure DijkstraRangeInv [Inhabited State] (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (aux : DijkstraAux State) : Prop where
  rootsWF : DijkstraRootsWF aux
  -- every open range is internally strongly connected
  connected : ∀ i, i < aux.roots.size → InternallyConnected succs (aux.range i)
  -- consecutive open ranges are tree-adjacent: range (i+1) was pushed as some range-i member's successor.
  chained : ∀ i, (h : i + 1 < aux.roots.size) → ∃ s ∈ aux.range i, ∃ t ∈ aux.range (i + 1), t ∈ succs s
  -- every bit of an open range's bitmask names a real edge with both endpoints inside that range
  bitSound : ∀ i, i < aux.roots.size → ∀ m, (aux.roots[i]!).2.testBit m = true →
    ∃ s ∈ aux.range i, ∃ t ∈ aux.range i, t ∈ succs s ∧ m ∈ edgeMarks s t
  -- every bit of a `dfsInfo` entry names the marks of the tree edge that pushed that state, from one depth below
  entrySound : ∀ k, k < aux.dfsInfo.size → ∀ m, (aux.dfsInfo[k]!).2.testBit m = true →
    0 < k ∧ aux.live[(aux.dfsInfo[k]!).1]! ∈ succs (aux.live[(aux.dfsInfo[k - 1]!).1]!) ∧
      m ∈ edgeMarks (aux.live[(aux.dfsInfo[k - 1]!).1]!) (aux.live[(aux.dfsInfo[k]!).1]!)

/-- Driver stack and `dfsInfo` in lockstep, so a frame's dfs-depth pins down its `roots`-range. -/
def DijkstraStackDfsInfo [Inhabited State] (aux : DijkstraAux State) (stack : List (DFSStep State Nat)) : Prop :=
  stack.length = aux.dfsInfo.size ∧
  -- stack top is index 0, `dfsInfo` top is its last entry, hence the reversed index
  (∀ i, (h : i < stack.length) → (stack[i]).pos = (aux.dfsInfo[stack.length - 1 - i]!).1) ∧
  ∀ st ∈ stack, aux.live[st.pos]! = st.state

/-- No edge with both endpoints inside range `i` discovered yet, retired members and dispatched prefixes alike.
Rules out an accepting SCC at `numMarks = 0`, where the bitmask says nothing. -/
def DijkstraNoInternalEdge [Inhabited State] (succs : State → Array State) (aux : DijkstraAux State)
    (stack : List (DFSStep State Nat)) (i : Nat) : Prop :=
  (∀ t ∈ aux.range i, (∀ st ∈ stack, st.state ≠ t) → ∀ x ∈ succs t, x ∉ aux.range i) ∧
  ∀ st ∈ stack, st.state ∈ aux.range i → ∀ x ∈ (st.succ.toList.take st.idx), x ∉ aux.range i

private theorem DijkstraNoInternalEdge.bump [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {succs : State → Array State} {aux : DijkstraAux State} {step : DFSStep State Nat}
    {rest : List (DFSStep State Nat)} {i : Nat} {d : State}
    (hdTake : step.succ.toList.take (step.idx + 1) = step.succ.toList.take step.idx ++ [d])
    (hdnot : d ∉ aux.range i)
    (h : DijkstraNoInternalEdge succs aux (step :: rest) i) :
    DijkstraNoInternalEdge succs aux (({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest) i := by
  refine ⟨fun t ht hexcl x hx => h.1 t ht (fun st hst => ?_) x hx, fun st hst hsr x hx => ?_⟩
  · rcases List.mem_cons.mp hst with heq | hst
    · rw [heq]; exact hexcl { step with idx := step.idx + 1 } (by simp)
    · exact hexcl st (List.mem_cons_of_mem _ hst)
  · rcases List.mem_cons.mp hst with rfl | hst
    · rw [show ({ step with idx := step.idx + 1 } : DFSStep State Nat).succ = step.succ from rfl,
        show ({ step with idx := step.idx + 1 } : DFSStep State Nat).idx = step.idx + 1 from rfl,
        hdTake] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h.2 step (by simp) hsr x hx
      · simp only [List.mem_singleton] at hx; exact hx ▸ hdnot
    · exact h.2 st (List.mem_cons_of_mem _ hst) hsr x hx

private theorem DijkstraNoInternalEdge.congr_range [Inhabited State]
    {succs : State → Array State} {aux aux' : DijkstraAux State} {stack : List (DFSStep State Nat)} {i : Nat}
    (hrange : aux'.range i = aux.range i) (h : DijkstraNoInternalEdge succs aux stack i) :
    DijkstraNoInternalEdge succs aux' stack i := by
  unfold DijkstraNoInternalEdge at h ⊢
  rw [hrange]; exact h

/-- A frame's dispatched prefix contains no stack member two or more frames above it, only its immediate child. -/
def NoBackDispatch [Inhabited State] : List (DFSStep State Nat) → Prop
  | [] => True
  | [_] => True
  | s :: t :: rest => (∀ st ∈ rest, s.state ∉ st.succ.toList.take st.idx) ∧ NoBackDispatch (t :: rest)

omit [BEq State] [Hashable State] in
private theorem NoBackDispatch.tail [Inhabited State] {s : DFSStep State Nat} {rest : List (DFSStep State Nat)}
    (h : NoBackDispatch (s :: rest)) : NoBackDispatch rest := by
  cases rest with
  | nil => trivial
  | cons t rest' => exact h.2

omit [BEq State] [Hashable State] in
private theorem NoBackDispatch.state_congr [Inhabited State] (s' : DFSStep State Nat)
    {s : DFSStep State Nat} {rest : List (DFSStep State Nat)} (h : NoBackDispatch (s :: rest))
    (hstate : s.state = s'.state) : NoBackDispatch (s' :: rest) := by
  cases rest with
  | nil => trivial
  | cons t rest' => exact ⟨hstate ▸ h.1, h.2⟩

private theorem dijkstraStackDfsInfo_pos_lt [Inhabited State] {aux : DijkstraAux State}
    {stack : List (DFSStep State Nat)} (hwf : DijkstraRootsWF aux) (hstackdfs : DijkstraStackDfsInfo aux stack)
    {st : DFSStep State Nat} (hst : st ∈ stack) : st.pos < aux.live.size := by
  obtain ⟨hlen, hpos, _⟩ := hstackdfs
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hst
  have hib : stack.length - 1 - i < aux.dfsInfo.size := by omega
  rw [← heq, hpos i hi]
  exact hwf.dfsInfoLt _ hib

private theorem dijkstraStackDfsInfo_pos_eq_push [Inhabited State] (aux : DijkstraAux State) (q : State)
    (marks : Std.HashSet Nat) {stack : List (DFSStep State Nat)} (hstackdfs : DijkstraStackDfsInfo aux stack)
    (i : Nat) (hi : i < stack.length) :
    (stack[i]).pos = ((dijkstraPush aux q marks).1.dfsInfo[stack.length - 1 - i]!).1 := by
  obtain ⟨hlen, hpos, _⟩ := hstackdfs
  have hib : stack.length - 1 - i < aux.dfsInfo.size := by omega
  unfold dijkstraPush
  simp only
  rw [Array.getElem!_push_lt hib]
  exact hpos i hi

private theorem dijkstraStackDfsInfo_live_eq_push [Inhabited State] (aux : DijkstraAux State) (q : State)
    (marks : Std.HashSet Nat) (hwf : DijkstraRootsWF aux) {stack : List (DFSStep State Nat)}
    (hstackdfs : DijkstraStackDfsInfo aux stack) {st : DFSStep State Nat} (hst : st ∈ stack) :
    (dijkstraPush aux q marks).1.live[st.pos]! = st.state := by
  have hlt := dijkstraStackDfsInfo_pos_lt hwf hstackdfs hst
  obtain ⟨_, _, hlive⟩ := hstackdfs
  unfold dijkstraPush
  simp only
  rw [Array.getElem!_push_lt hlt]
  exact hlive st hst

private theorem dijkstraStackDfsInfo_head_mem_top [Inhabited State] [LawfulBEq State]
    {aux : DijkstraAux State} {step : DFSStep State Nat} {rest : List (DFSStep State Nat)}
    (hwf : DijkstraRootsWF aux) (hstackdfs : DijkstraStackDfsInfo aux (step :: rest)) :
    step.state ∈ aux.range (aux.roots.size - 1) := by
  obtain ⟨hlen, hpos, hlive⟩ := hstackdfs
  have hne' : aux.dfsInfo.size > 0 := by
    have : (step :: rest).length > 0 := by simp
    omega
  have hne : 0 < aux.roots.size := hwf.roots_pos_of_dfsInfo_pos hne'
  obtain ⟨hbounds, hmono, hok, hdmono, hdlt, _, _⟩ := hwf
  have h0 : step.pos = (aux.dfsInfo[aux.dfsInfo.size - 1]!).1 := by
    have := hpos 0 (by simp)
    simpa [hlen] using this
  rw [DijkstraAux.mem_range_iff]
  refine ⟨step.pos, ?_, ?_, hlive step (by simp)⟩
  · set r := (aux.roots[aux.roots.size - 1]!).1 with hr_def
    have hrb : r < aux.dfsInfo.size := hbounds (aux.roots.size - 1) (by omega)
    rcases Nat.lt_or_eq_of_le (Nat.le_sub_one_of_lt hrb) with hlt | heq
    · unfold DijkstraAux.rangeStart
      rw [← hr_def, h0]
      exact (hdmono r (aux.dfsInfo.size - 1) hlt (by omega)).le
    · unfold DijkstraAux.rangeStart
      rw [← hr_def, heq, h0]
  · have hend : aux.rangeEnd (aux.roots.size - 1) = aux.live.size := by
      unfold DijkstraAux.rangeEnd
      simp only [show ¬ aux.roots.size - 1 + 1 < aux.roots.size from by omega, if_false]
    rw [hend, h0, min_self]
    exact hdlt (aux.dfsInfo.size - 1) (by omega)

private theorem DijkstraAux.rangeStart_mono {aux : DijkstraAux State} (hwf : DijkstraRootsWF aux)
    {i j : Nat} (hij : i < j) (hj : j < aux.roots.size) : aux.rangeStart i < aux.rangeStart j := by
  unfold DijkstraAux.rangeStart
  exact hwf.dfsInfoMono _ _ (hwf.rootsMono i j hij hj) (hwf.rootsBounds j hj)

private theorem DijkstraAux.rangeStart_le {aux : DijkstraAux State} (hwf : DijkstraRootsWF aux)
    {i j : Nat} (hij : i ≤ j) (hj : j < aux.roots.size) : aux.rangeStart i ≤ aux.rangeStart j := by
  rcases eq_or_lt_of_le hij with heq | hlt
  · rw [heq]
  · exact (DijkstraAux.rangeStart_mono hwf hlt hj).le

private theorem DijkstraAux.exists_range_index {aux : DijkstraAux State} :
    ∀ k i, k = aux.roots.size - i → i < aux.roots.size → ∀ p, aux.rangeStart i ≤ p → p < aux.live.size →
      ∃ j, i ≤ j ∧ j < aux.roots.size ∧ aux.rangeStart j ≤ p ∧ p < aux.rangeEnd j := by
  intro k
  induction k with
  | zero => intro i hk hi p _ _; exact absurd hk (by omega)
  | succ k ih =>
    intro i hk hi p hp1 hp2
    by_cases hlt : p < aux.rangeEnd i
    · exact ⟨i, le_refl _, hi, hp1, hlt⟩
    · push_neg at hlt
      have hi1 : i + 1 < aux.roots.size := by
        by_contra hc
        have hend : aux.rangeEnd i = aux.live.size := by
          unfold DijkstraAux.rangeEnd
          simp only [show ¬ i + 1 < aux.roots.size from by omega, if_false]
        omega
      have hstart : aux.rangeStart (i + 1) = aux.rangeEnd i := by
        unfold DijkstraAux.rangeEnd
        simp only [hi1, if_true]
      obtain ⟨j, hj1, hj2, hj3, hj4⟩ := ih (i + 1) (by omega) hi1 p (by rw [hstart]; exact hlt) hp2
      exact ⟨j, by omega, hj2, hj3, hj4⟩

private theorem DijkstraAux.range_mem_unique [Inhabited State] [LawfulBEq State] {aux : DijkstraAux State}
    (hrwf : DijkstraRootsWF aux) (hwf : DijkstraWellFormed aux) {i j : Nat} (hi : i < aux.roots.size)
    (hj : j < aux.roots.size) {x : State} (hxi : x ∈ aux.range i) (hxj : x ∈ aux.range j) : i = j := by
  rw [DijkstraAux.mem_range_iff] at hxi hxj
  obtain ⟨p, hp1, hp2, hp3⟩ := hxi
  obtain ⟨q, hq1, hq2, hq3⟩ := hxj
  have hpb : p < aux.live.size := lt_of_lt_of_le hp2 (min_le_right _ _)
  have hqb : q < aux.live.size := lt_of_lt_of_le hq2 (min_le_right _ _)
  have h1 := hwf.fwd p hpb
  have h2 := hwf.fwd q hqb
  rw [getElem!_pos aux.live p hpb] at hp3
  rw [getElem!_pos aux.live q hqb] at hq3
  rw [hp3] at h1
  rw [hq3] at h2
  have hpq : p = q := by rw [h1] at h2; exact Option.some.inj h2
  subst hpq
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hend_le : aux.rangeEnd i ≤ aux.rangeStart j := by
      unfold DijkstraAux.rangeEnd
      rw [if_pos (show i + 1 < aux.roots.size from by omega)]
      exact DijkstraAux.rangeStart_le hrwf (by omega) hj
    have hp2' : p < aux.rangeEnd i := lt_of_lt_of_le hp2 (min_le_left _ _)
    omega
  · have hend_le : aux.rangeEnd j ≤ aux.rangeStart i := by
      unfold DijkstraAux.rangeEnd
      rw [if_pos (show j + 1 < aux.roots.size from by omega)]
      exact DijkstraAux.rangeStart_le hrwf (by omega) hi
    have hq2' : p < aux.rangeEnd j := lt_of_lt_of_le hq2 (min_le_left _ _)
    omega

private theorem DijkstraAux.mem_range_pos [Inhabited State] [LawfulBEq State] {aux : DijkstraAux State}
    (hwf : DijkstraWellFormed aux) {i p : Nat} {x : State} (hx : x ∈ aux.range i)
    (hp : aux.live[p]! = x) (hpb : p < aux.live.size) :
    aux.rangeStart i ≤ p ∧ p < aux.rangeEnd i := by
  rw [DijkstraAux.mem_range_iff] at hx
  obtain ⟨p', hp1, hp2, hp3⟩ := hx
  have hp'b : p' < aux.live.size := lt_of_lt_of_le hp2 (min_le_right _ _)
  have h1 := hwf.fwd p' hp'b
  have h2 := hwf.fwd p hpb
  rw [getElem!_pos aux.live p' hp'b] at hp3
  rw [getElem!_pos aux.live p hpb] at hp
  rw [hp3] at h1
  rw [hp] at h2
  have hpp : p' = p := by rw [h1] at h2; exact Option.some.inj h2
  subst hpp
  exact ⟨hp1, lt_of_lt_of_le hp2 (min_le_left _ _)⟩

private theorem DijkstraAux.range_le_of_pos_lt {aux : DijkstraAux State} (hrwf : DijkstraRootsWF aux)
    {i j p q : Nat} (hi : i < aux.roots.size) (hpi : aux.rangeStart i ≤ p) (hqj : q < aux.rangeEnd j)
    (hpq : p < q) : i ≤ j := by
  by_contra hc
  push_neg at hc
  have hend_le : aux.rangeEnd j ≤ aux.rangeStart i := by
    unfold DijkstraAux.rangeEnd
    rw [if_pos (show j + 1 < aux.roots.size from by omega)]
    exact DijkstraAux.rangeStart_le hrwf (by omega) hi
  omega

private theorem dijkstraMerge_range_union [Inhabited State] [LawfulBEq State] {aux aux' : DijkstraAux State}
    {lo : Nat} (hlo : lo < aux.roots.size) (hwf : DijkstraRootsWF aux) (hsize : aux'.roots.size = lo + 1)
    (htop : (aux'.roots[lo]!).1 = (aux.roots[lo]!).1) (hdfs : aux'.dfsInfo = aux.dfsInfo)
    (hlive : aux'.live = aux.live) (x : State) :
    x ∈ aux'.range lo ↔ ∃ i, lo ≤ i ∧ i < aux.roots.size ∧ x ∈ aux.range i := by
  have hstart_eq : aux'.rangeStart lo = aux.rangeStart lo := by
    unfold DijkstraAux.rangeStart
    rw [htop, hdfs]
  have hend_eq : aux'.rangeEnd lo = aux.live.size := by
    unfold DijkstraAux.rangeEnd
    simp only [hsize, show ¬ lo + 1 < lo + 1 from by omega, if_false, hlive]
  rw [DijkstraAux.mem_range_iff, hstart_eq, hend_eq, hlive]
  constructor
  · rintro ⟨p, hp1, hp2, hp3⟩
    have hp2' : p < aux.live.size := lt_of_lt_of_le hp2 (min_le_right _ _)
    obtain ⟨j, hj1, hj2, hj3, hj4⟩ :=
      DijkstraAux.exists_range_index (aux.roots.size - lo) lo rfl hlo p hp1 hp2'
    exact ⟨j, hj1, hj2, (DijkstraAux.mem_range_iff aux j x).mpr ⟨p, hj3, Nat.lt_min.mpr ⟨hj4, hp2'⟩, hp3⟩⟩
  · rintro ⟨i, hloi, hin, hxi⟩
    rw [DijkstraAux.mem_range_iff] at hxi
    obtain ⟨p, hp1, hp2, hp3⟩ := hxi
    have hp2' : p < aux.live.size := lt_of_lt_of_le hp2 (min_le_right _ _)
    refine ⟨p, (DijkstraAux.rangeStart_le hwf hloi hin).trans hp1, Nat.lt_min.mpr ⟨hp2', hp2'⟩, hp3⟩

private theorem dijkstraMerge_connected [Inhabited State] [LawfulBEq State]
    {succs : State → Array State} {aux aux' : DijkstraAux State} {lo : Nat}
    (hlo : lo < aux.roots.size) (hwf : DijkstraRootsWF aux) (hsize : aux'.roots.size = lo + 1)
    (htop : (aux'.roots[lo]!).1 = (aux.roots[lo]!).1) (hdfs : aux'.dfsInfo = aux.dfsInfo)
    (hlive : aux'.live = aux.live)
    (hconn : ∀ i, lo ≤ i → i < aux.roots.size → InternallyConnected succs (aux.range i))
    (hchain : ∀ i, lo ≤ i → i + 1 < aux.roots.size →
      ∃ s ∈ aux.range i, ∃ t ∈ aux.range (i + 1), t ∈ succs s)
    (hback : ∃ s ∈ aux.range (aux.roots.size - 1), ∃ t ∈ aux.range lo, t ∈ succs s) :
    InternallyConnected succs (aux'.range lo) := by
  intro s hs t ht
  have hunion : ∀ x, x ∈ aux'.range lo ↔ ∃ i, lo ≤ i ∧ i < aux.roots.size ∧ x ∈ aux.range i :=
    dijkstraMerge_range_union hlo hwf hsize htop hdfs hlive
  obtain ⟨i, hloi, hin, hsi⟩ := (hunion s).mp hs
  obtain ⟨j, hloj, hjn, htj⟩ := (hunion t).mp ht
  have hmem : ∀ k, lo ≤ k → k ≤ aux.roots.size - 1 → ∀ x ∈ aux.range k, x ∈ aux'.range lo :=
    fun k hlok hkhi x hx => (hunion x).mpr ⟨k, hlok, by omega, hx⟩
  have hconn' : ∀ k, lo ≤ k → k ≤ aux.roots.size - 1 → InternallyConnected succs (aux.range k) :=
    fun k hlok hkhi => hconn k hlok (by omega)
  have hchain' : ∀ k, lo ≤ k → k < aux.roots.size - 1 →
      ∃ s ∈ aux.range k, ∃ t ∈ aux.range (k + 1), t ∈ succs s :=
    fun k hlok hklt => hchain k hlok (by omega)
  exact InternallyConnected.chain_merge hmem hconn' hchain' hback i hloi (by omega) j hloj (by omega) s hsi t htj

private theorem dijkstraMerge_range_prefix_eq [Inhabited State] {aux aux' : DijkstraAux State} {lo : Nat}
    (hlo : lo < aux.roots.size) (hsize : aux'.roots.size = lo + 1) (hdfs : aux'.dfsInfo = aux.dfsInfo)
    (hlive : aux'.live = aux.live) (htop : (aux'.roots[lo]!).1 = (aux.roots[lo]!).1)
    (hpre : ∀ i, i < lo → aux'.roots[i]! = aux.roots[i]!) (i : Nat) (hi : i < lo) :
    aux'.range i = aux.range i := by
  have hstart_le : ∀ j, j ≤ lo → aux'.rangeStart j = aux.rangeStart j := by
    intro j hj
    unfold DijkstraAux.rangeStart
    rcases lt_or_eq_of_le hj with hlt | heq
    · rw [hpre j hlt, hdfs]
    · rw [heq, htop, hdfs]
  have hend : aux'.rangeEnd i = aux.rangeEnd i := by
    unfold DijkstraAux.rangeEnd
    rw [if_pos (show i + 1 < aux'.roots.size from by omega), if_pos (show i + 1 < aux.roots.size from by omega),
      hstart_le (i + 1) (by omega)]
  unfold DijkstraAux.range
  rw [hstart_le i hi.le, hend, hlive]

private theorem dijkstraRangeInv_update [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {numMarks : Nat} {aux : DijkstraAux State} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {s d : State}
    (hwf : DijkstraWellFormed aux) (hinv : DijkstraRangeInv succs edgeMarks aux)
    (hroots_pos : 0 < aux.roots.size) (hd_contains : aux.liveIndex.contains d = true)
    (hsmem : s ∈ aux.range (aux.roots.size - 1)) (hdSucc : d ∈ succs s) :
    DijkstraRangeInv succs edgeMarks (dijkstraUpdate numMarks aux (edgeMarks s d) d).1 := by
  set aux' := (dijkstraUpdate numMarks aux (edgeMarks s d) d).1 with haux'def
  have hdfsInfo_eq : aux'.dfsInfo = aux.dfsInfo :=
    (dijkstraUpdate_fields numMarks aux (edgeMarks s d) d).2.2.2
  have hlive_eq : aux'.live = aux.live := (dijkstraUpdate_fields numMarks aux (edgeMarks s d) d).1
  obtain ⟨lo, hlo_lt, hd_range, haux'size, haux'pre, haux'top⟩ :=
    dijkstraUpdate_merge_locate numMarks aux (edgeMarks s d) d hwf hinv.rootsWF hroots_pos hd_contains
  rw [← haux'def] at haux'size haux'pre haux'top
  have hwfRoots' : DijkstraRootsWF aux' :=
    dijkstraRootsWF_update numMarks aux (edgeMarks s d) d hinv.rootsWF
  have hunion : ∀ x, x ∈ aux'.range lo ↔ ∃ i, lo ≤ i ∧ i < aux.roots.size ∧ x ∈ aux.range i :=
    dijkstraMerge_range_union hlo_lt hinv.rootsWF haux'size haux'top hdfsInfo_eq hlive_eq
  have hprefix_eq : ∀ i, i < lo → aux'.range i = aux.range i :=
    fun i hi => dijkstraMerge_range_prefix_eq hlo_lt haux'size hdfsInfo_eq hlive_eq haux'top haux'pre i hi
  have haux'startLo : aux'.rangeStart lo = aux.rangeStart lo := by
    unfold DijkstraAux.rangeStart; rw [haux'top, hdfsInfo_eq]
  have haux'endLo : aux'.rangeEnd lo = aux.live.size := by
    unfold DijkstraAux.rangeEnd
    simp only [show ¬ lo + 1 < aux'.roots.size from by omega, if_false, hlive_eq]
  -- every `live` slot at or above `rangeStart lo` is in the merged range, whose upper end is `live.size`
  have hmemLo : ∀ j, (aux.roots[lo]!).1 ≤ j → j < aux.dfsInfo.size →
      aux.live[(aux.dfsInfo[j]!).1]! ∈ aux'.range lo := by
    intro j hj1 hj2
    have hstartle : aux.rangeStart lo ≤ (aux.dfsInfo[j]!).1 := by
      unfold DijkstraAux.rangeStart
      rcases Nat.eq_or_lt_of_le hj1 with heq | hlt
      · rw [heq]
      · exact (hinv.rootsWF.dfsInfoMono _ j hlt hj2).le
    have hlt := hinv.rootsWF.dfsInfoLt j hj2
    rw [DijkstraAux.mem_range_iff, haux'startLo, haux'endLo, hlive_eq]
    exact ⟨(aux.dfsInfo[j]!).1, hstartle, Nat.lt_min.mpr ⟨hlt, hlt⟩, rfl⟩
  refine ⟨hwfRoots', ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [haux'size] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
    · rw [hprefix_eq i hilt]; exact hinv.connected i (by omega)
    · rw [hieq]
      exact dijkstraMerge_connected hlo_lt hinv.rootsWF haux'size haux'top hdfsInfo_eq hlive_eq
        (fun i _ hin => hinv.connected i hin) (fun i _ hi1 => hinv.chained i hi1)
        ⟨s, hsmem, d, hd_range, hdSucc⟩
  · intro i hi
    rw [haux'size] at hi
    have hilt : i < lo := by omega
    by_cases hi1 : i + 1 < lo
    · obtain ⟨t, ht, u, hu, htu⟩ := hinv.chained i (by omega)
      exact ⟨t, (hprefix_eq i hilt) ▸ ht, u, (hprefix_eq (i + 1) hi1) ▸ hu, htu⟩
    · have hieq : i + 1 = lo := by omega
      obtain ⟨t, ht, u, hu, htu⟩ := hinv.chained i (by omega)
      exact ⟨t, (hprefix_eq i hilt) ▸ ht, u, hieq ▸ (hunion u).mpr ⟨lo, le_refl _, hlo_lt, hieq ▸ hu⟩, htu⟩
  · obtain ⟨lo1, hlo1eq, helim⟩ :=
      dijkstraUpdate_merge_bitmask_elim numMarks aux (edgeMarks s d) d hroots_pos
    rw [← haux'def] at hlo1eq helim
    rw [show lo1 = lo from by omega] at helim
    intro i hi m hm
    rw [haux'size] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
    · rw [haux'pre i hilt] at hm
      rw [hprefix_eq i hilt]
      exact hinv.bitSound i (by omega) m hm
    · rw [hieq] at hm ⊢
      refine helim (fun m' => ∃ t ∈ aux'.range lo, ∃ u ∈ aux'.range lo,
        u ∈ succs t ∧ m' ∈ edgeMarks t u) ?_ ?_ ?_ m hm
      -- the closing back edge itself, both endpoints inside the merged range
      · exact fun m' hm' => ⟨s, (hunion s).mpr ⟨aux.roots.size - 1, by omega, by omega, hsmem⟩,
          d, (hunion d).mpr ⟨lo, le_refl _, hlo_lt, hd_range⟩, hdSucc, marksToBitmask_mem hm'⟩
      -- an absorbed range's own bitmask already named an edge internal to it
      · intro k hk1 hk2 m' hm'
        obtain ⟨t, ht, u, hu, htu, hmk⟩ := hinv.bitSound k hk2 m' hm'
        exact ⟨t, (hunion t).mpr ⟨k, hk1, hk2, ht⟩, u, (hunion u).mpr ⟨k, hk1, hk2, hu⟩, htu, hmk⟩
      -- an absorbed root's entry marks name a tree edge whose source sits one dfs-depth lower
      · intro k hk1 hk2 m' hm'
        have hkkb : (aux.roots[k]!).1 < aux.dfsInfo.size := hinv.rootsWF.rootsBounds k hk2
        have hrootlo : (aux.roots[lo]!).1 < (aux.roots[k]!).1 := hinv.rootsWF.rootsMono lo k hk1 hk2
        obtain ⟨hkkpos, hedge, hmk⟩ := hinv.entrySound _ hkkb m' hm'
        exact ⟨_, hmemLo ((aux.roots[k]!).1 - 1) (by omega) (by omega),
          _, hmemLo (aux.roots[k]!).1 (by omega) hkkb, hedge, hmk⟩
  · intro k hk m hm
    rw [hdfsInfo_eq] at hk hm ⊢
    rw [hlive_eq]
    exact hinv.entrySound k hk m hm

private theorem dijkstraPush_rangeStart_eq [Inhabited State] (aux : DijkstraAux State) (q : State)
    (marks : Std.HashSet Nat) (hwf : DijkstraRootsWF aux) (i : Nat) (hi : i < aux.roots.size) :
    (dijkstraPush aux q marks).1.rangeStart i = aux.rangeStart i := by
  unfold DijkstraAux.rangeStart dijkstraPush
  simp only
  rw [Array.getElem!_push_lt hi, Array.getElem!_push_lt (hwf.rootsBounds i hi)]

private theorem dijkstraPush_rangeEnd_eq [Inhabited State] (aux : DijkstraAux State) (q : State)
    (marks : Std.HashSet Nat) (hwf : DijkstraRootsWF aux) (i : Nat) (hi : i < aux.roots.size) :
    (dijkstraPush aux q marks).1.rangeEnd i = aux.rangeEnd i := by
  have hsize : (dijkstraPush aux q marks).1.roots.size = aux.roots.size + 1 := by
    unfold dijkstraPush; simp only [Array.size_push]
  by_cases hlt : i + 1 < aux.roots.size
  · unfold DijkstraAux.rangeEnd
    simp only [hlt, if_true, show i + 1 < (dijkstraPush aux q marks).1.roots.size from by omega, if_true]
    exact dijkstraPush_rangeStart_eq aux q marks hwf (i + 1) hlt
  · have hi' : i = aux.roots.size - 1 := by omega
    unfold DijkstraAux.rangeEnd
    simp only [hlt, if_false, show i + 1 < (dijkstraPush aux q marks).1.roots.size from by omega, if_true]
    unfold DijkstraAux.rangeStart dijkstraPush
    simp only
    rw [show i + 1 = aux.roots.size from by omega, Array.getElem!_push_eq, Array.getElem!_push_eq]

private theorem dijkstraRangeEnd_le_live [Inhabited State] (aux : DijkstraAux State) (hwf : DijkstraRootsWF aux)
    (i : Nat) : aux.rangeEnd i ≤ aux.live.size := by
  unfold DijkstraAux.rangeEnd
  by_cases h : i + 1 < aux.roots.size
  · simp only [h, if_true]
    exact (hwf.dfsInfoLt _ (hwf.rootsBounds (i + 1) h)).le
  · simp only [h, if_false, le_refl]

private theorem dijkstraPush_range_mem_iff [Inhabited State] [LawfulBEq State] (aux : DijkstraAux State)
    (q : State) (marks : Std.HashSet Nat) (hwf : DijkstraRootsWF aux) (i : Nat) (hi : i < aux.roots.size)
    (x : State) : x ∈ (dijkstraPush aux q marks).1.range i ↔ x ∈ aux.range i := by
  rw [DijkstraAux.mem_range_iff, DijkstraAux.mem_range_iff,
    dijkstraPush_rangeStart_eq aux q marks hwf i hi, dijkstraPush_rangeEnd_eq aux q marks hwf i hi]
  have hend_le := dijkstraRangeEnd_le_live aux hwf i
  have hlive_size : (dijkstraPush aux q marks).1.live.size = aux.live.size + 1 := by
    unfold dijkstraPush; simp only [Array.size_push]
  have hlive_eq : (dijkstraPush aux q marks).1.live = aux.live.push q := by unfold dijkstraPush; rfl
  constructor
  · rintro ⟨p, hp1, hp2, hp3⟩
    have hp2' : p < aux.rangeEnd i := lt_of_lt_of_le hp2 (min_le_left _ _)
    refine ⟨p, hp1, Nat.lt_min.mpr ⟨hp2', by omega⟩, ?_⟩
    rwa [hlive_eq, Array.getElem!_push_lt (by omega)] at hp3
  · rintro ⟨p, hp1, hp2, hp3⟩
    have hp2' : p < aux.rangeEnd i := lt_of_lt_of_le hp2 (min_le_left _ _)
    refine ⟨p, hp1, Nat.lt_min.mpr ⟨hp2', by omega⟩, ?_⟩
    rwa [hlive_eq, Array.getElem!_push_lt (by omega)]

private theorem dijkstraPush_range_eq [Inhabited State] (aux : DijkstraAux State) (q : State)
    (marks : Std.HashSet Nat) (hwf : DijkstraRootsWF aux) (i : Nat) (hi : i < aux.roots.size) :
    (dijkstraPush aux q marks).1.range i = aux.range i := by
  unfold DijkstraAux.range
  rw [dijkstraPush_rangeStart_eq aux q marks hwf i hi, dijkstraPush_rangeEnd_eq aux q marks hwf i hi]
  have hend_le := dijkstraRangeEnd_le_live aux hwf i
  have hlive_eq : (dijkstraPush aux q marks).1.live = aux.live.push q := by unfold dijkstraPush; rfl
  rw [hlive_eq, Array.extract_push_of_le hend_le]

private theorem dijkstraGetStatus_unknown_not_mem_range [Inhabited State] [LawfulBEq State]
    {aux : DijkstraAux State} (hwf : DijkstraWellFormed aux) {d : State}
    (hd : dijkstraGetStatus aux d = .unknown) (i : Nat) : d ∉ aux.range i := by
  intro hmem
  rw [DijkstraAux.mem_range_iff] at hmem
  obtain ⟨p, hp1, hp2, hp3⟩ := hmem
  have hpb : p < aux.live.size := lt_of_lt_of_le hp2 (min_le_right _ _)
  have hlk := hwf.fwd p hpb
  rw [getElem!_pos aux.live p hpb] at hp3
  rw [hp3] at hlk
  unfold dijkstraGetStatus dijkstraStatusOf at hd
  simp only [Std.HashMap.contains_eq_isSome_getElem?, hlk] at hd
  simp at hd

private theorem dijkstraGetStatus_dead_not_mem_range [Inhabited State] [LawfulBEq State]
    {aux : DijkstraAux State} (hwf : DijkstraWellFormed aux) {d : State}
    (hd : dijkstraGetStatus aux d = .dead) (i : Nat) : d ∉ aux.range i := by
  intro hmem
  rw [DijkstraAux.mem_range_iff] at hmem
  obtain ⟨p, hp1, hp2, hp3⟩ := hmem
  have hpb : p < aux.live.size := lt_of_lt_of_le hp2 (min_le_right _ _)
  have hlk := hwf.fwd p hpb
  rw [getElem!_pos aux.live p hpb] at hp3
  rw [hp3] at hlk
  unfold dijkstraGetStatus dijkstraStatusOf at hd
  simp only [Std.HashMap.contains_eq_isSome_getElem?, hlk] at hd
  simp at hd

private theorem dijkstraGetStatus_live_of_mem_range [Inhabited State] [LawfulBEq State]
    {aux : DijkstraAux State} (hwf : DijkstraWellFormed aux) {d : State} {i : Nat} (hd : d ∈ aux.range i) :
    dijkstraGetStatus aux d = .live := by
  cases hs : dijkstraGetStatus aux d with
  | live => rfl
  | dead => exact absurd hd (dijkstraGetStatus_dead_not_mem_range hwf hs i)
  | unknown => exact absurd hd (dijkstraGetStatus_unknown_not_mem_range hwf hs i)

private theorem dijkstraPush_new_range_mem_iff [Inhabited State] [LawfulBEq State]
    (aux : DijkstraAux State) (q : State) (marks : Std.HashSet Nat) (x : State) :
    x ∈ (dijkstraPush aux q marks).1.range aux.roots.size ↔ x = q := by
  have hsize : (dijkstraPush aux q marks).1.roots.size = aux.roots.size + 1 := by
    unfold dijkstraPush; simp only [Array.size_push]
  have hstart : (dijkstraPush aux q marks).1.rangeStart aux.roots.size = aux.live.size := by
    unfold DijkstraAux.rangeStart dijkstraPush
    simp only [Array.getElem!_push_eq]
  have hend : (dijkstraPush aux q marks).1.rangeEnd aux.roots.size = aux.live.size + 1 := by
    unfold DijkstraAux.rangeEnd
    simp only [hsize, show ¬ aux.roots.size + 1 < aux.roots.size + 1 from by omega, if_false]
    unfold dijkstraPush; simp only [Array.size_push]
  rw [DijkstraAux.mem_range_iff, hstart, hend]
  have hlive_eq : (dijkstraPush aux q marks).1.live = aux.live.push q := by unfold dijkstraPush; rfl
  have hlive_size : (dijkstraPush aux q marks).1.live.size = aux.live.size + 1 := by
    unfold dijkstraPush; simp only [Array.size_push]
  constructor
  · rintro ⟨p, hp1, hp2, hp3⟩
    have hp2' : p < aux.live.size + 1 := lt_of_lt_of_le hp2 (min_le_left _ _)
    have hpeq : p = aux.live.size := by omega
    rw [hpeq, hlive_eq, Array.getElem!_push_eq] at hp3
    exact hp3.symm
  · rintro rfl
    exact ⟨aux.live.size, le_refl _, Nat.lt_min.mpr ⟨by omega, by omega⟩,
      by rw [hlive_eq, Array.getElem!_push_eq]⟩

/-! ## Witness extraction and the `DFSOps` instance -/

/-- `sccHint`: the just-merged root's live-range is a valid (not necessarily maximal) accepting SCC.
The fallthrough is unreachable, `roots`/`dfsInfo` are never empty where this is called. -/
def dijkstraSccHint (aux : DijkstraAux State) : Std.HashSet State :=
  match aux.roots.back? with
  | none => Std.HashSet.emptyWithCapacity 0
  | some (r, _) =>
    match aux.dfsInfo[r]? with
    | none => Std.HashSet.emptyWithCapacity 0
    | some (startPos, _) =>
      -- `extract` is O(live.size - startPos), unlike `toList.drop`'s O(live.size).
      (aux.live.extract startPos aux.live.size).foldl
        (init := Std.HashSet.emptyWithCapacity 0) fun acc s => acc.insert s

/-- The hint is exactly the top open range, whose upper end is `live.size` since no range follows it. -/
theorem dijkstraSccHint_eq_top_range [Inhabited State] (aux : DijkstraAux State)
    (hwf : DijkstraRootsWF aux) (hpos : 0 < aux.roots.size) :
    dijkstraSccHint aux = aux.range (aux.roots.size - 1) := by
  unfold dijkstraSccHint DijkstraAux.range
  have hend : aux.rangeEnd (aux.roots.size - 1) = aux.live.size := by
    unfold DijkstraAux.rangeEnd
    simp only [show ¬ aux.roots.size - 1 + 1 < aux.roots.size from by omega, if_false]
  rcases hb : aux.roots.back? with _ | ⟨r, a⟩
  · exact absurd (Array.back?_eq_none_iff.mp hb) (by intro he; rw [he] at hpos; simp at hpos)
  · obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    have hidx : aux.roots.size - 1 = ys.size := by rw [hys]; simp
    have hr : (aux.roots[aux.roots.size - 1]!).1 = r := by rw [hidx, hys, Array.getElem!_push_eq]
    have hrlt : r < aux.dfsInfo.size := by rw [← hr]; exact hwf.rootsBounds _ (by omega)
    have hget : aux.dfsInfo[r]? = some aux.dfsInfo[r]! := by
      rw [getElem!_pos aux.dfsInfo r hrlt, Array.getElem?_eq_getElem hrlt]
    dsimp only
    rw [hget]
    dsimp only
    rw [hend]
    unfold DijkstraAux.rangeStart
    rw [hr]
    rfl

def dijkstraOps (numMarks : Nat) : DFSOps State where
  Aux := DijkstraAux State
  Position := Nat
  initAux := dijkstraInitAux
  sccHint := dijkstraSccHint
  -- `dead`/`live` are disjoint (a state only ever enters `dead` once flushed out of `live`, never
  -- re-pushed, per `dijkstraGetStatus`), so their sizes sum to every state ever pushed.
  numExplored := fun aux => aux.live.size + aux.dead.size
  getStatus := dijkstraGetStatus
  push := dijkstraPush
  update := dijkstraUpdate numMarks
  pop := dijkstraPop

/-- `dijkstraOps` is a lawful refinement: `DijkstraWellFormed` is preserved by `push`/`update`/`pop`, and the
three status-transition laws hold. -/
def dijkstraLawful [Inhabited State] [LawfulBEq State] [LawfulHashable State] (numMarks : Nat) :
    LawfulDFSOps (dijkstraOps numMarks) (State := State) where
  WellFormed := DijkstraWellFormed
  wf_push := fun aux q marks hq hwf => dijkstraWellFormed_push aux q marks hwf hq
  wf_update := dijkstraWellFormed_update numMarks
  wf_pop := dijkstraWellFormed_pop
  push_status := dijkstraPush_status
  update_status := dijkstraUpdate_status numMarks
  pop_status := fun aux pos q hwf => dijkstraPop_status aux pos hwf q

/-- `dfsGo_ne_none` instantiated against `dijkstraOps`, leaving a `FiniteReach` certificate as the caller's only obligation. -/
theorem dijkstraOps_ne_none [Inhabited State] [LawfulBEq State] [LawfulHashable State] (numMarks : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs)
    (aux : DijkstraAux State) (stack : List (DFSStep State Nat)) (hwf : DijkstraWellFormed aux)
    (hsucc : ∀ st ∈ stack, st.succ = succs st.state)
    (hreach : ∀ st ∈ stack, Reachable initialStates succs st.state) :
    dfsGo (dijkstraOps numMarks) succs edgeMarks aux stack ≠ none :=
  dfsGo_ne_none (dijkstraOps numMarks) succs edgeMarks initialStates fr (dijkstraLawful numMarks)
    aux stack hwf hsucc hreach

/-- `dfsFromRoot`'s own call shape, one fresh root pushed onto an arbitrary well-formed state. -/
theorem dijkstraOps_root_ne_none [Inhabited State] [LawfulBEq State] [LawfulHashable State] (numMarks : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs) :
    ∀ aux q, Reachable initialStates succs q → DijkstraWellFormed aux →
      dijkstraGetStatus aux q = .unknown →
      dfsGo (dijkstraOps numMarks) succs edgeMarks
        (dijkstraPush aux q (Std.HashSet.emptyWithCapacity 0)).1
        [({ state := q, pos := (dijkstraPush aux q (Std.HashSet.emptyWithCapacity 0)).2,
            acc := Std.HashSet.emptyWithCapacity 0, succ := succs q, idx := 0 } :
          DFSStep State Nat)] ≠ none := by
  intro aux q hqreach hwf hq
  refine dijkstraOps_ne_none numMarks succs edgeMarks initialStates fr _ _
    (dijkstraWellFormed_push aux q _ hwf hq) ?_ ?_
  · intro st hst; simp only [List.mem_singleton] at hst; rw [hst]
  · intro st hst; simp only [List.mem_singleton] at hst; rw [hst]; exact hqreach

/-- `genericDFS_closed` instantiated against `dijkstraOps`. -/
theorem dijkstraOps_closed [Inhabited State] [LawfulBEq State] [LawfulHashable State] (numMarks : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs)
    (roots : List State) (aux : DijkstraAux State)
    (hrootsReach : ∀ q ∈ roots, Reachable initialStates succs q)
    (hnone : (genericDFS (dijkstraOps numMarks) succs edgeMarks roots aux).1 = none)
    (hwf : DijkstraWellFormed aux)
    (hClosed : ∀ t, dijkstraGetStatus aux t ≠ .unknown → ∀ x ∈ succs t, dijkstraGetStatus aux x ≠ .unknown) :
    DijkstraWellFormed (genericDFS (dijkstraOps numMarks) succs edgeMarks roots aux).2 ∧
      ∀ t, dijkstraGetStatus (genericDFS (dijkstraOps numMarks) succs edgeMarks roots aux).2 t
          ≠ .unknown →
        ∀ x ∈ succs t, dijkstraGetStatus
          (genericDFS (dijkstraOps numMarks) succs edgeMarks roots aux).2 x ≠ .unknown :=
  genericDFS_closed (dijkstraOps numMarks) succs edgeMarks (dijkstraLawful numMarks)
    (Reachable initialStates succs)
    (fun aux q hq hwf hgs => dijkstraOps_root_ne_none numMarks succs edgeMarks initialStates fr aux q hq hwf hgs)
    roots aux hrootsReach (genericDFSGo_ne_none (dijkstraOps numMarks) succs edgeMarks roots aux)
    hnone hwf hClosed

/-- `genericDFS_returns_none_fully_explored` instantiated against `dijkstraOps`. -/
theorem dijkstraOps_returns_none_fully_explored [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (numMarks : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs)
    (hnone : (genericDFS (dijkstraOps numMarks) succs edgeMarks initialStates
      dijkstraInitAux).1 = none) :
    ∀ s, Reachable initialStates succs s →
      dijkstraGetStatus (genericDFS (dijkstraOps numMarks) succs edgeMarks initialStates
        dijkstraInitAux).2 s ≠ .unknown :=
  genericDFS_returns_none_fully_explored (dijkstraOps numMarks) succs edgeMarks (dijkstraLawful numMarks)
    (Reachable initialStates succs)
    (fun aux q hq hwf hgs => dijkstraOps_root_ne_none numMarks succs edgeMarks initialStates fr aux q hq hwf hgs)
    initialStates (fun q hq => Reachable.base hq)
    (genericDFSGo_ne_none (dijkstraOps numMarks) succs edgeMarks _ _)
    dijkstraWellFormed_init dijkstraGetStatus_initAux hnone

/-! ## Completeness: no accepting SCC survives an empty search -/

private theorem dijkstraPop_found_false (aux : DijkstraAux State) (pos : Nat) :
    (dijkstraPop aux pos).2 = false := by
  unfold dijkstraPop
  cases aux.roots.back? with
  | none => rfl
  | some x =>
    obtain ⟨r, _⟩ := x
    by_cases h : aux.dfsInfo.pop.size = r
    · simp only [h, if_true]
    · simp only [h, if_false]

private theorem dijkstraPop_rangeStart_eq_of_not_flush [Inhabited State] {aux : DijkstraAux State}
    {pos r0 a0 : Nat} (hwf : DijkstraRootsWF aux) (hback : aux.roots.back? = some (r0, a0))
    (hflush : ¬ aux.dfsInfo.pop.size = r0) (i : Nat) (hi : i < aux.roots.size) :
    (dijkstraPop aux pos).1.rangeStart i = aux.rangeStart i := by
  obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hback
  have hridx : aux.roots.size - 1 = ys.size := by rw [hys]; simp
  have hrtop : (aux.roots[aux.roots.size - 1]!).1 = r0 := by rw [hridx, hys, Array.getElem!_push_eq]
  have hile : (aux.roots[i]!).1 ≤ r0 := by
    rcases Nat.lt_or_eq_of_le (show i ≤ aux.roots.size - 1 from by omega) with hlt | heq
    · exact (hwf.rootsMono i (aux.roots.size - 1) hlt (by omega)).le.trans hrtop.le
    · rw [heq, hrtop]
  have hr0lt : r0 < aux.dfsInfo.pop.size := by
    have hb := hwf.rootsBounds (aux.roots.size - 1) (by omega)
    rw [hrtop] at hb
    have hps : aux.dfsInfo.pop.size = aux.dfsInfo.size - 1 := Array.size_pop
    omega
  have hilt : (aux.roots[i]!).1 < aux.dfsInfo.pop.size := lt_of_le_of_lt hile hr0lt
  unfold DijkstraAux.rangeStart dijkstraPop
  rw [hback]
  dsimp only
  rw [if_neg hflush]
  dsimp only
  exact congrArg Prod.fst (Array.getElem!_pop_lt hilt)

private theorem dijkstraPop_rangeEnd_eq_of_not_flush [Inhabited State] {aux : DijkstraAux State}
    {pos r0 a0 : Nat} (hwf : DijkstraRootsWF aux) (hback : aux.roots.back? = some (r0, a0))
    (hflush : ¬ aux.dfsInfo.pop.size = r0) (i : Nat) (hi : i < aux.roots.size) :
    (dijkstraPop aux pos).1.rangeEnd i = aux.rangeEnd i := by
  have hsizeEq : (dijkstraPop aux pos).1.roots.size = aux.roots.size := by
    unfold dijkstraPop
    rw [hback]
    dsimp only
    rw [if_neg hflush]
  unfold DijkstraAux.rangeEnd
  rw [hsizeEq]
  by_cases hlt : i + 1 < aux.roots.size
  · simp only [hlt, if_true]
    exact dijkstraPop_rangeStart_eq_of_not_flush hwf hback hflush (i + 1) hlt
  · simp only [hlt, if_false]
    unfold dijkstraPop
    rw [hback]
    dsimp only
    rw [if_neg hflush]

private theorem dijkstraPop_range_eq_of_not_flush [Inhabited State] {aux : DijkstraAux State}
    {pos r0 a0 : Nat} (hwf : DijkstraRootsWF aux) (hback : aux.roots.back? = some (r0, a0))
    (hflush : ¬ aux.dfsInfo.pop.size = r0) (i : Nat) (hi : i < aux.roots.size) :
    (dijkstraPop aux pos).1.range i = aux.range i := by
  unfold DijkstraAux.range
  rw [dijkstraPop_rangeStart_eq_of_not_flush hwf hback hflush i hi,
    dijkstraPop_rangeEnd_eq_of_not_flush hwf hback hflush i hi]
  have hliveEq : (dijkstraPop aux pos).1.live = aux.live := by
    unfold dijkstraPop
    rw [hback]
    dsimp only
    rw [if_neg hflush]
  rw [hliveEq]

private theorem dijkstraPop_rangeStart_eq_of_flush [Inhabited State] {aux : DijkstraAux State}
    {pos r0 a0 : Nat} (hwf : DijkstraRootsWF aux) (hback : aux.roots.back? = some (r0, a0))
    (hflush : aux.dfsInfo.pop.size = r0) (i : Nat) (hi : i < aux.roots.size - 1) :
    (dijkstraPop aux pos).1.rangeStart i = aux.rangeStart i := by
  obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hback
  have hridx : aux.roots.size - 1 = ys.size := by rw [hys]; simp
  have hrtop : (aux.roots[aux.roots.size - 1]!).1 = r0 := by rw [hridx, hys, Array.getElem!_push_eq]
  have hilt : (aux.roots[i]!).1 < r0 := by
    have hmono := hwf.rootsMono i (aux.roots.size - 1) hi (by omega)
    rwa [hrtop] at hmono
  have hpoplt : (aux.roots[i]!).1 < aux.dfsInfo.pop.size := by rw [hflush]; exact hilt
  have hpsize : aux.roots.pop.size = aux.roots.size - 1 := Array.size_pop
  have hrootspoplt : aux.roots.pop[i]! = aux.roots[i]! := Array.getElem!_pop_lt (by omega)
  unfold DijkstraAux.rangeStart dijkstraPop
  rw [hback]
  dsimp only
  rw [if_pos hflush]
  dsimp only
  rw [hrootspoplt]
  exact congrArg Prod.fst (Array.getElem!_pop_lt hpoplt)

private theorem dijkstraPop_rangeEnd_eq_of_flush [Inhabited State] {aux : DijkstraAux State}
    {pos r0 a0 : Nat} (hwf : DijkstraRootsWF aux) (hback : aux.roots.back? = some (r0, a0))
    (hflush : aux.dfsInfo.pop.size = r0) (hposle : pos ≤ aux.live.size) (hposeq : pos = (aux.dfsInfo[r0]!).1)
    (i : Nat) (hi : i < aux.roots.size - 1) :
    (dijkstraPop aux pos).1.rangeEnd i = aux.rangeEnd i := by
  have hsizeEq : (dijkstraPop aux pos).1.roots.size = aux.roots.size - 1 := by
    unfold dijkstraPop
    rw [hback]
    dsimp only
    rw [if_pos hflush]
    simp only [Array.size_pop]
  obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hback
  have hridx : aux.roots.size - 1 = ys.size := by rw [hys]; simp
  have hrtop : (aux.roots[aux.roots.size - 1]!).1 = r0 := by rw [hridx, hys, Array.getElem!_push_eq]
  by_cases hlt : i + 1 < aux.roots.size - 1
  · have hendEq : aux.rangeEnd i = aux.rangeStart (i + 1) := by
      unfold DijkstraAux.rangeEnd
      rw [if_pos (by omega : i + 1 < aux.roots.size)]
    rw [hendEq]
    unfold DijkstraAux.rangeEnd
    rw [hsizeEq, if_pos hlt]
    exact dijkstraPop_rangeStart_eq_of_flush hwf hback hflush (i + 1) hlt
  · have hieq : i + 1 = aux.roots.size - 1 := by omega
    have hendEq : aux.rangeEnd i = pos := by
      unfold DijkstraAux.rangeEnd
      rw [if_pos (by omega : i + 1 < aux.roots.size), hieq]
      unfold DijkstraAux.rangeStart
      rw [hrtop, hposeq]
    have hendEq' : (dijkstraPop aux pos).1.rangeEnd i = (dijkstraPop aux pos).1.live.size := by
      unfold DijkstraAux.rangeEnd
      rw [hsizeEq, if_neg hlt]
    have hlivesizeeq : (dijkstraPop aux pos).1.live.size = pos := by
      unfold dijkstraPop
      rw [hback]
      dsimp only
      rw [if_pos hflush]
      dsimp only
      exact dijkstraFlushLive_size pos aux.live aux.liveIndex aux.dead hposle
    rw [hendEq', hlivesizeeq, hendEq]

private theorem dijkstraPop_range_mem_iff_of_flush [Inhabited State] [LawfulBEq State] {aux : DijkstraAux State}
    {pos r0 a0 : Nat} (hwf : DijkstraRootsWF aux) (hback : aux.roots.back? = some (r0, a0))
    (hflush : aux.dfsInfo.pop.size = r0) (hposle : pos ≤ aux.live.size) (hposeq : pos = (aux.dfsInfo[r0]!).1)
    (i : Nat) (hi : i < aux.roots.size - 1) (x : State) :
    x ∈ (dijkstraPop aux pos).1.range i ↔ x ∈ aux.range i := by
  have hstartEq := dijkstraPop_rangeStart_eq_of_flush (pos := pos) hwf hback hflush i hi
  have hendEq := dijkstraPop_rangeEnd_eq_of_flush hwf hback hflush hposle hposeq i hi
  have hlivesizeeq : (dijkstraPop aux pos).1.live.size = pos := by
    unfold dijkstraPop
    rw [hback]
    dsimp only
    rw [if_pos hflush]
    dsimp only
    exact dijkstraFlushLive_size pos aux.live aux.liveIndex aux.dead hposle
  obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hback
  have hridx : aux.roots.size - 1 = ys.size := by rw [hys]; simp
  have hrtop : (aux.roots[aux.roots.size - 1]!).1 = r0 := by rw [hridx, hys, Array.getElem!_push_eq]
  have hstartTop : aux.rangeStart (aux.roots.size - 1) = pos := by
    unfold DijkstraAux.rangeStart
    rw [hrtop, hposeq]
  have hendLe : aux.rangeEnd i ≤ pos := by
    have hle := DijkstraAux.rangeStart_le hwf (show i + 1 ≤ aux.roots.size - 1 from by omega) (by omega)
    rw [hstartTop] at hle
    have hendVal : aux.rangeEnd i = aux.rangeStart (i + 1) := by
      unfold DijkstraAux.rangeEnd
      rw [if_pos (by omega : i + 1 < aux.roots.size)]
    rwa [hendVal]
  have haux'live : ∀ p, p < pos → (dijkstraPop aux pos).1.live[p]! = aux.live[p]! := by
    intro p hp
    unfold dijkstraPop
    rw [hback]
    dsimp only
    rw [if_pos hflush]
    dsimp only
    exact dijkstraFlushLive_getElem!_lt pos aux.live aux.liveIndex aux.dead p hp
  rw [DijkstraAux.mem_range_iff, DijkstraAux.mem_range_iff, hstartEq, hendEq, hlivesizeeq]
  constructor
  · rintro ⟨p, hp1, hp2, hp3⟩
    have hple : p < pos := lt_of_lt_of_le (lt_of_lt_of_le hp2 (min_le_left _ _)) hendLe
    exact ⟨p, hp1, Nat.lt_min.mpr ⟨lt_of_lt_of_le hp2 (min_le_left _ _), hple.trans_le hposle⟩,
      (haux'live p hple) ▸ hp3⟩
  · rintro ⟨p, hp1, hp2, hp3⟩
    have hple : p < pos := lt_of_lt_of_le (lt_of_lt_of_le hp2 (min_le_left _ _)) hendLe
    exact ⟨p, hp1, Nat.lt_min.mpr ⟨lt_of_lt_of_le hp2 (min_le_left _ _), hple⟩, (haux'live p hple).symm ▸ hp3⟩

private theorem DijkstraWellFormed.pos_inj [Inhabited State] [LawfulBEq State] {aux : DijkstraAux State}
    (hwf : DijkstraWellFormed aux) {p q : Nat} (hp : p < aux.live.size) (hq : q < aux.live.size)
    (heq : aux.live[p]! = aux.live[q]!) : p = q := by
  have h1 := hwf.fwd p hp
  have h2 := hwf.fwd q hq
  rw [getElem!_pos aux.live p hp, getElem!_pos aux.live q hq] at heq
  rw [heq] at h1
  exact Option.some.inj (h1.symm.trans h2)

private theorem dijkstraGetStatus_live_of_pos [Inhabited State] [LawfulBEq State] {aux : DijkstraAux State}
    (hwf : DijkstraWellFormed aux) {p : Nat} (hp : p < aux.live.size) {q : State} (heqv : aux.live[p]! = q) :
    dijkstraGetStatus aux q = .live := by
  have hfwd := hwf.fwd p hp
  rw [getElem!_pos aux.live p hp] at heqv
  rw [heqv] at hfwd
  unfold dijkstraGetStatus dijkstraStatusOf
  simp [Std.HashMap.contains_eq_isSome_getElem?, hfwd]

set_option maxHeartbeats 4000000 in
/-- The crux completeness theorem: once a state is flushed to `dead`, it is in no reachable `AcceptingSCC`.
A run that drains its stack without a witness also hands the idle-state bundle back. -/
theorem dijkstra_dead_not_accepting [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    :
    ∀ aux (stack : List (DFSStep State Nat)) (r : Option (State × List State) × DijkstraAux State),
    dfsGo (dijkstraOps numMarks) succs edgeMarks aux stack = some r →
    DijkstraWellFormed aux →
    (∀ st ∈ stack, st.succ = succs st.state) →
    -- a dispatched edge never leaves its target unknown
    (∀ st ∈ stack, ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux x ≠ .unknown) →
    (∀ st ∈ stack, Reachable initialStates succs st.state) →
    DijkstraRangeInv succs edgeMarks aux →
    DijkstraStackDfsInfo aux stack →
    -- a retired range member's edges stay in the range or point at dead states
    (∀ i, i < aux.roots.size → ∀ t ∈ aux.range i, (∀ st ∈ stack, st.state ≠ t) →
      ∀ x ∈ succs t, dijkstraGetStatus aux x ≠ .unknown →
        x ∈ aux.range i ∨ dijkstraGetStatus aux x = .dead) →
    -- retired members are fully dispatched, nothing unknown left behind them
    (∀ i, i < aux.roots.size → ∀ t ∈ aux.range i, (∀ st ∈ stack, st.state ≠ t) →
      ∀ x ∈ succs t, dijkstraGetStatus aux x ≠ .unknown) →
    -- bitmask completeness, an internal edge's marks are already on the range
    (∀ i, i < aux.roots.size → ∀ t ∈ aux.range i, (∀ st ∈ stack, st.state ≠ t) →
      ∀ x ∈ succs t, x ∈ aux.range i → ∀ m ∈ edgeMarks t x, (aux.roots[i]!).2.testBit m = true) →
    -- same for a still-open frame's dispatched prefix
    (∀ st ∈ stack, ∀ x ∈ (st.succ.toList.take st.idx), ∀ i, i < aux.roots.size →
      x ∈ aux.range i → st.state ∈ aux.range i → ∀ m ∈ edgeMarks st.state x,
        (aux.roots[i]!).2.testBit m = true) →
    -- a dispatched live successor either shares a range or sits higher on the stack
    (∀ st ∈ stack, ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux x = .live →
      (∃ i, i < aux.roots.size ∧ st.state ∈ aux.range i ∧ x ∈ aux.range i) ∨
      (∃ st' ∈ stack, st'.state = x ∧ Nat.lt st.pos st'.pos)) →
    -- cross-frame edge marks land on the target range's bitmask or on its entry
    (∀ st ∈ stack, ∀ st' ∈ stack, st'.state ∈ (st.succ.toList.take st.idx) → Nat.lt st.pos st'.pos →
      ∀ j, j < aux.roots.size → st'.state ∈ aux.range j → ∀ m ∈ edgeMarks st.state st'.state,
        (aux.roots[j]!).2.testBit m = true ∨ (aux.dfsInfo[(aux.roots[j]!).1]!).2.testBit m = true) →
    -- only pending edges point back into the path
    NoBackDispatch stack →
    (∀ i : Nat, (aux.roots[i]!).2 < 2 ^ numMarks) →
    (∀ i : Nat, (aux.dfsInfo[i]!).2 < 2 ^ numMarks) →
    -- a range whose bitmask already reads all-ones has no internal edge yet, this is what covers `numMarks = 0`
    (∀ i, i < aux.roots.size → (aux.roots[i]!).2 ≠ (1 <<< numMarks) - 1 ∨
      DijkstraNoInternalEdge succs aux stack i) →
    -- the conclusion carried through the induction
    (∀ s ∈ aux.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) →
    (∀ s ∈ r.2.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) ∧
    (r.1 = none → DijkstraWellFormed r.2 ∧ DijkstraRangeInv succs edgeMarks r.2 ∧ r.2.dfsInfo.size = 0) ∧
    (∀ anchor stem, r.1 = some (anchor, stem) →
      InternallyConnected succs (dijkstraSccHint r.2) ∧
      AcceptingMarks succs edgeMarks numMarks (dijkstraSccHint r.2) ∧
      anchor ∈ dijkstraSccHint r.2) := by
  refine dfsGo.partial_correctness (dijkstraOps numMarks) succs edgeMarks
    (fun aux stack r =>
      DijkstraWellFormed aux →
      (∀ st ∈ stack, st.succ = succs st.state) →
      (∀ st ∈ stack, ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux x ≠ .unknown) →
      (∀ st ∈ stack, Reachable initialStates succs st.state) →
      DijkstraRangeInv succs edgeMarks aux →
      DijkstraStackDfsInfo aux stack →
      (∀ i, i < aux.roots.size → ∀ t ∈ aux.range i, (∀ st ∈ stack, st.state ≠ t) →
        ∀ x ∈ succs t, dijkstraGetStatus aux x ≠ .unknown →
          x ∈ aux.range i ∨ dijkstraGetStatus aux x = .dead) →
      (∀ i, i < aux.roots.size → ∀ t ∈ aux.range i, (∀ st ∈ stack, st.state ≠ t) →
        ∀ x ∈ succs t, dijkstraGetStatus aux x ≠ .unknown) →
      (∀ i, i < aux.roots.size → ∀ t ∈ aux.range i, (∀ st ∈ stack, st.state ≠ t) →
        ∀ x ∈ succs t, x ∈ aux.range i → ∀ m ∈ edgeMarks t x, (aux.roots[i]!).2.testBit m = true) →
      (∀ st ∈ stack, ∀ x ∈ (st.succ.toList.take st.idx), ∀ i, i < aux.roots.size →
        x ∈ aux.range i → st.state ∈ aux.range i → ∀ m ∈ edgeMarks st.state x,
          (aux.roots[i]!).2.testBit m = true) →
      (∀ st ∈ stack, ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux x = .live →
        (∃ i, i < aux.roots.size ∧ st.state ∈ aux.range i ∧ x ∈ aux.range i) ∨
        (∃ st' ∈ stack, st'.state = x ∧ Nat.lt st.pos st'.pos)) →
      (∀ st ∈ stack, ∀ st' ∈ stack, st'.state ∈ (st.succ.toList.take st.idx) → Nat.lt st.pos st'.pos →
        ∀ j, j < aux.roots.size → st'.state ∈ aux.range j → ∀ m ∈ edgeMarks st.state st'.state,
          (aux.roots[j]!).2.testBit m = true ∨ (aux.dfsInfo[(aux.roots[j]!).1]!).2.testBit m = true) →
      NoBackDispatch stack →
      (∀ i : Nat, (aux.roots[i]!).2 < 2 ^ numMarks) →
      (∀ i : Nat, (aux.dfsInfo[i]!).2 < 2 ^ numMarks) →
      (∀ i, i < aux.roots.size → (aux.roots[i]!).2 ≠ (1 <<< numMarks) - 1 ∨
        DijkstraNoInternalEdge succs aux stack i) →
      (∀ s ∈ aux.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) →
      (∀ s ∈ r.2.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) ∧
      (r.1 = none → DijkstraWellFormed r.2 ∧ DijkstraRangeInv succs edgeMarks r.2 ∧ r.2.dfsInfo.size = 0) ∧
      (∀ anchor stem, r.1 = some (anchor, stem) →
        InternallyConnected succs (dijkstraSccHint r.2) ∧
        AcceptingMarks succs edgeMarks numMarks (dijkstraSccHint r.2) ∧
        anchor ∈ dijkstraSccHint r.2)) ?_
  intro go ih aux stack r hr
  cases stack with
  | nil =>
    simp only [Option.some.injEq] at hr
    intro hwf _ _ _ hrangeinv hstackdfs _ _ _ _ _ _ _ _ _ _ hdead
    rw [← hr]
    exact ⟨hdead, fun _ => ⟨hwf, hrangeinv, by simpa using hstackdfs.1.symm⟩,
      fun _ _ h => absurd h (by simp)⟩
  | cons step rest =>
  intro hwf hsucceq hprefix hreach hrangeinv hstackdfs hrangeclosed hdispatched hmarksClosed hmarksOpen hmerged
    hTreeMarks hNoBack hrootsBound hdfsInfoBound hrootsNotFull hdead
  have hstepSuccEq : step.succ = succs step.state := hsucceq step (by simp)
  have hrestSuccEq : ∀ st ∈ rest, st.succ = succs st.state :=
    fun st hst => hsucceq st (List.mem_cons_of_mem _ hst)
  have hstepPrefix : ∀ x ∈ (step.succ.toList.take step.idx), dijkstraGetStatus aux x ≠ .unknown :=
    hprefix step (by simp)
  have hrestPrefix : ∀ st ∈ rest, ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux x ≠ .unknown :=
    fun st hst => hprefix st (List.mem_cons_of_mem _ hst)
  have hstepMarksOpen : ∀ x ∈ (step.succ.toList.take step.idx), ∀ i, i < aux.roots.size →
      x ∈ aux.range i → step.state ∈ aux.range i → ∀ m ∈ edgeMarks step.state x,
        (aux.roots[i]!).2.testBit m = true :=
    hmarksOpen step (by simp)
  have hrestMarksOpen : ∀ st ∈ rest, ∀ x ∈ (st.succ.toList.take st.idx), ∀ i, i < aux.roots.size →
      x ∈ aux.range i → st.state ∈ aux.range i → ∀ m ∈ edgeMarks st.state x,
        (aux.roots[i]!).2.testBit m = true :=
    fun st hst => hmarksOpen st (List.mem_cons_of_mem _ hst)
  have hne0 : 0 < aux.roots.size := hrangeinv.rootsWF.roots_pos_of_dfsInfo_pos (by
    have h1 := hstackdfs.1; simp only [List.length_cons] at h1; omega)
  have hstepMem : step.state ∈ aux.range (aux.roots.size - 1) :=
    dijkstraStackDfsInfo_head_mem_top hrangeinv.rootsWF hstackdfs
  -- The head's own dfs-depth is always `dfsInfo.size - 1`, the largest, so `dfsInfoMono` bounds every
  -- other still-open frame's `live` position strictly below it.
  have hrestPosLt : ∀ st ∈ rest, Nat.lt st.pos step.pos := by
    obtain ⟨hlen, hposCorr, _⟩ := hstackdfs
    have h0pos : step.pos = (aux.dfsInfo[aux.dfsInfo.size - 1]!).1 := by
      have := hposCorr 0 (by simp)
      simpa [hlen] using this
    intro st hst
    obtain ⟨k, hk, heq⟩ := List.getElem_of_mem hst
    have hk' : k + 1 < (step :: rest).length := by simp only [List.length_cons]; omega
    have hcorr := hposCorr (k + 1) hk'
    have hval : (step :: rest)[k + 1]'hk' = st := by
      simp only [List.getElem_cons_succ]
      exact heq
    have hcorr2 : st.pos = (aux.dfsInfo[(step :: rest).length - 1 - (k + 1)]!).1 :=
      (congrArg (·.pos) hval).symm.trans hcorr
    have hidxlt : (step :: rest).length - 1 - (k + 1) < aux.dfsInfo.size - 1 := by
      simp only [List.length_cons] at hlen ⊢; omega
    have hmono := hrangeinv.rootsWF.dfsInfoMono ((step :: rest).length - 1 - (k + 1)) (aux.dfsInfo.size - 1)
      hidxlt (by omega)
    rw [← h0pos] at hmono
    rw [hcorr2]
    exact hmono
  -- The current head always sits at the largest `live` position among the currently open frames.
  have hHeadMax : ∀ st' ∈ (step :: rest), Nat.le st'.pos step.pos := by
    intro st' hst'
    rcases List.mem_cons.mp hst' with rfl | hst'
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (hrestPosLt st' hst')
  have hstepMerged : ∀ x ∈ (step.succ.toList.take step.idx),
      dijkstraGetStatus aux x = .live → ∃ i, i < aux.roots.size ∧ step.state ∈ aux.range i ∧ x ∈ aux.range i := by
    intro x hx hlive
    by_cases hxs : x = step.state
    · exact ⟨aux.roots.size - 1, by omega, hstepMem, hxs ▸ hstepMem⟩
    · rcases hmerged step (by simp) x hx hlive with hgood | ⟨st', hst', heq, hlt⟩
      · exact hgood
      · exact absurd (Nat.lt_of_lt_of_le hlt (hHeadMax st' hst')) (Nat.lt_irrefl _)
  -- Genuine dispatched-and-live back-edges always resolve, the "still open above" escape only fires for
  -- targets currently on the stack, which case-neg's own callers (below) always rule out separately.
  have hrestMerged : ∀ st ∈ rest, ∀ x ∈ (st.succ.toList.take st.idx),
      dijkstraGetStatus aux x = .live →
      (∃ i, i < aux.roots.size ∧ st.state ∈ aux.range i ∧ x ∈ aux.range i) ∨
      (∃ st' ∈ step :: rest, st'.state = x ∧ Nat.lt st.pos st'.pos) :=
    fun st hst x hx hlive => hmerged st (List.mem_cons_of_mem _ hst) x hx hlive
  -- Every open frame still occupies its own `live` slot, so its state reads back as `.live`.
  have hStackLive : ∀ st ∈ (step :: rest), dijkstraGetStatus aux st.state = .live := fun st hst =>
    dijkstraGetStatus_live_of_pos hwf (dijkstraStackDfsInfo_pos_lt hrangeinv.rootsWF hstackdfs hst)
      (hstackdfs.2.2 st hst)
  have hstepReach : Reachable initialStates succs step.state := hreach step (by simp)
  have hrestReach : ∀ st ∈ rest, Reachable initialStates succs st.state :=
    fun st hst => hreach st (List.mem_cons_of_mem _ hst)
  by_cases h : step.idx < step.succ.size
  case pos =>
    simp only [h, dite_true] at hr
    simp only [dijkstraOps] at hr
    set d := step.succ[step.idx] with hd_def
    have hdSucc : d ∈ succs step.state := hstepSuccEq ▸ Array.getElem_mem h
    have hdTake : step.succ.toList.take (step.idx + 1) = step.succ.toList.take step.idx ++ [d] := by
      rw [List.take_add_one]; congr 1; simp [hd_def]
    have hSuccEq' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
        st.succ = succs st.state := by
      intro st hst
      rcases List.mem_cons.mp hst with rfl | hst
      · exact hstepSuccEq
      · exact hrestSuccEq st hst
    have hdfs'Reach : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
        Reachable initialStates succs st.state := by
      intro st hst
      rcases List.mem_cons.mp hst with rfl | hst
      · exact hstepReach
      · exact hrestReach st hst
    have hstackdfs' : DijkstraStackDfsInfo aux
        (({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest) := by
      obtain ⟨hlen, hpos, hlive⟩ := hstackdfs
      refine ⟨hlen, fun i hi => ?_, fun st hst => ?_⟩
      · have := hpos i hi
        rcases i with _ | i
        · exact this
        · exact this
      · rcases List.mem_cons.mp hst with rfl | hst
        · exact hlive step (by simp)
        · exact hlive st (List.mem_cons_of_mem _ hst)
    -- The bumped head keeps `step`'s own state and position, and nothing dispatches into the head from
    -- below (it already sits at the largest open position), so `hTreeMarks` transports across the bump.
    have hTreeMarksBump : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
        ∀ st' ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
        st'.state ∈ (st.succ.toList.take st.idx) → Nat.lt st.pos st'.pos →
        ∀ j, j < aux.roots.size → st'.state ∈ aux.range j → ∀ m ∈ edgeMarks st.state st'.state,
          (aux.roots[j]!).2.testBit m = true ∨ (aux.dfsInfo[(aux.roots[j]!).1]!).2.testBit m = true := by
      intro st hst st' hst' hdisp hlt j hj hjr m hm
      rcases List.mem_cons.mp hst with rfl | hst
      · rcases List.mem_cons.mp hst' with rfl | hst'
        · exact absurd hlt (Nat.lt_irrefl _)
        · exact absurd (Nat.lt_trans hlt (hrestPosLt st' hst')) (Nat.lt_irrefl _)
      · rcases List.mem_cons.mp hst' with rfl | hst'
        · exact hTreeMarks st (List.mem_cons_of_mem _ hst) step (by simp) hdisp hlt j hj hjr m hm
        · exact hTreeMarks st (List.mem_cons_of_mem _ hst) st' (List.mem_cons_of_mem _ hst') hdisp hlt j hj hjr m hm
    cases hgs : dijkstraGetStatus aux d with
    | dead =>
      simp only [hgs] at hr
      have hPrefix' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux x ≠ .unknown := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · show ∀ x ∈ step.succ.toList.take (step.idx + 1), dijkstraGetStatus aux x ≠ .unknown
          rw [hdTake]
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hstepPrefix x hx
          · simp only [List.mem_singleton] at hx; rw [hx]; simp [hgs]
        · exact hrestPrefix st hst
      have hexcl_iff : ∀ t, (∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          st.state ≠ t) → (∀ st ∈ step :: rest, st.state ≠ t) := by
        intro t hexcl st hst
        rcases List.mem_cons.mp hst with heq | hst
        · rw [heq]; exact hexcl { step with idx := step.idx + 1 } (by simp)
        · exact hexcl _ (List.mem_cons_of_mem _ hst)
      have hrangeclosed' : ∀ i, i < aux.roots.size → ∀ t ∈ aux.range i,
          (∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest, st.state ≠ t) →
          ∀ x ∈ succs t, dijkstraGetStatus aux x ≠ .unknown →
            x ∈ aux.range i ∨ dijkstraGetStatus aux x = .dead :=
        fun i hi t ht hexcl x hx hxne => hrangeclosed i hi t ht (hexcl_iff t hexcl) x hx hxne
      have hdispatched' : ∀ i, i < aux.roots.size → ∀ t ∈ aux.range i,
          (∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest, st.state ≠ t) →
          ∀ x ∈ succs t, dijkstraGetStatus aux x ≠ .unknown :=
        fun i hi t ht hexcl x hx => hdispatched i hi t ht (hexcl_iff t hexcl) x hx
      have hMarksOpen' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          ∀ x ∈ (st.succ.toList.take st.idx), ∀ i, i < aux.roots.size →
            x ∈ aux.range i → st.state ∈ aux.range i → ∀ m ∈ edgeMarks st.state x,
              (aux.roots[i]!).2.testBit m = true := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · show ∀ x ∈ step.succ.toList.take (step.idx + 1), ∀ i, i < aux.roots.size →
            x ∈ aux.range i → step.state ∈ aux.range i → ∀ m ∈ edgeMarks step.state x,
              (aux.roots[i]!).2.testBit m = true
          rw [hdTake]
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hstepMarksOpen x hx
          · simp only [List.mem_singleton] at hx
            subst hx
            intro i _ hxi
            exact absurd hxi (dijkstraGetStatus_dead_not_mem_range hwf hgs i)
        · exact hrestMarksOpen st hst
      have hmarksClosed' : ∀ i, i < aux.roots.size → ∀ t ∈ aux.range i,
          (∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest, st.state ≠ t) →
          ∀ x ∈ succs t, x ∈ aux.range i → ∀ m ∈ edgeMarks t x, (aux.roots[i]!).2.testBit m = true :=
        fun i hi t ht hexcl x hx hxr m hm => hmarksClosed i hi t ht (hexcl_iff t hexcl) x hx hxr m hm
      have hmerged' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux x = .live →
          (∃ i, i < aux.roots.size ∧ st.state ∈ aux.range i ∧ x ∈ aux.range i) ∨
          (∃ st' ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
            st'.state = x ∧ Nat.lt st.pos st'.pos) := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · show ∀ x ∈ step.succ.toList.take (step.idx + 1), dijkstraGetStatus aux x = .live →
            (∃ i, i < aux.roots.size ∧ step.state ∈ aux.range i ∧ x ∈ aux.range i) ∨
            (∃ st' ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
              st'.state = x ∧ Nat.lt step.pos st'.pos)
          rw [hdTake]
          intro x hx hlive
          rcases List.mem_append.mp hx with hx | hx
          · exact Or.inl (hstepMerged x hx hlive)
          · simp only [List.mem_singleton] at hx
            subst hx
            rw [hgs] at hlive
            simp at hlive
        · intro x hx hlive
          rcases hrestMerged st hst x hx hlive with hgood | ⟨st', hst', heq, hlt⟩
          · exact Or.inl hgood
          · right
            rcases List.mem_cons.mp hst' with heq' | hst'
            · exact ⟨{ step with idx := step.idx + 1 }, by simp, heq' ▸ heq, heq' ▸ hlt⟩
            · exact ⟨st', List.mem_cons_of_mem _ hst', heq, hlt⟩
      exact ih aux _ r hr hwf hSuccEq' hPrefix' hdfs'Reach hrangeinv hstackdfs' hrangeclosed' hdispatched'
        hmarksClosed' hMarksOpen' hmerged' hTreeMarksBump
        (NoBackDispatch.state_congr ({ step with idx := step.idx + 1 }) hNoBack rfl) hrootsBound hdfsInfoBound
        (fun i hi => (hrootsNotFull i hi).imp id
          (DijkstraNoInternalEdge.bump hdTake (dijkstraGetStatus_dead_not_mem_range hwf hgs i))) hdead
    | live =>
      simp only [hgs] at hr
      rcases hupdeq : dijkstraUpdate numMarks aux (edgeMarks step.state d) d with ⟨aux', found⟩
      simp only [hupdeq] at hr
      have haux'1 : (dijkstraUpdate numMarks aux (edgeMarks step.state d) d).1 = aux' :=
        congrArg Prod.fst hupdeq
      have hdead_eq : aux'.dead = aux.dead := by
        have := (dijkstraUpdate_fields numMarks aux (edgeMarks step.state d) d).2.2.1
        rwa [haux'1] at this
      have hdfsInfo_eq : aux'.dfsInfo = aux.dfsInfo := by
        have := (dijkstraUpdate_fields numMarks aux (edgeMarks step.state d) d).2.2.2
        rwa [haux'1] at this
      have hstatus_eq : ∀ q, dijkstraGetStatus aux' q = dijkstraGetStatus aux q := by
        intro q
        have := dijkstraUpdate_status numMarks aux (edgeMarks step.state d) d q
        rwa [haux'1] at this
      have hlive_eq : aux'.live = aux.live := by
        have := (dijkstraUpdate_fields numMarks aux (edgeMarks step.state d) d).1
        rwa [haux'1] at this
      have hroots_pos : 0 < aux.roots.size := hrangeinv.rootsWF.roots_pos_of_dfsInfo_pos (by
        have h1 := hstackdfs.1
        simp only [List.length_cons] at h1
        omega)
      have hd_contains : aux.liveIndex.contains d = true := by
        unfold dijkstraGetStatus dijkstraStatusOf at hgs
        by_cases hc : aux.liveIndex.contains d = true
        · exact hc
        · exfalso
          rw [if_neg hc] at hgs
          split at hgs <;> cases hgs
      obtain ⟨lo, hlo_lt, hd_range, haux'size, haux'pre, haux'top⟩ :=
        dijkstraUpdate_merge_locate numMarks aux (edgeMarks step.state d) d hwf hrangeinv.rootsWF hroots_pos
          hd_contains
      rw [haux'1] at haux'size haux'pre haux'top
      have hunion : ∀ x, x ∈ aux'.range lo ↔ ∃ i, lo ≤ i ∧ i < aux.roots.size ∧ x ∈ aux.range i :=
        dijkstraMerge_range_union hlo_lt hrangeinv.rootsWF haux'size haux'top hdfsInfo_eq hlive_eq
      have hprefix_eq : ∀ i, i < lo → aux'.range i = aux.range i :=
        fun i hi => dijkstraMerge_range_prefix_eq hlo_lt haux'size hdfsInfo_eq hlive_eq haux'top haux'pre i hi
      have hrangeinv' : DijkstraRangeInv succs edgeMarks aux' :=
        haux'1 ▸ dijkstraRangeInv_update hwf hrangeinv hroots_pos hd_contains hstepMem hdSucc
      by_cases hf : found = true
      -- The reported range is the merged top one: connected by `hrangeinv'`, and its bitmask being
      -- all-ones turns `bitSound` into `AcceptingMarks` one mark at a time.
      · simp only [hf, if_true, Option.some.injEq] at hr
        have hhint : dijkstraSccHint aux' = aux'.range lo := by
          rw [dijkstraSccHint_eq_top_range aux' hrangeinv'.rootsWF (by omega),
            show aux'.roots.size - 1 = lo from by omega]
        have hstepLo : step.state ∈ aux'.range lo :=
          (hunion step.state).mpr ⟨aux.roots.size - 1, by omega, by omega, hstepMem⟩
        have hfull : (aux'.roots[lo]!).2 = (1 <<< numMarks) - 1 := by
          obtain ⟨lo2, hlo2eq, hfoundeq⟩ :=
            dijkstraUpdate_merge_found numMarks aux (edgeMarks step.state d) d hroots_pos
          rw [haux'1] at hlo2eq hfoundeq
          rw [show lo2 = lo from by omega] at hfoundeq
          have : (dijkstraUpdate numMarks aux (edgeMarks step.state d) d).2 = found :=
            congrArg Prod.snd hupdeq
          rw [this, hf] at hfoundeq
          exact eq_of_beq hfoundeq.symm
        have hcov : ∀ m, m < numMarks → ∃ s ∈ aux'.range lo, ∃ t ∈ aux'.range lo,
            t ∈ succs s ∧ m ∈ edgeMarks s t := by
          intro m hm
          refine hrangeinv'.bitSound lo (by omega) m ?_
          rw [hfull, allOnesMask_eq, Nat.testBit_two_pow_sub_one]
          exact decide_eq_true hm
        rw [← hr]
        refine ⟨fun s hs => hdead s (by rwa [hdead_eq] at hs), by simp, ?_⟩
        intro anchor stem heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        rw [hhint, ← heq.1]
        exact ⟨hrangeinv'.connected lo (by omega),
          ⟨⟨step.state, hstepLo, d, (hunion d).mpr ⟨lo, le_refl _, hlo_lt, hd_range⟩, hdSucc⟩, hcov⟩,
          hstepLo⟩
      · simp only [hf] at hr
        have hwf' : DijkstraWellFormed aux' :=
          haux'1 ▸ dijkstraWellFormed_update numMarks aux (edgeMarks step.state d) d hwf
        have hPrefix' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
            ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux' x ≠ .unknown := by
          intro st hst
          rcases List.mem_cons.mp hst with rfl | hst
          · show ∀ x ∈ step.succ.toList.take (step.idx + 1), dijkstraGetStatus aux' x ≠ .unknown
            rw [hdTake]
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · rw [hstatus_eq]; exact hstepPrefix x hx
            · simp only [List.mem_singleton] at hx; rw [hx, hstatus_eq]; simp [hgs]
          · intro x hx; rw [hstatus_eq]; exact hrestPrefix st hst x hx
        have hstackdfs' : DijkstraStackDfsInfo aux'
            (({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest) := by
          obtain ⟨hlen, hpos, hlive⟩ := hstackdfs
          refine ⟨?_, fun i hi => ?_, fun st hst => ?_⟩
          · rw [hdfsInfo_eq]; exact hlen
          · rw [hdfsInfo_eq]
            have := hpos i hi
            rcases i with _ | i
            · exact this
            · exact this
          · rw [hlive_eq]
            rcases List.mem_cons.mp hst with rfl | hst
            · exact hlive step (by simp)
            · exact hlive st (List.mem_cons_of_mem _ hst)
        have hdead' : ∀ s ∈ aux'.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc := by
          rw [hdead_eq]; exact hdead
        have hexcl_iff : ∀ t, (∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
            st.state ≠ t) → (∀ st ∈ step :: rest, st.state ≠ t) := by
          intro t hexcl st hst
          rcases List.mem_cons.mp hst with heq | hst
          · rw [heq]; exact hexcl { step with idx := step.idx + 1 } (by simp)
          · exact hexcl _ (List.mem_cons_of_mem _ hst)
        have hrangeclosed' : ∀ i, i < aux'.roots.size → ∀ t ∈ aux'.range i,
            (∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest, st.state ≠ t) →
            ∀ x ∈ succs t, dijkstraGetStatus aux' x ≠ .unknown →
              x ∈ aux'.range i ∨ dijkstraGetStatus aux' x = .dead := by
          intro i hi t ht hexcl x hx hxne
          rw [hstatus_eq x] at hxne
          rw [haux'size] at hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
          · rw [hprefix_eq i hilt] at ht
            rcases hrangeclosed i (by omega) t ht (hexcl_iff t hexcl) x hx hxne with hc | hc
            · exact Or.inl (by rw [hprefix_eq i hilt]; exact hc)
            · exact Or.inr (by rw [hstatus_eq x]; exact hc)
          · subst hieq
            obtain ⟨k, hlok, hkn, htk⟩ := (hunion t).mp ht
            rcases hrangeclosed k hkn t htk (hexcl_iff t hexcl) x hx hxne with hc | hc
            · exact Or.inl ((hunion x).mpr ⟨k, hlok, hkn, hc⟩)
            · exact Or.inr (by rw [hstatus_eq x]; exact hc)
        have hdispatched' : ∀ i, i < aux'.roots.size → ∀ t ∈ aux'.range i,
            (∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest, st.state ≠ t) →
            ∀ x ∈ succs t, dijkstraGetStatus aux' x ≠ .unknown := by
          intro i hi t ht hexcl x hx
          rw [hstatus_eq x]
          rw [haux'size] at hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
          · rw [hprefix_eq i hilt] at ht
            exact hdispatched i (by omega) t ht (hexcl_iff t hexcl) x hx
          · subst hieq
            obtain ⟨k, hlok, hkn, htk⟩ := (hunion t).mp ht
            exact hdispatched k hkn t htk (hexcl_iff t hexcl) x hx
        -- Every bitmask the merge absorbs (the old top's own, this edge's marks, and every range in between)
        -- persists into the new top range's bitmask.
        obtain ⟨lo1, hlo1eq, hlo1top, hlo1abs, hlo1dfs⟩ :=
          dijkstraUpdate_merge_bitmask numMarks aux (edgeMarks step.state d) d hroots_pos
        rw [haux'1] at hlo1eq hlo1top hlo1abs hlo1dfs
        have hlo1lo : lo1 = lo := by omega
        rw [hlo1lo] at hlo1top hlo1abs hlo1dfs
        have hbitAbsorb : ∀ k, lo ≤ k → k < aux.roots.size → ∀ m, (aux.roots[k]!).2.testBit m = true →
            (aux'.roots[lo]!).2.testBit m = true := by
          intro k hk1 hk2 m hm
          by_cases hklt : k < aux.roots.size - 1
          · exact hlo1abs k hk1 hklt m hm
          · have hkeq : k = aux.roots.size - 1 := by omega
            subst hkeq
            exact hlo1top m (by simp [hm])
        -- Only ranges strictly above `lo`, the tree edge entering the merged range's own root starts below
        -- it, so `dijkstraUpdate` deliberately leaves its marks out.
        have hbitDfsAbsorb : ∀ k, lo < k → k < aux.roots.size → ∀ m,
            (aux.dfsInfo[(aux.roots[k]!).1]!).2.testBit m = true → (aux'.roots[lo]!).2.testBit m = true :=
          hlo1dfs
        -- Any old pair sharing a range still shares one afterwards, ranges below `lo` are untouched and
        -- everything from `lo` up is absorbed into the single new top range.
        have hpairLift : ∀ j, j < aux.roots.size → ∀ y z, y ∈ aux.range j → z ∈ aux.range j →
            ∃ i, i < aux'.roots.size ∧ y ∈ aux'.range i ∧ z ∈ aux'.range i := by
          intro j hj y z hy hz
          by_cases hjlo : j < lo
          · exact ⟨j, by omega, by rw [hprefix_eq j hjlo]; exact hy, by rw [hprefix_eq j hjlo]; exact hz⟩
          · exact ⟨lo, by omega, (hunion y).mpr ⟨j, by omega, hj, hy⟩, (hunion z).mpr ⟨j, by omega, hj, hz⟩⟩
        have hmarksClosed' : ∀ i, i < aux'.roots.size → ∀ t ∈ aux'.range i,
            (∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest, st.state ≠ t) →
            ∀ x ∈ succs t, x ∈ aux'.range i → ∀ m ∈ edgeMarks t x, (aux'.roots[i]!).2.testBit m = true := by
          intro i hi t ht hexcl x hx hxr m hm
          rw [haux'size] at hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
          · rw [hprefix_eq i hilt] at ht hxr
            rw [haux'pre i hilt]
            exact hmarksClosed i (by omega) t ht (hexcl_iff t hexcl) x hx hxr m hm
          · subst hieq
            obtain ⟨k, hlok, hkn, htk⟩ := (hunion t).mp ht
            obtain ⟨k', _, _, hxk'⟩ := (hunion x).mp hxr
            -- `t` is retired, so its successor `x` either stayed inside `t`'s own old range or went dead,
            -- and dead states sit in no range at all.
            rcases hrangeclosed k hkn t htk (hexcl_iff t hexcl) x hx
              (hdispatched k hkn t htk (hexcl_iff t hexcl) x hx) with hxrk | hxd
            · exact hbitAbsorb k hlok hkn m (hmarksClosed k hkn t htk (hexcl_iff t hexcl) x hx hxrk m hm)
            · exact absurd hxk' (dijkstraGetStatus_dead_not_mem_range hwf hxd k')
        -- The merge folds in every absorbed range's own bitmask and its root's `dfsInfo` entry, so a tree
        -- edge's marks land in the merged range's bitmask whichever of the two held them before.
        have hTreeMarks' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
            ∀ st' ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
            st'.state ∈ (st.succ.toList.take st.idx) → Nat.lt st.pos st'.pos →
            ∀ j, j < aux'.roots.size → st'.state ∈ aux'.range j → ∀ m ∈ edgeMarks st.state st'.state,
              (aux'.roots[j]!).2.testBit m = true ∨ (aux'.dfsInfo[(aux'.roots[j]!).1]!).2.testBit m = true := by
          intro st hst st' hst' hdisp hlt j hj hjr m hm
          rw [hdfsInfo_eq]
          rw [haux'size] at hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | hjeq
          · rw [hprefix_eq j hjlt] at hjr
            rw [haux'pre j hjlt]
            exact hTreeMarksBump st hst st' hst' hdisp hlt j (by omega) hjr m hm
          · subst hjeq
            obtain ⟨k, hlok, hkn, hjk⟩ := (hunion st'.state).mp hjr
            rcases hTreeMarksBump st hst st' hst' hdisp hlt k hkn hjk m hm with hb | hb
            · exact Or.inl (hbitAbsorb k hlok hkn m hb)
            · rcases Nat.eq_or_lt_of_le hlok with hkeq | hklt
              -- `k = lo`, so the merged range's own root entry is literally the one already holding these marks
              · exact Or.inr (by rw [haux'top, hkeq]; exact hb)
              · exact Or.inl (hbitDfsAbsorb k hklt hkn m hb)
        have hMarksOpen' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
            ∀ x ∈ (st.succ.toList.take st.idx), ∀ i, i < aux'.roots.size →
              x ∈ aux'.range i → st.state ∈ aux'.range i → ∀ m ∈ edgeMarks st.state x,
                (aux'.roots[i]!).2.testBit m = true := by
          intro st hst
          rcases List.mem_cons.mp hst with rfl | hst
          · show ∀ x ∈ step.succ.toList.take (step.idx + 1), ∀ i, i < aux'.roots.size →
              x ∈ aux'.range i → step.state ∈ aux'.range i → ∀ m ∈ edgeMarks step.state x,
                (aux'.roots[i]!).2.testBit m = true
            rw [hdTake]
            intro x hx i hi hxr hsr m hm
            rw [haux'size] at hi
            rcases List.mem_append.mp hx with hx | hx
            · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
              · rw [hprefix_eq i hilt] at hxr hsr
                rw [haux'pre i hilt]
                exact hstepMarksOpen x hx i (by omega) hxr hsr m hm
              · subst hieq
                obtain ⟨k', _, hkn', hxk'⟩ := (hunion x).mp hxr
                obtain ⟨jj, hjj, hsjj, hxjj⟩ := hstepMerged x hx (dijkstraGetStatus_live_of_mem_range hwf hxk')
                have hjjtop : jj = aux.roots.size - 1 :=
                  DijkstraAux.range_mem_unique hrangeinv.rootsWF hwf hjj (by omega) hsjj hstepMem
                exact hbitAbsorb jj (by omega) hjj m (hstepMarksOpen x hx jj hjj hxjj hsjj m hm)
            · simp only [List.mem_singleton] at hx
              subst hx
              rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
              · exfalso
                rw [hprefix_eq i hilt] at hxr
                exact absurd (DijkstraAux.range_mem_unique hrangeinv.rootsWF hwf (by omega) hlo_lt hxr hd_range)
                  (by omega)
              · subst hieq
                -- this edge's own marks are folded in by `dijkstraUpdate` itself
                exact hlo1top m (by simp [marksToBitmask_testBit hm])
          · intro x hx i hi hxr hsr m hm
            rw [haux'size] at hi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
            · rw [hprefix_eq i hilt] at hxr hsr
              rw [haux'pre i hilt]
              exact hrestMarksOpen st hst x hx i (by omega) hxr hsr m hm
            · subst hieq
              obtain ⟨k', hlok', hkn', hxk'⟩ := (hunion x).mp hxr
              obtain ⟨k'', hlok'', hkn'', hsk''⟩ := (hunion st.state).mp hsr
              rcases hrestMerged st hst x hx (dijkstraGetStatus_live_of_mem_range hwf hxk') with
                ⟨jj, hjj, hsjj, hxjj⟩ | ⟨st', hst', heq, hlt⟩
              · have hjjeq : jj = k'' :=
                  DijkstraAux.range_mem_unique hrangeinv.rootsWF hwf hjj hkn'' hsjj hsk''
                exact hbitAbsorb jj (by omega) hjj m (hrestMarksOpen st hst x hx jj hjj hxjj hsjj m hm)
              · -- `x` is a still-open frame, so this is `st`'s own tree edge into it. `st.state` sits at the
                -- lower `live` position, so its own old range index never exceeds `x`'s.
                have hstpos := hstackdfs.2.2 st (List.mem_cons_of_mem _ hst)
                have hxpos := hstackdfs.2.2 st' hst'
                have hxk'' : st'.state ∈ aux.range k' := by rw [heq]; exact hxk'
                have hk''le : k'' ≤ k' :=
                  DijkstraAux.range_le_of_pos_lt hrangeinv.rootsWF hkn''
                    (DijkstraAux.mem_range_pos hwf hsk'' hstpos
                      (dijkstraStackDfsInfo_pos_lt hrangeinv.rootsWF hstackdfs
                        (List.mem_cons_of_mem _ hst))).1
                    (DijkstraAux.mem_range_pos hwf hxk'' hxpos
                      (dijkstraStackDfsInfo_pos_lt hrangeinv.rootsWF hstackdfs hst')).2 hlt
                rcases Nat.eq_or_lt_of_le hk''le with hkeq | hklt
                -- both endpoints already shared a range before the merge, so `hmarksOpen` applies directly
                · exact hbitAbsorb k' hlok' hkn' m
                    (hrestMarksOpen st hst x hx k' hkn' hxk' (hkeq ▸ hsk'') m hm)
                · rcases hTreeMarks st (List.mem_cons_of_mem _ hst) st' hst' (heq ▸ hx) hlt k' hkn'
                    (heq ▸ hxk') m (heq ▸ hm) with hb | hb
                  · exact hbitAbsorb k' hlok' hkn' m hb
                  · exact hbitDfsAbsorb k' (by omega) hkn' m hb
        have hmerged' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
            ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux' x = .live →
            (∃ i, i < aux'.roots.size ∧ st.state ∈ aux'.range i ∧ x ∈ aux'.range i) ∨
            (∃ st' ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
              st'.state = x ∧ Nat.lt st.pos st'.pos) := by
          intro st hst
          rcases List.mem_cons.mp hst with rfl | hst
          · show ∀ x ∈ step.succ.toList.take (step.idx + 1), dijkstraGetStatus aux' x = .live →
              (∃ i, i < aux'.roots.size ∧ step.state ∈ aux'.range i ∧ x ∈ aux'.range i) ∨
              (∃ st' ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
                st'.state = x ∧ Nat.lt step.pos st'.pos)
            rw [hdTake]
            intro x hx hlive
            rw [hstatus_eq] at hlive
            rcases List.mem_append.mp hx with hx | hx
            · obtain ⟨j, hj, hsj, hxj⟩ := hstepMerged x hx hlive
              exact Or.inl (hpairLift j hj step.state x hsj hxj)
            · simp only [List.mem_singleton] at hx
              subst hx
              -- The merge is exactly what puts `step.state` and its live target `d` in one range.
              exact Or.inl ⟨lo, by omega, (hunion step.state).mpr ⟨aux.roots.size - 1, by omega, by omega, hstepMem⟩,
                (hunion d).mpr ⟨lo, Nat.le_refl _, hlo_lt, hd_range⟩⟩
          · intro x hx hlive
            rw [hstatus_eq] at hlive
            rcases hrestMerged st hst x hx hlive with hgood | ⟨st', hst', heq, hlt⟩
            · obtain ⟨j, hj, hsj, hxj⟩ := hgood
              exact Or.inl (hpairLift j hj st.state x hsj hxj)
            · right
              rcases List.mem_cons.mp hst' with heq' | hst''
              · exact ⟨{ step with idx := step.idx + 1 }, by simp, heq' ▸ heq, heq' ▸ hlt⟩
              · exact ⟨st', List.mem_cons_of_mem _ hst'', heq, hlt⟩
        have hdfsInfoBound' : ∀ i : Nat, (aux'.dfsInfo[i]!).2 < 2 ^ numMarks := by
          rw [hdfsInfo_eq]; exact hdfsInfoBound
        have hrootsBound' : ∀ i : Nat, (aux'.roots[i]!).2 < 2 ^ numMarks := by
          obtain ⟨lo', hlo'eq, hlo'bound⟩ := dijkstraUpdate_merge_bound numMarks aux (edgeMarks step.state d) d
            hroots_pos hdfsInfoBound hrootsBound (marksToBitmask_lt (hmarksBound step.state d))
          rw [haux'1] at hlo'eq hlo'bound
          have hloeq : lo' = lo := by omega
          intro i
          by_cases hi : i < lo
          · rw [haux'pre i hi]; exact hrootsBound i
          · by_cases hieq : i = lo
            · subst hieq; rw [← hloeq]; exact hlo'bound
            · rw [getElem!_neg aux'.roots i (by omega)]
              exact getElem!_pair_default_snd_lt numMarks
        have hffalse : found = false := by cases found with
          | true => exact absurd rfl hf
          | false => rfl
        have hrootsNotFull' : ∀ i, i < aux'.roots.size → (aux'.roots[i]!).2 ≠ (1 <<< numMarks) - 1 ∨
          DijkstraNoInternalEdge succs aux'
            (({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest) i := by
          obtain ⟨lo'', hlo''eq, hfoundeq⟩ :=
            dijkstraUpdate_merge_found numMarks aux (edgeMarks step.state d) d hroots_pos
          have hfound2 : (dijkstraUpdate numMarks aux (edgeMarks step.state d) d).2 = found :=
            congrArg Prod.snd hupdeq
          rw [haux'1] at hlo''eq hfoundeq
          rw [hfound2] at hfoundeq
          have hloeq'' : lo'' = lo := by omega
          intro i hi
          by_cases hilt : i < lo
          -- untouched prefix range: transport both disjuncts across the bump and the range equality
          · have hdnot : d ∉ aux.range i := fun hc =>
              absurd (DijkstraAux.range_mem_unique hrangeinv.rootsWF hwf (by omega) hlo_lt hc hd_range)
                (by omega)
            refine (hrootsNotFull i (by omega)).imp (fun hne => ?_)
              (fun hno => (DijkstraNoInternalEdge.bump hdTake hdnot hno).congr_range (hprefix_eq i hilt))
            rw [haux'pre i hilt]; exact hne
          · by_cases hieq : i = lo
            · subst hieq
              rw [hloeq''] at hfoundeq
              refine Or.inl ?_
              intro hcontra
              rw [hcontra, beq_self_eq_true, hffalse] at hfoundeq
              exact Bool.noConfusion hfoundeq
            · exfalso; omega
        exact ih aux' _ r hr hwf' hSuccEq' hPrefix' hdfs'Reach hrangeinv' hstackdfs' hrangeclosed' hdispatched'
          hmarksClosed' hMarksOpen' hmerged' hTreeMarks'
          (NoBackDispatch.state_congr ({ step with idx := step.idx + 1 }) hNoBack rfl)
          hrootsBound' hdfsInfoBound' hrootsNotFull' hdead'
    | unknown =>
      simp only [hgs] at hr
      rcases hpsheq : dijkstraPush aux d (edgeMarks step.state d) with ⟨aux', pos'⟩
      simp only [hpsheq] at hr
      have haux'2 : (dijkstraPush aux d (edgeMarks step.state d)).1 = aux' := congrArg Prod.fst hpsheq
      have hwf' : DijkstraWellFormed aux' :=
        haux'2 ▸ dijkstraWellFormed_push aux d (edgeMarks step.state d) hwf hgs
      have hpeq : ∀ q, dijkstraGetStatus aux' q = if q == d then .live else dijkstraGetStatus aux q :=
        fun q => haux'2 ▸ dijkstraPush_status aux d (edgeMarks step.state d) q
      -- `push` only ever extends `live`/`roots`/`dfsInfo`, `dead` is untouched by construction.
      have hdeq : aux'.dead = aux.dead := by rw [← haux'2]; rfl
      have hpos'_eq : pos' = aux.live.size := by
        have h2 : (dijkstraPush aux d (edgeMarks step.state d)).2 = pos' := congrArg Prod.snd hpsheq
        rw [← h2]; rfl
      set newStep : DFSStep State Nat :=
        { state := d, pos := pos', acc := edgeMarks step.state d, succ := succs d, idx := 0 } with hnewStep_def
      have hSuccEq'' : ∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          st.succ = succs st.state := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · rfl
        · exact hSuccEq' st hst
      have hReach'' : ∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          Reachable initialStates succs st.state := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · exact Reachable.step hstepReach hdSucc
        · exact hdfs'Reach st hst
      have hPrefix'' : ∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux' x ≠ .unknown := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · simp [hnewStep_def]
        · rcases List.mem_cons.mp hst with rfl | hst
          · show ∀ x ∈ step.succ.toList.take (step.idx + 1), dijkstraGetStatus aux' x ≠ .unknown
            rw [hdTake]
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · rw [hpeq]
              by_cases hxd : x == d
              · simp [hxd]
              · simp only [hxd]; exact hstepPrefix x hx
            · simp only [List.mem_singleton] at hx
              rw [hx, hpeq]; simp
          · intro x hx
            rw [hpeq]
            by_cases hxd : x == d
            · simp [hxd]
            · simp only [hxd]; exact hrestPrefix st hst x hx
      -- The new singleton range `{d}` chains to the old top and starts with an empty bitmask.
      have hwfOld := hrangeinv.rootsWF
      have hne : 0 < aux.roots.size :=
        hwfOld.roots_pos_of_dfsInfo_pos (by
          obtain ⟨hlen, _, _⟩ := hstackdfs; simp only [List.length_cons] at hlen; omega)
      have hsize' : aux'.roots.size = aux.roots.size + 1 := by
        rw [← haux'2]; unfold dijkstraPush; simp only [Array.size_push]
      have hwf'' : DijkstraRootsWF aux' :=
        haux'2 ▸ dijkstraRootsWF_push aux d (edgeMarks step.state d) hwfOld
      have hrangeEq : ∀ i, i < aux.roots.size → aux'.range i = aux.range i := by
        intro i hi
        rw [← haux'2]
        exact dijkstraPush_range_eq aux d (edgeMarks step.state d) hwfOld i hi
      have hnewRangeIff : ∀ x, x ∈ aux'.range aux.roots.size ↔ x = d := by
        intro x
        rw [← haux'2]
        exact dijkstraPush_new_range_mem_iff aux d (edgeMarks step.state d) x
      have hstepTop : step.state ∈ aux'.range (aux.roots.size - 1) := by
        rw [hrangeEq (aux.roots.size - 1) (by omega)]
        exact dijkstraStackDfsInfo_head_mem_top hwfOld hstackdfs
      have hconnected' : ∀ i, i < aux'.roots.size → InternallyConnected succs (aux'.range i) := by
        intro i hi
        rw [hsize'] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
        · rw [hrangeEq i hilt]; exact hrangeinv.connected i hilt
        · subst hieq
          intro s hs t ht
          left; rw [(hnewRangeIff s).mp hs, (hnewRangeIff t).mp ht]
      have hchained' : ∀ i, (h : i + 1 < aux'.roots.size) →
          ∃ s ∈ aux'.range i, ∃ t ∈ aux'.range (i + 1), t ∈ succs s := by
        intro i hi
        rw [hsize'] at hi
        by_cases hilt : i + 1 < aux.roots.size
        · obtain ⟨s, hs, t, ht, hst⟩ := hrangeinv.chained i hilt
          exact ⟨s, (hrangeEq i (by omega)) ▸ hs, t, (hrangeEq (i + 1) hilt) ▸ ht, hst⟩
        · have hieq : i = aux.roots.size - 1 := by omega
          refine ⟨step.state, ?_, d, ?_, hdSucc⟩
          · rw [hieq]; exact hstepTop
          · rw [show i + 1 = aux.roots.size from by omega]; exact (hnewRangeIff d).mpr rfl
      have hdfsPush' : aux'.dfsInfo =
          aux.dfsInfo.push (aux.live.size, marksToBitmask (edgeMarks step.state d)) := by
        rw [← haux'2]; rfl
      have hlivePush' : aux'.live = aux.live.push d := by rw [← haux'2]; rfl
      have hrootsPush' : aux'.roots = aux.roots.push (aux.dfsInfo.size, 0) := by rw [← haux'2]; rfl
      have hbitSound' : ∀ i, i < aux'.roots.size → ∀ m, (aux'.roots[i]!).2.testBit m = true →
          ∃ s ∈ aux'.range i, ∃ t ∈ aux'.range i, t ∈ succs s ∧ m ∈ edgeMarks s t := by
        intro i hi m hm
        rw [hsize'] at hi
        rw [hrootsPush'] at hm
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
        · rw [Array.getElem!_push_lt hilt] at hm
          rw [hrangeEq i hilt]
          exact hrangeinv.bitSound i hilt m hm
        -- the fresh singleton range starts with an empty bitmask, so it claims no marks at all
        · exact absurd (hieq ▸ hm) (by rw [Array.getElem!_push_eq]; simp)
      have hentrySound' : ∀ k, k < aux'.dfsInfo.size → ∀ m, (aux'.dfsInfo[k]!).2.testBit m = true →
          0 < k ∧ aux'.live[(aux'.dfsInfo[k]!).1]! ∈ succs (aux'.live[(aux'.dfsInfo[k - 1]!).1]!) ∧
            m ∈ edgeMarks (aux'.live[(aux'.dfsInfo[k - 1]!).1]!) (aux'.live[(aux'.dfsInfo[k]!).1]!) := by
        have hdfsPos : 0 < aux.dfsInfo.size := by
          obtain ⟨hlen, _, _⟩ := hstackdfs; simp only [List.length_cons] at hlen; omega
        intro k hk m hm
        rw [hdfsPush', Array.size_push] at hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hklt | hkeq
        · have hk1 : k - 1 < aux.dfsInfo.size := by omega
          rw [hdfsPush', Array.getElem!_push_lt hklt] at hm ⊢
          rw [Array.getElem!_push_lt hk1, hlivePush',
            Array.getElem!_push_lt (hrangeinv.rootsWF.dfsInfoLt k hklt),
            Array.getElem!_push_lt (hrangeinv.rootsWF.dfsInfoLt (k - 1) hk1)]
          exact hrangeinv.entrySound k hklt m hm
        -- the freshly pushed frame: its entry marks are exactly this tree edge's, from the parent frame
        · subst hkeq
          have hparent : (aux.dfsInfo[aux.dfsInfo.size - 1]!).1 = step.pos := by
            obtain ⟨hlen, hposCorr, _⟩ := hstackdfs
            have := hposCorr 0 (by simp)
            simpa [hlen] using this.symm
          have hsteplt := dijkstraStackDfsInfo_pos_lt hrangeinv.rootsWF hstackdfs
            (show step ∈ step :: rest by simp)
          rw [hdfsPush', Array.getElem!_push_eq] at hm ⊢
          rw [Array.getElem!_push_lt (show aux.dfsInfo.size - 1 < aux.dfsInfo.size from by omega),
            hparent, hlivePush', Array.getElem!_push_eq, Array.getElem!_push_lt hsteplt,
            hstackdfs.2.2 step (by simp)]
          exact ⟨by omega, hdSucc, marksToBitmask_mem hm⟩
      have hrangeinv' : DijkstraRangeInv succs edgeMarks aux' :=
        ⟨hwf'', hconnected', hchained', hbitSound', hentrySound'⟩
      -- `DijkstraStackDfsInfo` for the new stack: `newStep` fresh at the top, `dfs'` pushed through.
      have hstackdfs'' : DijkstraStackDfsInfo aux'
          (newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest) := by
        obtain ⟨hlen, hpos, hlive⟩ := hstackdfs'
        have hlen'' : aux'.dfsInfo.size = aux.dfsInfo.size + 1 := by
          rw [← haux'2]; unfold dijkstraPush; simp only [Array.size_push]
        refine ⟨?_, fun i hi => ?_, fun st hst => ?_⟩
        · simp only [List.length_cons] at hlen ⊢; omega
        · rcases i with _ | i
          · simp only [List.getElem_cons_zero]
            have hidx : (newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest).length - 1 - 0 =
                aux.dfsInfo.size := by simp only [List.length_cons] at hlen ⊢; omega
            rw [hidx, hnewStep_def]
            show pos' = (aux'.dfsInfo[aux.dfsInfo.size]!).1
            rw [hpos'_eq, ← haux'2]
            unfold dijkstraPush
            simp only [Array.getElem!_push_eq]
          · simp only [List.getElem_cons_succ]
            have hib : i < (({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest).length := by
              simp only [List.length_cons] at hi ⊢; omega
            have hidx : (newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest).length - 1 -
                (i + 1) = (({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest).length - 1 - i := by
              simp only [List.length_cons]; omega
            rw [hidx, ← haux'2]
            exact dijkstraStackDfsInfo_pos_eq_push aux d (edgeMarks step.state d) ⟨hlen, hpos, hlive⟩ i hib
        · rcases List.mem_cons.mp hst with rfl | hst
          · show aux'.live[newStep.pos]! = newStep.state
            rw [hnewStep_def]
            show aux'.live[pos']! = d
            rw [hpos'_eq, ← haux'2]; unfold dijkstraPush; simp only [Array.getElem!_push_eq]
          · rw [← haux'2]
            exact dijkstraStackDfsInfo_live_eq_push aux d (edgeMarks step.state d) hwfOld ⟨hlen, hpos, hlive⟩ hst
      -- The extra excluded state (`newStep.state = d`) never sat in any old range (`d` was `.unknown`),
      -- so old-range obligations transport unchanged via `hdispatched`/`hrangeclosed`, and the new range's own
      -- obligation is vacuous, `d` sits on the stack so its exclusion hypothesis never holds.
      have hexcl_iff : ∀ t, (∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          st.state ≠ t) → (∀ st ∈ step :: rest, st.state ≠ t) := by
        intro t hexcl st hst
        rcases List.mem_cons.mp hst with heq | hst
        · rw [heq]; exact hexcl { step with idx := step.idx + 1 } (by simp)
        · exact hexcl _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hst))
      have hdispatched'' : ∀ i, i < aux'.roots.size → ∀ t ∈ aux'.range i,
          (∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest, st.state ≠ t) →
          ∀ x ∈ succs t, dijkstraGetStatus aux' x ≠ .unknown := by
        intro i hi t ht hexcl x hx
        rw [hsize'] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
        · rw [hrangeEq i hilt] at ht
          have hxne := hdispatched i hilt t ht (hexcl_iff t hexcl) x hx
          rw [hpeq]
          by_cases hxd : x == d
          · simp [hxd]
          · simpa [hxd] using hxne
        · exfalso
          apply hexcl newStep (by simp)
          rw [hieq] at ht
          exact ((hnewRangeIff t).mp ht).symm
      have hrangeclosed'' : ∀ i, i < aux'.roots.size → ∀ t ∈ aux'.range i,
          (∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest, st.state ≠ t) →
          ∀ x ∈ succs t, dijkstraGetStatus aux' x ≠ .unknown →
            x ∈ aux'.range i ∨ dijkstraGetStatus aux' x = .dead := by
        intro i hi t ht hexcl x hx _
        rw [hsize'] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
        · rw [hrangeEq i hilt] at ht
          by_cases hxd : x = d
          · exact absurd (hdispatched i hilt t ht (hexcl_iff t hexcl) x (hxd ▸ hx)) (by rw [hxd, hgs]; simp)
          · have hxne : dijkstraGetStatus aux x ≠ .unknown := hdispatched i hilt t ht (hexcl_iff t hexcl) x hx
            rcases hrangeclosed i hilt t ht (hexcl_iff t hexcl) x hx hxne with hc | hc
            · left; rw [hrangeEq i hilt]; exact hc
            · right; rw [hpeq]; simp only [beq_iff_eq, hxd, if_false]; exact hc
        · exfalso
          apply hexcl newStep (by simp)
          rw [hieq] at ht
          exact ((hnewRangeIff t).mp ht).symm
      have hdead' : ∀ s ∈ aux'.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc := by
        rw [hdeq]; exact hdead
      have hrootsPush : aux'.roots = aux.roots.push (aux.dfsInfo.size, 0) := by rw [← haux'2]; rfl
      have hmarksClosed'' : ∀ i, i < aux'.roots.size → ∀ t ∈ aux'.range i,
          (∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest, st.state ≠ t) →
          ∀ x ∈ succs t, x ∈ aux'.range i → ∀ m ∈ edgeMarks t x, (aux'.roots[i]!).2.testBit m = true := by
        intro i hi t ht hexcl x hx hxr m hm
        rw [hsize'] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
        · rw [hrangeEq i hilt] at ht hxr
          rw [hrootsPush, Array.getElem!_push_lt hilt]
          exact hmarksClosed i hilt t ht (hexcl_iff t hexcl) x hx hxr m hm
        · exfalso
          apply hexcl newStep (by simp)
          rw [hieq] at ht
          exact ((hnewRangeIff t).mp ht).symm
      have hMarksOpen'' : ∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          ∀ x ∈ (st.succ.toList.take st.idx), ∀ i, i < aux'.roots.size →
            x ∈ aux'.range i → st.state ∈ aux'.range i → ∀ m ∈ edgeMarks st.state x,
              (aux'.roots[i]!).2.testBit m = true := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · simp [hnewStep_def]
        · rcases List.mem_cons.mp hst with rfl | hst
          · show ∀ x ∈ step.succ.toList.take (step.idx + 1), ∀ i, i < aux'.roots.size →
              x ∈ aux'.range i → step.state ∈ aux'.range i → ∀ m ∈ edgeMarks step.state x,
                (aux'.roots[i]!).2.testBit m = true
            rw [hdTake]
            intro x hx i hi hxr hsr m hm
            rcases List.mem_append.mp hx with hx | hx
            · have hxd : x ≠ d := by
                intro heq; apply hstepPrefix x hx; rw [heq]; exact hgs
              rw [hsize'] at hi
              rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
              · rw [hrangeEq i hilt] at hxr hsr
                rw [hrootsPush, Array.getElem!_push_lt hilt]
                exact hstepMarksOpen x hx i hilt hxr hsr m hm
              · exfalso
                subst hieq
                exact hxd ((hnewRangeIff x).mp hxr)
            · simp only [List.mem_singleton] at hx
              subst hx
              rw [hsize'] at hi
              rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
              · exfalso
                rw [hrangeEq i hilt] at hxr
                exact absurd hxr (dijkstraGetStatus_unknown_not_mem_range hwf hgs i)
              · exfalso
                subst hieq
                have heq2 := DijkstraAux.range_mem_unique hwf'' hwf'
                  (show aux.roots.size - 1 < aux'.roots.size from by omega)
                  (show aux.roots.size < aux'.roots.size from by omega) hstepTop hsr
                omega
          · intro x hx i hi hxr hsr m hm
            rw [hsize'] at hi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
            · rw [hrangeEq i hilt] at hxr hsr
              rw [hrootsPush, Array.getElem!_push_lt hilt]
              exact hrestMarksOpen st hst x hx i hilt hxr hsr m hm
            · exfalso
              subst hieq
              have hxeq : x = d := (hnewRangeIff x).mp hxr
              exact hrestPrefix st hst x hx (by rw [hxeq]; exact hgs)
      have hnewStepPos : Nat.lt step.pos newStep.pos := by
        rw [hnewStep_def]
        show Nat.lt step.pos pos'
        rw [hpos'_eq]
        exact dijkstraStackDfsInfo_pos_lt hrangeinv.rootsWF hstackdfs (show step ∈ step :: rest from by simp)
      have hmerged'' : ∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux' x = .live →
          (∃ i, i < aux'.roots.size ∧ st.state ∈ aux'.range i ∧ x ∈ aux'.range i) ∨
          (∃ st' ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
            st'.state = x ∧ Nat.lt st.pos st'.pos) := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · simp [hnewStep_def]
        · rcases List.mem_cons.mp hst with rfl | hst
          · show ∀ x ∈ step.succ.toList.take (step.idx + 1), dijkstraGetStatus aux' x = .live →
              (∃ i, i < aux'.roots.size ∧ step.state ∈ aux'.range i ∧ x ∈ aux'.range i) ∨
              (∃ st' ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
                st'.state = x ∧ Nat.lt step.pos st'.pos)
            rw [hdTake]
            intro x hx hlive
            rcases List.mem_append.mp hx with hx | hx
            · have hxd3 : x ≠ d := by
                intro heq; exact absurd (hstepPrefix x hx) (by rw [heq, hgs]; simp)
              rw [hpeq] at hlive
              have hxd2 : (x == d) = false := beq_eq_false_iff_ne.mpr hxd3
              rw [hxd2] at hlive
              obtain ⟨i, hi, hsr, hxr⟩ := hstepMerged x hx hlive
              exact Or.inl ⟨i, by omega, hrangeEq i hi ▸ hsr, hrangeEq i hi ▸ hxr⟩
            · simp only [List.mem_singleton] at hx
              subst hx
              exact Or.inr ⟨newStep, by simp, by rw [hnewStep_def], hnewStepPos⟩
          · intro x hx hlive
            have hxne : x ≠ d := by
              intro heq
              exact absurd (hrestPrefix st hst x hx) (by rw [heq, hgs]; simp)
            rw [hpeq] at hlive
            have hxd2 : (x == d) = false := beq_eq_false_iff_ne.mpr hxne
            rw [hxd2] at hlive
            rcases hrestMerged st hst x hx hlive with hgood | ⟨st', hst', heq, hlt⟩
            · obtain ⟨i, hi, hsr, hxr⟩ := hgood
              exact Or.inl ⟨i, by omega, hrangeEq i hi ▸ hsr, hrangeEq i hi ▸ hxr⟩
            · right
              rcases List.mem_cons.mp hst' with heq' | hst'
              · exact ⟨{ step with idx := step.idx + 1 }, by simp, heq' ▸ heq, heq' ▸ hlt⟩
              · exact ⟨st', List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hst'), heq, hlt⟩
      have hdfsInfoBound' : ∀ i : Nat, (aux'.dfsInfo[i]!).2 < 2 ^ numMarks := by
        intro i
        rw [← haux'2]
        unfold dijkstraPush
        simp only
        by_cases hi : i < aux.dfsInfo.size
        · rw [Array.getElem!_push_lt hi]; exact hdfsInfoBound i
        · by_cases hieq : i = aux.dfsInfo.size
          · subst hieq; rw [Array.getElem!_push_eq]; exact marksToBitmask_lt (hmarksBound step.state d)
          · rw [getElem!_neg _ i (by simp only [Array.size_push]; omega)]
            exact getElem!_pair_default_snd_lt numMarks
      have hrootsBound' : ∀ i : Nat, (aux'.roots[i]!).2 < 2 ^ numMarks := by
        intro i
        rw [← haux'2]
        unfold dijkstraPush
        simp only
        by_cases hi : i < aux.roots.size
        · rw [Array.getElem!_push_lt hi]; exact hrootsBound i
        · by_cases hieq : i = aux.roots.size
          · subst hieq; rw [Array.getElem!_push_eq]; exact Nat.two_pow_pos numMarks
          · rw [getElem!_neg _ i (by simp only [Array.size_push]; omega)]
            exact getElem!_pair_default_snd_lt numMarks
      have hrootsNotFull' : ∀ i, i < aux'.roots.size → (aux'.roots[i]!).2 ≠ (1 <<< numMarks) - 1 ∨
          DijkstraNoInternalEdge succs aux' (newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest) i := by
        have hdStack : ∀ st ∈ (step :: rest), st.state ≠ d := fun st hst hc =>
          absurd (hc ▸ hStackLive st hst) (by rw [hgs]; simp)
        have hdnot : ∀ j, d ∉ aux.range j := fun j =>
          dijkstraGetStatus_unknown_not_mem_range hwf hgs j
        intro i hi
        by_cases hilt : i < aux.roots.size
        · refine (hrootsNotFull i hilt).imp (fun hne => ?_) (fun hno => ?_)
          · rw [← haux'2]; unfold dijkstraPush; simp only
            rw [Array.getElem!_push_lt hilt]; exact hne
          -- old ranges are untouched, and the fresh frame's own state is in none of them
          · refine DijkstraNoInternalEdge.congr_range (hrangeEq i hilt) ?_
            obtain ⟨h1, h2⟩ := DijkstraNoInternalEdge.bump hdTake (hdnot i) hno
            refine ⟨fun t ht hexcl x hx => h1 t ht
              (fun st hst => hexcl st (List.mem_cons_of_mem _ hst)) x hx, fun st hst hsr x hx => ?_⟩
            rcases List.mem_cons.mp hst with heq | hst
            · rw [heq] at hsr; exact absurd hsr (hdnot i)
            · exact h2 st hst hsr x hx
        -- the fresh singleton range `{d}`: its only member is the frame that just opened it, so nothing
        -- has been dispatched out of it and the "no internal edge" disjunct holds outright
        · have hieq : i = aux.roots.size := by rw [hsize'] at hi; omega
          subst hieq
          refine Or.inr ⟨fun t ht hexcl x hx => ?_, fun st hst hsr x hx => ?_⟩
          · exact absurd ((hnewRangeIff t).mp ht).symm (hexcl newStep (by simp))
          · rcases List.mem_cons.mp hst with heq | hst
            · rw [heq] at hx; simp [hnewStep_def] at hx
            · refine absurd ((hnewRangeIff st.state).mp hsr) ?_
              rcases List.mem_cons.mp hst with heq' | hst'
              · rw [heq']; exact hdStack step (by simp)
              · exact hdStack st (List.mem_cons_of_mem _ hst')
      have hNoBack'' : NoBackDispatch (newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest) :=
        ⟨fun st hst hcontra => absurd (hrestPrefix st hst d hcontra) (by rw [hgs]; simp),
          NoBackDispatch.state_congr ({ step with idx := step.idx + 1 }) hNoBack rfl⟩
      have hdfsPush : aux'.dfsInfo =
          aux.dfsInfo.push (aux.live.size, marksToBitmask (edgeMarks step.state d)) := by
        rw [← haux'2]; rfl
      have hTreeMarks'' : ∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          ∀ st' ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          st'.state ∈ (st.succ.toList.take st.idx) → Nat.lt st.pos st'.pos →
          ∀ j, j < aux'.roots.size → st'.state ∈ aux'.range j → ∀ m ∈ edgeMarks st.state st'.state,
            (aux'.roots[j]!).2.testBit m = true ∨ (aux'.dfsInfo[(aux'.roots[j]!).1]!).2.testBit m = true := by
        intro st hst st' hst' hdisp hlt j hj hjr m hm
        rw [hsize'] at hj
        rcases List.mem_cons.mp hst with rfl | hst
        · simp [hnewStep_def] at hdisp
        · rcases List.mem_cons.mp hst' with rfl | hst'
          · -- `push` is what records this tree edge's own marks, in the new frame's `dfsInfo` entry
            rcases List.mem_cons.mp hst with rfl | hstr
            · have hjrd : d ∈ aux'.range j := by rw [hnewStep_def] at hjr; exact hjr
              have hjeq : j = aux.roots.size := by
                rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | hjeq
                · exact absurd (dijkstraGetStatus_live_of_mem_range hwf ((hrangeEq j hjlt) ▸ hjrd))
                    (by rw [hgs]; simp)
                · exact hjeq
              subst hjeq
              right
              rw [hrootsPush, Array.getElem!_push_eq, hdfsPush, Array.getElem!_push_eq]
              exact marksToBitmask_testBit hm
            · exact absurd (hrestPrefix st hstr d (by rw [hnewStep_def] at hdisp; exact hdisp))
                (by rw [hgs]; simp)
          · have hjlt : j < aux.roots.size := by
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | hjeq
              · exact hjlt
              · exfalso
                subst hjeq
                have hxd : st'.state = d := (hnewRangeIff st'.state).mp hjr
                have hlive' : dijkstraGetStatus aux st'.state = .live := by
                  rcases List.mem_cons.mp hst' with rfl | hst'2
                  · exact hStackLive step (by simp)
                  · exact hStackLive st' (List.mem_cons_of_mem _ hst'2)
                exact absurd hlive' (by rw [hxd, hgs]; simp)
            rw [hrangeEq j hjlt] at hjr
            rw [hrootsPush, Array.getElem!_push_lt hjlt, hdfsPush,
              Array.getElem!_push_lt (hrangeinv.rootsWF.rootsBounds j hjlt)]
            exact hTreeMarksBump st hst st' hst' hdisp hlt j hjlt hjr m hm
      exact ih aux' _ r hr hwf' hSuccEq'' hPrefix'' hReach'' hrangeinv' hstackdfs'' hrangeclosed'' hdispatched''
        hmarksClosed'' hMarksOpen'' hmerged'' hTreeMarks'' hNoBack'' hrootsBound' hdfsInfoBound' hrootsNotFull'
        hdead'
  case neg =>
    simp only [h, dite_false] at hr
    simp only [dijkstraOps] at hr
    rcases hpopeq : dijkstraPop aux step.pos with ⟨aux', found⟩
    simp only [hpopeq] at hr
    have hff : found = false := by
      have hpf := dijkstraPop_found_false aux step.pos
      rw [hpopeq] at hpf
      exact hpf
    subst hff
    simp only at hr
    have haux'eq : (dijkstraPop aux step.pos).1 = aux' := congrArg Prod.fst hpopeq
    have hwf' : DijkstraWellFormed aux' := haux'eq ▸ dijkstraWellFormed_pop aux step.pos hwf
    have hSuccEq' : ∀ st ∈ rest, st.succ = succs st.state := hrestSuccEq
    have hReach' : ∀ st ∈ rest, Reachable initialStates succs st.state := hrestReach
    obtain ⟨hlen, hposCorr, hliveCorr⟩ := hstackdfs
    have hstackdfsPacked : DijkstraStackDfsInfo aux (step :: rest) := ⟨hlen, hposCorr, hliveCorr⟩
    have hdfsInfoPos : 0 < aux.dfsInfo.size := lt_of_lt_of_le hne0 hrangeinv.rootsWF.dfsInfoOk
    have h0pos : step.pos = (aux.dfsInfo[aux.dfsInfo.size - 1]!).1 := by
      have := hposCorr 0 (by simp)
      simpa [hlen] using this
    have hstepAllTaken : step.succ.toList.take step.idx = step.succ.toList :=
      List.take_of_length_le (by simp only [Array.length_toList]; omega)
    have hstepDispatched : ∀ x ∈ succs step.state, dijkstraGetStatus aux x ≠ .unknown := by
      intro x hx
      apply hstepPrefix x
      rw [hstepAllTaken, hstepSuccEq]
      simpa using hx
    have hstepClosed : ∀ x ∈ succs step.state,
        x ∈ aux.range (aux.roots.size - 1) ∨ dijkstraGetStatus aux x = .dead := by
      intro x hx
      cases hxs : dijkstraGetStatus aux x with
      | dead => exact Or.inr rfl
      | live =>
        left
        have hxtake : x ∈ step.succ.toList.take step.idx := by
          rw [hstepAllTaken, hstepSuccEq]; simpa using hx
        obtain ⟨i, hi, hsr, hxr⟩ := hstepMerged x hxtake hxs
        have heq := DijkstraAux.range_mem_unique hrangeinv.rootsWF hwf hi (by omega) hsr hstepMem
        rwa [heq] at hxr
      | unknown => exact absurd hxs (hstepDispatched x hx)
    have hstepMarksClosed : ∀ x ∈ succs step.state, x ∈ aux.range (aux.roots.size - 1) →
        ∀ m ∈ edgeMarks step.state x, (aux.roots[aux.roots.size - 1]!).2.testBit m = true := by
      intro x hx hxr m hm
      have hxtake : x ∈ step.succ.toList.take step.idx := by
        rw [hstepAllTaken, hstepSuccEq]; simpa using hx
      exact hstepMarksOpen x hxtake (aux.roots.size - 1) (by omega) hxr hstepMem m hm
    obtain ⟨r0, a0, hback⟩ : ∃ r0 a0, aux.roots.back? = some (r0, a0) := by
      rcases hbk : aux.roots.back? with _ | p
      · exact absurd (Array.back?_eq_none_iff.mp hbk) (by intro he; rw [he] at hne0; simp at hne0)
      · exact ⟨p.1, p.2, by simp⟩
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hback
    have hridx : aux.roots.size - 1 = ys.size := by rw [hys]; simp
    have hrtop : aux.roots[aux.roots.size - 1]! = (r0, a0) := by rw [hridx, hys, Array.getElem!_push_eq]
    have hposCond : ∀ r snd, aux.roots.back? = some (r, snd) → aux.dfsInfo.pop.size = r →
        step.pos = (aux.dfsInfo[r]!).1 := by
      intro r snd hbk hfl
      rw [hback] at hbk
      simp only [Option.some.injEq, Prod.mk.injEq] at hbk
      obtain ⟨hreq, _⟩ := hbk
      subst hreq
      rw [← hfl, Array.size_pop]
      exact h0pos
    have hwfRoots' : DijkstraRootsWF aux' :=
      haux'eq ▸ dijkstraRootsWF_pop aux step.pos hrangeinv.rootsWF hposCond
    have hstatusEither : ∀ q, dijkstraGetStatus aux' q = dijkstraGetStatus aux q ∨
        (dijkstraGetStatus aux q = .live ∧ dijkstraGetStatus aux' q = .dead) :=
      fun q => haux'eq ▸ dijkstraPop_status aux step.pos hwf q
    have hxneTrans : ∀ x, dijkstraGetStatus aux x ≠ .unknown → dijkstraGetStatus aux' x ≠ .unknown := by
      intro x hx
      rcases hstatusEither x with heqs | ⟨h1, h2⟩
      · rw [heqs]; exact hx
      · rw [h2]; simp
    have hPrefix' : ∀ st ∈ rest, ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux' x ≠ .unknown :=
      fun st hst x hx => hxneTrans x (hrestPrefix st hst x hx)
    have hxneBack : ∀ x, dijkstraGetStatus aux' x ≠ .unknown → dijkstraGetStatus aux x ≠ .unknown := by
      intro x hx
      rcases hstatusEither x with heqs | ⟨h1, _⟩
      · rw [← heqs]; exact hx
      · rw [h1]; simp
    have hdeadPersist : ∀ q, dijkstraGetStatus aux q = .dead → dijkstraGetStatus aux' q = .dead := by
      intro q hq
      rcases hstatusEither q with heqs | ⟨h1, h2⟩
      · rw [heqs]; exact hq
      · exact h2
    have hliveBack : ∀ x, dijkstraGetStatus aux' x = .live → dijkstraGetStatus aux x = .live := by
      intro x hx
      rcases hstatusEither x with heqs | ⟨h1, h2⟩
      · rw [← heqs]; exact hx
      · rw [h2] at hx; cases hx
    have haux'dfsInfo : aux'.dfsInfo = aux.dfsInfo.pop := by
      rw [← haux'eq]
      unfold dijkstraPop
      rw [hback]
      dsimp only
      split_ifs with hfl <;> rfl
    have hdfsInfoBound' : ∀ i : Nat, (aux'.dfsInfo[i]!).2 < 2 ^ numMarks := by
      rw [haux'dfsInfo]; exact array_pop_bitmask_bound hdfsInfoBound
    by_cases hflush : aux.dfsInfo.pop.size = r0
    · -- flush: the top range `D := aux.range (aux.roots.size - 1)` is confirmed and flushed to `dead`.
      have haux'defF : aux' = { aux with
          dfsInfo := aux.dfsInfo.pop
          roots := aux.roots.pop
          live := (dijkstraFlushLive aux.live aux.liveIndex aux.dead step.pos).1
          liveIndex := (dijkstraFlushLive aux.live aux.liveIndex aux.dead step.pos).2.1
          dead := (dijkstraFlushLive aux.live aux.liveIndex aux.dead step.pos).2.2 } := by
        rw [← haux'eq]
        unfold dijkstraPop
        rw [hback]
        dsimp only
        rw [if_pos hflush]
      have haux'rootsF : aux'.roots = aux.roots.pop := by rw [haux'defF]
      have haux'deadF : aux'.dead = (dijkstraFlushLive aux.live aux.liveIndex aux.dead step.pos).2.2 := by
        rw [haux'defF]
      have hr0eq : r0 = aux.dfsInfo.size - 1 := by
        have hps : aux.dfsInfo.pop.size = aux.dfsInfo.size - 1 := Array.size_pop
        omega
      have htopStart : aux.rangeStart (aux.roots.size - 1) = step.pos := by
        unfold DijkstraAux.rangeStart
        rw [show (aux.roots[aux.roots.size - 1]!).1 = r0 from by rw [hrtop], hr0eq, ← h0pos]
      have htopEnd : aux.rangeEnd (aux.roots.size - 1) = aux.live.size := by
        unfold DijkstraAux.rangeEnd
        simp only [show ¬ aux.roots.size - 1 + 1 < aux.roots.size from by omega, if_false]
      have hposle : Nat.le step.pos aux.live.size := by
        rw [h0pos]
        exact (hrangeinv.rootsWF.dfsInfoLt (aux.dfsInfo.size - 1) (by omega)).le
      have hposeqF : step.pos = (aux.dfsInfo[r0]!).1 := by rw [h0pos, hr0eq]
      -- `t ∈ D`, `t ≠ step.state`, is already off the current stack.
      have hDposNe : ∀ t ∈ aux.range (aux.roots.size - 1), t ≠ step.state → ∀ st ∈ step :: rest, st.state ≠ t := by
        intro t ht htne st hst hcontra
        rcases List.mem_cons.mp hst with rfl | hst
        · exact htne hcontra.symm
        · rw [DijkstraAux.mem_range_iff, htopStart] at ht
          obtain ⟨p, hp1, hp2, hp3⟩ := ht
          have hpb : p < aux.live.size := lt_of_lt_of_le hp2 (min_le_right _ _)
          have hstb : Nat.lt st.pos aux.live.size :=
            dijkstraStackDfsInfo_pos_lt hrangeinv.rootsWF hstackdfsPacked (List.mem_cons_of_mem _ hst)
          have hstlive := hliveCorr st (List.mem_cons_of_mem _ hst)
          rw [hcontra] at hstlive
          have hpeq : p = st.pos := hwf.pos_inj hpb hstb (hp3.trans hstlive.symm)
          have hstlt := hrestPosLt st hst
          have hle : Nat.le step.pos st.pos := hpeq ▸ hp1
          exact absurd hstlt (Nat.not_lt.mpr hle)
      have hDdispatched : ∀ t ∈ aux.range (aux.roots.size - 1), ∀ x ∈ succs t, dijkstraGetStatus aux x ≠ .unknown := by
        intro t ht x hx
        by_cases hts : t = step.state
        · rw [hts] at hx; exact hstepDispatched x hx
        · exact hdispatched (aux.roots.size - 1) (by omega) t ht (hDposNe t ht hts) x hx
      have hDrangeclosed : ∀ t ∈ aux.range (aux.roots.size - 1), ∀ x ∈ succs t,
          x ∈ aux.range (aux.roots.size - 1) ∨ dijkstraGetStatus aux x = .dead := by
        intro t ht x hx
        by_cases hts : t = step.state
        · subst hts; exact hstepClosed x hx
        · exact hrangeclosed (aux.roots.size - 1) (by omega) t ht (hDposNe t ht hts) x hx (hDdispatched t ht x hx)
      have hDmarksClosed : ∀ t ∈ aux.range (aux.roots.size - 1), ∀ x ∈ succs t, x ∈ aux.range (aux.roots.size - 1) →
          ∀ m ∈ edgeMarks t x, (aux.roots[aux.roots.size - 1]!).2.testBit m = true := by
        intro t ht x hx hxr m hm
        by_cases hts : t = step.state
        · subst hts; exact hstepMarksClosed x hx hxr m hm
        · exact hmarksClosed (aux.roots.size - 1) (by omega) t ht (hDposNe t ht hts) x hx hxr m hm
      have hdead' : ∀ s ∈ aux'.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc := by
        intro s hsdead' A hsA
        rw [haux'deadF] at hsdead'
        rcases dijkstraFlushLive_dead_or_old step.pos aux.live aux.liveIndex aux.dead s hsdead'
          with hc | ⟨p, hp1, hp2, hp3⟩
        · exact hdead s hc A hsA
        · have hsD : s ∈ aux.range (aux.roots.size - 1) := by
            rw [DijkstraAux.mem_range_iff, htopStart, htopEnd]
            exact ⟨p, hp1, Nat.lt_min.mpr ⟨hp2, hp2⟩, hp3⟩
          have hDsub : ∀ u ∈ A.scc, u ∈ aux.range (aux.roots.size - 1) := by
            intro u hu
            rcases A.connected s hsA u hu with heq | hp'
            · rw [← heq]; exact hsD
            · exact hp'.closed hsD (fun x hxD y hy => by
                obtain ⟨hySucc, hyA⟩ := Array.mem_filter.mp hy
                rcases hDrangeclosed x hxD y hySucc with hc2 | hc2
                · exact hc2
                · exfalso
                  have hyDead : y ∈ aux.dead := by
                    unfold dijkstraGetStatus dijkstraStatusOf at hc2
                    by_cases h1 : aux.liveIndex.contains y
                    · simp [h1] at hc2
                    · by_cases h2 : aux.dead.contains y
                      · exact Std.HashSet.mem_iff_contains.mpr h2
                      · simp [h1, h2] at hc2
                  exact absurd (Std.HashSet.mem_iff_contains.mpr hyA) (hdead y hyDead A))
          obtain ⟨_, hcov⟩ := A.covers
          have hDbitmaskCover : ∀ m, m < numMarks → (aux.roots[aux.roots.size - 1]!).2.testBit m = true := by
            intro m hmlt
            obtain ⟨s1, hs1, t1, ht1, hedge1, hmark1⟩ := hcov m hmlt
            exact hDmarksClosed s1 (hDsub s1 hs1) t1 hedge1 (hDsub t1 ht1) m hmark1
          have hDbound : (aux.roots[aux.roots.size - 1]!).2 < 2 ^ numMarks := hrootsBound (aux.roots.size - 1)
          have hDeq : (aux.roots[aux.roots.size - 1]!).2 = (1 <<< numMarks) - 1 :=
            eq_allOnesMask_of_testBit_cover hDbound hDbitmaskCover
          -- Either the bitmask route contradicts, or (when `numMarks = 0` makes it uninformative) the
          -- range is known to hold no discovered internal edge, which `A.covers`' own edge violates.
          rcases hrootsNotFull (aux.roots.size - 1) (by omega) with hne | ⟨hretired, hopen⟩
          · exact absurd hDeq hne
          · obtain ⟨⟨s0, hs0, t0, ht0, hedge0⟩, -⟩ := A.covers
            by_cases hs0step : s0 = step.state
            · rw [hs0step] at hedge0
              refine hopen step (by simp) (hs0step ▸ hDsub s0 hs0) t0 ?_ (hDsub t0 ht0)
              have hmem : t0 ∈ step.succ.toList := by rw [hstepSuccEq]; exact Array.mem_def.mp hedge0
              rwa [List.take_of_length_le (by simp only [Array.length_toList]; omega)]
            · exact hretired s0 (hDsub s0 hs0) (hDposNe s0 (hDsub s0 hs0) hs0step) t0 hedge0
                (hDsub t0 ht0)
      have hrangeEqF : ∀ i, i < aux.roots.size - 1 → ∀ x, x ∈ aux'.range i ↔ x ∈ aux.range i := by
        intro i hi x
        rw [← haux'eq]
        exact dijkstraPop_range_mem_iff_of_flush hrangeinv.rootsWF hback hflush hposle hposeqF i hi x
      have haux'sizeF : aux'.roots.size = aux.roots.size - 1 := by rw [haux'rootsF, Array.size_pop]
      have hconnected' : ∀ i, i < aux'.roots.size → InternallyConnected succs (aux'.range i) := by
        intro i hi
        rw [haux'sizeF] at hi
        intro s hs t ht
        rw [hrangeEqF i hi] at hs ht
        rcases hrangeinv.connected i (by omega) s hs t ht with heq | hp
        · exact Or.inl heq
        · exact Or.inr (hp.mono_succs
            (fun a b hab => sccSuccs_mono (fun x hx => (hrangeEqF i hi x).mpr hx) hab))
      have hchained' : ∀ i, (h' : i + 1 < aux'.roots.size) →
          ∃ s ∈ aux'.range i, ∃ t ∈ aux'.range (i + 1), t ∈ succs s := by
        intro i hi
        rw [haux'sizeF] at hi
        obtain ⟨s, hs, t, ht, hst⟩ := hrangeinv.chained i (by omega)
        exact ⟨s, (hrangeEqF i (by omega) s).mpr hs, t, (hrangeEqF (i + 1) (by omega) t).mpr ht, hst⟩
      have hbitSound' : ∀ i, i < aux'.roots.size → ∀ m, (aux'.roots[i]!).2.testBit m = true →
          ∃ s ∈ aux'.range i, ∃ t ∈ aux'.range i, t ∈ succs s ∧ m ∈ edgeMarks s t := by
        intro i hi m hm
        rw [haux'sizeF] at hi
        have hipop : i < aux.roots.pop.size := by
          have hps : aux.roots.pop.size = aux.roots.size - 1 := Array.size_pop
          omega
        rw [haux'rootsF, Array.getElem!_pop_lt hipop] at hm
        obtain ⟨s, hs, t, ht, hst, hmk⟩ := hrangeinv.bitSound i (by omega) m hm
        exact ⟨s, (hrangeEqF i hi s).mpr hs, t, (hrangeEqF i hi t).mpr ht, hst, hmk⟩
      -- `live` shrinks to `step.pos`, but every surviving `dfsInfo` entry names a position strictly below it.
      have hentrySound' : ∀ k, k < aux'.dfsInfo.size → ∀ m, (aux'.dfsInfo[k]!).2.testBit m = true →
          0 < k ∧ aux'.live[(aux'.dfsInfo[k]!).1]! ∈ succs (aux'.live[(aux'.dfsInfo[k - 1]!).1]!) ∧
            m ∈ edgeMarks (aux'.live[(aux'.dfsInfo[k - 1]!).1]!) (aux'.live[(aux'.dfsInfo[k]!).1]!) := by
        intro k hk m hm
        rw [haux'dfsInfo] at hk
        have hkr : k < r0 := by omega
        have hkk : k < aux.dfsInfo.pop.size := by omega
        have hk1 : k - 1 < aux.dfsInfo.pop.size := by omega
        have hposbelow : ∀ j, j < r0 → (aux.dfsInfo[j]!).1 < step.pos := by
          intro j hj
          rw [hposeqF]
          exact hrangeinv.rootsWF.dfsInfoMono j r0 hj (by omega)
        have hliveEq : ∀ j, j < r0 → aux'.live[(aux.dfsInfo[j]!).1]! = aux.live[(aux.dfsInfo[j]!).1]! := by
          intro j hj
          rw [haux'defF]
          exact dijkstraFlushLive_getElem!_lt step.pos aux.live aux.liveIndex aux.dead _ (hposbelow j hj)
        rw [haux'dfsInfo, Array.getElem!_pop_lt hkk] at hm ⊢
        rw [Array.getElem!_pop_lt hk1, hliveEq k hkr, hliveEq (k - 1) (by omega)]
        exact hrangeinv.entrySound k (by omega) m hm
      have hrangeinv' : DijkstraRangeInv succs edgeMarks aux' :=
        ⟨hwfRoots', hconnected', hchained', hbitSound', hentrySound'⟩
      have hstackdfs' : DijkstraStackDfsInfo aux' rest := by
        refine ⟨?_, ?_, ?_⟩
        · rw [haux'dfsInfo, Array.size_pop]
          simp only [List.length_cons] at hlen
          omega
        · intro i hi
          have hi' : i + 1 < (step :: rest).length := by simp only [List.length_cons]; omega
          have hcorr := hposCorr (i + 1) hi'
          simp only [List.getElem_cons_succ] at hcorr
          rw [hcorr, haux'dfsInfo]
          have hbound : rest.length - 1 - i < aux.dfsInfo.pop.size := by
            simp only [Array.size_pop]
            simp only [List.length_cons] at hlen
            omega
          rw [Array.getElem!_pop_lt hbound]
          congr 2
          simp only [List.length_cons] at hlen ⊢
          omega
        · intro st hst
          have hstpos := hliveCorr st (List.mem_cons_of_mem _ hst)
          rw [haux'defF]
          dsimp only
          have hstlt : st.pos < step.pos := hrestPosLt st hst
          exact (dijkstraFlushLive_getElem!_lt step.pos aux.live aux.liveIndex aux.dead st.pos hstlt).trans hstpos
      have hexclF : ∀ i, i < aux.roots.size - 1 → ∀ t ∈ aux.range i, t ≠ step.state := by
        intro i hi t ht heq
        rw [heq] at ht
        have := DijkstraAux.range_mem_unique hrangeinv.rootsWF hwf (by omega) (by omega) ht hstepMem
        omega
      have hexclLiftF : ∀ i, i < aux.roots.size - 1 → ∀ t ∈ aux.range i, (∀ st ∈ rest, st.state ≠ t) →
          (∀ st ∈ step :: rest, st.state ≠ t) := by
        intro i hi t ht hexcl st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · exact (hexclF i hi t ht).symm
        · exact hexcl st hst
      have hrangeclosed' : ∀ i, i < aux'.roots.size → ∀ t ∈ aux'.range i, (∀ st ∈ rest, st.state ≠ t) →
          ∀ x ∈ succs t, dijkstraGetStatus aux' x ≠ .unknown → x ∈ aux'.range i ∨ dijkstraGetStatus aux' x = .dead := by
        intro i hi t ht hexcl x hx hxne
        rw [haux'sizeF] at hi
        rw [hrangeEqF i hi t] at ht
        rcases hrangeclosed i (by omega) t ht (hexclLiftF i hi t ht hexcl) x hx (hxneBack x hxne) with hc | hc
        · exact Or.inl ((hrangeEqF i hi x).mpr hc)
        · exact Or.inr (hdeadPersist x hc)
      have hdispatched' : ∀ i, i < aux'.roots.size → ∀ t ∈ aux'.range i, (∀ st ∈ rest, st.state ≠ t) →
          ∀ x ∈ succs t, dijkstraGetStatus aux' x ≠ .unknown := by
        intro i hi t ht hexcl x hx
        rw [haux'sizeF] at hi
        rw [hrangeEqF i hi t] at ht
        exact hxneTrans x (hdispatched i (by omega) t ht (hexclLiftF i hi t ht hexcl) x hx)
      have hmarksClosed' : ∀ i, i < aux'.roots.size → ∀ t ∈ aux'.range i, (∀ st ∈ rest, st.state ≠ t) →
          ∀ x ∈ succs t, x ∈ aux'.range i → ∀ m ∈ edgeMarks t x, (aux'.roots[i]!).2.testBit m = true := by
        intro i hi t ht hexcl x hx hxr m hm
        rw [haux'sizeF] at hi
        rw [hrangeEqF i hi t] at ht
        rw [hrangeEqF i hi x] at hxr
        have hipoplt : i < aux.roots.pop.size := by
          have hps : aux.roots.pop.size = aux.roots.size - 1 := Array.size_pop
          omega
        rw [haux'rootsF, Array.getElem!_pop_lt hipoplt]
        exact hmarksClosed i (by omega) t ht (hexclLiftF i hi t ht hexcl) x hx hxr m hm
      have hMarksOpen' : ∀ st ∈ rest, ∀ x ∈ (st.succ.toList.take st.idx), ∀ i, i < aux'.roots.size →
          x ∈ aux'.range i → st.state ∈ aux'.range i → ∀ m ∈ edgeMarks st.state x, (aux'.roots[i]!).2.testBit m = true := by
        intro st hst x hx i hi hxr hsr m hm
        rw [haux'sizeF] at hi
        rw [hrangeEqF i hi x] at hxr
        rw [hrangeEqF i hi st.state] at hsr
        have hipoplt : i < aux.roots.pop.size := by
          have hps : aux.roots.pop.size = aux.roots.size - 1 := Array.size_pop
          omega
        rw [haux'rootsF, Array.getElem!_pop_lt hipoplt]
        exact hrestMarksOpen st hst x hx i (by omega) hxr hsr m hm
      have hstepposlt : Nat.lt step.pos aux.live.size :=
        dijkstraStackDfsInfo_pos_lt hrangeinv.rootsWF hstackdfsPacked List.mem_cons_self
      have hstepLiveOld : dijkstraGetStatus aux step.state = .live :=
        dijkstraGetStatus_live_of_pos hwf hstepposlt (hliveCorr step (by simp))
      have hstepd : dijkstraGetStatus aux' step.state = .dead := by
        rcases hstatusEither step.state with heqs | ⟨_, h2⟩
        · exfalso
          rw [hstepLiveOld] at heqs
          have hcontains : aux'.liveIndex.contains step.state = true := by
            unfold dijkstraGetStatus dijkstraStatusOf at heqs
            by_cases hc : aux'.liveIndex.contains step.state
            · exact hc
            · rw [if_neg hc] at heqs; split at heqs <;> cases heqs
          rw [Std.HashMap.contains_eq_isSome_getElem?] at hcontains
          obtain ⟨p, hpv⟩ := Option.isSome_iff_exists.mp hcontains
          obtain ⟨hplt, hpstate⟩ := hwf'.bwd step.state p hpv
          have hlive'size : aux'.live.size = step.pos := by
            rw [haux'defF]
            exact dijkstraFlushLive_size step.pos aux.live aux.liveIndex aux.dead hposle
          have hplt' : p < step.pos := by omega
          have hpstateOld : aux.live[p]! = step.state := by
            rw [← hpstate, haux'defF]
            dsimp only
            exact (dijkstraFlushLive_getElem!_lt step.pos aux.live aux.liveIndex aux.dead p hplt').symm
          have hpb : p < aux.live.size := lt_of_lt_of_le hplt' hposle
          have hpeq : p = step.pos :=
            hwf.pos_inj hpb hstepposlt (hpstateOld.trans (hliveCorr step (by simp)).symm)
          omega
        · exact h2
      have hmerged' : ∀ st ∈ rest, ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux' x = .live →
          (∃ i, i < aux'.roots.size ∧ st.state ∈ aux'.range i ∧ x ∈ aux'.range i) ∨
          (∃ st' ∈ rest, st'.state = x ∧ Nat.lt st.pos st'.pos) := by
        intro st hst x hx hlive
        by_cases hxs : x = step.state
        · exfalso; rw [hxs, hstepd] at hlive; exact absurd hlive (by simp)
        · have hlive2 : dijkstraGetStatus aux x = .live := hliveBack x hlive
          rcases hrestMerged st hst x hx hlive2 with ⟨i, hi, hsr, hxr⟩ | ⟨st', hst', heq, hlt⟩
          · have hstNeStep : st.state ≠ step.state := by
              intro heq
              have hstlive := hliveCorr st (List.mem_cons_of_mem _ hst)
              have hsteplive := hliveCorr step (by simp)
              have hpeq := hwf.pos_inj
                (dijkstraStackDfsInfo_pos_lt hrangeinv.rootsWF hstackdfsPacked (List.mem_cons_of_mem _ hst))
                hstepposlt (hstlive.trans (heq.trans hsteplive.symm))
              have hlt := hrestPosLt st hst
              rw [hpeq] at hlt
              exact Nat.lt_irrefl _ hlt
            have hiNe : i ≠ aux.roots.size - 1 := by
              intro hieq
              rw [hieq] at hsr
              exact absurd rfl (hDposNe st.state hsr hstNeStep st (List.mem_cons_of_mem _ hst))
            have hi' : i < aux.roots.size - 1 := by omega
            exact Or.inl ⟨i, by rw [haux'sizeF]; exact hi', (hrangeEqF i hi' st.state).mpr hsr,
              (hrangeEqF i hi' x).mpr hxr⟩
          · right
            rcases List.mem_cons.mp hst' with heq' | hst'
            · exact absurd (heq' ▸ heq).symm hxs
            · exact ⟨st', hst', heq, hlt⟩
      have hrootsBound' : ∀ i : Nat, (aux'.roots[i]!).2 < 2 ^ numMarks := by
        intro i; rw [haux'rootsF]; exact array_pop_bitmask_bound hrootsBound i
      have hrootsNotFull' : ∀ i, i < aux'.roots.size → (aux'.roots[i]!).2 ≠ (1 <<< numMarks) - 1 ∨
          DijkstraNoInternalEdge succs aux' rest i := by
        intro i hi
        rw [haux'sizeF] at hi
        have hipoplt : i < aux.roots.pop.size := by
          have hps : aux.roots.pop.size = aux.roots.size - 1 := Array.size_pop
          omega
        refine (hrootsNotFull i (by omega)).imp (fun hne => ?_) (fun hno => ?_)
        · rw [haux'rootsF, Array.getElem!_pop_lt hipoplt]; exact hne
        -- surviving ranges keep their members, and `step.state` belonged to the flushed one
        · refine ⟨fun t ht hexcl x hx => ?_, fun st hst hsr x hx => ?_⟩
          · rw [hrangeEqF i hi] at ht ⊢
            exact hno.1 t ht (fun st hst => by
              rcases List.mem_cons.mp hst with heq | hst
              · rw [heq]
                intro hc
                exact absurd (hc ▸ ht) (fun hcc =>
                  absurd (DijkstraAux.range_mem_unique hrangeinv.rootsWF hwf (by omega) (by omega)
                    hcc hstepMem) (by omega))
              · exact hexcl st hst) x hx
          · rw [hrangeEqF i hi] at hsr ⊢
            exact hno.2 st (List.mem_cons_of_mem _ hst) hsr x hx

      -- The flushed range's own root is the last `dfsInfo` entry, so every surviving range's root, and its
      -- own `dfsInfo` entry, sits strictly below the popped one.
      have hTreeMarks' : ∀ st ∈ rest, ∀ st' ∈ rest,
          st'.state ∈ (st.succ.toList.take st.idx) → Nat.lt st.pos st'.pos →
          ∀ j, j < aux'.roots.size → st'.state ∈ aux'.range j → ∀ m ∈ edgeMarks st.state st'.state,
            (aux'.roots[j]!).2.testBit m = true ∨ (aux'.dfsInfo[(aux'.roots[j]!).1]!).2.testBit m = true := by
        intro st hst st' hst' hdisp hlt j hj hjr m hm
        rw [haux'sizeF] at hj
        rw [hrangeEqF j hj st'.state] at hjr
        have hjpoplt : j < aux.roots.pop.size := by
          have hps : aux.roots.pop.size = aux.roots.size - 1 := Array.size_pop
          omega
        have hrlt : (aux.roots[j]!).1 < aux.dfsInfo.pop.size := by
          rw [hflush]
          have hmono := hrangeinv.rootsWF.rootsMono j (aux.roots.size - 1) (by omega) (by omega)
          rwa [show (aux.roots[aux.roots.size - 1]!).1 = r0 from by rw [hrtop]] at hmono
        rw [haux'rootsF, Array.getElem!_pop_lt hjpoplt, haux'dfsInfo, Array.getElem!_pop_lt hrlt]
        exact hTreeMarks st (List.mem_cons_of_mem _ hst) st' (List.mem_cons_of_mem _ hst') hdisp hlt j
          (by omega) hjr m hm
      exact ih aux' rest r hr hwf' hSuccEq' hPrefix' hReach' hrangeinv' hstackdfs' hrangeclosed' hdispatched'
        hmarksClosed' hMarksOpen' hmerged' hTreeMarks' hNoBack.tail hrootsBound' hdfsInfoBound' hrootsNotFull'
        hdead'
    · -- non-flush: `roots`/`live`/`liveIndex`/`dead` are all untouched, only `dfsInfo` shrinks.
      have haux'defNF : aux' = { aux with dfsInfo := aux.dfsInfo.pop } := by
        rw [← haux'eq]
        unfold dijkstraPop
        rw [hback]
        dsimp only
        rw [if_neg hflush]
      have haux'rootsNF : aux'.roots = aux.roots := by rw [haux'defNF]
      have haux'liveNF : aux'.live = aux.live := by rw [haux'defNF]
      have haux'deadNF : aux'.dead = aux.dead := by rw [haux'defNF]
      have hrangeEqNF : ∀ i, i < aux.roots.size → aux'.range i = aux.range i :=
        fun i hi => haux'eq ▸ dijkstraPop_range_eq_of_not_flush hrangeinv.rootsWF hback hflush i hi
      have hexclLiftNF : ∀ t, (∀ st ∈ rest, st.state ≠ t) → t ≠ step.state → (∀ st ∈ step :: rest, st.state ≠ t) := by
        intro t hexcl hne st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · exact Ne.symm hne
        · exact hexcl st hst
      have hconnected' : ∀ i, i < aux'.roots.size → InternallyConnected succs (aux'.range i) := by
        intro i hi
        rw [haux'rootsNF] at hi
        rw [hrangeEqNF i hi]
        exact hrangeinv.connected i hi
      have hchained' : ∀ i, (h' : i + 1 < aux'.roots.size) →
          ∃ s ∈ aux'.range i, ∃ t ∈ aux'.range (i + 1), t ∈ succs s := by
        intro i hi
        rw [haux'rootsNF] at hi
        obtain ⟨s, hs, t, ht, hst⟩ := hrangeinv.chained i hi
        exact ⟨s, (hrangeEqNF i (by omega)) ▸ hs, t, (hrangeEqNF (i + 1) hi) ▸ ht, hst⟩
      have hbitSound' : ∀ i, i < aux'.roots.size → ∀ m, (aux'.roots[i]!).2.testBit m = true →
          ∃ s ∈ aux'.range i, ∃ t ∈ aux'.range i, t ∈ succs s ∧ m ∈ edgeMarks s t := by
        intro i hi m hm
        rw [haux'rootsNF] at hi hm
        rw [hrangeEqNF i hi]
        exact hrangeinv.bitSound i hi m hm
      have hentrySound' : ∀ k, k < aux'.dfsInfo.size → ∀ m, (aux'.dfsInfo[k]!).2.testBit m = true →
          0 < k ∧ aux'.live[(aux'.dfsInfo[k]!).1]! ∈ succs (aux'.live[(aux'.dfsInfo[k - 1]!).1]!) ∧
            m ∈ edgeMarks (aux'.live[(aux'.dfsInfo[k - 1]!).1]!) (aux'.live[(aux'.dfsInfo[k]!).1]!) := by
        intro k hk m hm
        rw [haux'dfsInfo, Array.size_pop] at hk
        have hkk : k < aux.dfsInfo.pop.size := by rw [Array.size_pop]; omega
        have hk1 : k - 1 < aux.dfsInfo.pop.size := by rw [Array.size_pop]; omega
        rw [haux'dfsInfo, Array.getElem!_pop_lt hkk] at hm ⊢
        rw [Array.getElem!_pop_lt hk1, haux'liveNF]
        exact hrangeinv.entrySound k (by omega) m hm
      have hrangeinv' : DijkstraRangeInv succs edgeMarks aux' :=
        ⟨hwfRoots', hconnected', hchained', hbitSound', hentrySound'⟩
      have hstackdfs' : DijkstraStackDfsInfo aux' rest := by
        refine ⟨?_, ?_, ?_⟩
        · rw [haux'dfsInfo, Array.size_pop]
          simp only [List.length_cons] at hlen
          omega
        · intro i hi
          have hi' : i + 1 < (step :: rest).length := by simp only [List.length_cons]; omega
          have hcorr := hposCorr (i + 1) hi'
          simp only [List.getElem_cons_succ] at hcorr
          rw [hcorr, haux'dfsInfo]
          have hbound : rest.length - 1 - i < aux.dfsInfo.pop.size := by
            simp only [Array.size_pop]
            simp only [List.length_cons] at hlen
            omega
          rw [Array.getElem!_pop_lt hbound]
          congr 2
          simp only [List.length_cons] at hlen ⊢
          omega
        · intro st hst
          rw [haux'liveNF]
          exact hliveCorr st (List.mem_cons_of_mem _ hst)
      have hrangeclosed' : ∀ i, i < aux'.roots.size → ∀ t ∈ aux'.range i, (∀ st ∈ rest, st.state ≠ t) →
          ∀ x ∈ succs t, dijkstraGetStatus aux' x ≠ .unknown → x ∈ aux'.range i ∨ dijkstraGetStatus aux' x = .dead := by
        intro i hi t ht hexcl x hx hxne
        rw [haux'rootsNF] at hi
        rw [hrangeEqNF i hi] at ht
        by_cases hts : t = step.state
        · subst hts
          have hieq : i = aux.roots.size - 1 :=
            DijkstraAux.range_mem_unique hrangeinv.rootsWF hwf hi (by omega) ht hstepMem
          subst hieq
          rcases hstepClosed x hx with hc | hc
          · left; rw [hrangeEqNF _ hi]; exact hc
          · right; exact hdeadPersist x hc
        · rcases hrangeclosed i hi t ht (hexclLiftNF t hexcl hts) x hx (hxneBack x hxne) with hc | hc
          · left; rw [hrangeEqNF _ hi]; exact hc
          · right; exact hdeadPersist x hc
      have hdispatched' : ∀ i, i < aux'.roots.size → ∀ t ∈ aux'.range i, (∀ st ∈ rest, st.state ≠ t) →
          ∀ x ∈ succs t, dijkstraGetStatus aux' x ≠ .unknown := by
        intro i hi t ht hexcl x hx
        rw [haux'rootsNF] at hi
        rw [hrangeEqNF i hi] at ht
        by_cases hts : t = step.state
        · subst hts
          exact hxneTrans x (hstepDispatched x hx)
        · exact hxneTrans x (hdispatched i hi t ht (hexclLiftNF t hexcl hts) x hx)
      have hmarksClosed' : ∀ i, i < aux'.roots.size → ∀ t ∈ aux'.range i, (∀ st ∈ rest, st.state ≠ t) →
          ∀ x ∈ succs t, x ∈ aux'.range i → ∀ m ∈ edgeMarks t x, (aux'.roots[i]!).2.testBit m = true := by
        intro i hi t ht hexcl x hx hxr m hm
        rw [haux'rootsNF] at hi
        rw [hrangeEqNF i hi] at ht
        rw [hrangeEqNF i hi] at hxr
        rw [haux'rootsNF]
        by_cases hts : t = step.state
        · subst hts
          have hieq : i = aux.roots.size - 1 :=
            DijkstraAux.range_mem_unique hrangeinv.rootsWF hwf hi (by omega) ht hstepMem
          subst hieq
          exact hstepMarksClosed x hx hxr m hm
        · exact hmarksClosed i hi t ht (hexclLiftNF t hexcl hts) x hx hxr m hm
      have hMarksOpen' : ∀ st ∈ rest, ∀ x ∈ (st.succ.toList.take st.idx), ∀ i, i < aux'.roots.size →
          x ∈ aux'.range i → st.state ∈ aux'.range i → ∀ m ∈ edgeMarks st.state x, (aux'.roots[i]!).2.testBit m = true := by
        intro st hst x hx i hi hxr hsr m hm
        rw [haux'rootsNF] at hi
        rw [haux'rootsNF]
        rw [hrangeEqNF i hi] at hxr hsr
        exact hrestMarksOpen st hst x hx i hi hxr hsr m hm
      have hmerged' : ∀ st ∈ rest, ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux' x = .live →
          (∃ i, i < aux'.roots.size ∧ st.state ∈ aux'.range i ∧ x ∈ aux'.range i) ∨
          (∃ st' ∈ rest, st'.state = x ∧ Nat.lt st.pos st'.pos) := by
        intro st hst x hx hlive
        have hlive2 : dijkstraGetStatus aux x = .live := hliveBack x hlive
        by_cases hxs : x = step.state
        · subst hxs
          left
          rcases rest with _ | ⟨t, rest'⟩
          · exact absurd hst (by simp)
          · rcases List.mem_cons.mp hst with heq | hst'
            · -- `st = t`, the immediate parent that just retired `step`: `t` sits in the same top
              -- range as `step`, since a non-flush pop only happens when some open frame's own
              -- dfs-depth is still `≥ r0`, `dfsInfoMono` then bounds its `live`-position the same way.
              rw [heq]
              have h1lt : 1 < (step :: t :: rest').length := by simp only [List.length_cons]; omega
              have hval1 : (step :: t :: rest')[1]'h1lt = t := rfl
              have hcorr1 := hposCorr 1 h1lt
              have htcorr : t.pos = (aux.dfsInfo[aux.dfsInfo.size - 2]!).1 := by
                have hidxeq : (step :: t :: rest').length - 1 - 1 = aux.dfsInfo.size - 2 := by
                  simp only [List.length_cons] at hlen ⊢; omega
                rw [← hidxeq]
                exact (congrArg (·.pos) hval1).symm.trans hcorr1
              have hr0lt : r0 < aux.dfsInfo.size := by
                have hb := hrangeinv.rootsWF.rootsBounds (aux.roots.size - 1) (by omega)
                rwa [hrtop] at hb
              have hr0ne : r0 ≠ aux.dfsInfo.size - 1 := by
                intro heq2
                apply hflush
                rw [Array.size_pop, heq2]
              have hr0le : r0 ≤ aux.dfsInfo.size - 2 := by omega
              have htpos : Nat.lt t.pos aux.live.size :=
                dijkstraStackDfsInfo_pos_lt hrangeinv.rootsWF hstackdfsPacked
                  (List.mem_cons_of_mem step List.mem_cons_self)
              have htmem : t.state ∈ aux.range (aux.roots.size - 1) := by
                rw [DijkstraAux.mem_range_iff]
                refine ⟨t.pos, ?_, ?_, hliveCorr t (List.mem_cons_of_mem step List.mem_cons_self)⟩
                · show aux.rangeStart (aux.roots.size - 1) ≤ t.pos
                  unfold DijkstraAux.rangeStart
                  rw [hrtop, htcorr]
                  rcases Nat.lt_or_eq_of_le hr0le with hlt2 | heq3
                  · exact (hrangeinv.rootsWF.dfsInfoMono r0 (aux.dfsInfo.size - 2) hlt2 (by omega)).le
                  · rw [heq3]
                · have hend : aux.rangeEnd (aux.roots.size - 1) = aux.live.size := by
                    unfold DijkstraAux.rangeEnd
                    simp only [show ¬ aux.roots.size - 1 + 1 < aux.roots.size from by omega, if_false]
                  rw [hend, min_self]
                  exact htpos
              refine ⟨aux.roots.size - 1, by rw [haux'rootsNF]; omega, ?_, ?_⟩
              · rw [hrangeEqNF (aux.roots.size - 1) (by omega)]; exact htmem
              · rw [hrangeEqNF (aux.roots.size - 1) (by omega)]; exact hstepMem
            · -- `st ∈ rest'`, strictly below the immediate parent: `step` could never have been a
              -- live target of an already-dispatched edge that far back, `hNoBack` rules it out directly.
              exact absurd hx (hNoBack.1 st hst')
        · rcases hrestMerged st hst x hx hlive2 with hgood | ⟨st', hst', heq, hlt⟩
          · obtain ⟨i, hi, hsr, hxr⟩ := hgood
            exact Or.inl ⟨i, by rw [haux'rootsNF]; exact hi, by rw [hrangeEqNF i hi]; exact hsr,
              by rw [hrangeEqNF i hi]; exact hxr⟩
          · right
            rcases List.mem_cons.mp hst' with heq' | hst''
            · exact absurd (heq' ▸ heq).symm hxs
            · exact ⟨st', hst'', heq, hlt⟩
      have hrootsBound' : ∀ i : Nat, (aux'.roots[i]!).2 < 2 ^ numMarks := by
        intro i; rw [haux'rootsNF]; exact hrootsBound i
      have hrootsNotFull' : ∀ i, i < aux'.roots.size → (aux'.roots[i]!).2 ≠ (1 <<< numMarks) - 1 ∨
          DijkstraNoInternalEdge succs aux' rest i := by
        intro i hi
        rw [haux'rootsNF] at hi ⊢
        refine (hrootsNotFull i hi).imp id (fun hno => ?_)
        -- `step` retires here, and its own dispatched prefix was already the whole successor array
        refine ⟨fun t ht hexcl x hx => ?_, fun st hst hsr x hx => ?_⟩
        · rw [hrangeEqNF i hi] at ht ⊢
          by_cases hts : t = step.state
          · refine hno.2 step (by simp) (hts ▸ ht) x ?_
            rw [List.take_of_length_le (by simp only [Array.length_toList]; omega), hstepSuccEq, ← hts]
            exact Array.mem_def.mp hx
          · exact hno.1 t ht (hexclLiftNF t hexcl hts) x hx
        · rw [hrangeEqNF i hi] at hsr ⊢
          exact hno.2 st (List.mem_cons_of_mem _ hst) hsr x hx
      have hdead' : ∀ s ∈ aux'.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc := by
        rw [haux'deadNF]; exact hdead
      -- Not flushing means the top range's own root is not the popped `dfsInfo` entry, so no range's root is.
      have hTreeMarks' : ∀ st ∈ rest, ∀ st' ∈ rest,
          st'.state ∈ (st.succ.toList.take st.idx) → Nat.lt st.pos st'.pos →
          ∀ j, j < aux'.roots.size → st'.state ∈ aux'.range j → ∀ m ∈ edgeMarks st.state st'.state,
            (aux'.roots[j]!).2.testBit m = true ∨ (aux'.dfsInfo[(aux'.roots[j]!).1]!).2.testBit m = true := by
        intro st hst st' hst' hdisp hlt j hj hjr m hm
        rw [haux'rootsNF] at hj ⊢
        rw [hrangeEqNF j hj] at hjr
        have hr0lt : r0 < aux.dfsInfo.pop.size := by
          have hb := hrangeinv.rootsWF.rootsBounds (aux.roots.size - 1) (by omega)
          rw [show (aux.roots[aux.roots.size - 1]!).1 = r0 from by rw [hrtop]] at hb
          have hps : aux.dfsInfo.pop.size = aux.dfsInfo.size - 1 := Array.size_pop
          omega
        have hrlt : (aux.roots[j]!).1 < aux.dfsInfo.pop.size := by
          rcases Nat.lt_or_eq_of_le (show j ≤ aux.roots.size - 1 from by omega) with hjlt | hjeq
          · exact Nat.lt_trans (by
              have hmono := hrangeinv.rootsWF.rootsMono j (aux.roots.size - 1) hjlt (by omega)
              rwa [show (aux.roots[aux.roots.size - 1]!).1 = r0 from by rw [hrtop]] at hmono) hr0lt
          · rw [hjeq, show (aux.roots[aux.roots.size - 1]!).1 = r0 from by rw [hrtop]]
            exact hr0lt
        rw [haux'dfsInfo, Array.getElem!_pop_lt hrlt]
        exact hTreeMarks st (List.mem_cons_of_mem _ hst) st' (List.mem_cons_of_mem _ hst') hdisp hlt j hj hjr m hm
      exact ih aux' rest r hr hwf' hSuccEq' hPrefix' hReach' hrangeinv' hstackdfs' hrangeclosed' hdispatched'
        hmarksClosed' hMarksOpen' hmerged' hTreeMarks' hNoBack.tail hrootsBound' hdfsInfoBound' hrootsNotFull'
        hdead'

/-! ## Lifting completeness to the whole search

The outer loop carries one bundle between roots: `DijkstraWellFormed`, `DijkstraRangeInv`, `dfsInfo` empty, and
`dead` meeting no `AcceptingSCC`. `dijkstraInitAux` satisfies it and every completed root search restores it, so
each root starts from an idle state, no open range and an empty stack. -/

/-- The initial search state satisfies the range invariant vacuously (`roots`/`dfsInfo` are both empty). -/
theorem dijkstraRangeInv_init [Inhabited State] [LawfulBEq State] {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} :
    DijkstraRangeInv succs edgeMarks (dijkstraInitAux (State := State)) :=
  ⟨dijkstraRootsWF_init, by intro i hi; simp [dijkstraInitAux] at hi,
    by intro i hi; simp [dijkstraInitAux] at hi,
    by intro i hi; simp [dijkstraInitAux] at hi,
    by intro k hk; simp [dijkstraInitAux] at hk⟩

/-- An idle state has nothing live left, `dfsInfo` empty forces `live` empty. -/
theorem dijkstraGetStatus_ne_live_of_idle [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {aux : DijkstraAux State} (hwf : DijkstraWellFormed aux) (hrwf : DijkstraRootsWF aux)
    (hidle : aux.dfsInfo.size = 0) (q : State) : dijkstraGetStatus aux q ≠ .live := by
  have hlive : aux.live.size = 0 := hrwf.liveEmptyOfDfsEmpty hidle
  intro hq
  unfold dijkstraGetStatus dijkstraStatusOf at hq
  have hc : aux.liveIndex.contains q = true := by
    by_cases hc : aux.liveIndex.contains q
    · exact hc
    · rw [if_neg hc] at hq; split at hq <;> cases hq
  rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hc
  exact absurd (hwf.bwd q p hp).1 (by omega)

set_option maxHeartbeats 1000000 in
/-- `dijkstra_dead_not_accepting` across one root's own search: starts from an idle state and restores an idle state if there's no witness.
Pushing a fresh root onto an idle state makes every range- and stack-indexed hypothesis trivial. -/
theorem dijkstraFromRoot_dead_not_accepting [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs)
    (aux : DijkstraAux State) (q0 : State) (hq0 : dijkstraGetStatus aux q0 = .unknown)
    (hq0mem : q0 ∈ initialStates) (hwf : DijkstraWellFormed aux)
    (hrangeinv : DijkstraRangeInv succs edgeMarks aux) (hidle : aux.dfsInfo.size = 0)
    (hdead : ∀ s ∈ aux.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) :
    (∀ s ∈ (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks aux q0).2.dead,
      ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) ∧
    ((dfsFromRoot (dijkstraOps numMarks) succs edgeMarks aux q0).1 = none →
      DijkstraWellFormed (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks aux q0).2 ∧
      DijkstraRangeInv succs edgeMarks (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks aux q0).2 ∧
      (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks aux q0).2.dfsInfo.size = 0) ∧
    (∀ anchor stem, (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks aux q0).1 = some (anchor, stem) →
      InternallyConnected succs (dijkstraSccHint (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks aux q0).2) ∧
      AcceptingMarks succs edgeMarks numMarks
        (dijkstraSccHint (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks aux q0).2) ∧
      anchor ∈ dijkstraSccHint (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks aux q0).2 ∧
      ∃ hs : stem ≠ [], stem.head hs ∈ initialStates ∧
        (∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs (stem[i])) ∧
        stem.getLast hs = anchor) := by
  have hrs0 : aux.roots.size = 0 := by have := hrangeinv.rootsWF.dfsInfoOk; omega
  have hlive0 : aux.live.size = 0 := hrangeinv.rootsWF.liveEmptyOfDfsEmpty hidle
  set step : DFSStep State Nat :=
    { state := q0, pos := (dijkstraPush aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
      acc := Std.HashSet.emptyWithCapacity 0, succ := succs q0, idx := 0 } with hstepdef
  set aux' := (dijkstraPush aux q0 (Std.HashSet.emptyWithCapacity 0)).1 with haux'def
  obtain ⟨r, hrr⟩ : ∃ r, dfsGo (dijkstraOps numMarks) succs edgeMarks aux' [step] = some r :=
    Option.ne_none_iff_exists'.mp (dijkstraOps_root_ne_none numMarks succs edgeMarks initialStates fr
      aux q0 (Reachable.base hq0mem) hwf hq0)
  have hfr : dfsFromRoot (dijkstraOps numMarks) succs edgeMarks aux q0 = r := by
    show (dfsGo (dijkstraOps numMarks) succs edgeMarks aux' [step]).getD (none, aux') = r
    rw [hrr]; rfl
  rw [hfr]
  -- `push` on an idle state opens exactly one range, the singleton `{q0}`, at `live`/`dfsInfo` index `0`.
  have hrootsPush : aux'.roots = aux.roots.push (aux.dfsInfo.size, 0) := rfl
  have hdfsPush : aux'.dfsInfo =
    aux.dfsInfo.push (aux.live.size, marksToBitmask (Std.HashSet.emptyWithCapacity 0)) := rfl
  have hlivePush : aux'.live = aux.live.push q0 := rfl
  have hpos0 : step.pos = 0 := by
    have h : step.pos = aux.live.size := rfl
    rw [h]; exact hlive0
  have hrootsSize : aux'.roots.size = 1 := by rw [hrootsPush, Array.size_push]; omega
  have hdfsSize : aux'.dfsInfo.size = 1 := by rw [hdfsPush, Array.size_push]; omega
  have hroots0 : aux'.roots[0]! = (0, 0) := by
    rw [hrootsPush, Array.getElem!_push_of_size_zero _ hrs0, hidle]
  have hdfs0 : aux'.dfsInfo[0]! = (0, marksToBitmask (Std.HashSet.emptyWithCapacity 0)) := by
    rw [hdfsPush, Array.getElem!_push_of_size_zero _ hidle, hlive0]
  have hlive0' : aux'.live[0]! = q0 := by
    rw [hlivePush, Array.getElem!_push_of_size_zero _ hlive0]
  have hnewRange : ∀ x, x ∈ aux'.range 0 ↔ x = q0 := by
    intro x
    have h := dijkstraPush_new_range_mem_iff aux q0 (Std.HashSet.emptyWithCapacity 0) x
    rwa [hrs0] at h
  have hrootsWF' : DijkstraRootsWF aux' :=
    dijkstraRootsWF_push aux q0 (Std.HashSet.emptyWithCapacity 0) hrangeinv.rootsWF
  have hidx0 : ∀ i, i < aux'.roots.size → i = 0 := by intro i hi; rw [hrootsSize] at hi; omega
  have hbound0 : ∀ i : Nat, (aux'.roots[i]!).2 < 2 ^ numMarks := by
    intro i
    by_cases hi : i = 0
    · rw [hi, hroots0]; exact Nat.two_pow_pos numMarks
    · rw [getElem!_neg aux'.roots i (by rw [hrootsSize]; omega)]
      exact getElem!_pair_default_snd_lt numMarks
  -- The one-frame starting stack is already a `succs`-path from `q0`, so `dfsGo` hands back a real stem.
  have hstem : ∀ anchor stem, r.1 = some (anchor, stem) →
      ∃ hs : stem ≠ [], stem.head hs ∈ initialStates ∧
        (∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs (stem[i])) ∧
        stem.getLast hs = anchor :=
    dfsGo_stem_path (dijkstraOps numMarks) succs edgeMarks initialStates aux' [step] r hrr
      (by intro st hst; simp only [List.mem_singleton] at hst; rw [hst, hstepdef])
      ⟨by intro i hi; simp at hi, by intro _; simpa [hstepdef] using hq0mem⟩
  refine (fun h => ⟨h.1, h.2.1, fun anchor stem heq => ⟨(h.2.2 anchor stem heq).1,
      (h.2.2 anchor stem heq).2.1, (h.2.2 anchor stem heq).2.2, hstem anchor stem heq⟩⟩)
    (dijkstra_dead_not_accepting numMarks succs edgeMarks initialStates hmarksBound
    aux' [step] r hrr (dijkstraWellFormed_push aux q0 _ hwf hq0)
    (by intro st hst; simp only [List.mem_singleton] at hst; rw [hst, hstepdef])
    (by intro st hst x hx; simp only [List.mem_singleton] at hst; rw [hst, hstepdef] at hx; simp at hx)
    (by intro st hst; simp only [List.mem_singleton] at hst; rw [hst, hstepdef]
        exact Reachable.base hq0mem)
    ⟨hrootsWF', ?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ trivial hbound0 ?_ ?_ hdead)
  -- `connected`: the one open range is a singleton
  · intro i _ s hs t ht
    rw [hidx0 i (by omega)] at hs ht
    exact Or.inl (((hnewRange s).mp hs).trans ((hnewRange t).mp ht).symm)
  -- `chained`: there is no second range
  · intro i hi; exact absurd hi (by omega)
  -- `bitSound`/`entrySound`: the single fresh range and its single `dfsInfo` entry both start empty
  · intro i hi m hm
    rw [hidx0 i hi, hroots0] at hm
    simp at hm
  · intro k hk m hm
    rw [hdfsSize] at hk
    rw [show k = 0 from by omega, hdfs0] at hm
    simp [marksToBitmask] at hm
  · show [step].length = aux'.dfsInfo.size
    rw [hdfsSize]; rfl
  · intro i hi
    simp only [List.length_singleton] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    show step.pos = (aux'.dfsInfo[0]!).1
    rw [hpos0, hdfs0]
  · intro st hst
    simp only [List.mem_singleton] at hst
    rw [hst]
    show aux'.live[step.pos]! = q0
    rw [hpos0]; exact hlive0'
  -- `rangeClosed`/`dispatched`/`marksClosed`: the only range member is the frame's own state
  · intro i hi t ht hexcl
    exact absurd ((hnewRange t).mp (hidx0 i hi ▸ ht)).symm (hexcl step (by simp))
  · intro i hi t ht hexcl
    exact absurd ((hnewRange t).mp (hidx0 i hi ▸ ht)).symm (hexcl step (by simp))
  · intro i hi t ht hexcl
    exact absurd ((hnewRange t).mp (hidx0 i hi ▸ ht)).symm (hexcl step (by simp))
  -- `marksOpen`/`merged`/`treeMarks`: the only frame has dispatched nothing
  · intro st hst x hx
    simp only [List.mem_singleton] at hst
    rw [hst, hstepdef] at hx; simp at hx
  · intro st hst x hx
    simp only [List.mem_singleton] at hst
    rw [hst, hstepdef] at hx; simp at hx
  · intro st hst st' _ hx
    simp only [List.mem_singleton] at hst
    rw [hst, hstepdef] at hx; simp at hx
  · intro i
    by_cases hi : i = 0
    · rw [hi, hdfs0]
      exact marksToBitmask_lt (by simp)
    · rw [getElem!_neg aux'.dfsInfo i (by rw [hdfsSize]; omega)]
      exact getElem!_pair_default_snd_lt numMarks
  -- the single fresh range holds only `q0`, which is the frame that just opened it, so nothing has
  -- been dispatched out of it yet
  · intro i hi
    rw [hidx0 i hi]
    refine Or.inr ⟨fun t ht hexcl x hx => ?_, fun st hst hsr x hx => ?_⟩
    · exact absurd ((hnewRange t).mp ht).symm (hexcl step (by simp))
    · simp only [List.mem_singleton] at hst
      rw [hst, hstepdef] at hx
      simp at hx

private theorem dijkstraGetStatus_dead_mem [LawfulBEq State] [LawfulHashable State]
    {aux : DijkstraAux State} {q : State} (h : dijkstraGetStatus aux q = .dead) : q ∈ aux.dead := by
  unfold dijkstraGetStatus dijkstraStatusOf at h
  by_cases hl : aux.liveIndex.contains q
  · rw [if_pos hl] at h; cases h
  · rw [if_neg hl] at h
    by_cases hd : aux.dead.contains q
    · exact Std.HashSet.mem_iff_contains.mpr hd
    · rw [if_neg hd] at h; cases h

/-- `dijkstra_dead_not_accepting` across the outer loop: an already-touched root changes nothing, a fresh one
runs its own search and restores an idle state for the next. -/
theorem dijkstraGo_dead_not_accepting [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs) :
    ∀ (roots : List State) aux (r : Option (State × List State) × DijkstraAux State),
    genericDFSGo (dijkstraOps numMarks) succs edgeMarks roots aux = some r →
    (∀ q ∈ roots, q ∈ initialStates) →
    DijkstraWellFormed aux → DijkstraRangeInv succs edgeMarks aux → aux.dfsInfo.size = 0 →
    (∀ s ∈ aux.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) →
    (r.1 = none →
      (∀ s ∈ r.2.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) ∧
      DijkstraWellFormed r.2 ∧ DijkstraRangeInv succs edgeMarks r.2 ∧ r.2.dfsInfo.size = 0) ∧
    (∀ anchor stem, r.1 = some (anchor, stem) →
      InternallyConnected succs (dijkstraSccHint r.2) ∧
      AcceptingMarks succs edgeMarks numMarks (dijkstraSccHint r.2) ∧
      anchor ∈ dijkstraSccHint r.2 ∧
      ∃ hs : stem ≠ [], stem.head hs ∈ initialStates ∧
        (∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs (stem[i])) ∧
        stem.getLast hs = anchor) := by
  refine genericDFSGo.partial_correctness (dijkstraOps numMarks) succs edgeMarks
    (fun roots aux r => (∀ q ∈ roots, q ∈ initialStates) →
      DijkstraWellFormed aux → DijkstraRangeInv succs edgeMarks aux → aux.dfsInfo.size = 0 →
      (∀ s ∈ aux.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) →
      (r.1 = none →
        (∀ s ∈ r.2.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) ∧
        DijkstraWellFormed r.2 ∧ DijkstraRangeInv succs edgeMarks r.2 ∧ r.2.dfsInfo.size = 0) ∧
      (∀ anchor stem, r.1 = some (anchor, stem) →
        InternallyConnected succs (dijkstraSccHint r.2) ∧
        AcceptingMarks succs edgeMarks numMarks (dijkstraSccHint r.2) ∧
        anchor ∈ dijkstraSccHint r.2 ∧
        ∃ hs : stem ≠ [], stem.head hs ∈ initialStates ∧
          (∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs (stem[i])) ∧
          stem.getLast hs = anchor)) ?_
  intro go ih roots aux r hr
  cases roots with
  | nil =>
    simp only [Option.some.injEq] at hr
    intro _ hwf hrangeinv hidle hdead
    rw [← hr]
    exact ⟨fun _ => ⟨hdead, hwf, hrangeinv, hidle⟩, fun _ _ h => absurd h (by simp)⟩
  | cons q rest =>
  intro hmem hwf hrangeinv hidle hdead
  have hrestMem : ∀ q' ∈ rest, q' ∈ initialStates :=
    fun q' hq' => hmem q' (List.mem_cons_of_mem _ hq')
  cases hgs : (dijkstraOps numMarks).getStatus aux q with
  | dead => simp only [hgs] at hr; exact ih rest aux r hr hrestMem hwf hrangeinv hidle hdead
  | live => simp only [hgs] at hr; exact ih rest aux r hr hrestMem hwf hrangeinv hidle hdead
  | unknown =>
    simp only [hgs] at hr
    rcases hdfr : dfsFromRoot (dijkstraOps numMarks) succs edgeMarks aux q with ⟨found?, aux'⟩
    simp only [hdfr] at hr
    have haux'eq : (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks aux q).2 = aux' := by rw [hdfr]
    have hgs' : dijkstraGetStatus aux q = .unknown := hgs
    obtain ⟨hdead', hbundle, hfound⟩ := dijkstraFromRoot_dead_not_accepting numMarks succs edgeMarks
      initialStates hmarksBound fr aux q hgs' (hmem q (by simp)) hwf hrangeinv hidle hdead
    rw [haux'eq] at hdead' hbundle hfound
    cases hf : found? with
    -- this root's own search reported the counterexample, so its `sccHint` is the one that must be accepting
    | some val =>
      simp only [hf, Option.some.injEq] at hr
      rw [← hr]
      refine ⟨fun h => absurd h (by simp), fun anchor stem heq => ?_⟩
      simp only [Option.some.injEq] at heq
      exact hfound anchor stem (by rw [hdfr]; simp only [hf, heq])
    | none =>
      simp only [hf] at hr
      obtain ⟨hwf', hrangeinv', hidle'⟩ := hbundle (by rw [hdfr]; exact hf)
      exact ih rest aux' r hr hrestMem hwf' hrangeinv' hidle' hdead'

/-- The whole search from `dijkstraInitAux`: an idle start makes every hypothesis above trivial, so an empty
result means every state ever flushed to `dead` is in no `AcceptingSCC`, and the final state is idle again. -/
theorem dijkstra_genericDFS_dead_not_accepting [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs)
    (hnone : (genericDFS (dijkstraOps numMarks) succs edgeMarks initialStates dijkstraInitAux).1 = none) :
    (∀ s ∈ (genericDFS (dijkstraOps numMarks) succs edgeMarks initialStates dijkstraInitAux).2.dead,
      ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) ∧
    DijkstraWellFormed (genericDFS (dijkstraOps numMarks) succs edgeMarks initialStates dijkstraInitAux).2 ∧
    DijkstraRangeInv succs edgeMarks
      (genericDFS (dijkstraOps numMarks) succs edgeMarks initialStates dijkstraInitAux).2 ∧
    (genericDFS (dijkstraOps numMarks) succs edgeMarks initialStates dijkstraInitAux).2.dfsInfo.size = 0 := by
  obtain ⟨r, hrr⟩ : ∃ r, genericDFSGo (dijkstraOps numMarks) succs edgeMarks initialStates
      dijkstraInitAux = some r := Option.ne_none_iff_exists'.mp (genericDFSGo_ne_none (dijkstraOps numMarks) succs edgeMarks _ _)
  have hgd : genericDFS (dijkstraOps numMarks) succs edgeMarks initialStates dijkstraInitAux = r := by
    show (genericDFSGo (dijkstraOps numMarks) succs edgeMarks initialStates dijkstraInitAux).getD _ = r
    rw [hrr]; rfl
  rw [hgd] at hnone ⊢
  exact (dijkstraGo_dead_not_accepting numMarks succs edgeMarks initialStates hmarksBound
    fr initialStates dijkstraInitAux r hrr (fun _ hq => hq)
    dijkstraWellFormed_init dijkstraRangeInv_init
    (by simp [dijkstraInitAux]) (by intro s hs; simp [dijkstraInitAux] at hs)).1 hnone

/-- Soundness: whenever the search reports a counterexample, the hint it reports is a real accepting,
internally connected set containing the anchor. -/
theorem dijkstra_genericDFS_found_acceptingSCC [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs) :
    SccHintSound (dijkstraOps numMarks) succs edgeMarks numMarks initialStates := by
  unfold SccHintSound
  obtain ⟨r, hrr⟩ : ∃ r, genericDFSGo (dijkstraOps numMarks) succs edgeMarks initialStates
      dijkstraInitAux = some r := Option.ne_none_iff_exists'.mp (genericDFSGo_ne_none (dijkstraOps numMarks) succs edgeMarks _ _)
  have hgd : genericDFS (dijkstraOps numMarks) succs edgeMarks initialStates
      (dijkstraOps numMarks).initAux = r := by
    show (genericDFSGo (dijkstraOps numMarks) succs edgeMarks initialStates dijkstraInitAux).getD _ = r
    rw [hrr]; rfl
  rw [hgd]
  exact (dijkstraGo_dead_not_accepting numMarks succs edgeMarks initialStates hmarksBound
    fr initialStates dijkstraInitAux r hrr (fun _ hq => hq)
    dijkstraWellFormed_init dijkstraRangeInv_init
    (by simp [dijkstraInitAux]) (by intro s hs; simp [dijkstraInitAux] at hs)).2

/-- Completeness: a search that reports no counterexample proves there is no reachable `AcceptingSCC` at all.
Every reachable state is explored and an idle final state leaves nothing `.live`, so all of them ended in `dead`. -/
theorem dijkstra_no_acceptingSCC_of_none [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs)
    (hnone : (genericDFS (dijkstraOps numMarks) succs edgeMarks initialStates dijkstraInitAux).1 = none)
    (A : AcceptingSCC initialStates succs edgeMarks numMarks) : False := by
  obtain ⟨hdead, hwf, hrangeinv, hidle⟩ := dijkstra_genericDFS_dead_not_accepting numMarks succs edgeMarks
    initialStates hmarksBound fr hnone
  obtain ⟨s, hs⟩ := A.nonempty
  have hexplored := dijkstraOps_returns_none_fully_explored numMarks succs edgeMarks initialStates fr
    hnone s (A.reachable s hs)
  have hnotlive := dijkstraGetStatus_ne_live_of_idle hwf hrangeinv.rootsWF hidle s
  have hsdead : dijkstraGetStatus
      (genericDFS (dijkstraOps numMarks) succs edgeMarks initialStates dijkstraInitAux).2 s = .dead := by
    cases hst : dijkstraGetStatus
        (genericDFS (dijkstraOps numMarks) succs edgeMarks initialStates dijkstraInitAux).2 s with
    | dead => rfl
    | live => exact absurd hst hnotlive
    | unknown => exact absurd hst hexplored
  exact hdead s (dijkstraGetStatus_dead_mem hsdead) A hs

/-- Dijkstra's SCC-based emptiness check: `dijkstraOps` decides emptiness, and `checkWithWitness` rebuilds the
`.nonEmpty` witness by plain graph BFS. -/
def dijkstraCheck [LawfulBEq State] [LawfulHashable State] (succs : State → Array State)
    (initialStates : List State) (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat) :
    EmptinessResult State :=
  checkWithWitness (dijkstraOps numMarks) succs edgeMarks numMarks initialStates


/-! ## The `TEmptinessChecker` contract -/

/-- Soundness (`TEmptinessChecker.nonEmpty_valid`):
A reported `stem`/`loop` really is a `TAcceptingCycle`'s own stem and cycle. -/
theorem dijkstraCheck_nonEmpty_valid [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs)
    {stem loop : List State}
    (h : dijkstraCheck succs initialStates edgeMarks numMarks = .nonEmpty stem loop) :
    ∃ ac : TAcceptingCycle initialStates succs edgeMarks numMarks, ac.stem = stem ∧ ac.cycle = loop.tail :=
  checkWithWitness_nonEmpty_valid (dijkstraOps numMarks) succs edgeMarks numMarks initialStates
    (dijkstra_genericDFS_found_acceptingSCC numMarks succs edgeMarks initialStates hmarksBound
      fr) h

/-- Completeness (`TEmptinessChecker.empty_no_cycle`): An `.empty` answer proves no `TAcceptingCycle` exists.
`dijkstra_genericDFS_found_acceptingSCC` rules out `checkWithWitness`'s `cycle = []` fallback. -/
theorem dijkstraCheck_empty_no_cycle [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs)
    {n : Nat} (h : dijkstraCheck succs initialStates edgeMarks numMarks = .empty n) :
    ¬∃ _ac : TAcceptingCycle initialStates succs edgeMarks numMarks, True := by
  have hnone := checkWithWitness_empty_of_none (dijkstraOps numMarks) succs edgeMarks numMarks initialStates
    (dijkstra_genericDFS_found_acceptingSCC numMarks succs edgeMarks initialStates hmarksBound
      fr) h
  intro hcyc
  obtain ⟨A, -⟩ := acceptingSCC_iff_acceptingCycle.mpr hcyc
  exact dijkstra_no_acceptingSCC_of_none numMarks succs edgeMarks initialStates hmarksBound
    fr hnone A

/-- `dijkstraCheck` packaged as a `TEmptinessChecker` instance. `check` ignores the contract's `FiniteReach` certificate,
the two proof fields take their own and use it for termination (`dijkstraOps_ne_none`). -/
def dijkstraTChecker [LawfulBEq State] [LawfulHashable State] [Inhabited State] :
    TEmptinessChecker State where
  check := fun succs initialStates _fr edgeMarks numMarks =>
    dijkstraCheck succs initialStates edgeMarks numMarks
  nonEmpty_valid := fun {succs initialStates fr edgeMarks numMarks _stem _loop} hmarksBound h =>
    dijkstraCheck_nonEmpty_valid numMarks succs edgeMarks initialStates hmarksBound fr h
  empty_no_cycle := fun {succs initialStates fr edgeMarks numMarks _n} hmarksBound h =>
    dijkstraCheck_empty_no_cycle numMarks succs edgeMarks initialStates hmarksBound fr h

end LTLLib
