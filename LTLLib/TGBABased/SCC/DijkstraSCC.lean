module

/-
  Dijkstra's SCC-based emptiness check (Algorithm 3 of [RDKP13]), refining `GenericDFS.lean`'s abstract operations with
  two stacks, the live states and the open SCC candidates among them.

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

  `roots` names each candidate's root by its `live` position rather than by its dfs-depth, and carries that root's own
  entry-edge marks beside the merged ones, so `dfs[r].pos` is `root`, `dfs[r].acc` is `entry`, and the driver's stack is
  never read. `push_trivial` and `push_non_trivial` are plain pushes, without roots-stack compression. Mark sets are `Nat`
  bitmasks, so `a = F` is an equality against the all-ones mask `(1 <<< numMarks) - 1`.

  Defines:
  - `RootEntry`, `DijkstraAux`, `dijkstraOps`: an open SCC candidate, the search state, and the refinement
  - `DijkstraRootsWF`, `DijkstraRangeInv`: the ranges of `roots` tile `live`, are internally connected and tree-adjacent,
    and carry sound bitmasks
  - `DijkstraStackRoots`, `DijkstraNoInternalEdge`, `NoBackDispatch`: the stack-side invariants carried with them
  - `dijkstraCheck`, `dijkstraTChecker`: the emptiness check and its `TEmptinessChecker` instance

  Proves:
  - `dijkstra_dead_not_accepting`: a state flushed to `dead` is in no reachable `AcceptingSCC`
  - `dijkstra_genericDFS_found_acceptingSCC`, `dijkstra_no_acceptingSCC_of_none`: a reported hint is an accepting SCC
    holding the anchor, and a search reporting nothing proves there is no reachable `AcceptingSCC`
  - `dijkstraCheck_nonEmpty_valid`, `dijkstraCheck_empty_no_cycle`: a reported stem and loop form a `TAcceptingCycle`,
    and an `.empty` answer proves none exists

  References:
  - [RDKP13] Renault, Duret-Lutz, Kordon, Poitrenaud. Three SCC-based Emptiness Checks for Generalized Büchi
    Automata. LPAR-19, 2013.

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

public import Std
public import LTLLib.AbstractSpec.EmptinessCheck
public import LTLLib.AbstractSpec.GraphPaths
public import LTLLib.TGBABased.AbstractSpec.EmptinessCheck
public import LTLLib.TGBABased.AbstractSpec.SCCTheory
public import LTLLib.TGBABased.SCC.GenericDFS
public import LTLLib.TGBABased.SCC.LiveStack
meta import LTLLib.Tactic.Set

public section

namespace LTLLib

variable {State : Type u} [BEq State] [Hashable State]

/-! ## Dijkstra's search state -/

/-- One open SCC candidate. -/
structure RootEntry where
  root : Nat  -- where this candidate's root sits in `live`, which is also where its range begins
  acc : Nat  -- the marks already known to lie on edges internal to the candidate, as a bitmask
  entry : Nat  -- the marks on the tree edge that pushed the root, folded in when the candidate merges downward
deriving Inhabited

/-- Dijkstra's private search state, the live states and the open SCC candidates among them. The candidate rooted at
`roots[i]` owns the `live` positions `roots[i].root`, …, `roots[i+1].root - 1`, [RDKP13] §3.2 with roots named by `live`
position rather than by dfs-depth. -/
structure DijkstraAux (State : Type u) [BEq State] [Hashable State] where
  live : Array State
  liveIndex : Std.HashMap State Nat -- position of each live state, for O(1) membership
  dead : Std.HashSet State
  roots : Array RootEntry

@[expose] def dijkstraInitAux : DijkstraAux State where
  live := #[]
  liveIndex := Std.HashMap.emptyWithCapacity 0
  dead := Std.HashSet.emptyWithCapacity 0
  roots := #[]

def dijkstraGetStatus (aux : DijkstraAux State) (q : State) : DFSStatus :=
  liveStatusOf aux.liveIndex aux.dead q

/-! ## PUSH and UPDATE -/

/-- `PUSH`, line 24: a newly visited state starts as a trivial SCC candidate, non-trivial ones only arise by merging on a
back-edge. -/
@[expose] def dijkstraPush (aux : DijkstraAux State) (q : State) (marks : Std.HashSet Nat) :
    DijkstraAux State × Nat :=
  let pos := aux.live.size
  ({ aux with
      live := aux.live.push q
      liveIndex := aux.liveIndex.insert q pos
      roots := aux.roots.push ⟨pos, 0, marksToBitmask marks⟩ },
   pos)

/-- The merge loop of `UPDATE`, lines 20-23, with `r` and its entry marks `e` already popped. It folds in each abandoned
entry's marks, and the settled root's entry marks stay out of `a`. -/
private def dijkstraMergeRoots (dpos : Nat) (roots : Array RootEntry) (r a e : Nat) :
    Array RootEntry × Nat × Nat × Nat :=
  if dpos < r then
    match _h : roots.back? with
    | none => (roots, r, a, e)
    | some ⟨r1, la, e1⟩ => dijkstraMergeRoots dpos roots.pop r1 (a ||| e ||| la) e1
  else (roots, r, a, e)
termination_by roots.size
decreasing_by
  have hne : roots.size > 0 := by
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp _h
    simp [hys]
  simp only [Array.size_pop]; omega

def dijkstraUpdate (numMarks : Nat) (aux : DijkstraAux State)
    (marks : Std.HashSet Nat) (d : State) : DijkstraAux State × Bool :=
  match aux.roots.back? with
  | none => (aux, false)
  | some ⟨r0, a0, e0⟩ =>
    let dpos := aux.liveIndex.getD d 0
    -- line 19 (`a ← a ∪ acc`), the loop folds in entry marks if it moves past the top
    let a0' := a0 ||| marksToBitmask marks
    let (roots, r, a, e) := dijkstraMergeRoots dpos aux.roots.pop r0 a0' e0
    -- `a = F`, against the all-ones mask
    let found := a == (1 <<< numMarks) - 1
    ({ aux with roots := roots.push ⟨r, a, e⟩ }, found)

/-! ## POP -/

/-- `POP`, lines 27-32. The merge is eager, so POP only confirms a root and flushes, and never reports. -/
def dijkstraPop (aux : DijkstraAux State) (pos : Nat) : DijkstraAux State × Bool :=
  match aux.roots.back? with
  | none => (aux, false)
  | some ⟨r, _, _⟩ =>
    -- the popped frame is the top candidate's root exactly when it sits at that candidate's `live` position
    if pos = r then
      let (live, liveIndex, dead) := liveFlush aux.live aux.liveIndex aux.dead pos
      ({ aux with
        roots := aux.roots.pop
        live := live
        liveIndex := liveIndex
        dead := dead }, false)
    else (aux, false)

/-! ## Well-formedness and the basic status axioms

The `LawfulDFSOps` status laws fail for an arbitrary `aux`, and hold under `DijkstraWellFormed`. -/

/-- `live` and `liveIndex` agree in both directions. -/
abbrev DijkstraWellFormed [Inhabited State] (aux : DijkstraAux State) : Prop :=
  LiveWF aux.live aux.liveIndex

theorem dijkstraWellFormed_init [Inhabited State] : DijkstraWellFormed (dijkstraInitAux (State := State)) :=
  liveWF_init 0

theorem dijkstraWellFormed_push [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (aux : DijkstraAux State) (q : State) (marks : Std.HashSet Nat) (hwf : DijkstraWellFormed aux)
    (hq : dijkstraGetStatus aux q = .unknown) : DijkstraWellFormed (dijkstraPush aux q marks).1 := by
  refine hwf.push ?_
  by_contra hc
  simp only [Bool.not_eq_false] at hc
  rw [dijkstraGetStatus, liveStatusOf, if_pos hc] at hq
  exact absurd hq (by simp)

/-- PUSH marks its target live and leaves every other state's status untouched. -/
theorem dijkstraPush_status [LawfulBEq State] [LawfulHashable State] (aux : DijkstraAux State) (q : State)
    (marks : Std.HashSet Nat) (q' : State) :
    dijkstraGetStatus (dijkstraPush aux q marks).1 q' = if q' == q then .live else dijkstraGetStatus aux q' :=
  liveStatusOf_insert aux.liveIndex aux.dead q aux.live.size q'

/-- UPDATE only touches `roots`. -/
theorem dijkstraUpdate_fields (numMarks : Nat) (aux : DijkstraAux State) (marks : Std.HashSet Nat) (d : State) :
    (dijkstraUpdate numMarks aux marks d).1.live = aux.live ∧
    (dijkstraUpdate numMarks aux marks d).1.liveIndex = aux.liveIndex ∧
    (dijkstraUpdate numMarks aux marks d).1.dead = aux.dead := by
  unfold dijkstraUpdate
  cases aux.roots.back? with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some x => obtain ⟨r0, a0, e0⟩ := x; exact ⟨rfl, rfl, rfl⟩

theorem dijkstraWellFormed_update [Inhabited State] (numMarks : Nat) (aux : DijkstraAux State)
    (marks : Std.HashSet Nat) (d : State) (hwf : DijkstraWellFormed aux) :
    DijkstraWellFormed (dijkstraUpdate numMarks aux marks d).1 := by
  obtain ⟨hlive, hli, _⟩ := dijkstraUpdate_fields numMarks aux marks d
  refine ⟨fun i h => ?_, fun q p h => ?_⟩
  · simp only [hlive] at h ⊢
    simp only [hli]
    exact hwf.fwd i h
  · simp only [hli] at h
    simp only [hlive]
    exact hwf.bwd q p h

/-- UPDATE never changes any state's status. -/
theorem dijkstraUpdate_status (numMarks : Nat) (aux : DijkstraAux State) (marks : Std.HashSet Nat) (d q : State) :
    dijkstraGetStatus (dijkstraUpdate numMarks aux marks d).1 q = dijkstraGetStatus aux q := by
  obtain ⟨_, hli, hdead⟩ := dijkstraUpdate_fields numMarks aux marks d
  unfold dijkstraGetStatus
  simp only [hli, hdead]

/-- POP preserves well-formedness. -/
theorem dijkstraWellFormed_pop [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (aux : DijkstraAux State) (pos : Nat) (hwf : DijkstraWellFormed aux) :
    DijkstraWellFormed (dijkstraPop aux pos).1 := by
  rcases hb : aux.roots.back? with _ | ⟨r, a0, e0⟩
  · simp only [dijkstraPop, hb]
    exact hwf
  · by_cases h : pos = r
    · simp only [dijkstraPop, hb, if_pos h]
      exact hwf.flush pos
    · simp only [dijkstraPop, hb, if_neg h]
      exact hwf

/-- On a well-formed state, POP only ever promotes states from live to dead. -/
theorem dijkstraPop_status [Inhabited State] [LawfulBEq State] [LawfulHashable State] (aux : DijkstraAux State)
    (pos : Nat) (hwf : DijkstraWellFormed aux) (q : State) :
    dijkstraGetStatus (dijkstraPop aux pos).1 q = dijkstraGetStatus aux q ∨
    (dijkstraGetStatus aux q = .live ∧ dijkstraGetStatus (dijkstraPop aux pos).1 q = .dead) := by
  rcases hb : aux.roots.back? with _ | ⟨r, a0, e0⟩
  · simp only [dijkstraGetStatus, dijkstraPop, hb]
    exact Or.inl trivial
  · by_cases h : pos = r
    · simp only [dijkstraGetStatus, dijkstraPop, hb, if_pos h]
      exact (liveFlush_spec pos aux.live aux.liveIndex aux.dead hwf.fwd hwf.bwd).2.2 q
    · simp only [dijkstraGetStatus, dijkstraPop, hb, if_neg h]
      exact Or.inl trivial

theorem dijkstraGetStatus_initAux [LawfulBEq State] [LawfulHashable State] (q : State) :
    dijkstraGetStatus (dijkstraInitAux (State := State)) q = .unknown := by
  unfold dijkstraGetStatus liveStatusOf dijkstraInitAux
  simp

/-! ## Range bookkeeping and `DijkstraRootsWF`

Each `roots[i]` owns a contiguous slice of `live`. Positions and the merge's bitmask arithmetic only, no `succs`. -/

/-- Position in `live` where the range rooted at `roots[i]` begins. -/
def DijkstraAux.rangeStart (aux : DijkstraAux State) (i : Nat) : Nat := (aux.roots[i]!).root

/-- One past the range's last `live` position, the next range's start, or `live.size` at the top. -/
def DijkstraAux.rangeEnd (aux : DijkstraAux State) (i : Nat) : Nat :=
  if i + 1 < aux.roots.size then aux.rangeStart (i + 1) else aux.live.size

/-- The states currently in the range rooted at `roots[i]`. -/
@[expose] def DijkstraAux.range (aux : DijkstraAux State) (i : Nat) : Std.HashSet State :=
  (aux.live.extract (aux.rangeStart i) (aux.rangeEnd i)).foldl
    (init := Std.HashSet.emptyWithCapacity 0) fun acc s => acc.insert s

private theorem mem_foldl_insert [LawfulBEq State] (l : List State) (init : Std.HashSet State) (x : State) :
    x ∈ l.foldl (fun acc s => acc.insert s) init ↔ x ∈ init ∨ x ∈ l := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Std.HashSet.mem_insert, List.mem_cons, beq_iff_eq]
    grind

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

/-- Positional invariant on `roots` alone, the ranges tiling `live` without gaps or overlaps. -/
structure DijkstraRootsWF (aux : DijkstraAux State) : Prop where
  -- root positions increase strictly, so consecutive ranges abut and never overlap
  rootsMono : ∀ i j, i < j → j < aux.roots.size → (aux.roots[i]!).root < (aux.roots[j]!).root
  rootsLt : ∀ i, i < aux.roots.size → (aux.roots[i]!).root < aux.live.size
  -- the bottom range starts at position 0, and `live` is empty exactly when no candidate is open
  rootsBase : 0 < aux.roots.size → (aux.roots[0]!).root = 0
  liveEmptyOfRootsEmpty : aux.roots.size = 0 → aux.live.size = 0

/-- A live state always has a `roots`-range to sit inside. -/
theorem DijkstraRootsWF.roots_pos_of_live_pos {aux : DijkstraAux State} (hwf : DijkstraRootsWF aux)
    (h : 0 < aux.live.size) : 0 < aux.roots.size := by
  by_contra hc
  exact absurd (hwf.liveEmptyOfRootsEmpty (by omega)) (by omega)

theorem dijkstraRootsWF_init : DijkstraRootsWF (dijkstraInitAux (State := State)) :=
  ⟨fun i j _ hj => by simp [dijkstraInitAux] at hj, fun i hi => by simp [dijkstraInitAux] at hi,
   fun h => by simp [dijkstraInitAux] at h, fun _ => by simp [dijkstraInitAux]⟩

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
  obtain ⟨hmono, hlt, hbase, hlempty⟩ := hwf
  unfold dijkstraPush
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij h
    simp only [Array.size_push] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hjlt | hjeq
    · rw [Array.getElem!_push_lt (Nat.lt_trans hij hjlt), Array.getElem!_push_lt hjlt]
      exact hmono i j hij hjlt
    · subst hjeq
      rw [Array.getElem!_push_lt hij, Array.getElem!_push_eq]
      exact hlt i hij
  · intro i h
    simp only [Array.size_push] at h
    simp only [Array.size_push]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hilt | heq
    · rw [Array.getElem!_push_lt hilt]; exact Nat.lt_trans (hlt i hilt) (by omega)
    · subst heq; rw [Array.getElem!_push_eq]; simp
  · intro _
    simp only
    by_cases hc : 0 < aux.roots.size
    · rw [Array.getElem!_push_lt hc]; exact hbase hc
    · have hz : aux.roots.size = 0 := by omega
      have hkey : (aux.roots.push ⟨aux.live.size, 0, marksToBitmask marks⟩)[aux.roots.size]! =
          ⟨aux.live.size, 0, marksToBitmask marks⟩ := Array.getElem!_push_eq
      rw [hz] at hkey
      rw [hkey]
      exact hlempty hz
  · simp only [Array.size_push]; omega

/-- `DijkstraRootsWF`'s `roots`-only facts, relative to an arbitrary `bound`. -/
private def RootsChain (roots : Array RootEntry) (bound : Nat) : Prop :=
  (∀ i, i < roots.size → (roots[i]!).root < bound) ∧
  (∀ i j, i < j → j < roots.size → (roots[i]!).root < (roots[j]!).root) ∧
  (0 < roots.size → (roots[0]!).root = 0) ∧
  (roots.size = 0 → bound = 0)

private theorem DijkstraRootsWF.chain_pop {aux : DijkstraAux State} (hwf : DijkstraRootsWF aux)
    {ys : Array RootEntry} {r0 a0 e0 : Nat} (hys : aux.roots = ys.push ⟨r0, a0, e0⟩) :
    RootsChain ys r0 := by
  obtain ⟨hmono, _, hbase, _⟩ := hwf
  refine ⟨fun i hi => ?_, fun i j hij hj => ?_, fun hpos => ?_, fun hemp => ?_⟩
  · have := hmono i ys.size hi (by rw [hys]; simp)
    rwa [hys, Array.getElem!_push_lt hi, Array.getElem!_push_eq] at this
  · have hjb : j < aux.roots.size := by rw [hys]; simp; omega
    have := hmono i j hij hjb
    rwa [hys, Array.getElem!_push_lt (Nat.lt_trans hij hj), Array.getElem!_push_lt hj] at this
  · have hb0 := hbase (show 0 < aux.roots.size from by rw [hys]; simp)
    rwa [hys, Array.getElem!_push_lt hpos] at hb0
  · have hb0 := hbase (show 0 < aux.roots.size from by rw [hys]; simp)
    have hb0' : aux.roots[ys.size]!.root = 0 := by rw [hemp]; exact hb0
    rwa [hys, Array.getElem!_push_eq] at hb0'

private theorem dijkstraMergeRoots_spec (dpos : Nat) :
    ∀ (roots : Array RootEntry) (r a e : Nat), RootsChain roots r →
    (dijkstraMergeRoots dpos roots r a e).1.size ≤ roots.size ∧
    (dijkstraMergeRoots dpos roots r a e).2.1 ≤ r ∧
    RootsChain (dijkstraMergeRoots dpos roots r a e).1 (dijkstraMergeRoots dpos roots r a e).2.1 ∧
    ∀ i, i < (dijkstraMergeRoots dpos roots r a e).1.size →
      (dijkstraMergeRoots dpos roots r a e).1[i]! = roots[i]! := by
  intro roots r a e
  induction roots, r, a, e using dijkstraMergeRoots.induct dpos with
  | case1 roots r a e hcond hnone =>
    intro hchain
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hnone]
    exact ⟨Nat.le_refl _, Nat.le_refl _, hchain, fun i _ => rfl⟩
  | case2 roots r a e hcond r1 la e1 hb ih =>
    intro hchain
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    obtain ⟨hbounds, hmono, hbase0, hrzero⟩ := hchain
    have hpop : (ys.push ⟨r1, la, e1⟩).pop = ys := by simp
    have hr1 : r1 < r := by
      have := hbounds ys.size (by simp)
      rwa [Array.getElem!_push_eq] at this
    have hys' : RootsChain ys r1 := by
      refine ⟨fun i hi => ?_, fun i j hij hj => ?_, fun hpos => ?_, fun hempty => ?_⟩
      · have := hmono i ys.size hi (by simp)
        rwa [Array.getElem!_push_lt hi, Array.getElem!_push_eq] at this
      · have := hmono i j hij (Nat.lt_trans hj (by simp))
        rwa [Array.getElem!_push_lt (Nat.lt_trans hij hj), Array.getElem!_push_lt hj] at this
      · have hb0 := hbase0 (show 0 < (ys.push ⟨r1, la, e1⟩).size from by simp)
        rwa [Array.getElem!_push_lt hpos] at hb0
      · have hb0 := hbase0 (show 0 < (ys.push ⟨r1, la, e1⟩).size from by simp)
        have hb0' : (ys.push ⟨r1, la, e1⟩)[ys.size]!.root = 0 := by rw [hempty]; exact hb0
        rwa [Array.getElem!_push_eq] at hb0'
    have hihyp := ih (by rw [hpop]; exact hys')
    rw [hpop] at hihyp
    obtain ⟨h1, h2, h3, h4⟩ := hihyp
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hb]
    dsimp only
    rw [hpop]
    refine ⟨by simp only [Array.size_push]; omega, by omega, h3, fun i hi => ?_⟩
    have hilt : i < ys.size := Nat.lt_of_lt_of_le hi h1
    rw [h4 i hi, Array.getElem!_push_lt hilt]
  | case3 roots r a e hcond =>
    intro hchain
    unfold dijkstraMergeRoots
    simp only [hcond, if_false]
    exact ⟨Nat.le_refl _, Nat.le_refl _, hchain, fun i _ => trivial⟩

private theorem dijkstraMergeRoots_bitmask_mono (dpos m : Nat) :
    ∀ (roots : Array RootEntry) (r a e : Nat), a.testBit m = true →
      (dijkstraMergeRoots dpos roots r a e).2.2.1.testBit m = true := by
  intro roots r a e
  induction roots, r, a, e using dijkstraMergeRoots.induct dpos with
  | case1 roots r a e hcond hnone =>
    intro hm
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hnone]
    exact hm
  | case2 roots r a e hcond r1 la e1 hb ih =>
    intro hm
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hb]
    dsimp only
    exact ih (by simp [Nat.testBit_or, hm])
  | case3 roots r a e hcond =>
    intro hm
    unfold dijkstraMergeRoots
    simp only [hcond, if_false]
    exact hm

private theorem dijkstraMergeRoots_bitmask_absorbs (dpos : Nat) :
    ∀ (roots : Array RootEntry) (r a e : Nat) (j : Nat),
      (dijkstraMergeRoots dpos roots r a e).1.size ≤ j → j < roots.size → ∀ m,
        (roots[j]!).acc.testBit m = true → (dijkstraMergeRoots dpos roots r a e).2.2.1.testBit m = true := by
  intro roots r a e
  induction roots, r, a, e using dijkstraMergeRoots.induct dpos with
  | case1 roots r a e hcond hnone =>
    intro j hj1 hj2 m hm
    have hempty : roots = #[] := Array.back?_eq_none_iff.mp hnone
    rw [hempty] at hj2
    simp at hj2
  | case2 roots r a e hcond r1 la e1 hb ih =>
    intro j hj1 hj2 m hm
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push ⟨r1, la, e1⟩).pop = ys := by simp
    have hj1' : (dijkstraMergeRoots dpos (ys.push ⟨r1, la, e1⟩).pop r1
        (a ||| e ||| la) e1).1.size ≤ j := by
      unfold dijkstraMergeRoots at hj1
      simp only [hcond, if_true] at hj1
      rw [hb] at hj1
      dsimp only at hj1
      exact hj1
    by_cases hje : j < ys.size
    · have hm' : (ys[j]!).acc.testBit m = true := by rwa [Array.getElem!_push_lt hje] at hm
      have hres := ih j hj1' (by rwa [hpop]) m (by rwa [hpop])
      simp only [hpop] at hres
      unfold dijkstraMergeRoots
      simp only [hcond, if_true]
      rw [hb]
      dsimp only
      simp only [hpop]
      exact hres
    · have hjeq : j = ys.size := by simp at hj2; omega
      have heq : (ys.push ⟨r1, la, e1⟩)[j]! = ⟨r1, la, e1⟩ := by rw [hjeq]; exact Array.getElem!_push_eq
      rw [heq] at hm
      have hfold : (a ||| e ||| la).testBit m = true := by
        simp only [Nat.testBit_or, hm, Bool.or_true]
      have hres := dijkstraMergeRoots_bitmask_mono dpos m ys r1 _ e1 hfold
      unfold dijkstraMergeRoots
      simp only [hcond, if_true]
      rw [hb]
      dsimp only
      rw [hpop]
      exact hres
  | case3 roots r a e hcond =>
    intro j hj1 hj2 m hm
    unfold dijkstraMergeRoots at hj1
    simp only [hcond, if_false] at hj1
    omega

private theorem dijkstraMergeRoots_entry_absorbs_self (dpos : Nat) :
    ∀ (roots : Array RootEntry) (r a e : Nat),
      (dijkstraMergeRoots dpos roots r a e).1.size < roots.size → ∀ m,
        e.testBit m = true →
          (dijkstraMergeRoots dpos roots r a e).2.2.1.testBit m = true := by
  intro roots r a e
  induction roots, r, a, e using dijkstraMergeRoots.induct dpos with
  | case1 roots r a e hcond hnone =>
    intro hlt m hm
    have hempty : roots = #[] := Array.back?_eq_none_iff.mp hnone
    rw [hempty] at hlt
    simp at hlt
  | case2 roots r a e hcond r1 la e1 hb _ =>
    intro _ m hm
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push ⟨r1, la, e1⟩).pop = ys := by simp
    have hfold : (a ||| e ||| la).testBit m = true := by
      simp only [Nat.testBit_or, hm, Bool.or_true, Bool.true_or]
    have hres := dijkstraMergeRoots_bitmask_mono dpos m ys r1 _ e1 hfold
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hb]
    dsimp only
    rw [hpop]
    exact hres
  | case3 roots r a e hcond =>
    intro hlt m hm
    unfold dijkstraMergeRoots at hlt
    simp only [hcond, if_false] at hlt
    omega

private theorem dijkstraMergeRoots_entry_absorbs (dpos : Nat) :
    ∀ (roots : Array RootEntry) (r a e : Nat) (j : Nat),
      (dijkstraMergeRoots dpos roots r a e).1.size < j → j < roots.size → ∀ m,
        (roots[j]!).entry.testBit m = true →
          (dijkstraMergeRoots dpos roots r a e).2.2.1.testBit m = true := by
  intro roots r a e
  induction roots, r, a, e using dijkstraMergeRoots.induct dpos with
  | case1 roots r a e hcond hnone =>
    intro j hj1 hj2 m hm
    have hempty : roots = #[] := Array.back?_eq_none_iff.mp hnone
    rw [hempty] at hj2
    simp at hj2
  | case2 roots r a e hcond r1 la e1 hb ih =>
    intro j hj1 hj2 m hm
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push ⟨r1, la, e1⟩).pop = ys := by simp
    have hj1' : (dijkstraMergeRoots dpos (ys.push ⟨r1, la, e1⟩).pop r1
        (a ||| e ||| la) e1).1.size < j := by
      unfold dijkstraMergeRoots at hj1
      simp only [hcond, if_true] at hj1
      rw [hb] at hj1
      dsimp only at hj1
      exact hj1
    by_cases hje : j < ys.size
    · have hm' : (ys[j]!).entry.testBit m = true := by
        rwa [Array.getElem!_push_lt hje] at hm
      have hres := ih j hj1' (by rwa [hpop]) m (by rwa [hpop])
      simp only [hpop] at hres
      unfold dijkstraMergeRoots
      simp only [hcond, if_true]
      rw [hb]
      dsimp only
      simp only [hpop]
      exact hres
    -- `j` is the entry being stripped right now, so its root picks the marks up one step later
    · have hjeq : j = ys.size := by simp at hj2; omega
      have heq : (ys.push ⟨r1, la, e1⟩)[j]! = ⟨r1, la, e1⟩ := by rw [hjeq]; exact Array.getElem!_push_eq
      simp only [heq] at hm
      have hres := dijkstraMergeRoots_entry_absorbs_self dpos ys r1
        (a ||| e ||| la) e1 (by rw [hpop] at hj1'; omega) m hm
      unfold dijkstraMergeRoots
      simp only [hcond, if_true]
      rw [hb]
      dsimp only
      rw [hpop]
      exact hres
  | case3 roots r a e hcond =>
    intro j hj1 hj2 m hm
    unfold dijkstraMergeRoots at hj1
    simp only [hcond, if_false] at hj1
    omega

private theorem dijkstraMergeRoots_size_le (dpos : Nat) :
    ∀ (roots : Array RootEntry) (r a e : Nat),
      (dijkstraMergeRoots dpos roots r a e).1.size ≤ roots.size := by
  intro roots r a e
  induction roots, r, a, e using dijkstraMergeRoots.induct dpos with
  | case1 roots r a e hcond hnone =>
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hnone]; exact Nat.le_refl _
  | case2 roots r a e hcond r1 la e1 hb ih =>
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push ⟨r1, la, e1⟩).pop = ys := by simp
    simp only [hpop] at ih
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hb]
    dsimp only
    rw [hpop]
    simp only [Array.size_push]
    omega
  | case3 roots r a e hcond =>
    unfold dijkstraMergeRoots
    simp only [hcond, if_false]
    exact Nat.le_refl _

private theorem dijkstraMergeRoots_bitmask_elim (dpos : Nat) (P : Nat → Prop) :
    ∀ (roots : Array RootEntry) (r a e : Nat),
      (∀ m, a.testBit m = true → P m) →
      (∀ j, (dijkstraMergeRoots dpos roots r a e).1.size ≤ j → j < roots.size →
        ∀ m, (roots[j]!).acc.testBit m = true → P m) →
      ((dijkstraMergeRoots dpos roots r a e).1.size < roots.size →
        ∀ m, e.testBit m = true → P m) →
      (∀ j, (dijkstraMergeRoots dpos roots r a e).1.size < j → j < roots.size →
        ∀ m, (roots[j]!).entry.testBit m = true → P m) →
      ∀ m, (dijkstraMergeRoots dpos roots r a e).2.2.1.testBit m = true → P m := by
  intro roots r a e
  induction roots, r, a, e using dijkstraMergeRoots.induct dpos with
  | case1 roots r a e hcond hnone =>
    intro ha _ _ _ m hm
    refine ha m ?_
    unfold dijkstraMergeRoots at hm
    simp only [hcond, if_true] at hm
    rwa [hnone] at hm
  | case2 roots r a e hcond r1 la e1 hb ih =>
    intro ha hroots hself hdfs m hm
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push ⟨r1, la, e1⟩).pop = ys := by simp
    simp only [hpop] at ih
    have hstep : dijkstraMergeRoots dpos (ys.push ⟨r1, la, e1⟩) r a e =
        dijkstraMergeRoots dpos ys r1 (a ||| e ||| la) e1 := by
      conv => lhs; unfold dijkstraMergeRoots
      simp only [hcond, if_true]
      rw [hb]
      dsimp only
      rw [hpop]
    rw [hstep] at hroots hself hdfs hm
    have hle := dijkstraMergeRoots_size_le dpos ys r1 (a ||| e ||| la) e1
    have hsizelt : (dijkstraMergeRoots dpos ys r1 (a ||| e ||| la) e1).1.size
        < (ys.push ⟨r1, la, e1⟩).size := by simp only [Array.size_push]; omega
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
  | case3 roots r a e hcond =>
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
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hbound (Nat.pow_le_pow_right (by omega) (by omega)))

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

private theorem getElem!_default_acc_lt (numMarks : Nat) : (default : RootEntry).acc < 2 ^ numMarks :=
  Nat.two_pow_pos numMarks

private theorem getElem!_default_entry_lt (numMarks : Nat) :
    (default : RootEntry).entry < 2 ^ numMarks :=
  Nat.two_pow_pos numMarks

private theorem dijkstraMergeRoots_bitmask_bound (dpos numMarks : Nat) :
    ∀ (roots : Array RootEntry) (r a e : Nat), a < 2 ^ numMarks → e < 2 ^ numMarks →
      (∀ i : Nat, (roots[i]!).acc < 2 ^ numMarks) → (∀ i : Nat, (roots[i]!).entry < 2 ^ numMarks) →
      (dijkstraMergeRoots dpos roots r a e).2.2.1 < 2 ^ numMarks := by
  intro roots r a e
  induction roots, r, a, e using dijkstraMergeRoots.induct dpos with
  | case1 roots r a e hcond hnone =>
    intro ha _ _ _
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hnone]
    exact ha
  | case2 roots r a e hcond r1 la e1 hb ih =>
    intro ha he hroots hentry
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push ⟨r1, la, e1⟩).pop = ys := by simp
    simp only [hpop] at ih
    have hla : la < 2 ^ numMarks := by
      have := hroots ys.size
      rwa [Array.getElem!_push_eq] at this
    have he1 : e1 < 2 ^ numMarks := by
      have := hentry ys.size
      rwa [Array.getElem!_push_eq] at this
    have hys' : ∀ i : Nat, (ys[i]!).acc < 2 ^ numMarks := by
      intro i
      by_cases hi : i < ys.size
      · have := hroots i; rwa [Array.getElem!_push_lt hi] at this
      · rw [getElem!_neg ys i hi]; exact getElem!_default_acc_lt numMarks
    have hys'' : ∀ i : Nat, (ys[i]!).entry < 2 ^ numMarks := by
      intro i
      by_cases hi : i < ys.size
      · have := hentry i; rwa [Array.getElem!_push_lt hi] at this
      · rw [getElem!_neg ys i hi]; exact getElem!_default_entry_lt numMarks
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hb]
    dsimp only
    rw [hpop]
    exact ih (Nat.or_lt_two_pow (Nat.or_lt_two_pow ha he) hla) he1 hys' hys''
  | case3 roots r a e hcond =>
    intro ha _ _ _
    unfold dijkstraMergeRoots
    simp only [hcond, if_false]
    exact ha

private theorem array_pop_bitmask_bound {numMarks : Nat} {xs : Array RootEntry}
    (hxs : ∀ i : Nat, (xs[i]!).acc < 2 ^ numMarks) : ∀ i : Nat, (xs.pop[i]!).acc < 2 ^ numMarks := by
  intro i
  by_cases hi : i < xs.pop.size
  · rw [Array.getElem!_pop_lt hi]; exact hxs i
  · rw [getElem!_neg xs.pop i hi]; exact getElem!_default_acc_lt numMarks

private theorem dijkstraMergeRoots_locate (dpos : Nat) :
    ∀ (full roots : Array RootEntry) (r a e : Nat), roots.size ≤ full.size →
    RootsChain roots r → (∀ i, i < roots.size → roots[i]! = full[i]!) → r = (full[roots.size]!).root →
    e = (full[roots.size]!).entry →
    (dijkstraMergeRoots dpos roots r a e).2.1 =
      (full[(dijkstraMergeRoots dpos roots r a e).1.size]!).root ∧
    (dijkstraMergeRoots dpos roots r a e).2.2.2 =
      (full[(dijkstraMergeRoots dpos roots r a e).1.size]!).entry ∧
    (dijkstraMergeRoots dpos roots r a e).2.1 ≤ dpos ∧
    ((dijkstraMergeRoots dpos roots r a e).1.size = roots.size ∨
      (dijkstraMergeRoots dpos roots r a e).1.size < roots.size ∧
      dpos < (full[(dijkstraMergeRoots dpos roots r a e).1.size + 1]!).root) := by
  intro full roots r a e
  induction roots, r, a, e using dijkstraMergeRoots.induct dpos with
  | case1 roots r a e hcond hnone =>
    intro hsub hchain hpre hridx hentry
    have hrsize : roots.size = 0 := by
      have := Array.back?_eq_none_iff.mp hnone; simp [this]
    have hrzero : r = 0 := hchain.2.2.2 hrsize
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hnone]
    refine ⟨hridx, hentry, ?_, ?_⟩
    · rw [hrzero]; omega
    · exact Or.inl rfl
  | case2 roots r a e hcond r1 la e1 hb ih =>
    intro hsub hchain hpre hridx hentry
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    subst hys
    have hpop : (ys.push ⟨r1, la, e1⟩).pop = ys := by simp
    have hr1 : r1 < r := by
      have := hchain.1 ys.size (by simp)
      rwa [Array.getElem!_push_eq] at this
    have hys' : RootsChain ys r1 := by
      obtain ⟨hbounds, hmono, hbase0, hrzero⟩ := hchain
      refine ⟨fun i hi => ?_, fun i j hij hj => ?_, fun hpos => ?_, fun hempty => ?_⟩
      · have := hmono i ys.size hi (by simp)
        rwa [Array.getElem!_push_lt hi, Array.getElem!_push_eq] at this
      · have := hmono i j hij (Nat.lt_trans hj (by simp))
        rwa [Array.getElem!_push_lt (Nat.lt_trans hij hj), Array.getElem!_push_lt hj] at this
      · have hb0 := hbase0 (show 0 < (ys.push ⟨r1, la, e1⟩).size from by simp)
        rwa [Array.getElem!_push_lt hpos] at hb0
      · have hb0 := hbase0 (show 0 < (ys.push ⟨r1, la, e1⟩).size from by simp)
        have hb0' : (ys.push ⟨r1, la, e1⟩)[ys.size]!.root = 0 := by rw [hempty]; exact hb0
        rwa [Array.getElem!_push_eq] at hb0'
    have hpre' : ∀ i, i < ys.size → ys[i]! = full[i]! := by
      intro i hi
      have := hpre i (by simp only [Array.size_push]; omega)
      rwa [Array.getElem!_push_lt hi] at this
    have hridx' : r1 = (full[ys.size]!).root := by
      have hval := hpre ys.size (by simp)
      rw [Array.getElem!_push_eq] at hval
      rw [← hval]
    have hsub' : (ys.push ⟨r1, la, e1⟩).pop.size ≤ full.size := by
      rw [hpop]; simp only [Array.size_push] at hsub; omega
    have hychain : RootsChain (ys.push ⟨r1, la, e1⟩).pop r1 := by rw [hpop]; exact hys'
    have hypre : ∀ i, i < (ys.push ⟨r1, la, e1⟩).pop.size → (ys.push ⟨r1, la, e1⟩).pop[i]! = full[i]! := by
      rw [hpop]; exact hpre'
    have hyridx : r1 = (full[(ys.push ⟨r1, la, e1⟩).pop.size]!).root := by rw [hpop]; exact hridx'
    have hentry' : e1 = (full[ys.size]!).entry := by
      have hval := hpre ys.size (by simp)
      rw [Array.getElem!_push_eq] at hval
      rw [← hval]
    have hyentry : e1 = (full[(ys.push ⟨r1, la, e1⟩).pop.size]!).entry := by rw [hpop]; exact hentry'
    have hihyp := ih hsub' hychain hypre hyridx hyentry
    rw [hpop] at hihyp
    unfold dijkstraMergeRoots
    simp only [hcond, if_true]
    rw [hb]
    dsimp only
    rw [hpop]
    refine ⟨hihyp.1, hihyp.2.1, hihyp.2.2.1, Or.inr ⟨by simp only [Array.size_push]; omega, ?_⟩⟩
    rcases hihyp.2.2.2 with heq | ⟨_, hlt⟩
    · rw [heq, show ys.size + 1 = (ys.push ⟨r1, la, e1⟩).size from by simp, ← hridx]
      exact hcond
    · exact hlt
  | case3 roots r a e hcond =>
    intro hsub hchain hpre hridx hentry
    unfold dijkstraMergeRoots
    simp only [hcond, if_false]
    refine ⟨hridx, hentry, by omega, ?_⟩
    exact Or.inl trivial

theorem dijkstraRootsWF_update (numMarks : Nat) (aux : DijkstraAux State) (marks : Std.HashSet Nat)
    (d : State) (hwf : DijkstraRootsWF aux) : DijkstraRootsWF (dijkstraUpdate numMarks aux marks d).1 := by
  unfold dijkstraUpdate
  cases haux : aux.roots.back? with
  | none =>
    obtain ⟨hmono, hlt, hbase, hlempty⟩ := hwf
    dsimp only; exact ⟨hmono, hlt, hbase, hlempty⟩
  | some x =>
    obtain ⟨r0, a0, e0⟩ := x
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp haux
    have hpop : aux.roots.pop = ys := by rw [hys]; simp
    have hys' : RootsChain ys r0 := hwf.chain_pop hys
    obtain ⟨hmono, hlt, hbase, hlempty⟩ := hwf
    have hr0 : r0 < aux.live.size := by
      have := hlt ys.size (by rw [hys]; simp)
      rwa [hys, Array.getElem!_push_eq] at this
    set res := dijkstraMergeRoots (aux.liveIndex.getD d 0) ys r0
      (a0 ||| marksToBitmask marks) e0 with hres
    have hspec := dijkstraMergeRoots_spec (aux.liveIndex.getD d 0) ys r0
      (a0 ||| marksToBitmask marks) e0 hys'
    rw [hpop]
    obtain ⟨hs1, hs2, ⟨hs3a, hs3b, hs3c, hs3d⟩, hs4⟩ := hspec
    refine ⟨fun i j hij hj => ?_, fun i hi => ?_, fun _ => ?_,
      fun h => by simp only [Array.size_push] at h; omega⟩
    · simp only [Array.size_push] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | hjeq
      · rw [Array.getElem!_push_lt (Nat.lt_trans hij hjlt), Array.getElem!_push_lt hjlt]
        exact hs3b i j hij hjlt
      · subst hjeq
        rw [Array.getElem!_push_lt hij, Array.getElem!_push_eq]
        exact hs3a i hij
    · simp only [Array.size_push] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | heq
      · rw [Array.getElem!_push_lt hilt]
        exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hs3a i hilt) hs2) (Nat.le_of_lt hr0)
      · subst heq
        rw [Array.getElem!_push_eq]
        exact Nat.lt_of_le_of_lt hs2 hr0
    · -- new top-level `rootsBase`: either the merge survived (its own `roots0`) or fully collapsed (its `rZero`)
      by_cases hc : 0 < res.1.size
      · rw [Array.getElem!_push_lt hc]; exact hs3c hc
      · have hz : res.1.size = 0 := by omega
        have hkey : (res.1.push ⟨res.2.1, res.2.2.1, res.2.2.2⟩)[res.1.size]! =
            ⟨res.2.1, res.2.2.1, res.2.2.2⟩ := Array.getElem!_push_eq
        rw [hz] at hkey
        rw [hkey]; exact hs3d hz

private theorem dijkstraUpdate_merge_locate [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (numMarks : Nat) (aux : DijkstraAux State) (marks : Std.HashSet Nat) (d : State)
    (hwf : DijkstraWellFormed aux) (hrwf : DijkstraRootsWF aux) (hroots_pos : 0 < aux.roots.size)
    (hd_contains : aux.liveIndex.contains d = true) :
    ∃ lo, lo < aux.roots.size ∧ d ∈ aux.range lo ∧
      (dijkstraUpdate numMarks aux marks d).1.roots.size = lo + 1 ∧
      (∀ i, i < lo → (dijkstraUpdate numMarks aux marks d).1.roots[i]! = aux.roots[i]!) ∧
      ((dijkstraUpdate numMarks aux marks d).1.roots[lo]!).root = (aux.roots[lo]!).root ∧
      ((dijkstraUpdate numMarks aux marks d).1.roots[lo]!).entry = (aux.roots[lo]!).entry := by
  obtain ⟨r0, a0, e0, hback⟩ : ∃ r0 a0 e0, aux.roots.back? = some ⟨r0, a0, e0⟩ := by
    rcases hbk : aux.roots.back? with _ | p
    · exact absurd (Array.back?_eq_none_iff.mp hbk) (by
        intro he; rw [he] at hroots_pos; simp at hroots_pos)
    · exact ⟨p.root, p.acc, p.entry, by simp⟩
  obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hback
  have hpop : aux.roots.pop = ys := by rw [hys]; simp
  have hys' : RootsChain ys r0 := hrwf.chain_pop hys
  have hr0 : r0 < aux.live.size := by
    have := hrwf.rootsLt ys.size (by rw [hys]; simp)
    rwa [hys, Array.getElem!_push_eq] at this
  have hmergePre : ∀ i, i < ys.size → ys[i]! = aux.roots[i]! := by
    intro i hi; rw [hys, Array.getElem!_push_lt hi]
  have hridx : r0 = (aux.roots[ys.size]!).root := by rw [hys, Array.getElem!_push_eq]
  have hentry0 : e0 = (aux.roots[ys.size]!).entry := by rw [hys, Array.getElem!_push_eq]
  have hsub : ys.size ≤ aux.roots.size := by rw [hys]; simp
  have hrootssize : aux.roots.size = ys.size + 1 := by rw [hys]; simp
  set dpos := aux.liveIndex.getD d 0 with hdpos_def
  set a0' := a0 ||| marksToBitmask marks with ha0'_def
  have haux'roots : (dijkstraUpdate numMarks aux marks d).1.roots =
      (dijkstraMergeRoots dpos ys r0 a0' e0).1.push
      ⟨(dijkstraMergeRoots dpos ys r0 a0' e0).2.1,
       (dijkstraMergeRoots dpos ys r0 a0' e0).2.2.1,
       (dijkstraMergeRoots dpos ys r0 a0' e0).2.2.2⟩ := by
    unfold dijkstraUpdate
    rw [hback]
    dsimp only
    rw [hpop]
  have hdp_eq : aux.liveIndex[d]? = some dpos :=
    Std.HashMap.getElem?_eq_some_getD_of_contains hd_contains
  obtain ⟨hdpos_lt, hdpos_val⟩ := hwf.bwd d dpos hdp_eq
  have hlocate := dijkstraMergeRoots_locate dpos
    aux.roots ys r0 a0' e0 hsub hys' hmergePre hridx hentry0
  set res := dijkstraMergeRoots dpos ys r0 a0' e0 with hres_def
  set lo := res.1.size with hlo_def
  have hlo_le_ys : lo ≤ ys.size := (dijkstraMergeRoots_spec dpos ys r0 a0' e0 hys').1
  have hlo_lt : lo < aux.roots.size := by omega
  have hd_range : d ∈ aux.range lo := by
    rw [DijkstraAux.mem_range_iff]
    refine ⟨dpos, ?_, ?_, hdpos_val⟩
    · show aux.rangeStart lo ≤ dpos
      unfold DijkstraAux.rangeStart
      rw [← hlocate.1]
      exact hlocate.2.2.1
    · rcases hlocate.2.2.2 with heq | ⟨hlt_size, hlt⟩
      · have hend : aux.rangeEnd lo = aux.live.size := by
          unfold DijkstraAux.rangeEnd
          rw [heq]
          simp only [show ¬ ys.size + 1 < aux.roots.size from by omega, if_false]
        rw [hend, Nat.min_self]; exact hdpos_lt
      · have hlo1 : lo + 1 < aux.roots.size := by omega
        have hend : aux.rangeEnd lo = aux.rangeStart (lo + 1) := by
          unfold DijkstraAux.rangeEnd
          rw [if_pos hlo1]
        have hstart_eq : aux.rangeStart (lo + 1) = (aux.roots[lo + 1]!).root := rfl
        rw [hend, hstart_eq]
        exact Nat.lt_min.mpr ⟨hlt, hdpos_lt⟩
  refine ⟨lo, hlo_lt, hd_range, ?_, ?_, ?_, ?_⟩
  · rw [haux'roots]; simp only [Array.size_push, hlo_def]
  · intro i hi
    rw [haux'roots, Array.getElem!_push_lt (show i < res.1.size from by omega)]
    exact ((dijkstraMergeRoots_spec dpos ys r0 a0' e0 hys').2.2.2 i (by omega)).trans
      (hmergePre i (by omega))
  · rw [haux'roots, Array.getElem!_push_eq, hlocate.1]
  · rw [haux'roots, Array.getElem!_push_eq, hlocate.2.1]

private theorem dijkstraUpdate_merge_bitmask [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (numMarks : Nat) (aux : DijkstraAux State) (marks : Std.HashSet Nat) (d : State)
    (hpos : 0 < aux.roots.size) :
    ∃ lo, lo + 1 = (dijkstraUpdate numMarks aux marks d).1.roots.size ∧
    (∀ m, ((aux.roots[aux.roots.size - 1]!).acc ||| marksToBitmask marks).testBit m = true →
      ((dijkstraUpdate numMarks aux marks d).1.roots[lo]!).acc.testBit m = true) ∧
    (∀ k, lo ≤ k → k < aux.roots.size - 1 → ∀ m, (aux.roots[k]!).acc.testBit m = true →
      ((dijkstraUpdate numMarks aux marks d).1.roots[lo]!).acc.testBit m = true) ∧
    (∀ k, lo < k → k < aux.roots.size → ∀ m, (aux.roots[k]!).entry.testBit m = true →
      ((dijkstraUpdate numMarks aux marks d).1.roots[lo]!).acc.testBit m = true) := by
  unfold dijkstraUpdate
  cases haux : aux.roots.back? with
  | none =>
    exfalso
    have := Array.back?_eq_none_iff.mp haux
    rw [this] at hpos
    simp at hpos
  | some x =>
    obtain ⟨r0, a0, e0⟩ := x
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp haux
    have hpop : aux.roots.pop = ys := by rw [hys]; simp
    have hidx : aux.roots.size - 1 = ys.size := by rw [hys]; simp
    have hrsize : aux.roots.size = ys.size + 1 := by rw [hys]; simp
    have htop : aux.roots[aux.roots.size - 1]! = ⟨r0, a0, e0⟩ := by rw [hidx, hys, Array.getElem!_push_eq]
    dsimp only
    rw [hpop]
    refine ⟨(dijkstraMergeRoots (aux.liveIndex.getD d 0) ys r0
        (a0 ||| marksToBitmask marks) e0).1.size, by simp only [Array.size_push],
      fun m hm => ?_, fun k hk1 hk2 m hm => ?_, fun k hk1 hk2 m hm => ?_⟩
    · rw [htop] at hm
      dsimp only at hm
      rw [Array.getElem!_push_eq]
      exact dijkstraMergeRoots_bitmask_mono (aux.liveIndex.getD d 0) m ys r0 _ e0 hm
    · rw [hidx] at hk2
      have hm' : (ys[k]!).acc.testBit m = true := by
        have hke : ys[k]! = aux.roots[k]! := by rw [hys, Array.getElem!_push_lt hk2]
        rw [hke]; exact hm
      rw [Array.getElem!_push_eq]
      exact dijkstraMergeRoots_bitmask_absorbs (aux.liveIndex.getD d 0) ys r0
        (a0 ||| marksToBitmask marks) e0 k hk1 hk2 m hm'
    · rw [Array.getElem!_push_eq]
      rcases Nat.lt_or_ge k ys.size with hklt | hkge
      · have hm' : (ys[k]!).entry.testBit m = true := by
          have hke : ys[k]! = aux.roots[k]! := by rw [hys, Array.getElem!_push_lt hklt]
          rw [hke]; exact hm
        exact dijkstraMergeRoots_entry_absorbs (aux.liveIndex.getD d 0) ys r0
          (a0 ||| marksToBitmask marks) e0 k hk1 hklt m hm'
      -- `k` is the pre-merge top itself, whose entry marks are folded as soon as the loop moves off it
      · have hkeq : k = ys.size := by omega
        have hm' : e0.testBit m = true := by
          rwa [hkeq, hys, Array.getElem!_push_eq] at hm
        exact dijkstraMergeRoots_entry_absorbs_self (aux.liveIndex.getD d 0) ys r0
          (a0 ||| marksToBitmask marks) e0 (by omega) m hm'

private theorem dijkstraUpdate_merge_bound [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (numMarks : Nat) (aux : DijkstraAux State) (marks : Std.HashSet Nat) (d : State)
    (hpos : 0 < aux.roots.size) (hrootsBound : ∀ i : Nat, (aux.roots[i]!).acc < 2 ^ numMarks)
    (hentryBound : ∀ i : Nat, (aux.roots[i]!).entry < 2 ^ numMarks)
    (hmarksLt : marksToBitmask marks < 2 ^ numMarks) :
    ∃ lo, lo + 1 = (dijkstraUpdate numMarks aux marks d).1.roots.size ∧
      ((dijkstraUpdate numMarks aux marks d).1.roots[lo]!).acc < 2 ^ numMarks := by
  unfold dijkstraUpdate
  cases haux : aux.roots.back? with
  | none =>
    exfalso
    have := Array.back?_eq_none_iff.mp haux
    rw [this] at hpos
    simp at hpos
  | some x =>
    obtain ⟨r0, a0, e0⟩ := x
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp haux
    have hpop : aux.roots.pop = ys := by rw [hys]; simp
    have hidx : aux.roots.size - 1 = ys.size := by rw [hys]; simp
    have ha0 : a0 < 2 ^ numMarks := by
      have := hrootsBound (aux.roots.size - 1)
      rwa [hidx, hys, Array.getElem!_push_eq] at this
    have he0 : e0 < 2 ^ numMarks := by
      have := hentryBound (aux.roots.size - 1)
      rwa [hidx, hys, Array.getElem!_push_eq] at this
    have hys' : ∀ i : Nat, (ys[i]!).acc < 2 ^ numMarks := by
      intro i
      by_cases hi : i < ys.size
      · have := hrootsBound i; rwa [hys, Array.getElem!_push_lt hi] at this
      · rw [getElem!_neg ys i hi]; exact getElem!_default_acc_lt numMarks
    have hys'' : ∀ i : Nat, (ys[i]!).entry < 2 ^ numMarks := by
      intro i
      by_cases hi : i < ys.size
      · have := hentryBound i; rwa [hys, Array.getElem!_push_lt hi] at this
      · rw [getElem!_neg ys i hi]; exact getElem!_default_entry_lt numMarks
    dsimp only
    rw [hpop]
    refine ⟨(dijkstraMergeRoots (aux.liveIndex.getD d 0) ys r0
        (a0 ||| marksToBitmask marks) e0).1.size, by simp only [Array.size_push], ?_⟩
    rw [Array.getElem!_push_eq]
    exact dijkstraMergeRoots_bitmask_bound (aux.liveIndex.getD d 0) numMarks ys r0 _ e0
      (Nat.or_lt_two_pow ha0 hmarksLt) he0 hys' hys''

private theorem dijkstraUpdate_merge_bitmask_elim [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (numMarks : Nat) (aux : DijkstraAux State) (marks : Std.HashSet Nat) (d : State)
    (hpos : 0 < aux.roots.size) :
    ∃ lo, lo + 1 = (dijkstraUpdate numMarks aux marks d).1.roots.size ∧
      ∀ P : Nat → Prop,
        (∀ m, (marksToBitmask marks).testBit m = true → P m) →
        (∀ k, lo ≤ k → k < aux.roots.size → ∀ m, (aux.roots[k]!).acc.testBit m = true → P m) →
        (∀ k, lo < k → k < aux.roots.size → ∀ m,
          (aux.roots[k]!).entry.testBit m = true → P m) →
        ∀ m, ((dijkstraUpdate numMarks aux marks d).1.roots[lo]!).acc.testBit m = true → P m := by
  unfold dijkstraUpdate
  cases haux : aux.roots.back? with
  | none =>
    exfalso
    have := Array.back?_eq_none_iff.mp haux
    rw [this] at hpos
    simp at hpos
  | some x =>
    obtain ⟨r0, a0, e0⟩ := x
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp haux
    have hpop : aux.roots.pop = ys := by rw [hys]; simp
    have hrsize : aux.roots.size = ys.size + 1 := by rw [hys]; simp
    have htop : aux.roots[ys.size]! = ⟨r0, a0, e0⟩ := by rw [hys, Array.getElem!_push_eq]
    dsimp only
    rw [hpop]
    have hle := dijkstraMergeRoots_size_le (aux.liveIndex.getD d 0) ys r0
      (a0 ||| marksToBitmask marks) e0
    refine ⟨(dijkstraMergeRoots (aux.liveIndex.getD d 0) ys r0
        (a0 ||| marksToBitmask marks) e0).1.size, by simp only [Array.size_push],
      fun P hedge hrange hentry m hm => ?_⟩
    rw [Array.getElem!_push_eq] at hm
    refine dijkstraMergeRoots_bitmask_elim (aux.liveIndex.getD d 0) P ys r0 _ e0
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
        (((dijkstraUpdate numMarks aux marks d).1.roots[lo]!).acc == (1 <<< numMarks) - 1) := by
  unfold dijkstraUpdate
  cases haux : aux.roots.back? with
  | none =>
    exfalso
    have := Array.back?_eq_none_iff.mp haux
    rw [this] at hpos
    simp at hpos
  | some x =>
    obtain ⟨r0, a0, e0⟩ := x
    dsimp only
    refine ⟨(dijkstraMergeRoots (aux.liveIndex.getD d 0) aux.roots.pop r0
        (a0 ||| marksToBitmask marks) e0).1.size, by simp only [Array.size_push], ?_⟩
    rw [Array.getElem!_push_eq]

private theorem mono_index_le {roots : Array RootEntry}
    (hmono : ∀ i j, i < j → j < roots.size → (roots[i]!).root < (roots[j]!).root) :
    ∀ i, i < roots.size → i ≤ (roots[i]!).root := by
  intro i
  induction i with
  | zero => intro _; omega
  | succ k ih =>
    intro hk1
    have := ih (by omega)
    have hstep := hmono k (k + 1) (by omega) hk1
    omega

theorem dijkstraRootsWF_pop (aux : DijkstraAux State) (pos : Nat) (hwf : DijkstraRootsWF aux) :
    DijkstraRootsWF (dijkstraPop aux pos).1 := by
  unfold dijkstraPop
  cases haux : aux.roots.back? with
  | none => exact hwf
  | some x =>
    obtain ⟨r, a, e⟩ := x
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp haux
    have hpop : aux.roots.pop = ys := by rw [hys]; simp
    have hchain : RootsChain ys r := hwf.chain_pop hys
    obtain ⟨hmono, hlt, hbase, hlempty⟩ := hwf
    have hrlive : r < aux.live.size := by
      have := hlt ys.size (by rw [hys]; simp)
      rwa [hys, Array.getElem!_push_eq] at this
    by_cases h : pos = r
    · subst h
      simp only [if_true]
      have hflushsize : (liveFlush aux.live aux.liveIndex aux.dead pos).1.size = pos :=
        liveFlush_size pos aux.live aux.liveIndex aux.dead (by omega)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hpop]; exact hchain.2.1
      · rw [hpop, hflushsize]; exact hchain.1
      · rw [hpop]; exact hchain.2.2.1
      · rw [hpop, hflushsize]; exact hchain.2.2.2
    · simp only [h, if_false]
      exact ⟨hmono, hlt, hbase, hlempty⟩

/-! ## The range invariant and its preservation

`DijkstraRangeInv` on every open `roots`-range: internal connectivity, tree-adjacency between consecutive ranges,
and bitmask soundness. Carried through `dfsGo`'s recursion with the stack-side `DijkstraNoInternalEdge` and `NoBackDispatch`. -/

/-- Connectivity and bitmask soundness on every currently open `roots`-range. -/
structure DijkstraRangeInv [Inhabited State] (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (aux : DijkstraAux State) : Prop where
  rootsWF : DijkstraRootsWF aux
  -- every open range is internally strongly connected
  connected : ∀ i, i < aux.roots.size → InternallyConnected succs (aux.range i)
  -- consecutive open ranges are tree-adjacent, range (i+1) was pushed as some range-i member's successor
  chained : ∀ i, i + 1 < aux.roots.size → ∃ s ∈ aux.range i, ∃ t ∈ aux.range (i + 1), t ∈ succs s
  -- every bit of an open range's bitmask names a real edge with both endpoints inside that range
  bitSound : ∀ i, i < aux.roots.size → ∀ m, (aux.roots[i]!).acc.testBit m = true →
    ∃ s ∈ aux.range i, ∃ t ∈ aux.range i, t ∈ succs s ∧ m ∈ edgeMarks s t
  -- every bit of a root's entry marks names the tree edge that pushed it, running in from the range one below
  entrySound : ∀ i, i < aux.roots.size → ∀ m, (aux.roots[i]!).entry.testBit m = true →
    0 < i ∧ ∃ s ∈ aux.range (i - 1), ∃ t ∈ aux.range i, t ∈ succs s ∧ m ∈ edgeMarks s t

/-- Frame positions decrease from the top of the driver stack downward. -/
@[expose] def DijkstraPosChain [Inhabited State] : List (DFSStep State Nat) → Prop
  | [] => True
  | [_] => True
  | s :: t :: rest => t.pos < s.pos ∧ DijkstraPosChain (t :: rest)

/-- Driver stack and `roots` in lockstep: each frame owns its own `live` slot, and every open candidate is rooted at a
frame still on the stack. -/
@[expose] def DijkstraStackRoots [Inhabited State] (aux : DijkstraAux State) (stack : List (DFSStep State Nat)) : Prop :=
  (∀ st ∈ stack, st.pos < aux.live.size ∧ aux.live[st.pos]! = st.state) ∧
  DijkstraPosChain stack ∧
  (∀ j, j < aux.roots.size → (aux.roots[j]!).root ∈ stack.map (·.pos)) ∧
  (stack = [] ↔ aux.roots.size = 0)

/-- No edge with both endpoints inside range `i` discovered yet, retired members and dispatched prefixes alike, the
`numMarks = 0` counterpart of the bitmask. -/
@[expose] def DijkstraNoInternalEdge [Inhabited State] (succs : State → Array State) (aux : DijkstraAux State)
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

omit [BEq State] [Hashable State] in
private theorem DijkstraPosChain.tail [Inhabited State] {s : DFSStep State Nat}
    {rest : List (DFSStep State Nat)} (h : DijkstraPosChain (s :: rest)) : DijkstraPosChain rest := by
  cases rest with
  | nil => trivial
  | cons t rest' => exact h.2

omit [BEq State] [Hashable State] in
/-- The top frame's position dominates the whole stack. -/
private theorem DijkstraPosChain.le_head [Inhabited State] {s : DFSStep State Nat}
    {rest : List (DFSStep State Nat)} (h : DijkstraPosChain (s :: rest)) :
    ∀ st ∈ s :: rest, st.pos ≤ s.pos := by
  induction rest generalizing s with
  | nil => intro st hst; simp only [List.mem_singleton] at hst; rw [hst]; exact Nat.le_refl _
  | cons t rest' ih =>
    intro st hst
    rcases List.mem_cons.mp hst with rfl | hst
    · exact Nat.le_refl _
    · exact Nat.le_trans (ih h.2 st hst) (Nat.le_of_lt h.1)

omit [BEq State] [Hashable State] in
omit [BEq State] [Hashable State] in
/-- Everything below the top frame sits at a strictly smaller position. -/
private theorem DijkstraPosChain.lt_head [Inhabited State] {s : DFSStep State Nat}
    {rest : List (DFSStep State Nat)} (h : DijkstraPosChain (s :: rest)) :
    ∀ st ∈ rest, st.pos < s.pos := by
  cases rest with
  | nil => intro st hst; simp at hst
  | cons t rest' => intro st hst; exact Nat.lt_of_le_of_lt (h.2.le_head st hst) h.1

omit [BEq State] [Hashable State] in
private theorem DijkstraPosChain.cons [Inhabited State] {s : DFSStep State Nat}
    {rest : List (DFSStep State Nat)} (h : DijkstraPosChain rest)
    (hlt : ∀ st ∈ rest, st.pos < s.pos) : DijkstraPosChain (s :: rest) := by
  cases rest with
  | nil => trivial
  | cons t rest' => exact ⟨hlt t (by simp), h⟩

private theorem dijkstraStackRoots_pos_lt [Inhabited State] {aux : DijkstraAux State}
    {stack : List (DFSStep State Nat)} (hsr : DijkstraStackRoots aux stack)
    {st : DFSStep State Nat} (hst : st ∈ stack) : st.pos < aux.live.size := (hsr.1 st hst).1

private theorem dijkstraStackRoots_live_eq_push [Inhabited State] (aux : DijkstraAux State) (q : State)
    (marks : Std.HashSet Nat) {stack : List (DFSStep State Nat)}
    (hsr : DijkstraStackRoots aux stack) {st : DFSStep State Nat} (hst : st ∈ stack) :
    (dijkstraPush aux q marks).1.live[st.pos]! = st.state := by
  unfold dijkstraPush
  simp only
  rw [Array.getElem!_push_lt (hsr.1 st hst).1]
  exact (hsr.1 st hst).2

/-- An `idx` bump of the top frame keeps the lockstep. -/
private theorem DijkstraStackRoots.bump [Inhabited State] {aux : DijkstraAux State}
    {step : DFSStep State Nat} {rest : List (DFSStep State Nat)}
    (h : DijkstraStackRoots aux (step :: rest)) (step' : DFSStep State Nat)
    (hpos : step'.pos = step.pos) (hstate : step'.state = step.state) :
    DijkstraStackRoots aux (step' :: rest) := by
  obtain ⟨hlive, hchain, hroot, hne⟩ := h
  refine ⟨fun st hst => ?_, ?_, fun j hj => ?_, ?_⟩
  · rcases List.mem_cons.mp hst with rfl | hst
    · rw [hpos, hstate]; exact hlive step (by simp)
    · exact hlive st (List.mem_cons_of_mem _ hst)
  · cases rest with
    | nil => trivial
    | cons t rest' => exact ⟨hpos ▸ hchain.1, hchain.2⟩
  · have := hroot j hj
    simpa [hpos] using this
  · simpa using hne

/-- `PUSH` seats the fresh frame at the top of `live` and opens a candidate rooted there. -/
private theorem DijkstraStackRoots.push [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {aux : DijkstraAux State} {stack : List (DFSStep State Nat)} {q : State} {marks : Std.HashSet Nat}
    (h : DijkstraStackRoots aux stack) (newStep : DFSStep State Nat)
    (hstate : newStep.state = q) (hpos : newStep.pos = aux.live.size) :
    DijkstraStackRoots (dijkstraPush aux q marks).1 (newStep :: stack) := by
  obtain ⟨hlive, hchain, hroot, _⟩ := h
  have hlivePush : (dijkstraPush aux q marks).1.live = aux.live.push q := rfl
  have hrootsPush : (dijkstraPush aux q marks).1.roots =
      aux.roots.push ⟨aux.live.size, 0, marksToBitmask marks⟩ := rfl
  refine ⟨fun st hst => ?_, ?_, fun j hj => ?_, ?_⟩
  · rw [hlivePush]
    rcases List.mem_cons.mp hst with rfl | hst
    · rw [hpos]
      exact ⟨by simp, by rw [Array.getElem!_push_eq]; exact hstate.symm⟩
    · obtain ⟨h1, h2⟩ := hlive st hst
      exact ⟨by simp only [Array.size_push]; omega, by rw [Array.getElem!_push_lt h1]; exact h2⟩
  · exact hchain.cons (fun st hst => hpos ▸ (hlive st hst).1)
  · rw [hrootsPush] at hj ⊢
    simp only [Array.size_push] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | hjeq
    · rw [Array.getElem!_push_lt hjlt]
      simp only [List.map_cons]
      exact List.mem_cons_of_mem _ (hroot j hjlt)
    · subst hjeq
      rw [Array.getElem!_push_eq]
      exact List.mem_map.mpr ⟨newStep, by simp, hpos⟩
  · rw [hrootsPush]
    simp only [Array.size_push]
    exact ⟨fun hc => by simp at hc, fun hc => by omega⟩

/-- `UPDATE` only merges candidates from the top down, so every surviving root is still a frame on the stack. -/
private theorem DijkstraStackRoots.update [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {numMarks : Nat} {aux : DijkstraAux State} {stack : List (DFSStep State Nat)}
    {marks : Std.HashSet Nat} {d : State} (hwf : DijkstraWellFormed aux) (hrwf : DijkstraRootsWF aux)
    (hrpos : 0 < aux.roots.size) (hd : aux.liveIndex.contains d = true)
    (h : DijkstraStackRoots aux stack) :
    DijkstraStackRoots (dijkstraUpdate numMarks aux marks d).1 stack := by
  obtain ⟨lo, hlo_lt, _, hsize, hpre, htop, _⟩ :=
    dijkstraUpdate_merge_locate numMarks aux marks d hwf hrwf hrpos hd
  obtain ⟨hlive, hchain, hroot, hne⟩ := h
  have hliveEq : (dijkstraUpdate numMarks aux marks d).1.live = aux.live :=
    (dijkstraUpdate_fields numMarks aux marks d).1
  refine ⟨fun st hst => by rw [hliveEq]; exact hlive st hst, hchain, fun j hj => ?_, ?_⟩
  · rw [hsize] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | hjeq
    · rw [hpre j hjlt]; exact hroot j (by omega)
    · rw [hjeq, htop]; exact hroot lo hlo_lt
  · rw [hsize]
    exact ⟨fun hemp => absurd (hne.mp hemp) (by omega), fun hz => absurd hz (by omega)⟩

/-- `POP` drops the top frame, and with it the candidate rooted there if the frame was its root. -/
private theorem DijkstraStackRoots.pop [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {aux : DijkstraAux State} {step : DFSStep State Nat} {rest : List (DFSStep State Nat)}
    (hwf : DijkstraRootsWF aux) (h : DijkstraStackRoots aux (step :: rest)) :
    DijkstraStackRoots (dijkstraPop aux step.pos).1 rest := by
  obtain ⟨hlive, hchain, hroot, hne⟩ := h
  have hrpos : 0 < aux.roots.size := by
    rcases Nat.eq_zero_or_pos aux.roots.size with hz | hz
    · exact absurd (hne.mpr hz) (by simp)
    · exact hz
  obtain ⟨r, a, e, hback⟩ : ∃ r a e, aux.roots.back? = some ⟨r, a, e⟩ := by
    rcases hbk : aux.roots.back? with _ | pp
    · exact absurd (Array.back?_eq_none_iff.mp hbk) (by intro he; rw [he] at hrpos; simp at hrpos)
    · exact ⟨pp.root, pp.acc, pp.entry, by simp⟩
  obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hback
  have hridx : aux.roots.size - 1 = ys.size := by rw [hys]; simp
  have hrtop : (aux.roots[aux.roots.size - 1]!).root = r := by rw [hridx, hys, Array.getElem!_push_eq]
  have hjle : ∀ j, j < aux.roots.size → (aux.roots[j]!).root ≤ r := by
    intro j hj
    rcases Nat.lt_or_eq_of_le (show j ≤ aux.roots.size - 1 from by omega) with hlt | heq
    · exact Nat.le_of_lt (hrtop ▸ hwf.rootsMono j (aux.roots.size - 1) hlt (by omega))
    · rw [heq, hrtop]; exact Nat.le_refl _
  have hrle : r ≤ step.pos := by
    obtain ⟨st, hst, hsteq⟩ := List.mem_map.mp (hroot (aux.roots.size - 1) (by omega))
    rw [← hrtop, ← hsteq]; exact hchain.le_head st hst
  have hmemRest : ∀ p, p ∈ (step :: rest).map (·.pos) → p ≠ step.pos → p ∈ rest.map (·.pos) := by
    intro p hp hpne
    simp only [List.map_cons, List.mem_cons] at hp
    exact hp.resolve_left hpne
  have hrestLt : ∀ st ∈ rest, st.pos < step.pos := hchain.lt_head
  unfold dijkstraPop
  rw [hback]
  dsimp only
  by_cases hfl : step.pos = r
  · rw [if_pos hfl]
    dsimp only
    have hflushsize : (liveFlush aux.live aux.liveIndex aux.dead step.pos).1.size = step.pos :=
      liveFlush_size step.pos aux.live aux.liveIndex aux.dead
        (by have := hwf.rootsLt (aux.roots.size - 1) (by omega); omega)
    have hjlt : ∀ j, j < aux.roots.pop.size → (aux.roots.pop[j]!).root < step.pos := by
      intro j hj
      have hjb : j < aux.roots.size := by simp only [Array.size_pop] at hj; omega
      rw [Array.getElem!_pop_lt hj, hfl, ← hrtop]
      exact hwf.rootsMono j (aux.roots.size - 1) (by simp only [Array.size_pop] at hj; omega) (by omega)
    refine ⟨fun st hst => ?_, hchain.tail, fun j hj => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hlive st (List.mem_cons_of_mem _ hst)
      refine ⟨?_, ?_⟩
      · show st.pos < (liveFlush aux.live aux.liveIndex aux.dead step.pos).1.size
        rw [hflushsize]; exact hrestLt st hst
      · show (liveFlush aux.live aux.liveIndex aux.dead step.pos).1[st.pos]! = st.state
        rw [liveFlush_getElem!_lt step.pos aux.live aux.liveIndex aux.dead st.pos (hrestLt st hst)]
        exact h2
    · have hj' : j < aux.roots.pop.size := hj
      show (aux.roots.pop[j]!).root ∈ rest.map (·.pos)
      refine hmemRest _ ?_ (by have := hjlt j hj'; omega)
      have hjb : j < aux.roots.size := by simp only [Array.size_pop] at hj'; omega
      rw [Array.getElem!_pop_lt hj']
      exact hroot j hjb
    · show rest = [] ↔ aux.roots.pop.size = 0
      simp only [Array.size_pop]
      constructor
      · intro hemp
        by_contra hc
        have h2 : aux.roots.size - 2 < aux.roots.size - 1 := by omega
        have hlt2 := hwf.rootsMono (aux.roots.size - 2) (aux.roots.size - 1) h2 (by omega)
        obtain ⟨st, hst, hsteq⟩ := List.mem_map.mp (hroot (aux.roots.size - 2) (by omega))
        rw [hemp] at hst
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
        rw [hst] at hsteq
        rw [hrtop, ← hfl] at hlt2
        omega
      · intro hz
        have hr0 : r = 0 := by rw [← hrtop, show aux.roots.size - 1 = 0 from by omega]; exact hwf.rootsBase (by omega)
        rcases hrest : rest with _ | ⟨t, tl⟩
        · rfl
        · exact absurd (hrestLt t (by rw [hrest]; simp)) (by rw [hfl, hr0]; omega)
  · rw [if_neg hfl]
    dsimp only
    refine ⟨fun st hst => hlive st (List.mem_cons_of_mem _ hst), hchain.tail, fun j hj => ?_, ?_⟩
    · exact hmemRest _ (hroot j hj) (by have := hjle j hj; omega)
    · constructor
      · intro hemp
        exfalso
        obtain ⟨st, hst, hsteq⟩ := List.mem_map.mp (hroot (aux.roots.size - 1) (by omega))
        rw [hemp] at hst
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
        rw [hst, hrtop] at hsteq
        exact hfl hsteq
      · intro hz; omega

/-- The top frame always lies in the top open range. -/
private theorem dijkstraStackRoots_head_mem_top [Inhabited State] [LawfulBEq State]
    {aux : DijkstraAux State} {step : DFSStep State Nat} {rest : List (DFSStep State Nat)}
    (hsr : DijkstraStackRoots aux (step :: rest)) :
    step.state ∈ aux.range (aux.roots.size - 1) := by
  obtain ⟨hlive, hchain, hroot, hne⟩ := hsr
  have hpos : 0 < aux.roots.size := by
    rcases Nat.eq_zero_or_pos aux.roots.size with hz | hz
    · exact absurd (hne.mpr hz) (by simp)
    · exact hz
  obtain ⟨st, hst, hsteq⟩ := List.mem_map.mp (hroot (aux.roots.size - 1) (by omega))
  rw [DijkstraAux.mem_range_iff]
  refine ⟨step.pos, ?_, ?_, (hlive step (by simp)).2⟩
  · show (aux.roots[aux.roots.size - 1]!).root ≤ step.pos
    rw [← hsteq]; exact hchain.le_head st hst
  · have hend : aux.rangeEnd (aux.roots.size - 1) = aux.live.size := by
      unfold DijkstraAux.rangeEnd
      simp only [show ¬ aux.roots.size - 1 + 1 < aux.roots.size from by omega, if_false]
    rw [hend, Nat.min_self]
    exact (hlive step (by simp)).1

private theorem DijkstraAux.rangeStart_mono {aux : DijkstraAux State} (hwf : DijkstraRootsWF aux)
    {i j : Nat} (hij : i < j) (hj : j < aux.roots.size) : aux.rangeStart i < aux.rangeStart j :=
  hwf.rootsMono i j hij hj

private theorem DijkstraAux.rangeStart_le {aux : DijkstraAux State} (hwf : DijkstraRootsWF aux)
    {i j : Nat} (hij : i ≤ j) (hj : j < aux.roots.size) : aux.rangeStart i ≤ aux.rangeStart j := by
  rcases Nat.eq_or_lt_of_le hij with heq | hlt
  · rw [heq]; exact Nat.le_refl _
  · exact Nat.le_of_lt (DijkstraAux.rangeStart_mono hwf hlt hj)

private theorem DijkstraAux.exists_range_index {aux : DijkstraAux State} :
    ∀ k i, k = aux.roots.size - i → i < aux.roots.size → ∀ p, aux.rangeStart i ≤ p → p < aux.live.size →
      ∃ j, i ≤ j ∧ j < aux.roots.size ∧ aux.rangeStart j ≤ p ∧ p < aux.rangeEnd j := by
  intro k
  induction k with
  | zero => intro i hk hi p _ _; exact absurd hk (by omega)
  | succ k ih =>
    intro i hk hi p hp1 hp2
    by_cases hlt : p < aux.rangeEnd i
    · exact ⟨i, Nat.le_refl _, hi, hp1, hlt⟩
    · rw [Nat.not_lt] at hlt
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
  have hpb : p < aux.live.size := Nat.lt_of_lt_of_le hp2 (Nat.min_le_right _ _)
  have hqb : q < aux.live.size := Nat.lt_of_lt_of_le hq2 (Nat.min_le_right _ _)
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
    have hp2' : p < aux.rangeEnd i := Nat.lt_of_lt_of_le hp2 (Nat.min_le_left _ _)
    omega
  · have hend_le : aux.rangeEnd j ≤ aux.rangeStart i := by
      unfold DijkstraAux.rangeEnd
      rw [if_pos (show j + 1 < aux.roots.size from by omega)]
      exact DijkstraAux.rangeStart_le hrwf (by omega) hi
    have hq2' : p < aux.rangeEnd j := Nat.lt_of_lt_of_le hq2 (Nat.min_le_left _ _)
    omega

private theorem DijkstraAux.mem_range_pos [Inhabited State] [LawfulBEq State] {aux : DijkstraAux State}
    (hwf : DijkstraWellFormed aux) {i p : Nat} {x : State} (hx : x ∈ aux.range i)
    (hp : aux.live[p]! = x) (hpb : p < aux.live.size) :
    aux.rangeStart i ≤ p ∧ p < aux.rangeEnd i := by
  rw [DijkstraAux.mem_range_iff] at hx
  obtain ⟨p', hp1, hp2, hp3⟩ := hx
  have hp'b : p' < aux.live.size := Nat.lt_of_lt_of_le hp2 (Nat.min_le_right _ _)
  have h1 := hwf.fwd p' hp'b
  have h2 := hwf.fwd p hpb
  rw [getElem!_pos aux.live p' hp'b] at hp3
  rw [getElem!_pos aux.live p hpb] at hp
  rw [hp3] at h1
  rw [hp] at h2
  have hpp : p' = p := by rw [h1] at h2; exact Option.some.inj h2
  subst hpp
  exact ⟨hp1, Nat.lt_of_lt_of_le hp2 (Nat.min_le_left _ _)⟩

private theorem DijkstraAux.range_le_of_pos_lt {aux : DijkstraAux State} (hrwf : DijkstraRootsWF aux)
    {i j p q : Nat} (hi : i < aux.roots.size) (hpi : aux.rangeStart i ≤ p) (hqj : q < aux.rangeEnd j)
    (hpq : p < q) : i ≤ j := by
  by_contra hc
  rw [Nat.not_le] at hc
  have hend_le : aux.rangeEnd j ≤ aux.rangeStart i := by
    unfold DijkstraAux.rangeEnd
    rw [if_pos (show j + 1 < aux.roots.size from by omega)]
    exact DijkstraAux.rangeStart_le hrwf (by omega) hi
  omega

private theorem dijkstraMerge_range_union [Inhabited State] [LawfulBEq State] {aux aux' : DijkstraAux State}
    {lo : Nat} (hlo : lo < aux.roots.size) (hwf : DijkstraRootsWF aux) (hsize : aux'.roots.size = lo + 1)
    (htop : (aux'.roots[lo]!).root = (aux.roots[lo]!).root) (hlive : aux'.live = aux.live) (x : State) :
    x ∈ aux'.range lo ↔ ∃ i, lo ≤ i ∧ i < aux.roots.size ∧ x ∈ aux.range i := by
  have hstart_eq : aux'.rangeStart lo = aux.rangeStart lo := by
    unfold DijkstraAux.rangeStart
    rw [htop]
  have hend_eq : aux'.rangeEnd lo = aux.live.size := by
    unfold DijkstraAux.rangeEnd
    simp only [hsize, show ¬ lo + 1 < lo + 1 from by omega, if_false, hlive]
  rw [DijkstraAux.mem_range_iff, hstart_eq, hend_eq, hlive]
  constructor
  · rintro ⟨p, hp1, hp2, hp3⟩
    have hp2' : p < aux.live.size := Nat.lt_of_lt_of_le hp2 (Nat.min_le_right _ _)
    obtain ⟨j, hj1, hj2, hj3, hj4⟩ :=
      DijkstraAux.exists_range_index (aux.roots.size - lo) lo rfl hlo p hp1 hp2'
    exact ⟨j, hj1, hj2, (DijkstraAux.mem_range_iff aux j x).mpr ⟨p, hj3, Nat.lt_min.mpr ⟨hj4, hp2'⟩, hp3⟩⟩
  · rintro ⟨i, hloi, hin, hxi⟩
    rw [DijkstraAux.mem_range_iff] at hxi
    obtain ⟨p, hp1, hp2, hp3⟩ := hxi
    have hp2' : p < aux.live.size := Nat.lt_of_lt_of_le hp2 (Nat.min_le_right _ _)
    refine ⟨p, Nat.le_trans (DijkstraAux.rangeStart_le hwf hloi hin) hp1, Nat.lt_min.mpr ⟨hp2', hp2'⟩, hp3⟩

private theorem dijkstraMerge_connected [Inhabited State] [LawfulBEq State]
    {succs : State → Array State} {aux aux' : DijkstraAux State} {lo : Nat}
    (hlo : lo < aux.roots.size) (hwf : DijkstraRootsWF aux) (hsize : aux'.roots.size = lo + 1)
    (htop : (aux'.roots[lo]!).root = (aux.roots[lo]!).root) (hlive : aux'.live = aux.live)
    (hconn : ∀ i, lo ≤ i → i < aux.roots.size → InternallyConnected succs (aux.range i))
    (hchain : ∀ i, lo ≤ i → i + 1 < aux.roots.size →
      ∃ s ∈ aux.range i, ∃ t ∈ aux.range (i + 1), t ∈ succs s)
    (hback : ∃ s ∈ aux.range (aux.roots.size - 1), ∃ t ∈ aux.range lo, t ∈ succs s) :
    InternallyConnected succs (aux'.range lo) := by
  intro s hs t ht
  have hunion : ∀ x, x ∈ aux'.range lo ↔ ∃ i, lo ≤ i ∧ i < aux.roots.size ∧ x ∈ aux.range i :=
    dijkstraMerge_range_union hlo hwf hsize htop hlive
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
    (hlo : lo < aux.roots.size) (hsize : aux'.roots.size = lo + 1)
    (hlive : aux'.live = aux.live) (htop : (aux'.roots[lo]!).root = (aux.roots[lo]!).root)
    (hpre : ∀ i, i < lo → aux'.roots[i]! = aux.roots[i]!) (i : Nat) (hi : i < lo) :
    aux'.range i = aux.range i := by
  have hstart_le : ∀ j, j ≤ lo → aux'.rangeStart j = aux.rangeStart j := by
    intro j hj
    unfold DijkstraAux.rangeStart
    rcases Nat.lt_or_eq_of_le hj with hlt | heq
    · rw [hpre j hlt]
    · rw [heq, htop]
  have hend : aux'.rangeEnd i = aux.rangeEnd i := by
    unfold DijkstraAux.rangeEnd
    rw [if_pos (show i + 1 < aux'.roots.size from by omega), if_pos (show i + 1 < aux.roots.size from by omega),
      hstart_le (i + 1) (by omega)]
  unfold DijkstraAux.range
  rw [hstart_le i (Nat.le_of_lt hi), hend, hlive]

private theorem dijkstraRangeInv_update [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {numMarks : Nat} {aux : DijkstraAux State} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {s d : State}
    (hwf : DijkstraWellFormed aux) (hinv : DijkstraRangeInv succs edgeMarks aux)
    (hroots_pos : 0 < aux.roots.size) (hd_contains : aux.liveIndex.contains d = true)
    (hsmem : s ∈ aux.range (aux.roots.size - 1)) (hdSucc : d ∈ succs s) :
    DijkstraRangeInv succs edgeMarks (dijkstraUpdate numMarks aux (edgeMarks s d) d).1 := by
  set aux' := (dijkstraUpdate numMarks aux (edgeMarks s d) d).1 with haux'def
  have hlive_eq : aux'.live = aux.live := (dijkstraUpdate_fields numMarks aux (edgeMarks s d) d).1
  obtain ⟨lo, hlo_lt, hd_range, haux'size, haux'pre, haux'top, haux'entry⟩ :=
    dijkstraUpdate_merge_locate numMarks aux (edgeMarks s d) d hwf hinv.rootsWF hroots_pos hd_contains
  rw [← haux'def] at haux'size haux'pre haux'top haux'entry
  have hwfRoots' : DijkstraRootsWF aux' :=
    dijkstraRootsWF_update numMarks aux (edgeMarks s d) d hinv.rootsWF
  have hunion : ∀ x, x ∈ aux'.range lo ↔ ∃ i, lo ≤ i ∧ i < aux.roots.size ∧ x ∈ aux.range i :=
    dijkstraMerge_range_union hlo_lt hinv.rootsWF haux'size haux'top hlive_eq
  have hprefix_eq : ∀ i, i < lo → aux'.range i = aux.range i :=
    fun i hi => dijkstraMerge_range_prefix_eq hlo_lt haux'size hlive_eq haux'top haux'pre i hi
  have haux'startLo : aux'.rangeStart lo = aux.rangeStart lo := by
    unfold DijkstraAux.rangeStart; rw [haux'top]
  have haux'endLo : aux'.rangeEnd lo = aux.live.size := by
    unfold DijkstraAux.rangeEnd
    simp only [show ¬ lo + 1 < aux'.roots.size from by omega, if_false, hlive_eq]
  refine ⟨hwfRoots', ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [haux'size] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
    · rw [hprefix_eq i hilt]; exact hinv.connected i (by omega)
    · rw [hieq]
      exact dijkstraMerge_connected hlo_lt hinv.rootsWF haux'size haux'top hlive_eq
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
      exact ⟨t, (hprefix_eq i hilt) ▸ ht, u, hieq ▸ (hunion u).mpr ⟨lo, Nat.le_refl _, hlo_lt, hieq ▸ hu⟩, htu⟩
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
          d, (hunion d).mpr ⟨lo, Nat.le_refl _, hlo_lt, hd_range⟩, hdSucc, marksToBitmask_mem hm'⟩
      -- an absorbed range's own bitmask already named an edge internal to it
      · intro k hk1 hk2 m' hm'
        obtain ⟨t, ht, u, hu, htu, hmk⟩ := hinv.bitSound k hk2 m' hm'
        exact ⟨t, (hunion t).mpr ⟨k, hk1, hk2, ht⟩, u, (hunion u).mpr ⟨k, hk1, hk2, hu⟩, htu, hmk⟩
      -- an absorbed root's entry marks name the tree edge running in from the range just below it
      · intro k hk1 hk2 m' hm'
        obtain ⟨hkpos, t, ht, u, hu, htu, hmk⟩ := hinv.entrySound k hk2 m' hm'
        exact ⟨t, (hunion t).mpr ⟨k - 1, by omega, by omega, ht⟩,
          u, (hunion u).mpr ⟨k, Nat.le_of_lt hk1, hk2, hu⟩, htu, hmk⟩
  -- the surviving root keeps its own entry marks, and the range just below it is untouched by the merge
  · intro i hi m hm
    rw [haux'size] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
    · rw [haux'pre i hilt] at hm
      obtain ⟨hipos, t, ht, u, hu, htu, hmk⟩ := hinv.entrySound i (by omega) m hm
      exact ⟨hipos, t, (hprefix_eq (i - 1) (by omega)) ▸ ht, u, (hprefix_eq i hilt) ▸ hu, htu, hmk⟩
    · rw [hieq] at hm ⊢
      rw [haux'entry] at hm
      obtain ⟨hipos, t, ht, u, hu, htu, hmk⟩ := hinv.entrySound lo hlo_lt m hm
      exact ⟨hipos, t, (hprefix_eq (lo - 1) (by omega)) ▸ ht,
        u, (hunion u).mpr ⟨lo, Nat.le_refl _, hlo_lt, hu⟩, htu, hmk⟩

private theorem dijkstraPush_rangeStart_eq [Inhabited State] (aux : DijkstraAux State) (q : State)
    (marks : Std.HashSet Nat) (i : Nat) (hi : i < aux.roots.size) :
    (dijkstraPush aux q marks).1.rangeStart i = aux.rangeStart i := by
  unfold DijkstraAux.rangeStart dijkstraPush
  simp only
  rw [Array.getElem!_push_lt hi]

private theorem dijkstraPush_rangeEnd_eq [Inhabited State] (aux : DijkstraAux State) (q : State)
    (marks : Std.HashSet Nat) (i : Nat) (hi : i < aux.roots.size) :
    (dijkstraPush aux q marks).1.rangeEnd i = aux.rangeEnd i := by
  have hsize : (dijkstraPush aux q marks).1.roots.size = aux.roots.size + 1 := by
    unfold dijkstraPush; simp only [Array.size_push]
  by_cases hlt : i + 1 < aux.roots.size
  · unfold DijkstraAux.rangeEnd
    simp only [hlt, if_true, show i + 1 < (dijkstraPush aux q marks).1.roots.size from by omega, if_true]
    exact dijkstraPush_rangeStart_eq aux q marks (i + 1) hlt
  · have hi' : i = aux.roots.size - 1 := by omega
    unfold DijkstraAux.rangeEnd
    simp only [hlt, if_false, show i + 1 < (dijkstraPush aux q marks).1.roots.size from by omega, if_true]
    unfold DijkstraAux.rangeStart dijkstraPush
    simp only
    rw [show i + 1 = aux.roots.size from by omega, Array.getElem!_push_eq]

private theorem dijkstraRangeEnd_le_live [Inhabited State] (aux : DijkstraAux State) (hwf : DijkstraRootsWF aux)
    (i : Nat) : aux.rangeEnd i ≤ aux.live.size := by
  unfold DijkstraAux.rangeEnd
  by_cases h : i + 1 < aux.roots.size
  · simp only [h, if_true]
    exact Nat.le_of_lt (hwf.rootsLt (i + 1) h)
  · simp only [h, if_false, Nat.le_refl]

private theorem dijkstraPush_range_mem_iff [Inhabited State] [LawfulBEq State] (aux : DijkstraAux State)
    (q : State) (marks : Std.HashSet Nat) (hwf : DijkstraRootsWF aux) (i : Nat) (hi : i < aux.roots.size)
    (x : State) : x ∈ (dijkstraPush aux q marks).1.range i ↔ x ∈ aux.range i := by
  rw [DijkstraAux.mem_range_iff, DijkstraAux.mem_range_iff,
    dijkstraPush_rangeStart_eq aux q marks i hi, dijkstraPush_rangeEnd_eq aux q marks i hi]
  have hend_le := dijkstraRangeEnd_le_live aux hwf i
  have hlive_size : (dijkstraPush aux q marks).1.live.size = aux.live.size + 1 := by
    unfold dijkstraPush; simp only [Array.size_push]
  have hlive_eq : (dijkstraPush aux q marks).1.live = aux.live.push q := by unfold dijkstraPush; rfl
  constructor
  · rintro ⟨p, hp1, hp2, hp3⟩
    have hp2' : p < aux.rangeEnd i := Nat.lt_of_lt_of_le hp2 (Nat.min_le_left _ _)
    refine ⟨p, hp1, Nat.lt_min.mpr ⟨hp2', by omega⟩, ?_⟩
    rwa [hlive_eq, Array.getElem!_push_lt (by omega)] at hp3
  · rintro ⟨p, hp1, hp2, hp3⟩
    have hp2' : p < aux.rangeEnd i := Nat.lt_of_lt_of_le hp2 (Nat.min_le_left _ _)
    refine ⟨p, hp1, Nat.lt_min.mpr ⟨hp2', by omega⟩, ?_⟩
    rwa [hlive_eq, Array.getElem!_push_lt (by omega)]

private theorem dijkstraPush_range_eq [Inhabited State] (aux : DijkstraAux State) (q : State)
    (marks : Std.HashSet Nat) (hwf : DijkstraRootsWF aux) (i : Nat) (hi : i < aux.roots.size) :
    (dijkstraPush aux q marks).1.range i = aux.range i := by
  unfold DijkstraAux.range
  rw [dijkstraPush_rangeStart_eq aux q marks i hi, dijkstraPush_rangeEnd_eq aux q marks i hi]
  have hend_le := dijkstraRangeEnd_le_live aux hwf i
  have hlive_eq : (dijkstraPush aux q marks).1.live = aux.live.push q := by unfold dijkstraPush; rfl
  rw [hlive_eq, Array.extract_push_of_le hend_le]

private theorem dijkstraGetStatus_unknown_not_mem_range [Inhabited State] [LawfulBEq State]
    {aux : DijkstraAux State} (hwf : DijkstraWellFormed aux) {d : State}
    (hd : dijkstraGetStatus aux d = .unknown) (i : Nat) : d ∉ aux.range i := by
  intro hmem
  rw [DijkstraAux.mem_range_iff] at hmem
  obtain ⟨p, hp1, hp2, hp3⟩ := hmem
  have hpb : p < aux.live.size := Nat.lt_of_lt_of_le hp2 (Nat.min_le_right _ _)
  have hlk := hwf.fwd p hpb
  rw [getElem!_pos aux.live p hpb] at hp3
  rw [hp3] at hlk
  unfold dijkstraGetStatus liveStatusOf at hd
  simp only [Std.HashMap.contains_eq_isSome_getElem?, hlk] at hd
  simp at hd

private theorem dijkstraGetStatus_dead_not_mem_range [Inhabited State] [LawfulBEq State]
    {aux : DijkstraAux State} (hwf : DijkstraWellFormed aux) {d : State}
    (hd : dijkstraGetStatus aux d = .dead) (i : Nat) : d ∉ aux.range i := by
  intro hmem
  rw [DijkstraAux.mem_range_iff] at hmem
  obtain ⟨p, hp1, hp2, hp3⟩ := hmem
  have hpb : p < aux.live.size := Nat.lt_of_lt_of_le hp2 (Nat.min_le_right _ _)
  have hlk := hwf.fwd p hpb
  rw [getElem!_pos aux.live p hpb] at hp3
  rw [hp3] at hlk
  unfold dijkstraGetStatus liveStatusOf at hd
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
    have hp2' : p < aux.live.size + 1 := Nat.lt_of_lt_of_le hp2 (Nat.min_le_left _ _)
    have hpeq : p = aux.live.size := by omega
    rw [hpeq, hlive_eq, Array.getElem!_push_eq] at hp3
    exact hp3.symm
  · rintro rfl
    exact ⟨aux.live.size, Nat.le_refl _, Nat.lt_min.mpr ⟨by omega, by omega⟩,
      by rw [hlive_eq, Array.getElem!_push_eq]⟩

/-! ## Witness extraction and the `DFSOps` instance -/

/-- `sccHint`: the top open range, which after a report is an accepting, not necessarily maximal, SCC. -/
@[expose] def dijkstraSccHint (aux : DijkstraAux State) : Std.HashSet State :=
  match aux.roots.back? with
  | none => Std.HashSet.emptyWithCapacity 0
  | some ⟨startPos, _, _⟩ =>
    (aux.live.extract startPos aux.live.size).foldl
      (init := Std.HashSet.emptyWithCapacity 0) fun acc s => acc.insert s

/-- The hint is exactly the top open range, whose upper end is `live.size` since no range follows it. -/
theorem dijkstraSccHint_eq_top_range [Inhabited State] (aux : DijkstraAux State)
    (hpos : 0 < aux.roots.size) :
    dijkstraSccHint aux = aux.range (aux.roots.size - 1) := by
  unfold dijkstraSccHint DijkstraAux.range
  have hend : aux.rangeEnd (aux.roots.size - 1) = aux.live.size := by
    unfold DijkstraAux.rangeEnd
    simp only [show ¬ aux.roots.size - 1 + 1 < aux.roots.size from by omega, if_false]
  rcases hb : aux.roots.back? with _ | ⟨r, a, e⟩
  · exact absurd (Array.back?_eq_none_iff.mp hb) (by intro he; rw [he] at hpos; simp at hpos)
  · obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb
    have hidx : aux.roots.size - 1 = ys.size := by rw [hys]; simp
    have hr : (aux.roots[aux.roots.size - 1]!).root = r := by rw [hidx, hys, Array.getElem!_push_eq]
    dsimp only
    rw [hend]
    unfold DijkstraAux.rangeStart
    rw [hr]

-- `implicit_reducible` so that `Aux` and `Position` read through the wrapper at `instances`
-- transparency, which is what Lean checks implicit arguments at since v4.32.
@[expose, implicit_reducible] def dijkstraOps (numMarks : Nat) : DFSOps State where
  Aux := DijkstraAux State
  Position := Nat
  initAux := dijkstraInitAux
  sccHint := dijkstraSccHint
  -- `dead` and `live` are disjoint, so this counts every state ever pushed
  numExplored := fun aux => aux.live.size + aux.dead.size
  getStatus := dijkstraGetStatus
  push := dijkstraPush
  update := dijkstraUpdate numMarks
  -- POP only needs the popped frame's `live` position
  pop := fun _succs _edgeMarks aux step => dijkstraPop aux step.pos

/-- `dijkstraOps` is a lawful refinement: PUSH, UPDATE and POP preserve `DijkstraWellFormed`, and the three status laws
hold. -/
def dijkstraLawful [Inhabited State] [LawfulBEq State] [LawfulHashable State] (numMarks : Nat) :
    LawfulDFSOps (dijkstraOps numMarks) (State := State) where
  WellFormed := DijkstraWellFormed
  wf_push := fun aux q marks hq hwf => dijkstraWellFormed_push aux q marks hwf hq
  wf_update := dijkstraWellFormed_update numMarks
  wf_pop := fun _succs _edgeMarks aux step hwf => dijkstraWellFormed_pop aux step.pos hwf
  push_status := dijkstraPush_status
  update_status := dijkstraUpdate_status numMarks
  pop_status := fun _succs _edgeMarks aux step q hwf => dijkstraPop_status aux step.pos hwf q

/-- `dfsGo_ne_none` for `dijkstraOps`. -/
theorem dijkstraOps_ne_none [Inhabited State] [LawfulBEq State] [LawfulHashable State] (numMarks : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State) (fr : FiniteReach initialStates succs)
    (aux : DijkstraAux State) (stack : List (DFSStep State Nat)) (hwf : DijkstraWellFormed aux)
    (hsucc : ∀ st ∈ stack, st.succ = succs st.state)
    (hreach : ∀ st ∈ stack, Reachable initialStates succs st.state) :
    dfsGo (dijkstraOps numMarks) succs edgeMarks expand aux stack ≠ none :=
  dfsGo_ne_none (dijkstraOps numMarks) succs edgeMarks expand hexp initialStates fr (dijkstraLawful numMarks)
    aux stack hwf hsucc hreach

/-- `dijkstraOps_ne_none` for one fresh root pushed onto a well-formed state. -/
theorem dijkstraOps_root_ne_none [Inhabited State] [LawfulBEq State] [LawfulHashable State] (numMarks : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State) (fr : FiniteReach initialStates succs) :
    ∀ aux q, Reachable initialStates succs q → DijkstraWellFormed aux →
      dijkstraGetStatus aux q = .unknown →
      dfsGo (dijkstraOps numMarks) succs edgeMarks expand
        (dijkstraPush aux q (Std.HashSet.emptyWithCapacity 0)).1
        [({ state := q, pos := (dijkstraPush aux q (Std.HashSet.emptyWithCapacity 0)).2,
            acc := 0, succ := (expand q).1, succMarks := (expand q).2.1, succOpts := (expand q).2.2, idx := 0 } :
          DFSStep State Nat)] ≠ none := by
  intro aux q hqreach hwf hq
  refine dijkstraOps_ne_none numMarks succs edgeMarks expand hexp initialStates fr _ _
    (dijkstraWellFormed_push aux q _ hwf hq) ?_ ?_
  · intro st hst; rcases List.mem_singleton.mp hst with rfl; exact hexp.fst q
  · intro st hst; rcases List.mem_singleton.mp hst with rfl; exact hqreach

/-- `genericDFS_closed` for `dijkstraOps`. -/
theorem dijkstraOps_closed [Inhabited State] [LawfulBEq State] [LawfulHashable State] (numMarks : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State) (fr : FiniteReach initialStates succs)
    (roots : List State) (aux : DijkstraAux State)
    (hrootsReach : ∀ q ∈ roots, Reachable initialStates succs q)
    (hnone : (genericDFS (dijkstraOps numMarks) succs edgeMarks expand roots aux).1 = none)
    (hwf : DijkstraWellFormed aux)
    (hClosed : ∀ t, dijkstraGetStatus aux t ≠ .unknown → ∀ x ∈ succs t, dijkstraGetStatus aux x ≠ .unknown) :
    DijkstraWellFormed (genericDFS (dijkstraOps numMarks) succs edgeMarks expand roots aux).2 ∧
      ∀ t, dijkstraGetStatus (genericDFS (dijkstraOps numMarks) succs edgeMarks expand roots aux).2 t
          ≠ .unknown →
        ∀ x ∈ succs t, dijkstraGetStatus
          (genericDFS (dijkstraOps numMarks) succs edgeMarks expand roots aux).2 x ≠ .unknown :=
  genericDFS_closed (dijkstraOps numMarks) succs edgeMarks expand hexp (dijkstraLawful numMarks)
    (Reachable initialStates succs)
    (fun aux q hq hwf hgs => dijkstraOps_root_ne_none numMarks succs edgeMarks expand hexp initialStates fr aux q hq hwf hgs)
    roots aux hrootsReach (genericDFSGo_ne_none (dijkstraOps numMarks) succs edgeMarks expand roots aux)
    hnone hwf hClosed

/-- `genericDFS_returns_none_fully_explored` for `dijkstraOps`. -/
theorem dijkstraOps_returns_none_fully_explored [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (numMarks : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State) (fr : FiniteReach initialStates succs)
    (hnone : (genericDFS (dijkstraOps numMarks) succs edgeMarks expand initialStates
      dijkstraInitAux).1 = none) :
    ∀ s, Reachable initialStates succs s →
      dijkstraGetStatus (genericDFS (dijkstraOps numMarks) succs edgeMarks expand initialStates
        dijkstraInitAux).2 s ≠ .unknown :=
  genericDFS_returns_none_fully_explored (dijkstraOps numMarks) succs edgeMarks expand hexp (dijkstraLawful numMarks)
    (Reachable initialStates succs)
    (fun aux q hq hwf hgs => dijkstraOps_root_ne_none numMarks succs edgeMarks expand hexp initialStates fr aux q hq hwf hgs)
    initialStates (fun _ hq => Reachable.base hq)
    (genericDFSGo_ne_none (dijkstraOps numMarks) succs edgeMarks expand _ _)
    dijkstraWellFormed_init dijkstraGetStatus_initAux hnone

/-! ## Completeness: no accepting SCC survives an empty search -/

private theorem dijkstraPop_found_false (aux : DijkstraAux State) (pos : Nat) :
    (dijkstraPop aux pos).2 = false := by
  unfold dijkstraPop
  cases aux.roots.back? with
  | none => rfl
  | some x =>
    obtain ⟨r, _, _⟩ := x
    dsimp only
    by_cases h : pos = r
    · rw [if_pos h]
    · rw [if_neg h]

private theorem dijkstraPop_rangeStart_eq_of_not_flush [Inhabited State] {aux : DijkstraAux State}
    {pos r0 a0 e0 : Nat} (hback : aux.roots.back? = some ⟨r0, a0, e0⟩) (hflush : ¬ pos = r0) (i : Nat) :
    (dijkstraPop aux pos).1.rangeStart i = aux.rangeStart i := by
  unfold DijkstraAux.rangeStart dijkstraPop
  rw [hback]
  dsimp only
  rw [if_neg hflush]

private theorem dijkstraPop_rangeEnd_eq_of_not_flush [Inhabited State] {aux : DijkstraAux State}
    {pos r0 a0 e0 : Nat} (hback : aux.roots.back? = some ⟨r0, a0, e0⟩) (hflush : ¬ pos = r0) (i : Nat) :
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
    exact dijkstraPop_rangeStart_eq_of_not_flush hback hflush (i + 1)
  · simp only [hlt, if_false]
    unfold dijkstraPop
    rw [hback]
    dsimp only
    rw [if_neg hflush]

private theorem dijkstraPop_range_eq_of_not_flush [Inhabited State] {aux : DijkstraAux State}
    {pos r0 a0 e0 : Nat} (hback : aux.roots.back? = some ⟨r0, a0, e0⟩) (hflush : ¬ pos = r0) (i : Nat) :
    (dijkstraPop aux pos).1.range i = aux.range i := by
  unfold DijkstraAux.range
  rw [dijkstraPop_rangeStart_eq_of_not_flush hback hflush i,
    dijkstraPop_rangeEnd_eq_of_not_flush hback hflush i]
  have hliveEq : (dijkstraPop aux pos).1.live = aux.live := by
    unfold dijkstraPop
    rw [hback]
    dsimp only
    rw [if_neg hflush]
  rw [hliveEq]

private theorem dijkstraPop_rangeStart_eq_of_flush [Inhabited State] {aux : DijkstraAux State}
    {pos r0 a0 e0 : Nat} (hback : aux.roots.back? = some ⟨r0, a0, e0⟩) (hflush : pos = r0)
    (i : Nat) (hi : i < aux.roots.size - 1) :
    (dijkstraPop aux pos).1.rangeStart i = aux.rangeStart i := by
  have hpsize : aux.roots.pop.size = aux.roots.size - 1 := Array.size_pop
  unfold DijkstraAux.rangeStart dijkstraPop
  rw [hback]
  dsimp only
  rw [if_pos hflush]
  dsimp only
  rw [Array.getElem!_pop_lt (by omega)]

private theorem dijkstraPop_rangeEnd_eq_of_flush [Inhabited State] {aux : DijkstraAux State}
    {pos r0 a0 e0 : Nat} (hback : aux.roots.back? = some ⟨r0, a0, e0⟩) (hflush : pos = r0)
    (hposle : pos ≤ aux.live.size) (i : Nat) (hi : i < aux.roots.size - 1) :
    (dijkstraPop aux pos).1.rangeEnd i = aux.rangeEnd i := by
  have hsizeEq : (dijkstraPop aux pos).1.roots.size = aux.roots.size - 1 := by
    unfold dijkstraPop
    rw [hback]
    dsimp only
    rw [if_pos hflush]
    simp only [Array.size_pop]
  obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hback
  have hridx : aux.roots.size - 1 = ys.size := by rw [hys]; simp
  have hrtop : (aux.roots[aux.roots.size - 1]!).root = r0 := by rw [hridx, hys, Array.getElem!_push_eq]
  by_cases hlt : i + 1 < aux.roots.size - 1
  · have hendEq : aux.rangeEnd i = aux.rangeStart (i + 1) := by
      unfold DijkstraAux.rangeEnd
      rw [if_pos (by omega : i + 1 < aux.roots.size)]
    rw [hendEq]
    unfold DijkstraAux.rangeEnd
    rw [hsizeEq, if_pos hlt]
    exact dijkstraPop_rangeStart_eq_of_flush hback hflush (i + 1) hlt
  · have hieq : i + 1 = aux.roots.size - 1 := by omega
    have hendEq : aux.rangeEnd i = pos := by
      unfold DijkstraAux.rangeEnd
      rw [if_pos (by omega : i + 1 < aux.roots.size), hieq]
      unfold DijkstraAux.rangeStart
      rw [hrtop]; exact hflush.symm
    have hendEq' : (dijkstraPop aux pos).1.rangeEnd i = (dijkstraPop aux pos).1.live.size := by
      unfold DijkstraAux.rangeEnd
      rw [hsizeEq, if_neg hlt]
    have hlivesizeeq : (dijkstraPop aux pos).1.live.size = pos := by
      unfold dijkstraPop
      rw [hback]
      dsimp only
      rw [if_pos hflush]
      dsimp only
      exact liveFlush_size pos aux.live aux.liveIndex aux.dead hposle
    rw [hendEq', hlivesizeeq, hendEq]

private theorem dijkstraPop_range_mem_iff_of_flush [Inhabited State] [LawfulBEq State] {aux : DijkstraAux State}
    {pos r0 a0 e0 : Nat} (hwf : DijkstraRootsWF aux) (hback : aux.roots.back? = some ⟨r0, a0, e0⟩)
    (hflush : pos = r0) (hposle : pos ≤ aux.live.size)
    (i : Nat) (hi : i < aux.roots.size - 1) (x : State) :
    x ∈ (dijkstraPop aux pos).1.range i ↔ x ∈ aux.range i := by
  have hstartEq := dijkstraPop_rangeStart_eq_of_flush (pos := pos) hback hflush i hi
  have hendEq := dijkstraPop_rangeEnd_eq_of_flush hback hflush hposle i hi
  have hlivesizeeq : (dijkstraPop aux pos).1.live.size = pos := by
    unfold dijkstraPop
    rw [hback]
    dsimp only
    rw [if_pos hflush]
    dsimp only
    exact liveFlush_size pos aux.live aux.liveIndex aux.dead hposle
  obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hback
  have hridx : aux.roots.size - 1 = ys.size := by rw [hys]; simp
  have hrtop : (aux.roots[aux.roots.size - 1]!).root = r0 := by rw [hridx, hys, Array.getElem!_push_eq]
  have hstartTop : aux.rangeStart (aux.roots.size - 1) = pos := by
    unfold DijkstraAux.rangeStart
    rw [hrtop]; exact hflush.symm
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
    exact liveFlush_getElem!_lt pos aux.live aux.liveIndex aux.dead p hp
  rw [DijkstraAux.mem_range_iff, DijkstraAux.mem_range_iff, hstartEq, hendEq, hlivesizeeq]
  constructor
  · rintro ⟨p, hp1, hp2, hp3⟩
    have hple : p < pos := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hp2 (Nat.min_le_left _ _)) hendLe
    exact ⟨p, hp1, Nat.lt_min.mpr ⟨Nat.lt_of_lt_of_le hp2 (Nat.min_le_left _ _), Nat.lt_of_lt_of_le hple hposle⟩,
      (haux'live p hple) ▸ hp3⟩
  · rintro ⟨p, hp1, hp2, hp3⟩
    have hple : p < pos := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hp2 (Nat.min_le_left _ _)) hendLe
    exact ⟨p, hp1, Nat.lt_min.mpr ⟨Nat.lt_of_lt_of_le hp2 (Nat.min_le_left _ _), hple⟩, (haux'live p hple).symm ▸ hp3⟩

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
  unfold dijkstraGetStatus liveStatusOf
  simp [Std.HashMap.contains_eq_isSome_getElem?, hfwd]

set_option maxHeartbeats 4000000 in
/-- Through a `dfsGo` run, `dead` stays disjoint from every `AcceptingSCC`, a run without a witness ends idle, and a
reported hint is an accepting SCC. -/
theorem dijkstra_dead_not_accepting [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    :
    ∀ aux (stack : List (DFSStep State Nat)) (r : Option (State × List State) × DijkstraAux State),
    dfsGo (dijkstraOps numMarks) succs edgeMarks expand aux stack = some r →
    DijkstraWellFormed aux →
    (∀ st ∈ stack, st.succ = succs st.state) →
    -- `DFSStep.marks` is `edgeMarks state`, applied once at push; see `GenericDFS.dfsGo`
    (∀ st ∈ stack, st.succMarks = st.succ.map (edgeMarks st.state)) →
    -- a dispatched edge never leaves its target unknown
    (∀ st ∈ stack, ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux x ≠ .unknown) →
    (∀ st ∈ stack, Reachable initialStates succs st.state) →
    DijkstraRangeInv succs edgeMarks aux →
    DijkstraStackRoots aux stack →
    -- a retired range member's edges stay in the range or point at dead states
    (∀ i, i < aux.roots.size → ∀ t ∈ aux.range i, (∀ st ∈ stack, st.state ≠ t) →
      ∀ x ∈ succs t, dijkstraGetStatus aux x ≠ .unknown →
        x ∈ aux.range i ∨ dijkstraGetStatus aux x = .dead) →
    -- retired members are fully dispatched, nothing unknown left behind them
    (∀ i, i < aux.roots.size → ∀ t ∈ aux.range i, (∀ st ∈ stack, st.state ≠ t) →
      ∀ x ∈ succs t, dijkstraGetStatus aux x ≠ .unknown) →
    -- bitmask completeness, an internal edge's marks are already on the range
    (∀ i, i < aux.roots.size → ∀ t ∈ aux.range i, (∀ st ∈ stack, st.state ≠ t) →
      ∀ x ∈ succs t, x ∈ aux.range i → ∀ m ∈ edgeMarks t x, (aux.roots[i]!).acc.testBit m = true) →
    -- same for a still-open frame's dispatched prefix
    (∀ st ∈ stack, ∀ x ∈ (st.succ.toList.take st.idx), ∀ i, i < aux.roots.size →
      x ∈ aux.range i → st.state ∈ aux.range i → ∀ m ∈ edgeMarks st.state x,
        (aux.roots[i]!).acc.testBit m = true) →
    -- a dispatched live successor either shares a range or sits higher on the stack
    (∀ st ∈ stack, ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux x = .live →
      (∃ i, i < aux.roots.size ∧ st.state ∈ aux.range i ∧ x ∈ aux.range i) ∨
      (∃ st' ∈ stack, st'.state = x ∧ Nat.lt st.pos st'.pos)) →
    -- cross-frame edge marks land on the target range's bitmask or on its entry
    (∀ st ∈ stack, ∀ st' ∈ stack, st'.state ∈ (st.succ.toList.take st.idx) → Nat.lt st.pos st'.pos →
      ∀ j, j < aux.roots.size → st'.state ∈ aux.range j → ∀ m ∈ edgeMarks st.state st'.state,
        (aux.roots[j]!).acc.testBit m = true ∨ (aux.roots[j]!).entry.testBit m = true) →
    -- only pending edges point back into the path
    NoBackDispatch stack →
    (∀ i : Nat, (aux.roots[i]!).acc < 2 ^ numMarks) →
    (∀ i : Nat, (aux.roots[i]!).entry < 2 ^ numMarks) →
    -- a range whose bitmask already reads all-ones has no internal edge yet
    (∀ i, i < aux.roots.size → (aux.roots[i]!).acc ≠ (1 <<< numMarks) - 1 ∨
      DijkstraNoInternalEdge succs aux stack i) →
    -- the conclusion carried through the induction
    (∀ s ∈ aux.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) →
    (∀ s ∈ r.2.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) ∧
    (r.1 = none → DijkstraWellFormed r.2 ∧ DijkstraRangeInv succs edgeMarks r.2 ∧ r.2.roots.size = 0) ∧
    (∀ anchor stem, r.1 = some (anchor, stem) →
      InternallyConnected succs (dijkstraSccHint r.2) ∧
      AcceptingMarks succs edgeMarks numMarks (dijkstraSccHint r.2) ∧
      anchor ∈ dijkstraSccHint r.2) := by
  refine dfsGo.partial_correctness (dijkstraOps numMarks) succs edgeMarks expand
    (fun aux stack r =>
      DijkstraWellFormed aux →
      (∀ st ∈ stack, st.succ = succs st.state) →
      (∀ st ∈ stack, st.succMarks = st.succ.map (edgeMarks st.state)) →
      (∀ st ∈ stack, ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux x ≠ .unknown) →
      (∀ st ∈ stack, Reachable initialStates succs st.state) →
      DijkstraRangeInv succs edgeMarks aux →
      DijkstraStackRoots aux stack →
      (∀ i, i < aux.roots.size → ∀ t ∈ aux.range i, (∀ st ∈ stack, st.state ≠ t) →
        ∀ x ∈ succs t, dijkstraGetStatus aux x ≠ .unknown →
          x ∈ aux.range i ∨ dijkstraGetStatus aux x = .dead) →
      (∀ i, i < aux.roots.size → ∀ t ∈ aux.range i, (∀ st ∈ stack, st.state ≠ t) →
        ∀ x ∈ succs t, dijkstraGetStatus aux x ≠ .unknown) →
      (∀ i, i < aux.roots.size → ∀ t ∈ aux.range i, (∀ st ∈ stack, st.state ≠ t) →
        ∀ x ∈ succs t, x ∈ aux.range i → ∀ m ∈ edgeMarks t x, (aux.roots[i]!).acc.testBit m = true) →
      (∀ st ∈ stack, ∀ x ∈ (st.succ.toList.take st.idx), ∀ i, i < aux.roots.size →
        x ∈ aux.range i → st.state ∈ aux.range i → ∀ m ∈ edgeMarks st.state x,
          (aux.roots[i]!).acc.testBit m = true) →
      (∀ st ∈ stack, ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux x = .live →
        (∃ i, i < aux.roots.size ∧ st.state ∈ aux.range i ∧ x ∈ aux.range i) ∨
        (∃ st' ∈ stack, st'.state = x ∧ Nat.lt st.pos st'.pos)) →
      (∀ st ∈ stack, ∀ st' ∈ stack, st'.state ∈ (st.succ.toList.take st.idx) → Nat.lt st.pos st'.pos →
        ∀ j, j < aux.roots.size → st'.state ∈ aux.range j → ∀ m ∈ edgeMarks st.state st'.state,
          (aux.roots[j]!).acc.testBit m = true ∨ (aux.roots[j]!).entry.testBit m = true) →
      NoBackDispatch stack →
      (∀ i : Nat, (aux.roots[i]!).acc < 2 ^ numMarks) →
      (∀ i : Nat, (aux.roots[i]!).entry < 2 ^ numMarks) →
      (∀ i, i < aux.roots.size → (aux.roots[i]!).acc ≠ (1 <<< numMarks) - 1 ∨
        DijkstraNoInternalEdge succs aux stack i) →
      (∀ s ∈ aux.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) →
      (∀ s ∈ r.2.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) ∧
      (r.1 = none → DijkstraWellFormed r.2 ∧ DijkstraRangeInv succs edgeMarks r.2 ∧ r.2.roots.size = 0) ∧
      (∀ anchor stem, r.1 = some (anchor, stem) →
        InternallyConnected succs (dijkstraSccHint r.2) ∧
        AcceptingMarks succs edgeMarks numMarks (dijkstraSccHint r.2) ∧
        anchor ∈ dijkstraSccHint r.2)) ?_
  intro go ih aux stack r hr
  cases stack with
  | nil =>
    simp only [Option.some.injEq] at hr
    intro hwf _ _ _ _ hrangeinv hstackdfs _ _ _ _ _ _ _ _ _ _ hdead
    rw [← hr]
    exact ⟨hdead, fun _ => ⟨hwf, hrangeinv, hstackdfs.2.2.2.mp rfl⟩,
      fun _ _ h => absurd h (by simp)⟩
  | cons step rest =>
  intro hwf hsucceq hmk hprefix hreach hrangeinv hstackdfs hrangeclosed hdispatched hmarksClosed hmarksOpen hmerged
    hTreeMarks hNoBack hrootsBound hentryBound hrootsNotFull hdead
  have hstepSuccEq : step.succ = succs step.state := hsucceq step (by simp)
  have hrestSuccEq : ∀ st ∈ rest, st.succ = succs st.state :=
    fun st hst => hsucceq st (List.mem_cons_of_mem _ hst)
  have hstepPrefix : ∀ x ∈ (step.succ.toList.take step.idx), dijkstraGetStatus aux x ≠ .unknown :=
    hprefix step (by simp)
  have hrestPrefix : ∀ st ∈ rest, ∀ x ∈ (st.succ.toList.take st.idx), dijkstraGetStatus aux x ≠ .unknown :=
    fun st hst => hprefix st (List.mem_cons_of_mem _ hst)
  have hstepMarksOpen : ∀ x ∈ (step.succ.toList.take step.idx), ∀ i, i < aux.roots.size →
      x ∈ aux.range i → step.state ∈ aux.range i → ∀ m ∈ edgeMarks step.state x,
        (aux.roots[i]!).acc.testBit m = true :=
    hmarksOpen step (by simp)
  have hrestMarksOpen : ∀ st ∈ rest, ∀ x ∈ (st.succ.toList.take st.idx), ∀ i, i < aux.roots.size →
      x ∈ aux.range i → st.state ∈ aux.range i → ∀ m ∈ edgeMarks st.state x,
        (aux.roots[i]!).acc.testBit m = true :=
    fun st hst => hmarksOpen st (List.mem_cons_of_mem _ hst)
  have hne0 : 0 < aux.roots.size := by
    rcases Nat.eq_zero_or_pos aux.roots.size with hz | hz
    · exact absurd (hstackdfs.2.2.2.mpr hz) (by simp)
    · exact hz
  have hstepMem : step.state ∈ aux.range (aux.roots.size - 1) :=
    dijkstraStackRoots_head_mem_top hstackdfs
  have hrestPosLt : ∀ st ∈ rest, Nat.lt st.pos step.pos := hstackdfs.2.1.lt_head
  -- the head sits at the largest `live` position among the open frames
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
  -- `hmerged` restricted to the frames below the head
  have hrestMerged : ∀ st ∈ rest, ∀ x ∈ (st.succ.toList.take st.idx),
      dijkstraGetStatus aux x = .live →
      (∃ i, i < aux.roots.size ∧ st.state ∈ aux.range i ∧ x ∈ aux.range i) ∨
      (∃ st' ∈ step :: rest, st'.state = x ∧ Nat.lt st.pos st'.pos) :=
    fun st hst x hx hlive => hmerged st (List.mem_cons_of_mem _ hst) x hx hlive
  -- every open frame still occupies its own `live` slot, so its state reads back as `.live`
  have hStackLive : ∀ st ∈ (step :: rest), dijkstraGetStatus aux st.state = .live := fun st hst =>
    dijkstraGetStatus_live_of_pos hwf (hstackdfs.1 st hst).1 (hstackdfs.1 st hst).2
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
    have hMk' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
        st.succMarks = st.succ.map (edgeMarks st.state) := by
      intro st hst
      rcases List.mem_cons.mp hst with rfl | hst
      · exact hmk step (by simp)
      · exact hmk st (List.mem_cons_of_mem _ hst)
    have hdfs'Reach : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
        Reachable initialStates succs st.state := by
      intro st hst
      rcases List.mem_cons.mp hst with rfl | hst
      · exact hstepReach
      · exact hrestReach st hst
    have hstackdfs' : DijkstraStackRoots aux
        (({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest) :=
      DijkstraStackRoots.bump hstackdfs _ rfl rfl
    -- the bumped head keeps `step`'s state and position, and nothing dispatches into it from below
    have hTreeMarksBump : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
        ∀ st' ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
        st'.state ∈ (st.succ.toList.take st.idx) → Nat.lt st.pos st'.pos →
        ∀ j, j < aux.roots.size → st'.state ∈ aux.range j → ∀ m ∈ edgeMarks st.state st'.state,
          (aux.roots[j]!).acc.testBit m = true ∨ (aux.roots[j]!).entry.testBit m = true := by
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
              (aux.roots[i]!).acc.testBit m = true := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · show ∀ x ∈ step.succ.toList.take (step.idx + 1), ∀ i, i < aux.roots.size →
            x ∈ aux.range i → step.state ∈ aux.range i → ∀ m ∈ edgeMarks step.state x,
              (aux.roots[i]!).acc.testBit m = true
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
          ∀ x ∈ succs t, x ∈ aux.range i → ∀ m ∈ edgeMarks t x, (aux.roots[i]!).acc.testBit m = true :=
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
      exact ih aux _ r hr hwf hSuccEq' hMk' hPrefix' hdfs'Reach hrangeinv hstackdfs' hrangeclosed' hdispatched'
        hmarksClosed' hMarksOpen' hmerged' hTreeMarksBump
        (NoBackDispatch.state_congr ({ step with idx := step.idx + 1 }) hNoBack rfl) hrootsBound hentryBound
        (fun i hi => (hrootsNotFull i hi).imp id
          (DijkstraNoInternalEdge.bump hdTake (dijkstraGetStatus_dead_not_mem_range hwf hgs i))) hdead
    | live =>
      simp only [hgs] at hr
      -- rewrite only the *applied* cache, not the `marks` field inside the frame record
      rw [show step.succMarks[step.idx]! = edgeMarks step.state d from
          DFSStep.succMarks_get (hmk step (by simp)) h] at hr
      rcases hupdeq : dijkstraUpdate numMarks aux (edgeMarks step.state d) d with ⟨aux', found⟩
      simp only [hupdeq] at hr
      have haux'1 : (dijkstraUpdate numMarks aux (edgeMarks step.state d) d).1 = aux' :=
        congrArg Prod.fst hupdeq
      have hdead_eq : aux'.dead = aux.dead := by
        have := (dijkstraUpdate_fields numMarks aux (edgeMarks step.state d) d).2.2
        rwa [haux'1] at this
      have hstatus_eq : ∀ q, dijkstraGetStatus aux' q = dijkstraGetStatus aux q := by
        intro q
        have := dijkstraUpdate_status numMarks aux (edgeMarks step.state d) d q
        rwa [haux'1] at this
      have hlive_eq : aux'.live = aux.live := by
        have := (dijkstraUpdate_fields numMarks aux (edgeMarks step.state d) d).1
        rwa [haux'1] at this
      have hroots_pos : 0 < aux.roots.size := hne0
      have hd_contains : aux.liveIndex.contains d = true := by
        unfold dijkstraGetStatus liveStatusOf at hgs
        by_cases hc : aux.liveIndex.contains d = true
        · exact hc
        · exfalso
          rw [if_neg hc] at hgs
          split at hgs <;> cases hgs
      obtain ⟨lo, hlo_lt, hd_range, haux'size, haux'pre, haux'top, haux'entry⟩ :=
        dijkstraUpdate_merge_locate numMarks aux (edgeMarks step.state d) d hwf hrangeinv.rootsWF hroots_pos
          hd_contains
      rw [haux'1] at haux'size haux'pre haux'top haux'entry
      have hunion : ∀ x, x ∈ aux'.range lo ↔ ∃ i, lo ≤ i ∧ i < aux.roots.size ∧ x ∈ aux.range i :=
        dijkstraMerge_range_union hlo_lt hrangeinv.rootsWF haux'size haux'top hlive_eq
      have hprefix_eq : ∀ i, i < lo → aux'.range i = aux.range i :=
        fun i hi => dijkstraMerge_range_prefix_eq hlo_lt haux'size hlive_eq haux'top haux'pre i hi
      have hrangeinv' : DijkstraRangeInv succs edgeMarks aux' :=
        haux'1 ▸ dijkstraRangeInv_update hwf hrangeinv hroots_pos hd_contains hstepMem hdSucc
      by_cases hf : found = true
      -- the reported range is the merged top one, connected, and its all-ones bitmask gives `AcceptingMarks`
      · simp only [hf, if_true, Option.some.injEq] at hr
        have hhint : dijkstraSccHint aux' = aux'.range lo := by
          rw [dijkstraSccHint_eq_top_range aux' (by omega),
            show aux'.roots.size - 1 = lo from by omega]
        have hstepLo : step.state ∈ aux'.range lo :=
          (hunion step.state).mpr ⟨aux.roots.size - 1, by omega, by omega, hstepMem⟩
        have hfull : (aux'.roots[lo]!).acc = (1 <<< numMarks) - 1 := by
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
          ⟨⟨step.state, hstepLo, d, (hunion d).mpr ⟨lo, Nat.le_refl _, hlo_lt, hd_range⟩, hdSucc⟩, hcov⟩,
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
        have hstackdfs' : DijkstraStackRoots aux'
            (({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest) :=
          haux'1 ▸ DijkstraStackRoots.update hwf hrangeinv.rootsWF hroots_pos hd_contains
            (DijkstraStackRoots.bump hstackdfs _ rfl rfl)
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
        -- every bitmask the merge absorbs persists into the new top range's bitmask
        obtain ⟨lo1, hlo1eq, hlo1top, hlo1abs, hlo1dfs⟩ :=
          dijkstraUpdate_merge_bitmask numMarks aux (edgeMarks step.state d) d hroots_pos
        rw [haux'1] at hlo1eq hlo1top hlo1abs hlo1dfs
        have hlo1lo : lo1 = lo := by omega
        rw [hlo1lo] at hlo1top hlo1abs hlo1dfs
        have hbitAbsorb : ∀ k, lo ≤ k → k < aux.roots.size → ∀ m, (aux.roots[k]!).acc.testBit m = true →
            (aux'.roots[lo]!).acc.testBit m = true := by
          intro k hk1 hk2 m hm
          by_cases hklt : k < aux.roots.size - 1
          · exact hlo1abs k hk1 hklt m hm
          · have hkeq : k = aux.roots.size - 1 := by omega
            subst hkeq
            exact hlo1top m (by simp [hm])
        -- only ranges strictly above `lo`, the entry edge of the merged range's root starts below it
        have hbitDfsAbsorb : ∀ k, lo < k → k < aux.roots.size → ∀ m,
            (aux.roots[k]!).entry.testBit m = true → (aux'.roots[lo]!).acc.testBit m = true :=
          hlo1dfs
        -- a pair sharing a range still shares one, ranges below `lo` are untouched and the rest merge into the top
        have hpairLift : ∀ j, j < aux.roots.size → ∀ y z, y ∈ aux.range j → z ∈ aux.range j →
            ∃ i, i < aux'.roots.size ∧ y ∈ aux'.range i ∧ z ∈ aux'.range i := by
          intro j hj y z hy hz
          by_cases hjlo : j < lo
          · exact ⟨j, by omega, by rw [hprefix_eq j hjlo]; exact hy, by rw [hprefix_eq j hjlo]; exact hz⟩
          · exact ⟨lo, by omega, (hunion y).mpr ⟨j, by omega, hj, hy⟩, (hunion z).mpr ⟨j, by omega, hj, hz⟩⟩
        have hmarksClosed' : ∀ i, i < aux'.roots.size → ∀ t ∈ aux'.range i,
            (∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest, st.state ≠ t) →
            ∀ x ∈ succs t, x ∈ aux'.range i → ∀ m ∈ edgeMarks t x, (aux'.roots[i]!).acc.testBit m = true := by
          intro i hi t ht hexcl x hx hxr m hm
          rw [haux'size] at hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
          · rw [hprefix_eq i hilt] at ht hxr
            rw [haux'pre i hilt]
            exact hmarksClosed i (by omega) t ht (hexcl_iff t hexcl) x hx hxr m hm
          · subst hieq
            obtain ⟨k, hlok, hkn, htk⟩ := (hunion t).mp ht
            obtain ⟨k', _, _, hxk'⟩ := (hunion x).mp hxr
            -- `t` is retired, so its successor `x` stayed in `t`'s old range or went dead, and dead states are in no range
            rcases hrangeclosed k hkn t htk (hexcl_iff t hexcl) x hx
              (hdispatched k hkn t htk (hexcl_iff t hexcl) x hx) with hxrk | hxd
            · exact hbitAbsorb k hlok hkn m (hmarksClosed k hkn t htk (hexcl_iff t hexcl) x hx hxrk m hm)
            · exact absurd hxk' (dijkstraGetStatus_dead_not_mem_range hwf hxd k')
        -- the merge folds in every absorbed range's bitmask and its root's entry marks
        have hTreeMarks' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
            ∀ st' ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
            st'.state ∈ (st.succ.toList.take st.idx) → Nat.lt st.pos st'.pos →
            ∀ j, j < aux'.roots.size → st'.state ∈ aux'.range j → ∀ m ∈ edgeMarks st.state st'.state,
              (aux'.roots[j]!).acc.testBit m = true ∨ (aux'.roots[j]!).entry.testBit m = true := by
          intro st hst st' hst' hdisp hlt j hj hjr m hm
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
              · exact Or.inr (by rw [haux'entry, hkeq]; exact hb)
              · exact Or.inl (hbitDfsAbsorb k hklt hkn m hb)
        have hMarksOpen' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
            ∀ x ∈ (st.succ.toList.take st.idx), ∀ i, i < aux'.roots.size →
              x ∈ aux'.range i → st.state ∈ aux'.range i → ∀ m ∈ edgeMarks st.state x,
                (aux'.roots[i]!).acc.testBit m = true := by
          intro st hst
          rcases List.mem_cons.mp hst with rfl | hst
          · show ∀ x ∈ step.succ.toList.take (step.idx + 1), ∀ i, i < aux'.roots.size →
              x ∈ aux'.range i → step.state ∈ aux'.range i → ∀ m ∈ edgeMarks step.state x,
                (aux'.roots[i]!).acc.testBit m = true
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
              · -- `x` is a still-open frame, so this is `st`'s tree edge into it, and `st`'s range index is at most `x`'s
                have hstpos := (hstackdfs.1 st (List.mem_cons_of_mem _ hst)).2
                have hxpos := (hstackdfs.1 st' hst').2
                have hxk'' : st'.state ∈ aux.range k' := by rw [heq]; exact hxk'
                have hk''le : k'' ≤ k' :=
                  DijkstraAux.range_le_of_pos_lt hrangeinv.rootsWF hkn''
                    (DijkstraAux.mem_range_pos hwf hsk'' hstpos
                      (hstackdfs.1 st (List.mem_cons_of_mem _ hst)).1).1
                    (DijkstraAux.mem_range_pos hwf hxk'' hxpos
                      (hstackdfs.1 st' hst').1).2 hlt
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
              -- the merge puts `step.state` and its live target `d` in one range
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
        have hentryBound' : ∀ i : Nat, (aux'.roots[i]!).entry < 2 ^ numMarks := by
          intro i
          by_cases hi : i < lo
          · rw [haux'pre i hi]; exact hentryBound i
          · by_cases hieq : i = lo
            · rw [hieq, haux'entry]; exact hentryBound lo
            · rw [getElem!_neg aux'.roots i (by omega)]
              exact getElem!_default_entry_lt numMarks
        have hrootsBound' : ∀ i : Nat, (aux'.roots[i]!).acc < 2 ^ numMarks := by
          obtain ⟨lo', hlo'eq, hlo'bound⟩ := dijkstraUpdate_merge_bound numMarks aux (edgeMarks step.state d) d
            hroots_pos hrootsBound hentryBound (marksToBitmask_lt (hmarksBound step.state d))
          rw [haux'1] at hlo'eq hlo'bound
          have hloeq : lo' = lo := by omega
          intro i
          by_cases hi : i < lo
          · rw [haux'pre i hi]; exact hrootsBound i
          · by_cases hieq : i = lo
            · subst hieq; rw [← hloeq]; exact hlo'bound
            · rw [getElem!_neg aux'.roots i (by omega)]
              exact getElem!_default_acc_lt numMarks
        have hffalse : found = false := by cases found with
          | true => exact absurd rfl hf
          | false => rfl
        have hrootsNotFull' : ∀ i, i < aux'.roots.size → (aux'.roots[i]!).acc ≠ (1 <<< numMarks) - 1 ∨
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
        exact ih aux' _ r hr hwf' hSuccEq' hMk' hPrefix' hdfs'Reach hrangeinv' hstackdfs' hrangeclosed' hdispatched'
          hmarksClosed' hMarksOpen' hmerged' hTreeMarks'
          (NoBackDispatch.state_congr ({ step with idx := step.idx + 1 }) hNoBack rfl)
          hrootsBound' hentryBound' hrootsNotFull' hdead'
    | unknown =>
      simp only [hgs] at hr
      -- rewrite only the *applied* cache, not the `marks` field inside the frame record
      rw [show step.succMarks[step.idx]! = edgeMarks step.state d from
          DFSStep.succMarks_get (hmk step (by simp)) h] at hr
      rcases hpsheq : dijkstraPush aux d (edgeMarks step.state d) with ⟨aux', pos'⟩
      simp only [hpsheq] at hr
      have haux'2 : (dijkstraPush aux d (edgeMarks step.state d)).1 = aux' := congrArg Prod.fst hpsheq
      have hwf' : DijkstraWellFormed aux' :=
        haux'2 ▸ dijkstraWellFormed_push aux d (edgeMarks step.state d) hwf hgs
      have hpeq : ∀ q, dijkstraGetStatus aux' q = if q == d then .live else dijkstraGetStatus aux q :=
        fun q => haux'2 ▸ dijkstraPush_status aux d (edgeMarks step.state d) q
      -- PUSH leaves `dead` untouched
      have hdeq : aux'.dead = aux.dead := by rw [← haux'2]; rfl
      have hpos'_eq : pos' = aux.live.size := by
        have h2 : (dijkstraPush aux d (edgeMarks step.state d)).2 = pos' := congrArg Prod.snd hpsheq
        rw [← h2]; rfl
      set newStep : DFSStep State Nat :=
        { state := d, pos := pos', acc := marksToBitmask (edgeMarks step.state d), succ := (expand d).1, succMarks := (expand d).2.1, succOpts := (expand d).2.2, idx := 0 } with hnewStep_def
      have hSuccEq'' : ∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          st.succ = succs st.state := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · exact hexp.fst d
        · exact hSuccEq' st hst
      have hMk'' : ∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          st.succMarks = st.succ.map (edgeMarks st.state) := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · show (expand d).2.1 = (expand d).1.map (edgeMarks d)
          rw [hexp.snd d, hexp.fst d]
        · exact hMk' st hst
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
      -- the new singleton range `{d}` chains to the old top and starts with an empty bitmask
      have hwfOld := hrangeinv.rootsWF
      have hne : 0 < aux.roots.size := hne0
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
        exact dijkstraStackRoots_head_mem_top hstackdfs
      have hconnected' : ∀ i, i < aux'.roots.size → InternallyConnected succs (aux'.range i) := by
        intro i hi
        rw [hsize'] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
        · rw [hrangeEq i hilt]; exact hrangeinv.connected i hilt
        · subst hieq
          intro s hs t ht
          left; rw [(hnewRangeIff s).mp hs, (hnewRangeIff t).mp ht]
      have hchained' : ∀ i, i + 1 < aux'.roots.size →
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
      have hlivePush' : aux'.live = aux.live.push d := by rw [← haux'2]; rfl
      have hrootsPush' : aux'.roots =
          aux.roots.push ⟨aux.live.size, 0, marksToBitmask (edgeMarks step.state d)⟩ := by
        rw [← haux'2]; rfl
      have hbitSound' : ∀ i, i < aux'.roots.size → ∀ m, (aux'.roots[i]!).acc.testBit m = true →
          ∃ s ∈ aux'.range i, ∃ t ∈ aux'.range i, t ∈ succs s ∧ m ∈ edgeMarks s t := by
        intro i hi m hm
        rw [hsize'] at hi
        rw [hrootsPush'] at hm
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
        · rw [Array.getElem!_push_lt hilt] at hm
          rw [hrangeEq i hilt]
          exact hrangeinv.bitSound i hilt m hm
        -- the fresh singleton range starts with an empty bitmask
        · exact absurd (hieq ▸ hm) (by rw [Array.getElem!_push_eq]; simp)
      have hentrySound' : ∀ i, i < aux'.roots.size → ∀ m, (aux'.roots[i]!).entry.testBit m = true →
          0 < i ∧ ∃ t ∈ aux'.range (i - 1), ∃ u ∈ aux'.range i, u ∈ succs t ∧ m ∈ edgeMarks t u := by
        intro i hi m hm
        rw [hsize'] at hi
        rw [hrootsPush'] at hm
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | hieq
        · rw [Array.getElem!_push_lt hilt] at hm
          obtain ⟨hipos, t, ht, u, hu, htu, hmk⟩ := hrangeinv.entrySound i hilt m hm
          exact ⟨hipos, t, (hrangeEq (i - 1) (by omega)) ▸ ht, u, (hrangeEq i hilt) ▸ hu, htu, hmk⟩
        -- the fresh singleton range, its entry marks are this tree edge's, running in from its parent
        · subst hieq
          rw [Array.getElem!_push_eq] at hm
          exact ⟨hne, step.state, hstepTop, d, (hnewRangeIff d).mpr rfl, hdSucc, marksToBitmask_mem hm⟩
      have hrangeinv' : DijkstraRangeInv succs edgeMarks aux' :=
        ⟨hwf'', hconnected', hchained', hbitSound', hentrySound'⟩
      have hstackdfs'' : DijkstraStackRoots aux'
          (newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest) := by
        have hpush := DijkstraStackRoots.push (marks := edgeMarks step.state d) hstackdfs' newStep
          (by rw [hnewStep_def]) (by rw [hnewStep_def]; exact hpos'_eq)
        rwa [haux'2] at hpush
      -- `d` was `.unknown`, so it sat in no old range, and the new range's obligation is vacuous since `d` is on the stack
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
      have hrootsPush : aux'.roots =
          aux.roots.push ⟨aux.live.size, 0, marksToBitmask (edgeMarks step.state d)⟩ := by
        rw [← haux'2]; rfl
      have hmarksClosed'' : ∀ i, i < aux'.roots.size → ∀ t ∈ aux'.range i,
          (∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest, st.state ≠ t) →
          ∀ x ∈ succs t, x ∈ aux'.range i → ∀ m ∈ edgeMarks t x, (aux'.roots[i]!).acc.testBit m = true := by
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
              (aux'.roots[i]!).acc.testBit m = true := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · simp [hnewStep_def]
        · rcases List.mem_cons.mp hst with rfl | hst
          · show ∀ x ∈ step.succ.toList.take (step.idx + 1), ∀ i, i < aux'.roots.size →
              x ∈ aux'.range i → step.state ∈ aux'.range i → ∀ m ∈ edgeMarks step.state x,
                (aux'.roots[i]!).acc.testBit m = true
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
        exact (hstackdfs.1 step (by simp)).1
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
      have hentryBound' : ∀ i : Nat, (aux'.roots[i]!).entry < 2 ^ numMarks := by
        intro i
        rw [hrootsPush]
        by_cases hi : i < aux.roots.size
        · rw [Array.getElem!_push_lt hi]; exact hentryBound i
        · by_cases hieq : i = aux.roots.size
          · rw [hieq, Array.getElem!_push_eq]; exact marksToBitmask_lt (hmarksBound step.state d)
          · rw [getElem!_neg _ i (by simp only [Array.size_push]; omega)]
            exact getElem!_default_acc_lt numMarks
      have hrootsBound' : ∀ i : Nat, (aux'.roots[i]!).acc < 2 ^ numMarks := by
        intro i
        rw [← haux'2]
        unfold dijkstraPush
        simp only
        by_cases hi : i < aux.roots.size
        · rw [Array.getElem!_push_lt hi]; exact hrootsBound i
        · by_cases hieq : i = aux.roots.size
          · subst hieq; rw [Array.getElem!_push_eq]; exact Nat.two_pow_pos numMarks
          · rw [getElem!_neg _ i (by simp only [Array.size_push]; omega)]
            exact getElem!_default_acc_lt numMarks
      have hrootsNotFull' : ∀ i, i < aux'.roots.size → (aux'.roots[i]!).acc ≠ (1 <<< numMarks) - 1 ∨
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
        -- the fresh singleton range `{d}`, nothing has been dispatched out of it yet
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
      have hTreeMarks'' : ∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          ∀ st' ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State Nat) :: rest,
          st'.state ∈ (st.succ.toList.take st.idx) → Nat.lt st.pos st'.pos →
          ∀ j, j < aux'.roots.size → st'.state ∈ aux'.range j → ∀ m ∈ edgeMarks st.state st'.state,
            (aux'.roots[j]!).acc.testBit m = true ∨ (aux'.roots[j]!).entry.testBit m = true := by
        intro st hst st' hst' hdisp hlt j hj hjr m hm
        rw [hsize'] at hj
        rcases List.mem_cons.mp hst with rfl | hst
        · simp [hnewStep_def] at hdisp
        · rcases List.mem_cons.mp hst' with rfl | hst'
          · -- PUSH records this tree edge's marks in the new candidate's entry field
            rcases List.mem_cons.mp hst with rfl | hstr
            · have hjrd : d ∈ aux'.range j := by rw [hnewStep_def] at hjr; exact hjr
              have hjeq : j = aux.roots.size := by
                rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | hjeq
                · exact absurd (dijkstraGetStatus_live_of_mem_range hwf ((hrangeEq j hjlt) ▸ hjrd))
                    (by rw [hgs]; simp)
                · exact hjeq
              rw [hjeq]
              right
              rw [hrootsPush, Array.getElem!_push_eq]
              exact marksToBitmask_testBit hm
            · exact absurd (hrestPrefix st hstr d (by rw [hnewStep_def] at hdisp; exact hdisp))
                (by rw [hgs]; simp)
          · have hjlt : j < aux.roots.size := by
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | hjeq
              · exact hjlt
              · exfalso
                rw [hjeq] at hjr
                have hxd : st'.state = d := (hnewRangeIff st'.state).mp hjr
                have hlive' : dijkstraGetStatus aux st'.state = .live := by
                  rcases List.mem_cons.mp hst' with rfl | hst'2
                  · exact hStackLive step (by simp)
                  · exact hStackLive st' (List.mem_cons_of_mem _ hst'2)
                exact absurd hlive' (by rw [hxd, hgs]; simp)
            rw [hrangeEq j hjlt] at hjr
            rw [hrootsPush, Array.getElem!_push_lt hjlt]
            exact hTreeMarksBump st hst st' hst' hdisp hlt j hjlt hjr m hm
      exact ih aux' _ r hr hwf' hSuccEq'' hMk'' hPrefix'' hReach'' hrangeinv' hstackdfs'' hrangeclosed'' hdispatched''
        hmarksClosed'' hMarksOpen'' hmerged'' hTreeMarks'' hNoBack'' hrootsBound' hentryBound' hrootsNotFull'
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
    have hMk' : ∀ st ∈ rest, st.succMarks = st.succ.map (edgeMarks st.state) :=
      fun st hst => hmk st (List.mem_cons_of_mem _ hst)
    have hReach' : ∀ st ∈ rest, Reachable initialStates succs st.state := hrestReach
    have hstackdfsPacked : DijkstraStackRoots aux (step :: rest) := hstackdfs
    have hliveCorr := hstackdfs.1
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
        ∀ m ∈ edgeMarks step.state x, (aux.roots[aux.roots.size - 1]!).acc.testBit m = true := by
      intro x hx hxr m hm
      have hxtake : x ∈ step.succ.toList.take step.idx := by
        rw [hstepAllTaken, hstepSuccEq]; simpa using hx
      exact hstepMarksOpen x hxtake (aux.roots.size - 1) (by omega) hxr hstepMem m hm
    obtain ⟨r0, a0, e0, hback⟩ : ∃ r0 a0 e0, aux.roots.back? = some ⟨r0, a0, e0⟩ := by
      rcases hbk : aux.roots.back? with _ | p
      · exact absurd (Array.back?_eq_none_iff.mp hbk) (by intro he; rw [he] at hne0; simp at hne0)
      · exact ⟨p.root, p.acc, p.entry, by simp⟩
    obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hback
    have hridx : aux.roots.size - 1 = ys.size := by rw [hys]; simp
    have hrtop : aux.roots[aux.roots.size - 1]! = ⟨r0, a0, e0⟩ := by rw [hridx, hys, Array.getElem!_push_eq]
    have hwfRoots' : DijkstraRootsWF aux' :=
      haux'eq ▸ dijkstraRootsWF_pop aux step.pos hrangeinv.rootsWF
    have hstackdfs' : DijkstraStackRoots aux' rest :=
      haux'eq ▸ DijkstraStackRoots.pop hrangeinv.rootsWF hstackdfsPacked
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
    have haux'rootsCases : aux'.roots = aux.roots ∨ aux'.roots = aux.roots.pop := by
      rw [← haux'eq]
      unfold dijkstraPop
      rw [hback]
      dsimp only
      split
      · exact Or.inr rfl
      · exact Or.inl rfl
    have hentryBound' : ∀ i : Nat, (aux'.roots[i]!).entry < 2 ^ numMarks := by
      intro i
      rcases haux'rootsCases with hc | hc
      · rw [hc]; exact hentryBound i
      · rw [hc]
        by_cases hi : i < aux.roots.pop.size
        · rw [Array.getElem!_pop_lt hi]; exact hentryBound i
        · rw [getElem!_neg _ i hi]; exact getElem!_default_entry_lt numMarks
    by_cases hflush : step.pos = r0
    · -- flush: the top range `D := aux.range (aux.roots.size - 1)` is confirmed and flushed to `dead`
      have haux'defF : aux' = { aux with
          roots := aux.roots.pop
          live := (liveFlush aux.live aux.liveIndex aux.dead step.pos).1
          liveIndex := (liveFlush aux.live aux.liveIndex aux.dead step.pos).2.1
          dead := (liveFlush aux.live aux.liveIndex aux.dead step.pos).2.2 } := by
        rw [← haux'eq]
        unfold dijkstraPop
        rw [hback]
        dsimp only
        rw [if_pos hflush]
      have haux'rootsF : aux'.roots = aux.roots.pop := by rw [haux'defF]
      have haux'deadF : aux'.dead = (liveFlush aux.live aux.liveIndex aux.dead step.pos).2.2 := by
        rw [haux'defF]
      have htopStart : aux.rangeStart (aux.roots.size - 1) = step.pos := by
        unfold DijkstraAux.rangeStart
        rw [show (aux.roots[aux.roots.size - 1]!).root = r0 from by rw [hrtop]]
        exact hflush.symm
      have htopEnd : aux.rangeEnd (aux.roots.size - 1) = aux.live.size := by
        unfold DijkstraAux.rangeEnd
        simp only [show ¬ aux.roots.size - 1 + 1 < aux.roots.size from by omega, if_false]
      have hposle : Nat.le step.pos aux.live.size := by
        rw [hflush, show r0 = (aux.roots[aux.roots.size - 1]!).root from by rw [hrtop]]
        exact Nat.le_of_lt (hrangeinv.rootsWF.rootsLt (aux.roots.size - 1) (by omega))
      -- `t ∈ D`, `t ≠ step.state`, is already off the current stack
      have hDposNe : ∀ t ∈ aux.range (aux.roots.size - 1), t ≠ step.state → ∀ st ∈ step :: rest, st.state ≠ t := by
        intro t ht htne st hst hcontra
        rcases List.mem_cons.mp hst with rfl | hst
        · exact htne hcontra.symm
        · rw [DijkstraAux.mem_range_iff, htopStart] at ht
          obtain ⟨p, hp1, hp2, hp3⟩ := ht
          have hpb : p < aux.live.size := Nat.lt_of_lt_of_le hp2 (Nat.min_le_right _ _)
          have hstb : Nat.lt st.pos aux.live.size :=
            (hliveCorr st (List.mem_cons_of_mem _ hst)).1
          have hstlive := (hliveCorr st (List.mem_cons_of_mem _ hst)).2
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
          ∀ m ∈ edgeMarks t x, (aux.roots[aux.roots.size - 1]!).acc.testBit m = true := by
        intro t ht x hx hxr m hm
        by_cases hts : t = step.state
        · subst hts; exact hstepMarksClosed x hx hxr m hm
        · exact hmarksClosed (aux.roots.size - 1) (by omega) t ht (hDposNe t ht hts) x hx hxr m hm
      have hdead' : ∀ s ∈ aux'.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc := by
        intro s hsdead' A hsA
        rw [haux'deadF] at hsdead'
        rcases liveFlush_dead_or_old step.pos aux.live aux.liveIndex aux.dead s hsdead'
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
                    unfold dijkstraGetStatus liveStatusOf at hc2
                    by_cases h1 : aux.liveIndex.contains y
                    · simp [h1] at hc2
                    · by_cases h2 : aux.dead.contains y
                      · exact Std.HashSet.mem_iff_contains.mpr h2
                      · simp [h1, h2] at hc2
                  exact absurd (Std.HashSet.mem_iff_contains.mpr hyA) (hdead y hyDead A))
          obtain ⟨_, hcov⟩ := A.covers
          have hDbitmaskCover : ∀ m, m < numMarks → (aux.roots[aux.roots.size - 1]!).acc.testBit m = true := by
            intro m hmlt
            obtain ⟨s1, hs1, t1, ht1, hedge1, hmark1⟩ := hcov m hmlt
            exact hDmarksClosed s1 (hDsub s1 hs1) t1 hedge1 (hDsub t1 ht1) m hmark1
          have hDbound : (aux.roots[aux.roots.size - 1]!).acc < 2 ^ numMarks := hrootsBound (aux.roots.size - 1)
          have hDeq : (aux.roots[aux.roots.size - 1]!).acc = (1 <<< numMarks) - 1 :=
            eq_allOnesMask_of_testBit_cover hDbound hDbitmaskCover
          -- the bitmask contradicts, or the range holds no discovered internal edge, which `A.covers` violates
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
        exact dijkstraPop_range_mem_iff_of_flush hrangeinv.rootsWF hback hflush hposle i hi x
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
      have hchained' : ∀ i, i + 1 < aux'.roots.size →
          ∃ s ∈ aux'.range i, ∃ t ∈ aux'.range (i + 1), t ∈ succs s := by
        intro i hi
        rw [haux'sizeF] at hi
        obtain ⟨s, hs, t, ht, hst⟩ := hrangeinv.chained i (by omega)
        exact ⟨s, (hrangeEqF i (by omega) s).mpr hs, t, (hrangeEqF (i + 1) (by omega) t).mpr ht, hst⟩
      have hbitSound' : ∀ i, i < aux'.roots.size → ∀ m, (aux'.roots[i]!).acc.testBit m = true →
          ∃ s ∈ aux'.range i, ∃ t ∈ aux'.range i, t ∈ succs s ∧ m ∈ edgeMarks s t := by
        intro i hi m hm
        rw [haux'sizeF] at hi
        have hipop : i < aux.roots.pop.size := by
          have hps : aux.roots.pop.size = aux.roots.size - 1 := Array.size_pop
          omega
        rw [haux'rootsF, Array.getElem!_pop_lt hipop] at hm
        obtain ⟨s, hs, t, ht, hst, hmk⟩ := hrangeinv.bitSound i (by omega) m hm
        exact ⟨s, (hrangeEqF i hi s).mpr hs, t, (hrangeEqF i hi t).mpr ht, hst, hmk⟩
      -- the flushed candidate is the top one, so every surviving entry keeps both its marks and its ranges
      have hentrySound' : ∀ i, i < aux'.roots.size → ∀ m, (aux'.roots[i]!).entry.testBit m = true →
          0 < i ∧ ∃ t ∈ aux'.range (i - 1), ∃ u ∈ aux'.range i, u ∈ succs t ∧ m ∈ edgeMarks t u := by
        intro i hi m hm
        have hipop : i < aux.roots.pop.size := by rw [← haux'rootsF]; exact hi
        have hib : i < aux.roots.size - 1 := by simp only [Array.size_pop] at hipop; omega
        rw [haux'rootsF, Array.getElem!_pop_lt hipop] at hm
        obtain ⟨hipos, t, ht, u, hu, htu, hmk⟩ := hrangeinv.entrySound i (by omega) m hm
        exact ⟨hipos, t, (hrangeEqF (i - 1) (by omega) t).mpr ht,
          u, (hrangeEqF i hib u).mpr hu, htu, hmk⟩
      have hrangeinv' : DijkstraRangeInv succs edgeMarks aux' :=
        ⟨hwfRoots', hconnected', hchained', hbitSound', hentrySound'⟩
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
          ∀ x ∈ succs t, x ∈ aux'.range i → ∀ m ∈ edgeMarks t x, (aux'.roots[i]!).acc.testBit m = true := by
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
          x ∈ aux'.range i → st.state ∈ aux'.range i → ∀ m ∈ edgeMarks st.state x, (aux'.roots[i]!).acc.testBit m = true := by
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
        (hliveCorr step List.mem_cons_self).1
      have hstepLiveOld : dijkstraGetStatus aux step.state = .live :=
        dijkstraGetStatus_live_of_pos hwf hstepposlt (hliveCorr step (by simp)).2
      have hstepd : dijkstraGetStatus aux' step.state = .dead := by
        rcases hstatusEither step.state with heqs | ⟨_, h2⟩
        · exfalso
          rw [hstepLiveOld] at heqs
          have hcontains : aux'.liveIndex.contains step.state = true := by
            unfold dijkstraGetStatus liveStatusOf at heqs
            by_cases hc : aux'.liveIndex.contains step.state
            · exact hc
            · rw [if_neg hc] at heqs; split at heqs <;> cases heqs
          rw [Std.HashMap.contains_eq_isSome_getElem?] at hcontains
          obtain ⟨p, hpv⟩ := Option.isSome_iff_exists.mp hcontains
          obtain ⟨hplt, hpstate⟩ := hwf'.bwd step.state p hpv
          have hlive'size : aux'.live.size = step.pos := by
            rw [haux'defF]
            exact liveFlush_size step.pos aux.live aux.liveIndex aux.dead hposle
          have hplt' : p < step.pos := by omega
          have hpstateOld : aux.live[p]! = step.state := by
            rw [← hpstate, haux'defF]
            dsimp only
            exact (liveFlush_getElem!_lt step.pos aux.live aux.liveIndex aux.dead p hplt').symm
          have hpb : p < aux.live.size := Nat.lt_of_lt_of_le hplt' hposle
          have hpeq : p = step.pos :=
            hwf.pos_inj hpb hstepposlt (hpstateOld.trans (hliveCorr step (by simp)).2.symm)
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
              have hstlive := (hliveCorr st (List.mem_cons_of_mem _ hst)).2
              have hsteplive := (hliveCorr step (by simp)).2
              have hpeq := hwf.pos_inj
                (hliveCorr st (List.mem_cons_of_mem _ hst)).1
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
      have hrootsBound' : ∀ i : Nat, (aux'.roots[i]!).acc < 2 ^ numMarks := by
        intro i; rw [haux'rootsF]; exact array_pop_bitmask_bound hrootsBound i
      have hrootsNotFull' : ∀ i, i < aux'.roots.size → (aux'.roots[i]!).acc ≠ (1 <<< numMarks) - 1 ∨
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

      -- every surviving range's root, and its entry, sits strictly below the popped frame
      have hTreeMarks' : ∀ st ∈ rest, ∀ st' ∈ rest,
          st'.state ∈ (st.succ.toList.take st.idx) → Nat.lt st.pos st'.pos →
          ∀ j, j < aux'.roots.size → st'.state ∈ aux'.range j → ∀ m ∈ edgeMarks st.state st'.state,
            (aux'.roots[j]!).acc.testBit m = true ∨ (aux'.roots[j]!).entry.testBit m = true := by
        intro st hst st' hst' hdisp hlt j hj hjr m hm
        rw [haux'sizeF] at hj
        rw [hrangeEqF j hj st'.state] at hjr
        have hjpoplt : j < aux.roots.pop.size := by
          have hps : aux.roots.pop.size = aux.roots.size - 1 := Array.size_pop
          omega
        rw [haux'rootsF, Array.getElem!_pop_lt hjpoplt]
        exact hTreeMarks st (List.mem_cons_of_mem _ hst) st' (List.mem_cons_of_mem _ hst') hdisp hlt j
          (by omega) hjr m hm
      exact ih aux' rest r hr hwf' hSuccEq' hMk' hPrefix' hReach' hrangeinv' hstackdfs' hrangeclosed' hdispatched'
        hmarksClosed' hMarksOpen' hmerged' hTreeMarks' hNoBack.tail hrootsBound' hentryBound' hrootsNotFull'
        hdead'
    · -- non-flush: POP confirms nothing, so the whole search state is untouched
      have haux'defNF : aux' = aux := by
        rw [← haux'eq]
        unfold dijkstraPop
        rw [hback]
        dsimp only
        rw [if_neg hflush]
      have haux'rootsNF : aux'.roots = aux.roots := by rw [haux'defNF]
      have haux'liveNF : aux'.live = aux.live := by rw [haux'defNF]
      have haux'deadNF : aux'.dead = aux.dead := by rw [haux'defNF]
      have hrangeEqNF : ∀ i, i < aux.roots.size → aux'.range i = aux.range i :=
        fun i _ => haux'eq ▸ dijkstraPop_range_eq_of_not_flush hback hflush i
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
      have hchained' : ∀ i, i + 1 < aux'.roots.size →
          ∃ s ∈ aux'.range i, ∃ t ∈ aux'.range (i + 1), t ∈ succs s := by
        intro i hi
        rw [haux'rootsNF] at hi
        obtain ⟨s, hs, t, ht, hst⟩ := hrangeinv.chained i hi
        exact ⟨s, (hrangeEqNF i (by omega)) ▸ hs, t, (hrangeEqNF (i + 1) hi) ▸ ht, hst⟩
      have hbitSound' : ∀ i, i < aux'.roots.size → ∀ m, (aux'.roots[i]!).acc.testBit m = true →
          ∃ s ∈ aux'.range i, ∃ t ∈ aux'.range i, t ∈ succs s ∧ m ∈ edgeMarks s t := by
        intro i hi m hm
        rw [haux'rootsNF] at hi hm
        rw [hrangeEqNF i hi]
        exact hrangeinv.bitSound i hi m hm
      have hentrySound' : ∀ i, i < aux'.roots.size → ∀ m, (aux'.roots[i]!).entry.testBit m = true →
          0 < i ∧ ∃ t ∈ aux'.range (i - 1), ∃ u ∈ aux'.range i, u ∈ succs t ∧ m ∈ edgeMarks t u := by
        intro i hi m hm
        rw [haux'rootsNF] at hi hm
        obtain ⟨hipos, t, ht, u, hu, htu, hmk⟩ := hrangeinv.entrySound i hi m hm
        exact ⟨hipos, t, (hrangeEqNF (i - 1) (by omega)) ▸ ht, u, (hrangeEqNF i hi) ▸ hu, htu, hmk⟩
      have hrangeinv' : DijkstraRangeInv succs edgeMarks aux' :=
        ⟨hwfRoots', hconnected', hchained', hbitSound', hentrySound'⟩
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
          ∀ x ∈ succs t, x ∈ aux'.range i → ∀ m ∈ edgeMarks t x, (aux'.roots[i]!).acc.testBit m = true := by
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
          x ∈ aux'.range i → st.state ∈ aux'.range i → ∀ m ∈ edgeMarks st.state x, (aux'.roots[i]!).acc.testBit m = true := by
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
            · -- `st = t`, the parent that just retired `step`: the top candidate's root is not `step`, so `t` is in its range
              rw [heq]
              have htpos : Nat.lt t.pos aux.live.size :=
                (hliveCorr t (List.mem_cons_of_mem step List.mem_cons_self)).1
              have hr0mem : r0 ∈ (t :: rest').map (·.pos) := by
                have := hstackdfs.2.2.1 (aux.roots.size - 1) (by omega)
                rw [show (aux.roots[aux.roots.size - 1]!).root = r0 from by rw [hrtop]] at this
                rw [List.map_cons, List.mem_cons] at this
                exact this.resolve_left (fun hc => hflush hc.symm)
              have hr0le : r0 ≤ t.pos := by
                obtain ⟨u, hu, hueq⟩ := List.mem_map.mp hr0mem
                rw [← hueq]
                exact hstackdfs.2.1.tail.le_head u hu
              have htmem : t.state ∈ aux.range (aux.roots.size - 1) := by
                rw [DijkstraAux.mem_range_iff]
                refine ⟨t.pos, ?_, ?_, (hliveCorr t (List.mem_cons_of_mem step List.mem_cons_self)).2⟩
                · show aux.rangeStart (aux.roots.size - 1) ≤ t.pos
                  unfold DijkstraAux.rangeStart
                  rw [show (aux.roots[aux.roots.size - 1]!).root = r0 from by rw [hrtop]]
                  exact hr0le
                · have hend : aux.rangeEnd (aux.roots.size - 1) = aux.live.size := by
                    unfold DijkstraAux.rangeEnd
                    simp only [show ¬ aux.roots.size - 1 + 1 < aux.roots.size from by omega, if_false]
                  rw [hend, Nat.min_self]
                  exact htpos
              refine ⟨aux.roots.size - 1, by rw [haux'rootsNF]; omega, ?_, ?_⟩
              · rw [hrangeEqNF (aux.roots.size - 1) (by omega)]; exact htmem
              · rw [hrangeEqNF (aux.roots.size - 1) (by omega)]; exact hstepMem
            · -- `st ∈ rest'`, strictly below the parent, `hNoBack` rules out `step` as a dispatched target
              exact absurd hx (hNoBack.1 st hst')
        · rcases hrestMerged st hst x hx hlive2 with hgood | ⟨st', hst', heq, hlt⟩
          · obtain ⟨i, hi, hsr, hxr⟩ := hgood
            exact Or.inl ⟨i, by rw [haux'rootsNF]; exact hi, by rw [hrangeEqNF i hi]; exact hsr,
              by rw [hrangeEqNF i hi]; exact hxr⟩
          · right
            rcases List.mem_cons.mp hst' with heq' | hst''
            · exact absurd (heq' ▸ heq).symm hxs
            · exact ⟨st', hst'', heq, hlt⟩
      have hrootsBound' : ∀ i : Nat, (aux'.roots[i]!).acc < 2 ^ numMarks := by
        intro i; rw [haux'rootsNF]; exact hrootsBound i
      have hrootsNotFull' : ∀ i, i < aux'.roots.size → (aux'.roots[i]!).acc ≠ (1 <<< numMarks) - 1 ∨
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
      have hTreeMarks' : ∀ st ∈ rest, ∀ st' ∈ rest,
          st'.state ∈ (st.succ.toList.take st.idx) → Nat.lt st.pos st'.pos →
          ∀ j, j < aux'.roots.size → st'.state ∈ aux'.range j → ∀ m ∈ edgeMarks st.state st'.state,
            (aux'.roots[j]!).acc.testBit m = true ∨ (aux'.roots[j]!).entry.testBit m = true := by
        intro st hst st' hst' hdisp hlt j hj hjr m hm
        rw [haux'rootsNF] at hj ⊢
        rw [hrangeEqNF j hj] at hjr
        exact hTreeMarks st (List.mem_cons_of_mem _ hst) st' (List.mem_cons_of_mem _ hst') hdisp hlt j hj hjr m hm
      exact ih aux' rest r hr hwf' hSuccEq' hMk' hPrefix' hReach' hrangeinv' hstackdfs' hrangeclosed' hdispatched'
        hmarksClosed' hMarksOpen' hmerged' hTreeMarks' hNoBack.tail hrootsBound' hentryBound' hrootsNotFull'
        hdead'

/-! ## Lifting completeness to the whole search

The outer loop carries one invariant between roots: `DijkstraWellFormed`, `DijkstraRangeInv`, `roots` empty, and `dead`
meeting no `AcceptingSCC`. -/

/-- The initial search state satisfies the range invariant vacuously, `roots` being empty. -/
theorem dijkstraRangeInv_init [Inhabited State] [LawfulBEq State] {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} :
    DijkstraRangeInv succs edgeMarks (dijkstraInitAux (State := State)) :=
  ⟨dijkstraRootsWF_init, by intro i hi; simp [dijkstraInitAux] at hi,
    by intro i hi; simp [dijkstraInitAux] at hi,
    by intro i hi; simp [dijkstraInitAux] at hi,
    by intro k hk; simp [dijkstraInitAux] at hk⟩

/-- An idle state has nothing live left. -/
theorem dijkstraGetStatus_ne_live_of_idle [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {aux : DijkstraAux State} (hwf : DijkstraWellFormed aux) (hrwf : DijkstraRootsWF aux)
    (hidle : aux.roots.size = 0) (q : State) : dijkstraGetStatus aux q ≠ .live := by
  have hlive : aux.live.size = 0 := hrwf.liveEmptyOfRootsEmpty hidle
  intro hq
  unfold dijkstraGetStatus liveStatusOf at hq
  have hc : aux.liveIndex.contains q = true := by
    by_cases hc : aux.liveIndex.contains q
    · exact hc
    · rw [if_neg hc] at hq; split at hq <;> cases hq
  rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hc
  exact absurd (hwf.bwd q p hp).1 (by omega)

set_option maxHeartbeats 1000000 in
/-- `dijkstra_dead_not_accepting` across one root's search, from an idle state back to an idle state if there is no
witness. -/
theorem dijkstraFromRoot_dead_not_accepting [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs)
    (aux : DijkstraAux State) (q0 : State) (hq0 : dijkstraGetStatus aux q0 = .unknown)
    (hq0mem : q0 ∈ initialStates) (hwf : DijkstraWellFormed aux)
    (hrangeinv : DijkstraRangeInv succs edgeMarks aux) (hidle : aux.roots.size = 0)
    (hdead : ∀ s ∈ aux.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) :
    (∀ s ∈ (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks expand aux q0).2.dead,
      ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) ∧
    ((dfsFromRoot (dijkstraOps numMarks) succs edgeMarks expand aux q0).1 = none →
      DijkstraWellFormed (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks expand aux q0).2 ∧
      DijkstraRangeInv succs edgeMarks (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks expand aux q0).2 ∧
      (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks expand aux q0).2.roots.size = 0) ∧
    (∀ anchor stem, (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks expand aux q0).1 = some (anchor, stem) →
      InternallyConnected succs (dijkstraSccHint (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks expand aux q0).2) ∧
      AcceptingMarks succs edgeMarks numMarks
        (dijkstraSccHint (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks expand aux q0).2) ∧
      anchor ∈ dijkstraSccHint (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks expand aux q0).2 ∧
      ∃ hs : stem ≠ [], stem.head hs ∈ initialStates ∧
        (∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs (stem[i])) ∧
        stem.getLast hs = anchor) := by
  have hrs0 : aux.roots.size = 0 := hidle
  have hlive0 : aux.live.size = 0 := hrangeinv.rootsWF.liveEmptyOfRootsEmpty hidle
  set step : DFSStep State Nat :=
    { state := q0, pos := (dijkstraPush aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
      acc := 0, succ := (expand q0).1, succMarks := (expand q0).2.1, succOpts := (expand q0).2.2, idx := 0 } with hstepdef
  set aux' := (dijkstraPush aux q0 (Std.HashSet.emptyWithCapacity 0)).1 with haux'def
  obtain ⟨r, hrr⟩ : ∃ r, dfsGo (dijkstraOps numMarks) succs edgeMarks expand aux' [step] = some r :=
    Option.ne_none_iff_exists'.mp (dijkstraOps_root_ne_none numMarks succs edgeMarks expand hexp initialStates fr
      aux q0 (Reachable.base hq0mem) hwf hq0)
  have hfr : dfsFromRoot (dijkstraOps numMarks) succs edgeMarks expand aux q0 = r := by
    show (dfsGo (dijkstraOps numMarks) succs edgeMarks expand aux' [step]).getD (none, aux') = r
    rw [hrr]; rfl
  rw [hfr]
  -- PUSH on an idle state opens exactly one range, the singleton `{q0}`, at `live` index `0`
  have hrootsPush : aux'.roots =
    aux.roots.push ⟨aux.live.size, 0, marksToBitmask (Std.HashSet.emptyWithCapacity 0)⟩ := rfl
  have hlivePush : aux'.live = aux.live.push q0 := rfl
  have hpos0 : step.pos = 0 := by
    have h : step.pos = aux.live.size := rfl
    rw [h]; exact hlive0
  have hrootsSize : aux'.roots.size = 1 := by rw [hrootsPush, Array.size_push]; omega
  have hroots0 : aux'.roots[0]! = ⟨0, 0, marksToBitmask (Std.HashSet.emptyWithCapacity 0)⟩ := by
    rw [hrootsPush, Array.getElem!_push_of_size_zero _ hrs0, hlive0]
  have hlive0' : aux'.live[0]! = q0 := by
    rw [hlivePush, Array.getElem!_push_of_size_zero _ hlive0]
  have hnewRange : ∀ x, x ∈ aux'.range 0 ↔ x = q0 := by
    intro x
    have h := dijkstraPush_new_range_mem_iff aux q0 (Std.HashSet.emptyWithCapacity 0) x
    rwa [hrs0] at h
  have hrootsWF' : DijkstraRootsWF aux' :=
    dijkstraRootsWF_push aux q0 (Std.HashSet.emptyWithCapacity 0) hrangeinv.rootsWF
  have hidx0 : ∀ i, i < aux'.roots.size → i = 0 := by intro i hi; rw [hrootsSize] at hi; omega
  have hbound0 : ∀ i : Nat, (aux'.roots[i]!).acc < 2 ^ numMarks := by
    intro i
    by_cases hi : i = 0
    · rw [hi, hroots0]; exact Nat.two_pow_pos numMarks
    · rw [getElem!_neg aux'.roots i (by rw [hrootsSize]; omega)]
      exact getElem!_default_acc_lt numMarks
  -- the one-frame starting stack is a `succs`-path from `q0`, so `dfsGo` hands back a real stem
  have hstem : ∀ anchor stem, r.1 = some (anchor, stem) →
      ∃ hs : stem ≠ [], stem.head hs ∈ initialStates ∧
        (∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs (stem[i])) ∧
        stem.getLast hs = anchor :=
    dfsGo_stem_path (dijkstraOps numMarks) succs edgeMarks expand hexp initialStates aux' [step] r hrr
      (by intro st hst; simp only [List.mem_singleton] at hst; rw [hst, hstepdef]; exact hexp.fst q0)
      ⟨by intro i hi; simp at hi, by intro _; simpa [hstepdef] using hq0mem⟩
  refine (fun h => ⟨h.1, h.2.1, fun anchor stem heq => ⟨(h.2.2 anchor stem heq).1,
      (h.2.2 anchor stem heq).2.1, (h.2.2 anchor stem heq).2.2, hstem anchor stem heq⟩⟩)
    (dijkstra_dead_not_accepting numMarks succs edgeMarks expand hexp initialStates hmarksBound
    aux' [step] r hrr (dijkstraWellFormed_push aux q0 _ hwf hq0)
    (by intro st hst; simp only [List.mem_singleton] at hst; rw [hst, hstepdef]; exact hexp.fst q0)
    (by intro st hst; simp only [List.mem_singleton] at hst; rw [hst, hstepdef]
        show (expand q0).2.1 = (expand q0).1.map (edgeMarks q0)
        rw [hexp.snd q0, hexp.fst q0])
    (by intro st hst x hx; simp only [List.mem_singleton] at hst; rw [hst, hstepdef] at hx; simp at hx)
    (by intro st hst; simp only [List.mem_singleton] at hst; rw [hst, hstepdef]
        exact Reachable.base hq0mem)
    ⟨hrootsWF', ?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ trivial hbound0 ?_ ?_ hdead)
  -- `connected`: the one open range is a singleton
  · intro i _ s hs t ht
    rw [hidx0 i (by omega)] at hs ht
    exact Or.inl (((hnewRange s).mp hs).trans ((hnewRange t).mp ht).symm)
  -- `chained`: there is no second range
  · intro i hi; exact absurd hi (by omega)
  -- `bitSound`/`entrySound`: the single fresh range and its entry marks both start empty
  · intro i hi m hm
    rw [hidx0 i hi, hroots0] at hm
    simp at hm
  · intro i hi m hm
    rw [hidx0 i hi, hroots0] at hm
    simp [marksToBitmask] at hm
  · intro st hst
    simp only [List.mem_singleton] at hst
    rw [hst]
    refine ⟨?_, ?_⟩
    · show step.pos < aux'.live.size
      rw [hpos0, hlivePush, Array.size_push]; omega
    · show aux'.live[step.pos]! = q0
      rw [hpos0]; exact hlive0'
  · trivial
  · intro j hj
    rw [hrootsSize] at hj
    rw [show j = 0 from by omega, hroots0]
    exact List.mem_map.mpr ⟨step, by simp, hpos0⟩
  · exact ⟨fun hc => by simp at hc, fun hc => by rw [hrootsSize] at hc; omega⟩
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
    · rw [hi, hroots0]
      exact marksToBitmask_lt (by simp)
    · rw [getElem!_neg aux'.roots i (by rw [hrootsSize]; omega)]
      exact getElem!_default_entry_lt numMarks
  -- the single fresh range holds only `q0`, which has dispatched nothing yet
  · intro i hi
    rw [hidx0 i hi]
    refine Or.inr ⟨fun t ht hexcl x hx => ?_, fun st hst hsr x hx => ?_⟩
    · exact absurd ((hnewRange t).mp ht).symm (hexcl step (by simp))
    · simp only [List.mem_singleton] at hst
      rw [hst, hstepdef] at hx
      simp at hx

private theorem dijkstraGetStatus_dead_mem [LawfulBEq State] [LawfulHashable State]
    {aux : DijkstraAux State} {q : State} (h : dijkstraGetStatus aux q = .dead) : q ∈ aux.dead := by
  unfold dijkstraGetStatus liveStatusOf at h
  by_cases hl : aux.liveIndex.contains q
  · rw [if_pos hl] at h; cases h
  · rw [if_neg hl] at h
    by_cases hd : aux.dead.contains q
    · exact Std.HashSet.mem_iff_contains.mpr hd
    · rw [if_neg hd] at h; cases h

/-- `dijkstra_dead_not_accepting` across the outer loop over the roots. -/
theorem dijkstraGo_dead_not_accepting [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs) :
    ∀ (roots : List State) aux (r : Option (State × List State) × DijkstraAux State),
    genericDFSGo (dijkstraOps numMarks) succs edgeMarks expand roots aux = some r →
    (∀ q ∈ roots, q ∈ initialStates) →
    DijkstraWellFormed aux → DijkstraRangeInv succs edgeMarks aux → aux.roots.size = 0 →
    (∀ s ∈ aux.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) →
    (r.1 = none →
      (∀ s ∈ r.2.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) ∧
      DijkstraWellFormed r.2 ∧ DijkstraRangeInv succs edgeMarks r.2 ∧ r.2.roots.size = 0) ∧
    (∀ anchor stem, r.1 = some (anchor, stem) →
      InternallyConnected succs (dijkstraSccHint r.2) ∧
      AcceptingMarks succs edgeMarks numMarks (dijkstraSccHint r.2) ∧
      anchor ∈ dijkstraSccHint r.2 ∧
      ∃ hs : stem ≠ [], stem.head hs ∈ initialStates ∧
        (∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs (stem[i])) ∧
        stem.getLast hs = anchor) := by
  refine genericDFSGo.partial_correctness (dijkstraOps numMarks) succs edgeMarks expand
    (fun roots aux r => (∀ q ∈ roots, q ∈ initialStates) →
      DijkstraWellFormed aux → DijkstraRangeInv succs edgeMarks aux → aux.roots.size = 0 →
      (∀ s ∈ aux.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) →
      (r.1 = none →
        (∀ s ∈ r.2.dead, ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) ∧
        DijkstraWellFormed r.2 ∧ DijkstraRangeInv succs edgeMarks r.2 ∧ r.2.roots.size = 0) ∧
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
    rcases hdfr : dfsFromRoot (dijkstraOps numMarks) succs edgeMarks expand aux q with ⟨found?, aux'⟩
    simp only [hdfr] at hr
    have haux'eq : (dfsFromRoot (dijkstraOps numMarks) succs edgeMarks expand aux q).2 = aux' := by rw [hdfr]
    have hgs' : dijkstraGetStatus aux q = .unknown := hgs
    obtain ⟨hdead', hbundle, hfound⟩ := dijkstraFromRoot_dead_not_accepting numMarks succs edgeMarks expand hexp
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

/-- After an empty search from `dijkstraInitAux`, no state in `dead` is in an `AcceptingSCC`, and the final state is
idle. -/
theorem dijkstra_genericDFS_dead_not_accepting [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs)
    (hnone : (genericDFS (dijkstraOps numMarks) succs edgeMarks expand initialStates dijkstraInitAux).1 = none) :
    (∀ s ∈ (genericDFS (dijkstraOps numMarks) succs edgeMarks expand initialStates dijkstraInitAux).2.dead,
      ∀ (A : AcceptingSCC initialStates succs edgeMarks numMarks), s ∉ A.scc) ∧
    DijkstraWellFormed (genericDFS (dijkstraOps numMarks) succs edgeMarks expand initialStates dijkstraInitAux).2 ∧
    DijkstraRangeInv succs edgeMarks
      (genericDFS (dijkstraOps numMarks) succs edgeMarks expand initialStates dijkstraInitAux).2 ∧
    (genericDFS (dijkstraOps numMarks) succs edgeMarks expand initialStates dijkstraInitAux).2.roots.size = 0 := by
  obtain ⟨r, hrr⟩ : ∃ r, genericDFSGo (dijkstraOps numMarks) succs edgeMarks expand initialStates
      dijkstraInitAux = some r := Option.ne_none_iff_exists'.mp (genericDFSGo_ne_none (dijkstraOps numMarks) succs edgeMarks expand _ _)
  have hgd : genericDFS (dijkstraOps numMarks) succs edgeMarks expand initialStates dijkstraInitAux = r := by
    show (genericDFSGo (dijkstraOps numMarks) succs edgeMarks expand initialStates dijkstraInitAux).getD _ = r
    rw [hrr]; rfl
  rw [hgd] at hnone ⊢
  exact (dijkstraGo_dead_not_accepting numMarks succs edgeMarks expand hexp initialStates hmarksBound
    fr initialStates dijkstraInitAux r hrr (fun _ hq => hq)
    dijkstraWellFormed_init dijkstraRangeInv_init
    (by simp [dijkstraInitAux]) (by intro s hs; simp [dijkstraInitAux] at hs)).1 hnone

/-- Soundness: whenever the search reports a counterexample, its hint is an accepting, internally connected set
containing the anchor. -/
theorem dijkstra_genericDFS_found_acceptingSCC [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs) :
    SccHintSound (dijkstraOps numMarks) succs edgeMarks expand numMarks initialStates := by
  unfold SccHintSound
  obtain ⟨r, hrr⟩ : ∃ r, genericDFSGo (dijkstraOps numMarks) succs edgeMarks expand initialStates
      dijkstraInitAux = some r := Option.ne_none_iff_exists'.mp (genericDFSGo_ne_none (dijkstraOps numMarks) succs edgeMarks expand _ _)
  have hgd : genericDFS (dijkstraOps numMarks) succs edgeMarks expand initialStates
      (dijkstraOps numMarks).initAux = r := by
    show (genericDFSGo (dijkstraOps numMarks) succs edgeMarks expand initialStates dijkstraInitAux).getD _ = r
    rw [hrr]; rfl
  rw [hgd]
  exact (dijkstraGo_dead_not_accepting numMarks succs edgeMarks expand hexp initialStates hmarksBound
    fr initialStates dijkstraInitAux r hrr (fun _ hq => hq)
    dijkstraWellFormed_init dijkstraRangeInv_init
    (by simp [dijkstraInitAux]) (by intro s hs; simp [dijkstraInitAux] at hs)).2

/-- Completeness: a search that reports no counterexample proves there is no reachable `AcceptingSCC`. -/
theorem dijkstra_no_acceptingSCC_of_none [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs)
    (hnone : (genericDFS (dijkstraOps numMarks) succs edgeMarks expand initialStates dijkstraInitAux).1 = none)
    (A : AcceptingSCC initialStates succs edgeMarks numMarks) : False := by
  obtain ⟨hdead, hwf, hrangeinv, hidle⟩ := dijkstra_genericDFS_dead_not_accepting numMarks succs edgeMarks expand hexp
    initialStates hmarksBound fr hnone
  obtain ⟨s, hs⟩ := A.nonempty
  have hexplored := dijkstraOps_returns_none_fully_explored numMarks succs edgeMarks expand hexp initialStates fr
    hnone s (A.reachable s hs)
  have hnotlive := dijkstraGetStatus_ne_live_of_idle hwf hrangeinv.rootsWF hidle s
  have hsdead : dijkstraGetStatus
      (genericDFS (dijkstraOps numMarks) succs edgeMarks expand initialStates dijkstraInitAux).2 s = .dead := by
    cases hst : dijkstraGetStatus
        (genericDFS (dijkstraOps numMarks) succs edgeMarks expand initialStates dijkstraInitAux).2 s with
    | dead => rfl
    | live => exact absurd hst hnotlive
    | unknown => exact absurd hst hexplored
  exact hdead s (dijkstraGetStatus_dead_mem hsdead) A hs

/-- Dijkstra's SCC-based emptiness check. -/
@[expose] def dijkstraCheck [LawfulBEq State] [LawfulHashable State] (succs : State → Array State)
    (initialStates : List State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) (numMarks : Nat) :
    EmptinessResult State :=
  checkWithWitness (dijkstraOps numMarks) succs edgeMarks expand numMarks initialStates


/-! ## The `TEmptinessChecker` contract -/

/-- Soundness: a reported `stem` and `loop` are a `TAcceptingCycle`'s stem and cycle. -/
theorem dijkstraCheck_nonEmpty_valid [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs)
    {stem loop : List State}
    (h : dijkstraCheck succs initialStates edgeMarks expand numMarks = .nonEmpty stem loop) :
    ∃ ac : TAcceptingCycle initialStates succs edgeMarks numMarks, ac.stem = stem ∧ ac.cycle = loop.tail :=
  checkWithWitness_nonEmpty_valid (dijkstraOps numMarks) succs edgeMarks expand numMarks initialStates
    (dijkstra_genericDFS_found_acceptingSCC numMarks succs edgeMarks expand hexp initialStates hmarksBound
      fr) h

/-- Completeness: an `.empty` answer proves no `TAcceptingCycle` exists. -/
theorem dijkstraCheck_empty_no_cycle [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs)
    {n : Nat} (h : dijkstraCheck succs initialStates edgeMarks expand numMarks = .empty n) :
    ¬∃ _ac : TAcceptingCycle initialStates succs edgeMarks numMarks, True := by
  have hnone := checkWithWitness_empty_of_none (dijkstraOps numMarks) succs edgeMarks expand numMarks initialStates
    (dijkstra_genericDFS_found_acceptingSCC numMarks succs edgeMarks expand hexp initialStates hmarksBound
      fr) h
  intro hcyc
  obtain ⟨A, -⟩ := acceptingSCC_iff_acceptingCycle.mpr hcyc
  exact dijkstra_no_acceptingSCC_of_none numMarks succs edgeMarks expand hexp initialStates hmarksBound
    fr hnone A

/-- `dijkstraCheck` as a `TEmptinessChecker`. -/
@[expose] def dijkstraTChecker [LawfulBEq State] [LawfulHashable State] [Inhabited State] :
    TEmptinessChecker State where
  check := dijkstraCheck
  nonEmpty_valid := fun {succs initialStates edgeMarks expand numMarks _stem _loop} fr hexp hmarksBound h =>
    dijkstraCheck_nonEmpty_valid numMarks succs edgeMarks expand hexp initialStates hmarksBound fr h
  empty_no_cycle := fun {succs initialStates edgeMarks expand numMarks _n} fr hexp hmarksBound h =>
    dijkstraCheck_empty_no_cycle numMarks succs edgeMarks expand hexp initialStates hmarksBound fr h

end LTLLib
