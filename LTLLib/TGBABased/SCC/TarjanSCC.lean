/-
  Algorithm 2 — Tarjan's SCC emptiness check: refines `GenericDFS.lean`'s
  abstract operations with low-link numbers.

  Renault, Duret-Lutz, Kordon, Poitrenaud, "Three SCC-based Emptiness
  Checks for Generalized Büchi Automata" (LPAR-19, 2013). See `TGBABased.md`.

  Deferred until after `DijkstraSCC.lean` is running and benchmarked. Algorithm spec transcribed
  below, see `TGBABased.md`'s "SCC algorithm refinements" section for the mechanics and how POP's
  own "report counterexample found" branch (lines 45-50 below) differs from Dijkstra/Gabow.


  struct P {lowlink : int; acc: 2F }
  live: hstack of ⟨Q⟩
  dead : store of ⟨Q⟩
  dstack : stack of ⟨P⟩

  GET STATUS(q ∈Q) → Status
    if live.get(q) ≠ -1
      return LIVE
    else if dead.has(q)
      return DEAD
    else
      return UNKNOWN

  UPDATE(acc ∈ 2^F, d ∈ Q)
    dstack.top().lowlink ←
      min(dstack.top().lowlink , live.get(d))
    dstack.top().acc ← acc ∪ dstack.top().acc
    if dstack.top().acc = F
      report counterexample found

  PUSH(q ∈Q) → Position
    Position p ← live.size()
    live.push(⟨q⟩)
    dstack.push(⟨p , ∅ ⟩)
    return p

  POP(s ∈Step)
    ⟨ll , acc ⟩ ← dstack.pop()
    if ll = s.pos
      // An SCC has been found.
      while live.size() > s.pos
        ⟨q⟩ ← live.pop()
        dead.add(q)
    else
      stack.top().lowlink ←
        min(dstack.top().lowlink, ll)
      dstack.top().acc ← s.acc ∪ dstack.top().acc ∪ acc
      if dstack.top().acc = F
        report counterexample found

  `tarjanSCCs_sound` holds, `tarjanSCCs` being `SCCEnumeration.lean`'s recording run at `tarjanView` rather
  than an enumeration of its own. Unproved for now: `tarjan_sccHintSound` and `tarjan_no_acceptingSCC_of_none`
  carry `sorry`, and the `TEmptinessChecker` instance below them is derived from the two.

  Sections:
  - Tarjan's search state
  - PUSH and UPDATE
  - POP
  - Witness extraction and the `DFSOps` instance
  - SCC enumeration
  - The `TEmptinessChecker` contract
-/

import Std
import LTLLib.AbstractSpec.EmptinessCheck
import LTLLib.AbstractSpec.GraphPaths
import LTLLib.TGBABased.AbstractSpec.EmptinessCheck
import LTLLib.TGBABased.AbstractSpec.SCCTheory
import LTLLib.TGBABased.SCC.GenericDFS
import LTLLib.TGBABased.SCC.LiveStack
import LTLLib.TGBABased.SCC.SCCEnumeration

namespace LTLLib

variable {State : Type u} [BEq State] [Hashable State]

/-! ## Tarjan's search state -/

/-- Tarjan's private search state, `dstack` being the paper's stack of `⟨lowlink, acc⟩`. The paper's `s.acc`
is the driver's own frame, which POP is handed, so nothing about the DFS stack is mirrored here. -/
structure TarjanAux (State : Type u) [BEq State] [Hashable State] where
  live : Array State
  liveIndex : Std.HashMap State Nat -- position of each live state, for O(1) membership
  dead : Std.HashSet State
  dstack : Array (Nat × Nat)  -- (lowlink, merged acc bitmask)

def tarjanInitAux : TarjanAux State where
  live := #[]
  liveIndex := Std.HashMap.emptyWithCapacity 0
  dead := Std.HashSet.emptyWithCapacity 0
  dstack := #[]

def tarjanGetStatus (aux : TarjanAux State) (q : State) : DFSStatus :=
  if aux.liveIndex.contains q then .live else if aux.dead.contains q then .dead else .unknown

/-- The all-ones mask, so `acc = F` is an O(1) equality. -/
private def fullMask (numMarks : Nat) : Nat := (1 <<< numMarks) - 1

/-! ## PUSH and UPDATE -/

/-- `PUSH`, lines 20-24: a fresh frame is its own lowlink with no marks yet. The edge's marks are not stored,
POP reads them off the driver's frame. -/
def tarjanPush (aux : TarjanAux State) (q : State) (_marks : Std.HashSet Nat) :
    TarjanAux State × Nat :=
  let pos := aux.live.size
  ({ aux with
      live := aux.live.push q
      liveIndex := aux.liveIndex.insert q pos
      dstack := aux.dstack.push (pos, 0) },
   pos)

/-- `UPDATE`, lines 12-16: a back-edge lowers the top frame's lowlink to its target and folds in the edge's marks. -/
def tarjanUpdate (numMarks : Nat) (aux : TarjanAux State)
    (marks : Std.HashSet Nat) (d : State) : TarjanAux State × Bool :=
  match aux.dstack.back? with
  | none => (aux, false)
  | some (ll, acc) =>
    let acc' := acc ||| marksToBitmask marks
    ({ aux with dstack := aux.dstack.pop.push (min ll (aux.liveIndex.getD d 0), acc') },
     acc' == fullMask numMarks)

/-! ## POP -/

/-- `POP`, lines 27-38. Unlike Dijkstra's, the merge into the parent happens here rather than on the back-edge,
so this is the one refinement whose POP can report a counterexample. `step.acc` is the spec's `s.acc`. -/
def tarjanPop (numMarks : Nat) (aux : TarjanAux State) (step : DFSStep State Nat) :
    TarjanAux State × Bool :=
  match aux.dstack.back? with
  | none => (aux, false)
  | some (ll, acc) =>
    let dstack' := aux.dstack.pop
    if ll = step.pos then
      let (live, liveIndex, dead) := liveFlush aux.live aux.liveIndex aux.dead step.pos
      ({ aux with dstack := dstack', live := live, liveIndex := liveIndex, dead := dead }, false)
    else
      match dstack'.back? with
      | none => ({ aux with dstack := dstack' }, false)
      | some (pll, pacc) =>
        let pacc' := pacc ||| step.acc ||| acc
        ({ aux with dstack := dstack'.pop.push (min pll ll, pacc') },
         pacc' == fullMask numMarks)

/-! ## Witness extraction and the `DFSOps` instance -/

/-- The open SCC candidate at the top frame, which is every live state from its lowlink upwards. -/
def tarjanSccHint (aux : TarjanAux State) : Std.HashSet State :=
  match aux.dstack.back? with
  | none => Std.HashSet.emptyWithCapacity 0
  | some (ll, _) =>
    (aux.live.extract ll aux.live.size).foldl
      (init := Std.HashSet.emptyWithCapacity 0) fun acc s => acc.insert s

def tarjanOps (numMarks : Nat) : DFSOps State where
  Aux := TarjanAux State
  Position := Nat
  initAux := tarjanInitAux
  sccHint := tarjanSccHint
  numExplored := fun aux => aux.live.size + aux.dead.size
  getStatus := tarjanGetStatus
  push := tarjanPush
  update := tarjanUpdate numMarks
  pop := fun _succs _edgeMarks aux step => tarjanPop numMarks aux step

/-- POP either leaves the live and dead bookkeeping alone, or flushes it at the closing frame's position. -/
private theorem tarjanPop_triple (numMarks : Nat) (aux : TarjanAux State) (step : DFSStep State Nat) :
    ((tarjanPop numMarks aux step).1.live, (tarjanPop numMarks aux step).1.liveIndex,
        (tarjanPop numMarks aux step).1.dead) = (aux.live, aux.liveIndex, aux.dead) ∨
      ((tarjanPop numMarks aux step).1.live, (tarjanPop numMarks aux step).1.liveIndex,
        (tarjanPop numMarks aux step).1.dead) = liveFlush aux.live aux.liveIndex aux.dead step.pos := by
  rcases hb : aux.dstack.back? with _ | ⟨ll, acc⟩
  · exact Or.inl (by simp [tarjanPop, hb])
  · by_cases h : ll = step.pos
    · exact Or.inr (by simp [tarjanPop, hb, h])
    · rcases hb2 : aux.dstack.pop.back? with _ | ⟨pll, pacc⟩ <;>
        exact Or.inl (by simp [tarjanPop, hb, h, hb2])

/-- `tarjanOps` is a lawful refinement: `LiveWF` is preserved by PUSH, UPDATE and POP, and the three
status-transition laws hold. -/
def tarjanLawful [Inhabited State] [LawfulBEq State] [LawfulHashable State] (numMarks : Nat) :
    LawfulDFSOps (tarjanOps numMarks (State := State)) where
  WellFormed := fun aux => LiveWF aux.live aux.liveIndex
  wf_push := fun aux q marks hq hwf => by
    show LiveWF (aux.live.push q) (aux.liveIndex.insert q aux.live.size)
    refine hwf.push ?_
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    rw [show (tarjanOps numMarks).getStatus aux q = liveStatusOf aux.liveIndex aux.dead q from rfl,
      liveStatusOf, if_pos hc] at hq
    exact absurd hq (by simp)
  wf_update := fun aux marks d hwf => by
    show LiveWF (tarjanUpdate numMarks aux marks d).1.live
      (tarjanUpdate numMarks aux marks d).1.liveIndex
    rcases hb : aux.dstack.back? with _ | ⟨ll, acc⟩ <;> simpa [tarjanUpdate, hb] using hwf
  wf_pop := fun _succs _edgeMarks aux step hwf => by
    show LiveWF (tarjanPop numMarks aux step).1.live (tarjanPop numMarks aux step).1.liveIndex
    rcases tarjanPop_triple numMarks aux step with h | h
    · have h1 : (tarjanPop numMarks aux step).1.live = aux.live := congrArg (fun t => t.1) h
      have h2 : (tarjanPop numMarks aux step).1.liveIndex = aux.liveIndex :=
        congrArg (fun t => t.2.1) h
      rw [h1, h2]; exact hwf
    · have h1 : (tarjanPop numMarks aux step).1.live =
          (liveFlush aux.live aux.liveIndex aux.dead step.pos).1 := congrArg (fun t => t.1) h
      have h2 : (tarjanPop numMarks aux step).1.liveIndex =
          (liveFlush aux.live aux.liveIndex aux.dead step.pos).2.1 := congrArg (fun t => t.2.1) h
      rw [h1, h2]; exact hwf.flush step.pos
  push_status := fun aux q marks q' => liveStatusOf_insert aux.liveIndex aux.dead q aux.live.size q'
  update_status := fun aux marks d q => by
    show liveStatusOf (tarjanUpdate numMarks aux marks d).1.liveIndex
      (tarjanUpdate numMarks aux marks d).1.dead q = liveStatusOf aux.liveIndex aux.dead q
    rcases hb : aux.dstack.back? with _ | ⟨ll, acc⟩ <;> simp [tarjanUpdate, hb]
  pop_status := fun _succs _edgeMarks aux step q hwf => by
    show liveStatusOf (tarjanPop numMarks aux step).1.liveIndex
          (tarjanPop numMarks aux step).1.dead q = liveStatusOf aux.liveIndex aux.dead q ∨
        (liveStatusOf aux.liveIndex aux.dead q = .live ∧
          liveStatusOf (tarjanPop numMarks aux step).1.liveIndex
            (tarjanPop numMarks aux step).1.dead q = .dead)
    rcases tarjanPop_triple numMarks aux step with h | h
    · have h2 : (tarjanPop numMarks aux step).1.liveIndex = aux.liveIndex :=
        congrArg (fun t => t.2.1) h
      have h3 : (tarjanPop numMarks aux step).1.dead = aux.dead := congrArg (fun t => t.2.2) h
      rw [h2, h3]
      exact Or.inl rfl
    · have h2 : (tarjanPop numMarks aux step).1.liveIndex =
          (liveFlush aux.live aux.liveIndex aux.dead step.pos).2.1 := congrArg (fun t => t.2.1) h
      have h3 : (tarjanPop numMarks aux step).1.dead =
          (liveFlush aux.live aux.liveIndex aux.dead step.pos).2.2 := congrArg (fun t => t.2.2) h
      rw [h2, h3]
      exact (liveFlush_spec step.pos aux.live aux.liveIndex aux.dead hwf.fwd hwf.bwd).2.2 q

/-! ## SCC enumeration

The sequence of sets POP flushes, named so the enumeration contract can be stated about it and so it can be
checked against a brute-force computation. It is not the hot path. A prune-based fairness check tests each set
as POP closes it and stores none of them, which is what `SCCEnumerationSound`'s covering clause justifies.
See `StreettPrune.md`. -/

/-- Tarjan's window onto its own search state, for the shared flush-enumeration contract. -/
def tarjanView (numMarks : Nat) : LowlinkView (tarjanOps numMarks (State := State)) where
  live := fun aux => aux.live
  liveIndex := fun aux => aux.liveIndex
  dead := fun aux => aux.dead
  lowlinks := fun aux => aux.dstack.map (·.1)
  accs := fun aux => aux.dstack.map (·.2)
  extraAcc := 0
  posNat := id

/-- Tarjan's search obeys the shared lowlink discipline, which is what lets `enumSCCs_sound` speak about the
sets its own POP flushes. -/
def tarjanLowlinkLawful (numMarks : Nat) :
    LowlinkLawful (tarjanOps numMarks (State := State)) (tarjanView numMarks) where
  status := fun _ _ => rfl
  push_live := fun _ _ _ => rfl
  push_liveIndex := fun _ _ _ => rfl
  push_dead := fun _ _ _ => rfl
  push_lowlinks := fun _ _ _ => by simp [tarjanView, tarjanOps, tarjanPush]
  push_accs := fun _ _ _ => by simp [tarjanView, tarjanOps, tarjanPush]
  push_pos := fun _ _ _ => rfl
  update_live := fun aux m d => by
    rcases hb : aux.dstack.back? with _ | ⟨ll, acc⟩ <;>
      simp [tarjanView, tarjanOps, tarjanUpdate, hb]
  update_liveIndex := fun aux m d => by
    rcases hb : aux.dstack.back? with _ | ⟨ll, acc⟩ <;>
      simp [tarjanView, tarjanOps, tarjanUpdate, hb]
  update_dead := fun aux m d => by
    rcases hb : aux.dstack.back? with _ | ⟨ll, acc⟩ <;>
      simp [tarjanView, tarjanOps, tarjanUpdate, hb]
  update_lowlinks := fun aux m d ll hll => by
    simp only [tarjanView, Array.back?_map, Option.map_eq_some_iff] at hll
    obtain ⟨⟨ll', acc⟩, hb, rfl⟩ := hll
    simp [tarjanView, tarjanOps, tarjanUpdate, hb, Array.map_pop]
  update_accs := fun aux m d acc hacc => by
    simp only [tarjanView, Array.back?_map, Option.map_eq_some_iff] at hacc
    obtain ⟨⟨ll', acc'⟩, hb, rfl⟩ := hacc
    simp [tarjanView, tarjanOps, tarjanUpdate, hb, Array.map_pop]
  pop_close := fun succs edgeMarks aux step hcl => by
    simp only [LowlinkView.closes, tarjanView, Array.back?_map, beq_iff_eq,
      Option.map_eq_some_iff] at hcl
    obtain ⟨⟨ll, acc⟩, hb, hll⟩ := hcl
    have hll' : ll = step.pos := by simpa using hll
    subst hll'
    exact ⟨by simp [tarjanView, tarjanOps, tarjanPop, hb],
      by simp [tarjanView, tarjanOps, tarjanPop, hb, Array.map_pop],
      by simp [tarjanView, tarjanOps, tarjanPop, hb, Array.map_pop]⟩
  pop_merge := fun succs edgeMarks aux step hcl => by
    rcases hb : aux.dstack.back? with _ | ⟨ll, acc⟩
    · exact ⟨by simp [tarjanView, tarjanOps, tarjanPop, hb],
        by simp [tarjanView, tarjanOps, tarjanPop, hb],
        by simp [tarjanView, tarjanOps, tarjanPop, hb]⟩
    · have hne : ll ≠ step.pos := by
        intro hEq
        simp only [LowlinkView.closes, tarjanView, Array.back?_map, hb, hEq] at hcl
        simp at hcl
      rcases hb2 : aux.dstack.pop.back? with _ | ⟨pll, pacc⟩ <;>
        exact ⟨by simp [tarjanView, tarjanOps, tarjanPop, hb, hne, hb2],
          by simp [tarjanView, tarjanOps, tarjanPop, hb, hne, hb2],
          by simp [tarjanView, tarjanOps, tarjanPop, hb, hne, hb2]⟩
  pop_merge_lowlinks := fun succs edgeMarks aux step ll hcl hb => by
    simp only [tarjanView, Array.back?_map, Option.map_eq_some_iff] at hb
    obtain ⟨⟨ll', acc⟩, hbk, hll⟩ := hb
    simp only at hll
    subst hll
    have hne : ll' ≠ step.pos := by
      intro hEq
      simp only [LowlinkView.closes, tarjanView, Array.back?_map, hbk, hEq] at hcl
      simp at hcl
    have hmb : ((aux.dstack.map (·.1)).pop).back? = Option.map (·.1) (aux.dstack.pop.back?) := by
      rw [← Array.map_pop, Array.back?_map]
    rcases hb2 : aux.dstack.pop.back? with _ | ⟨pll, pacc⟩
    · simp only [tarjanView, tarjanOps, tarjanPop, hbk, if_neg hne, hb2, hmb,
        Option.map_none, Array.map_pop]
    · simp only [tarjanView, tarjanOps, tarjanPop, hbk, if_neg hne, hb2, hmb,
        Option.map_some, Array.map_pop, Array.map_push]
  pop_merge_accs := fun succs edgeMarks aux step acc hcl hb => by
    simp only [tarjanView, Array.back?_map, Option.map_eq_some_iff] at hb
    obtain ⟨⟨ll', acc'⟩, hbk, hac⟩ := hb
    simp only at hac
    subst hac
    have hne : ll' ≠ step.pos := by
      intro hEq
      simp only [LowlinkView.closes, tarjanView, Array.back?_map, hbk, hEq] at hcl
      simp at hcl
    have hmb : ((aux.dstack.map (·.2)).pop).back? = Option.map (·.2) (aux.dstack.pop.back?) := by
      rw [← Array.map_pop, Array.back?_map]
    rcases hb2 : aux.dstack.pop.back? with _ | ⟨pll, pacc⟩
    · simp only [tarjanView, tarjanOps, tarjanPop, hbk, if_neg hne, hb2, hmb,
        Option.map_none, Array.map_pop]
    · simp [tarjanView, tarjanOps, tarjanPop, hbk, if_neg hne, hb2, hmb, Array.map_pop]
  init_live := rfl
  init_dead := by simp [tarjanView, tarjanOps, tarjanInitAux]
  init_lowlinks := by simp [tarjanView, tarjanOps, tarjanInitAux]
  init_accs := by simp [tarjanView, tarjanOps, tarjanInitAux]
  init_status := by simp [tarjanOps, tarjanGetStatus, tarjanInitAux]

/-- Every maximal SCC reachable from `initialStates`, trivial ones included, in the order POP closes them. The
recording run never reports, so the `numMarks` it runs at is irrelevant. -/
def tarjanSCCs [LawfulBEq State] [LawfulHashable State] (succs : State → Array State)
    (initialStates : List State) : List (Std.HashSet State) :=
  enumSCCs (tarjanOps 0) (tarjanView 0) succs (fun _ _ => ∅) initialStates

/-- The maximal SCCs of the subgraph `inside` induced on the states `keep` admits, which is what the prune
recurses on. Derived rather than primitive, since every state of the restricted graph is an initial state of
it, so its reachability is trivial and its `succs` is the existing `sccSuccs`. -/
def tarjanSCCsWithin [LawfulBEq State] [LawfulHashable State] (succs : State → Array State)
    (inside : Std.HashSet State) (keep : State → Bool) : List (Std.HashSet State) :=
  let C := inside.filter fun s => keep s
  tarjanSCCs (sccSuccs succs C) C.toList

/-- The flushes are the maximal SCCs of the reachable subgraph, by instantiating the shared contract at
`tarjanView`. -/
theorem tarjanSCCs_sound [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (succs : State → Array State) (initialStates : List State)
    (fr : FiniteReach initialStates succs) :
    SCCEnumerationSound initialStates succs (tarjanSCCs succs initialStates) :=
  enumSCCs_sound (tarjanOps 0) (tarjanView 0) (tarjanLowlinkLawful 0) (tarjanLawful 0)
    (liveWF_init 0) succs (fun _ _ => ∅) initialStates fr

/-! ## The `TEmptinessChecker` contract

The two obligations are stated but not yet discharged. `tarjan_sccHintSound` is the driver-level contract that
`checkWithWitness` needs, and `tarjan_no_acceptingSCC_of_none` is the completeness half, both mirroring the
`DijkstraSCC.lean` theorems of the same shape. Everything below them is derived, so proving these two closes
the file. -/

/-- Soundness obligation, mirroring `dijkstra`'s. -/
theorem tarjan_sccHintSound [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs) :
    SccHintSound (tarjanOps numMarks) succs edgeMarks numMarks initialStates := by
  sorry

/-- Completeness obligation, mirroring `dijkstra_no_acceptingSCC_of_none`. -/
theorem tarjan_no_acceptingSCC_of_none [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs)
    (hnone : (genericDFS (tarjanOps numMarks) succs edgeMarks initialStates tarjanInitAux).1 = none)
    (A : AcceptingSCC initialStates succs edgeMarks numMarks) : False := by
  sorry

/-- Tarjan's SCC-based emptiness check, sharing `checkWithWitness`'s witness reconstruction with Dijkstra's. -/
def tarjanCheck [LawfulBEq State] [LawfulHashable State] (succs : State → Array State)
    (initialStates : List State) (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat) :
    EmptinessResult State :=
  checkWithWitness (tarjanOps numMarks) succs edgeMarks numMarks initialStates

/-- Soundness (`TEmptinessChecker.nonEmpty_valid`):
A reported `stem`/`loop` really is a `TAcceptingCycle`'s own stem and cycle. -/
theorem tarjanCheck_nonEmpty_valid [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs)
    {stem loop : List State}
    (h : tarjanCheck succs initialStates edgeMarks numMarks = .nonEmpty stem loop) :
    ∃ ac : TAcceptingCycle initialStates succs edgeMarks numMarks, ac.stem = stem ∧ ac.cycle = loop.tail :=
  checkWithWitness_nonEmpty_valid (tarjanOps numMarks) succs edgeMarks numMarks initialStates
    (tarjan_sccHintSound numMarks succs edgeMarks initialStates hmarksBound fr) h

/-- Completeness (`TEmptinessChecker.empty_no_cycle`): An `.empty` answer proves no `TAcceptingCycle` exists. -/
theorem tarjanCheck_empty_no_cycle [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs)
    {n : Nat} (h : tarjanCheck succs initialStates edgeMarks numMarks = .empty n) :
    ¬∃ _ac : TAcceptingCycle initialStates succs edgeMarks numMarks, True := by
  have hnone := checkWithWitness_empty_of_none (tarjanOps numMarks) succs edgeMarks numMarks initialStates
    (tarjan_sccHintSound numMarks succs edgeMarks initialStates hmarksBound fr) h
  intro hcyc
  obtain ⟨A, -⟩ := acceptingSCC_iff_acceptingCycle.mpr hcyc
  exact tarjan_no_acceptingSCC_of_none numMarks succs edgeMarks initialStates hmarksBound fr hnone A

/-- `tarjanCheck` packaged as a `TEmptinessChecker` instance, interchangeable with `dijkstraTChecker`. -/
def tarjanTChecker [LawfulBEq State] [LawfulHashable State] [Inhabited State] :
    TEmptinessChecker State where
  check := fun succs initialStates _fr edgeMarks numMarks =>
    tarjanCheck succs initialStates edgeMarks numMarks
  nonEmpty_valid := fun {succs initialStates fr edgeMarks numMarks _stem _loop} hmarksBound h =>
    tarjanCheck_nonEmpty_valid numMarks succs edgeMarks initialStates hmarksBound fr h
  empty_no_cycle := fun {succs initialStates fr edgeMarks numMarks _n} hmarksBound h =>
    tarjanCheck_empty_no_cycle numMarks succs edgeMarks initialStates hmarksBound fr h

end LTLLib
