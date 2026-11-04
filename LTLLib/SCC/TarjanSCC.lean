module

/-
  Tarjan's SCC-based emptiness check (Algorithm 2 of [RDKP13]), refining `GenericDFS.lean`'s abstract operations with
  low-link numbers. It reports only at a closing POP whose merged accumulator is full, instead of the paper's early exit
  at UPDATE and at a merging POP, so the hint is always the flushed maximal SCC, connected by construction.

  Defines:
  - `TarjanAux`, `tarjanOps`: the search state and the refinement
  - `tarjanSCCs`, `tarjanSCCsWithin`: the maximal SCCs POP flushes, of the reachable graph and of an induced subgraph
  - `tarjanCheck`, `tarjanTChecker`: the emptiness check and its `TEmptinessChecker` instance

  Proves:
  - `tarjanSCCs_sound`: the flushes are the maximal SCCs of the reachable subgraph
  - `tarjan_acceptingMarks_of_full`, `tarjan_full_of_acceptingMarks`: at a closing POP the accumulator is full iff the
    flushed set covers every mark
  - `tarjanCheck_nonEmpty_valid`, `tarjanCheck_empty_no_cycle`: a reported stem and loop form a `TAcceptingCycle`, and an
    `.empty` answer proves none exists

  References:
  - [RDKP13] Renault, Duret-Lutz, Kordon, Poitrenaud. Three SCC-based Emptiness Checks for Generalized Büchi
    Automata. LPAR-19, 2013.
  - [CCLMT18] Chen, Cohen, Lévy, Merz, Théry. Formal Proofs of Tarjan's Algorithm in Why3, Coq, and Isabelle.
    arXiv:1810.11979, 2018.

  Sections:
  - Tarjan's search state
  - PUSH and UPDATE
  - POP
  - Witness extraction and the `DFSOps` instance
  - SCC enumeration
  - The accepting-mask test
  - The `TEmptinessChecker` contract
-/

public import Std
public import LTLLib.AbstractSpec.Reachability
public import LTLLib.AbstractSpec.GraphPaths
public import LTLLib.AbstractSpec.EmptinessCheck
public import LTLLib.AbstractSpec.SCCTheory
public import LTLLib.SCC.GenericDFS
public import LTLLib.SCC.LiveStack
public import LTLLib.SCC.SCCEnumeration
meta import Lentil
meta import LTLLib.Tactic.Set

public section

namespace LTLLib

variable {State : Type u} [BEq State] [Hashable State]

/-! ## Tarjan's search state

`acc` carries the property marks in bits `0 ..< numMarks` and "this frame's component has an internal edge" in bit
`numMarks`, the layout of `StreettPrune.lean`. -/

/-- Tarjan's private search state, `dstack` being the paper's stack of `⟨lowlink, acc⟩`. -/
structure TarjanAux (State : Type u) [BEq State] [Hashable State] where
  live : Array State
  liveIndex : Std.HashMap State Nat -- position of each live state, for O(1) membership
  dead : Std.HashSet State
  dstack : Array (Nat × Nat)  -- (lowlink, merged acc bitmask)
  witness : Array State  -- the flushed range at the reporting closing POP, empty until one is found

@[expose] def tarjanInitAux : TarjanAux State where
  live := #[]
  liveIndex := Std.HashMap.emptyWithCapacity 0
  dead := Std.HashSet.emptyWithCapacity 0
  dstack := #[]
  witness := #[]

@[expose] def tarjanGetStatus (aux : TarjanAux State) (q : State) : DFSStatus :=
  if aux.liveIndex.contains q then .live else if aux.dead.contains q then .dead else .unknown

/-- The all-ones mask including the internal-edge bit, so `acc = F` is an O(1) equality. -/
private def fullMask (numMarks : Nat) : Nat := (1 <<< (numMarks + 1)) - 1

/-! ## PUSH and UPDATE -/

/-- `PUSH`, lines 20-24: a fresh frame is its own lowlink with no marks yet. The edge's marks are not stored,
POP reads them off the driver's frame. -/
@[expose] def tarjanPush (aux : TarjanAux State) (q : State) (_marks : Std.HashSet Nat) :
    TarjanAux State × Nat :=
  let pos := aux.live.size
  ({ aux with
      live := aux.live.push q
      liveIndex := aux.liveIndex.insert q pos
      dstack := aux.dstack.push (pos, 0) },
   pos)

/-- `UPDATE`, lines 12-16: a back-edge lowers the top frame's lowlink to its target and folds in the edge's marks
and the internal-edge bit. It never reports. -/
@[expose] def tarjanUpdate (numMarks : Nat) (aux : TarjanAux State)
    (marks : Std.HashSet Nat) (d : State) : TarjanAux State × Bool :=
  match aux.dstack.back? with
  | none => (aux, false)
  | some (ll, acc) =>
    let acc' := acc ||| marksToBitmask marks ||| (1 <<< numMarks)
    ({ aux with dstack := aux.dstack.pop.push (min ll (aux.liveIndex.getD d 0), acc') }, false)

/-! ## POP -/

/-- `POP`, lines 27-38, testing the merged accumulator only once a frame closes rather than at every merge. -/
def tarjanPop (numMarks : Nat) (aux : TarjanAux State) (step : DFSStep State Nat) :
    TarjanAux State × Bool :=
  match aux.dstack.back? with
  | none => (aux, false)
  | some (ll, acc) =>
    let dstack' := aux.dstack.pop
    if ll = step.pos then
      if acc == fullMask numMarks then
        let witness := aux.live.extract step.pos aux.live.size
        let (live, liveIndex, dead) := liveFlush aux.live aux.liveIndex aux.dead step.pos
        ({ aux with
            dstack := dstack'
            live := live
            liveIndex := liveIndex
            dead := dead
            witness := witness }, true)
      else
        let (live, liveIndex, dead) := liveFlush aux.live aux.liveIndex aux.dead step.pos
        ({ aux with
            dstack := dstack'
            live := live
            liveIndex := liveIndex
            dead := dead }, false)
    else
      match dstack'.back? with
      | none => ({ aux with dstack := dstack' }, false)
      | some (pll, pacc) =>
        let pacc' := pacc ||| step.acc ||| acc ||| (1 <<< numMarks)
        ({ aux with dstack := dstack'.pop.push (min pll ll, pacc') }, false)

/-! ## Witness extraction and the `DFSOps` instance -/

/-- The SCC the test accepted, empty until POP reports. -/
def tarjanSccHint (aux : TarjanAux State) : Std.HashSet State :=
  aux.witness.foldl (init := Std.HashSet.emptyWithCapacity 0) fun h s => h.insert s

/-- Tarjan's check as a `DFSOps` instance, Algorithm 2 of [RDKP13]. -/
@[expose] def tarjanOps (numMarks : Nat) : DFSOps State where
  Aux := TarjanAux State
  Position := Nat
  initAux := tarjanInitAux
  sccHint := tarjanSccHint
  numExplored := fun aux => aux.live.size + aux.dead.size
  getStatus := tarjanGetStatus
  push := tarjanPush
  update := tarjanUpdate numMarks
  pop := fun _succs _edgeMarks aux step => tarjanPop numMarks aux step

/-- UPDATE never reports. -/
private theorem tarjanUpdate_snd (numMarks : Nat) (aux : TarjanAux State) (marks : Std.HashSet Nat) (d : State) :
    (tarjanUpdate numMarks aux marks d).2 = false := by
  rcases hb : aux.dstack.back? with _ | ⟨ll, acc⟩ <;> simp [tarjanUpdate, hb]

/-- POP either leaves the live and dead bookkeeping alone, or flushes it at the closing frame's position. -/
private theorem tarjanPop_triple (numMarks : Nat) (aux : TarjanAux State) (step : DFSStep State Nat) :
    ((tarjanPop numMarks aux step).1.live, (tarjanPop numMarks aux step).1.liveIndex,
        (tarjanPop numMarks aux step).1.dead) = (aux.live, aux.liveIndex, aux.dead) ∨
      ((tarjanPop numMarks aux step).1.live, (tarjanPop numMarks aux step).1.liveIndex,
        (tarjanPop numMarks aux step).1.dead) = liveFlush aux.live aux.liveIndex aux.dead step.pos := by
  rcases hb : aux.dstack.back? with _ | ⟨ll, acc⟩
  · exact Or.inl (by simp [tarjanPop, hb])
  · by_cases h : ll = step.pos
    · by_cases hacc : acc == fullMask numMarks
      · exact Or.inr (by simp only [tarjanPop, hb, if_pos h, if_pos hacc])
      · exact Or.inr (by simp only [tarjanPop, hb, if_pos h, if_neg hacc])
    · rcases hb2 : aux.dstack.pop.back? with _ | ⟨pll, pacc⟩ <;>
        exact Or.inl (by simp [tarjanPop, hb, h, hb2])

/-- POP reports only at a closing frame whose accumulator is full, recording the flushed range as the witness. -/
private theorem tarjanPop_eq_true (numMarks : Nat) {aux aux' : TarjanAux State} {step : DFSStep State Nat}
    (h : tarjanPop numMarks aux step = (aux', true)) :
    aux.dstack.back? = some (step.pos, fullMask numMarks) ∧
      aux'.witness = aux.live.extract step.pos aux.live.size := by
  have h2 : (tarjanPop numMarks aux step).2 = true := by rw [h]
  have hw : aux'.witness = (tarjanPop numMarks aux step).1.witness := by rw [h]
  rw [hw]
  rcases hb : aux.dstack.back? with _ | ⟨ll, acc⟩
  · simp only [tarjanPop, hb, Bool.false_eq_true] at h2
  · by_cases hll : ll = step.pos
    · by_cases hacc : acc == fullMask numMarks
      · have hacc' : acc = fullMask numMarks := by simpa using hacc
        exact ⟨by simp only [hll, hacc'], by simp only [tarjanPop, hb, if_pos hll, if_pos hacc]⟩
      · simp only [tarjanPop, hb, if_pos hll, if_neg hacc, Bool.false_eq_true] at h2
    · rcases hb2 : aux.dstack.pop.back? with _ | ⟨pll, pacc⟩ <;>
        simp only [tarjanPop, hb, if_neg hll, hb2, Bool.false_eq_true] at h2

/-- `tarjanOps` is a lawful refinement: PUSH, UPDATE and POP preserve `LiveWF`, and the three status laws hold. -/
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

The sequence of sets POP flushes, stated against the shared enumeration contract. -/

/-- Tarjan's view of its search state for the flush-enumeration contract, `extraAcc` being the internal-edge bit. -/
@[expose] def tarjanView (numMarks : Nat) : LowlinkView (tarjanOps numMarks (State := State)) where
  live := fun aux => aux.live
  liveIndex := fun aux => aux.liveIndex
  dead := fun aux => aux.dead
  lowlinks := fun aux => aux.dstack.map (·.1)
  accs := fun aux => aux.dstack.map (·.2)
  extraAcc := 1 <<< numMarks
  posNat := id

/-- Tarjan's search obeys the shared lowlink discipline. -/
theorem tarjanLowlinkLawful (numMarks : Nat) :
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
    refine ⟨?_, ?_, ?_⟩
    · by_cases hacc : acc == fullMask numMarks
      · simp only [tarjanView, tarjanOps, tarjanPop, hb, if_pos hll', if_pos hacc]; rfl
      · simp only [tarjanView, tarjanOps, tarjanPop, hb, if_pos hll', if_neg hacc]; rfl
    · subst hll'
      grind [tarjanPop, Array.map_pop, tarjanView, tarjanOps]
    · subst hll'
      grind [tarjanPop, Array.map_pop, tarjanView, tarjanOps]
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
recording run never reports, so `numMarks` is irrelevant. -/
@[expose] def tarjanSCCs [LawfulBEq State] [LawfulHashable State] (succs : State → Array State)
    (initialStates : List State) : List (Std.HashSet State) :=
  -- the recording run carries no marks, so the fused expansion is the plain successors with empty marks
  enumSCCs (tarjanOps 0) (tarjanView 0) succs (fun _ _ => ∅)
    (fun s => (succs s, (succs s).map (fun _ => ∅), #[])) initialStates

/-- The maximal SCCs of the subgraph induced on the states of `inside` that `keep` admits. -/
@[expose] def tarjanSCCsWithin [LawfulBEq State] [LawfulHashable State] (succs : State → Array State)
    (inside : Std.HashSet State) (keep : State → Bool) : List (Std.HashSet State) :=
  let C := inside.filter fun s => keep s
  tarjanSCCs (sccSuccs succs C) C.toList

/-- The flushes are the maximal SCCs of the reachable subgraph. -/
theorem tarjanSCCs_sound [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (succs : State → Array State) (initialStates : List State)
    (fr : FiniteReach initialStates succs) :
    SCCEnumerationSound initialStates succs (tarjanSCCs succs initialStates) :=
  enumSCCs_sound (tarjanOps 0) (tarjanView 0) (tarjanLowlinkLawful 0) (tarjanLawful 0)
    (liveWF_init 0) succs (fun _ _ => ∅) (fun s => (succs s, (succs s).map (fun _ => ∅), #[]))
    (fun _ => rfl) initialStates fr

/-! ## The accepting-mask test

Both directions of `accAt 0 = fullMask numMarks ↔ AcceptingMarks` on the flushed set at a closing POP. -/

/-- At a closing POP with a full accumulator, the flushed set covers every mark on its own internal edges,
[RDKP13]'s accumulator-soundness argument. -/
theorem tarjan_acceptingMarks_of_full [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (numMarks : Nat) {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat}
    {initialStates : List State} {aux : TarjanAux State} {step : DFSStep State Nat}
    {gray : List (GrayFrame State)}
    (hclose : (tarjanView numMarks (State := State)).closes aux step = true)
    (hwf : SearchWF (tarjanOps numMarks (State := State)) (tarjanView numMarks (State := State)) succs edgeMarks
      initialStates aux (⟨step.state, step.pos, step.idx, step.acc⟩ :: gray))
    (hfull : (tarjanView numMarks (State := State)).accAt aux 0 = (1 <<< (numMarks + 1)) - 1) :
    AcceptingMarks succs edgeMarks numMarks
      (flushedSet ((tarjanView numMarks (State := State)).live aux)
        ((tarjanView numMarks (State := State)).posNat step.pos)) := by
  set V := tarjanView numMarks (State := State)
  have hll0 : V.lowlinkAt aux 0 = V.posNat step.pos :=
    revGetD_zero (by rw [LowlinkView.closes] at hclose; exact beq_iff_eq.mp hclose)
  -- every bit of the full accumulator sits on an internal edge of the flushed set
  have hbit : ∀ b, b ≤ numMarks →
      ∃ u ∈ flushedSet (V.live aux) (V.posNat step.pos),
      ∃ v ∈ flushedSet (V.live aux) (V.posNat step.pos), v ∈ succs u ∧
        ((1 <<< numMarks).testBit b = true ∨ b ∈ edgeMarks u v) := by
    intro b hb
    have htb : (V.accAt aux 0).testBit b = true := by
      rw [hfull, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
      simpa using Nat.lt_succ_of_le hb
    obtain ⟨u, v, pu, pv, he, hu, hv, hlo, ⟨l, hl, hlb⟩, -, hmk⟩ := hwf.acc_sound 0 (by simp) b htb
    obtain rfl : l = 0 := by omega
    rw [hll0] at hlb
    obtain ⟨hpu, hpu'⟩ := hwf.liveWF.bwd u pu hu
    obtain ⟨hpv, hpv'⟩ := hwf.liveWF.bwd v pv hv
    rw [getElem!_pos (V.live aux) pu hpu] at hpu'
    rw [getElem!_pos (V.live aux) pv hpv] at hpv'
    exact ⟨u, (mem_flushedSet _ _ u).mpr ⟨pu, hpu, hlo, hpu'⟩,
      v, (mem_flushedSet _ _ v).mpr ⟨pv, hpv, hlb, hpv'⟩, he.mem, hmk⟩
  refine ⟨?_, fun m hm => ?_⟩
  · obtain ⟨u, hu, v, hv, he, -⟩ := hbit numMarks (Nat.le_refl _)
    exact ⟨u, hu, v, hv, he⟩
  · obtain ⟨u, hu, v, hv, he, hmk⟩ := hbit m (Nat.le_of_lt hm)
    refine ⟨u, hu, v, hv, he, hmk.resolve_left ?_⟩
    simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, decide_eq_true_eq]
    omega

/-- At a closing POP, a flushed set covering every mark leaves the accumulator full, the graph's own marks being
below `numMarks`. -/
theorem tarjan_full_of_acceptingMarks [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (numMarks : Nat) {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat}
    {initialStates : List State} {aux : TarjanAux State} {step : DFSStep State Nat}
    {gray : List (GrayFrame State)}
    (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (hsucc : step.succ = succs step.state) (hidx : ¬ step.idx < step.succ.size)
    (hwf : SearchWF (tarjanOps numMarks (State := State)) (tarjanView numMarks (State := State)) succs edgeMarks
      initialStates aux (⟨step.state, step.pos, step.idx, step.acc⟩ :: gray))
    (hA : AcceptingMarks succs edgeMarks numMarks
      (flushedSet ((tarjanView numMarks (State := State)).live aux)
        ((tarjanView numMarks (State := State)).posNat step.pos))) :
    (tarjanView numMarks (State := State)).accAt aux 0 = (1 <<< (numMarks + 1)) - 1 := by
  set V := tarjanView numMarks (State := State) with hV
  have hcomp := hwf.close_acc_complete hsucc hidx
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
  rcases Nat.lt_trichotomy b numMarks with hb | rfl | hb
  -- a property mark, carried by an internal edge
  · obtain ⟨u, hu, v, hv, he, hm⟩ := hA.2 b hb
    rw [hcomp u hu v hv he b (Or.inr hm)]
    exact (decide_eq_true (by omega)).symm
  -- the internal-edge bit
  · obtain ⟨u, hu, v, hv, he⟩ := hA.1
    rw [hcomp u hu v hv he _ (Or.inl (by simp [hV, tarjanView, Nat.shiftLeft_eq]))]
    exact (decide_eq_true (by omega)).symm
  -- nothing above it, since every bit comes from an edge mark or the internal-edge bit
  · have hfalse : (V.accAt aux 0).testBit b = false := by
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      obtain ⟨u, v, -, -, -, -, -, -, -, -, hmk⟩ := hwf.acc_sound 0 (by simp) b hc
      rcases hmk with hx | hx
      · simp [hV, tarjanView, Nat.shiftLeft_eq, Nat.testBit_two_pow] at hx
        omega
      · have := hmarksBound u v b hx
        omega
    rw [hfalse]
    exact (decide_eq_false (by omega)).symm

/-! ## The `TEmptinessChecker` contract -/

/-- A reported `(anchor, stem)` comes with a sound `sccHint`, read off the search invariant at the reporting closing
POP [CCLMT18]. -/
theorem tarjan_sccHintSound [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State)
    (fr : FiniteReach initialStates succs) :
    SccHintSound (tarjanOps numMarks) succs edgeMarks expand numMarks initialStates := by
  intro anchor stem hfound
  obtain ⟨-, hout⟩ := genericDFS_searchOutcome (tarjanOps numMarks) (tarjanView numMarks)
    (tarjanLowlinkLawful numMarks) (tarjanLawful numMarks) (liveWF_init 0) succs edgeMarks expand hexp initialStates fr
  obtain ⟨aux, step, gray, hwf, hsucc, hanchor, hrep⟩ := hout anchor stem hfound
  rcases hrep with ⟨hidx, hpop⟩ | ⟨d, -, -, hupd⟩
  swap
  -- UPDATE never reports
  · have h1 := congrArg Prod.snd hupd
    have h2 : ((tarjanOps numMarks).update aux (step.succMarks[step.idx]!) d).2 = false :=
      tarjanUpdate_snd numMarks aux _ d
    rw [h2] at h1
    exact absurd h1 (by simp)
  obtain ⟨hback, hwit⟩ := tarjanPop_eq_true numMarks hpop
  have hclose : (tarjanView numMarks).closes aux step = true := by
    simp [LowlinkView.closes, tarjanView, Array.back?_map, hback]
  obtain ⟨-, hconn⟩ := hwf.close_flushed hsucc hidx hclose
  set F := flushedSet ((tarjanView numMarks).live aux) ((tarjanView numMarks).posNat step.pos) with hF
  have hacc0 : (tarjanView numMarks).accAt aux 0 = fullMask numMarks :=
    revGetD_zero (by simp [tarjanView, Array.back?_map, hback])
  -- the hint holds exactly the flushed range
  have hFeq : F = tarjanSccHint (genericDFS (tarjanOps numMarks) succs edgeMarks expand initialStates
      (tarjanOps numMarks).initAux).2 := by
    simp only [hF, flushedSet, tarjanSccHint, hwit, tarjanView, id_eq]
  have hmemF : ∀ s, s ∈ F ↔
      s ∈ (tarjanOps numMarks).sccHint (genericDFS (tarjanOps numMarks) succs edgeMarks expand initialStates
        (tarjanOps numMarks).initAux).2 := fun s => hFeq ▸ Iff.rfl
  have hanchorF : anchor ∈ F := by
    obtain ⟨h1, h2⟩ := hwf.frame_pos ⟨step.state, (tarjanView numMarks).posNat step.pos, step.idx, step.acc⟩
      (List.mem_cons_self ..)
    rw [getElem!_pos ((tarjanView numMarks).live aux) _ h1] at h2
    exact (mem_flushedSet _ _ anchor).mpr ⟨_, h1, Nat.le_refl _, h2.trans hanchor⟩
  have hAF := tarjan_acceptingMarks_of_full numMarks hclose hwf hacc0
  exact ⟨hconn.congr hmemF, hAF.mono (fun s hs => (hmemF s).mp hs), (hmemF anchor).mp hanchorF,
    genericDFS_stem_path (tarjanOps numMarks) succs edgeMarks expand hexp initialStates _ anchor stem hfound⟩

private theorem tarjanMonotone (numMarks : Nat) :
    MonotoneAlong (tarjanOps numMarks (State := State)) (fun _ _ => True) where
  refl := fun _ => trivial
  trans := fun _ _ _ _ _ => trivial
  push := fun _ _ _ => trivial
  update := fun _ _ _ => trivial
  pop := fun _ _ _ _ => trivial

/-- A run that reports nothing leaves no `AcceptingSCC`. -/
theorem tarjan_no_acceptingSCC_of_none [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs)
    (hnone : (genericDFS (tarjanOps numMarks) succs edgeMarks expand initialStates tarjanInitAux).1 = none)
    (A : AcceptingSCC initialStates succs edgeMarks numMarks) : False := by
  have hsound := enumSCCs_sound (tarjanOps numMarks) (tarjanView numMarks) (tarjanLowlinkLawful numMarks)
    (tarjanLawful numMarks) (liveWF_init 0) succs edgeMarks expand hexp initialStates fr
  obtain ⟨C, hCmem, hCsub⟩ := hsound.2.2 A.scc A.nonempty A.connected A.reachable
  have hAC : AcceptingMarks succs edgeMarks numMarks C := A.covers.mono hCsub
  have hrec := enumRun_recordedAt (tarjanOps numMarks) (tarjanView numMarks) (tarjanLowlinkLawful numMarks)
    (tarjanLawful numMarks) (liveWF_init 0) (tarjanMonotone numMarks) succs edgeMarks expand hexp initialStates fr hnone
  simp only [enumSCCs, List.mem_map] at hCmem
  obtain ⟨p, hp, rfl⟩ := hCmem
  obtain ⟨step, gray, hwf, hsucc, hidx, hclose, hflush, hpopfalse, -⟩ := hrec p (by simpa using hp)
  rw [hflush] at hAC
  have hfull := tarjan_full_of_acceptingMarks numMarks hmarksBound hsucc hidx hwf hAC
  have hreport : ((tarjanOps numMarks).pop succs edgeMarks p.2 step).2 = true := by
    obtain ⟨x, hb, hx1⟩ : ∃ x, p.2.dstack.back? = some x ∧ x.1 = step.pos := by
      simp only [LowlinkView.closes, tarjanView, Array.back?_map, beq_iff_eq,
        Option.map_eq_some_iff] at hclose
      exact hclose
    have hx2 : x.2 = fullMask numMarks := by
      rw [fullMask, ← hfull]
      exact (revGetD_zero (by simp [tarjanView, Array.back?_map, hb])).symm
    obtain ⟨ll, acc⟩ := x
    simp only at hx1 hx2
    subst hx1 hx2
    simp [tarjanOps, tarjanPop, hb]
  rw [hreport] at hpopfalse
  exact absurd hpopfalse (by simp)

/-- Tarjan's SCC-based emptiness check. -/
@[expose] def tarjanCheck [LawfulBEq State] [LawfulHashable State] (succs : State → Array State)
    (initialStates : List State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) (numMarks : Nat) :
    EmptinessResult State :=
  checkWithWitness (tarjanOps numMarks) succs edgeMarks expand numMarks initialStates

/-- Soundness: a reported `stem` and `loop` are a `TAcceptingCycle`'s stem and cycle. -/
theorem tarjanCheck_nonEmpty_valid [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State)
    (fr : FiniteReach initialStates succs)
    {stem loop : List State}
    (h : tarjanCheck succs initialStates edgeMarks expand numMarks = .nonEmpty stem loop) :
    ∃ ac : TAcceptingCycle initialStates succs edgeMarks numMarks, ac.stem = stem ∧ ac.cycle = loop.tail :=
  checkWithWitness_nonEmpty_valid (tarjanOps numMarks) succs edgeMarks expand numMarks initialStates
    (tarjan_sccHintSound numMarks succs edgeMarks expand hexp initialStates fr) h

/-- Completeness: an `.empty` answer proves no `TAcceptingCycle` exists. -/
theorem tarjanCheck_empty_no_cycle [LawfulBEq State] [LawfulHashable State] [Inhabited State]
    (numMarks : Nat) (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand)
    (initialStates : List State) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (fr : FiniteReach initialStates succs)
    {n : Nat} (h : tarjanCheck succs initialStates edgeMarks expand numMarks = .empty n) :
    ¬∃ _ac : TAcceptingCycle initialStates succs edgeMarks numMarks, True := by
  have hnone := checkWithWitness_empty_of_none (tarjanOps numMarks) succs edgeMarks expand numMarks initialStates
    (tarjan_sccHintSound numMarks succs edgeMarks expand hexp initialStates fr) h
  intro hcyc
  obtain ⟨A, -⟩ := acceptingSCC_iff_acceptingCycle.mpr hcyc
  exact tarjan_no_acceptingSCC_of_none numMarks succs edgeMarks expand hexp initialStates hmarksBound fr hnone A

/-- `tarjanCheck` as a `TEmptinessChecker`. -/
def tarjanTChecker [LawfulBEq State] [LawfulHashable State] [Inhabited State] :
    TEmptinessChecker State where
  check := tarjanCheck
  nonEmpty_valid := fun {succs initialStates edgeMarks expand numMarks _stem _loop} fr hexp _ h =>
    tarjanCheck_nonEmpty_valid numMarks succs edgeMarks expand hexp initialStates fr h
  empty_no_cycle := fun {succs initialStates edgeMarks expand numMarks _n} fr hexp hmarksBound h =>
    tarjanCheck_empty_no_cycle numMarks succs edgeMarks expand hexp initialStates hmarksBound fr h

end LTLLib
