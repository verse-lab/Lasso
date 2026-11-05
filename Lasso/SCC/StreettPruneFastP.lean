module

/-
  The fast Streett prune with the live position carried by `getStatus`.

  In the fast route a back edge probes the same state twice, `getStatus` (`liveIndex.contains`) and then `update`
  (`liveIndex.getD`). Here `getStatus` returns the position it found and `update` takes it, so a back edge is one probe.

  This is a parallel driver and ops (`…P`), not a change to `DFSOps`/`dfsGo`: the proved driver and every theorem about it
  stay as they are, `streettCheckP` is what the router runs, and `streettCheckP_eq` is the one bridge to `streettCheckF`.

  Sections:
  - The interface with positions
  - The driver, as `dfsGo` with the position threaded
  - The Streett ops with the position
  - The easy facts
  - Drivers
  - The bridge: `streettCheckP` is `streettCheckF`
-/
public import Lasso.SCC.StreettPruneFast

public section

namespace Lasso

variable {State : Type u} {L : Type w} [BEq State] [Hashable State]

/-! ## The interface with positions -/

/-- `DFSStatus` with the live position attached. -/
inductive DFSStatusP (Position : Type w) where
  | dead
  | live (pos : Position)
  | unknown

/-- Forget the position. -/
def DFSStatusP.forget {Position : Type w} : DFSStatusP Position → DFSStatus
  | .dead => .dead
  | .live _ => .live
  | .unknown => .unknown

-- As in DFSOps, Aux and Position deliberately have independent universes.
set_option linter.checkUnivs false in
/-- `DFSOps` whose `getStatus` carries the live position and whose `update` takes it. -/
structure DFSOpsP (State : Type u) [BEq State] [Hashable State] where
  Aux : Type v
  Position : Type w
  initAux : Aux
  getStatus : Aux → State → DFSStatusP Position
  push : Aux → State → Std.HashSet Nat → Aux × Position
  update : Aux → Std.HashSet Nat → Position → Aux × Bool
  pop : (State → Array State) → (State → State → Std.HashSet Nat) → Aux → DFSStep State Position → Aux × Bool
  sccHint : Aux → Std.HashSet State
  numExplored : Aux → Nat

/-! ## The driver, as `dfsGo` with the position threaded -/

@[expose] def dfsGoP (ops : DFSOpsP State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) :
    ops.Aux → List (DFSStep State ops.Position) → Option (Option (State × List State) × ops.Aux)
  | aux, [] => some (none, aux)
  | aux, step :: rest =>
    if h : step.idx < step.succ.size then
      let d := step.succ[step.idx]
      let dfs' := { step with idx := step.idx + 1 } :: rest
      match ops.getStatus aux d with
      | .dead => dfsGoP ops succs edgeMarks expand aux dfs'
      | .live dpos =>
        let (aux', found) := ops.update aux step.succMarks[step.idx]! dpos
        if found then
          let stem := (dfs'.map (·.state)).reverse
          some (some (step.state, stem), aux')
        else dfsGoP ops succs edgeMarks expand aux' dfs'
      | .unknown =>
        let marks := step.succMarks[step.idx]!
        let (aux', pos') := ops.push aux d marks
        let e := expand d
        let newStep : DFSStep State ops.Position :=
          { state := d, pos := pos', acc := marksToBitmask marks, succ := e.1,
            succMarks := e.2.1, succOpts := e.2.2, idx := 0 }
        dfsGoP ops succs edgeMarks expand aux' (newStep :: dfs')
    else
      let (aux', found) := ops.pop succs edgeMarks aux step
      match found with
      | true => some (some (step.state, ((step :: rest).map (·.state)).reverse), aux')
      | false => dfsGoP ops succs edgeMarks expand aux' rest
partial_fixpoint

def dfsFromRootP (ops : DFSOpsP State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) (aux : ops.Aux) (q0 : State) :
    Option (State × List State) × ops.Aux :=
  let (aux', pos') := ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)
  let e := expand q0
  let step : DFSStep State ops.Position :=
    { state := q0, pos := pos', acc := 0, succ := e.1,
      succMarks := e.2.1, succOpts := e.2.2, idx := 0 }
  (dfsGoP ops succs edgeMarks expand aux' [step]).getD (none, aux')

def genericDFSGoP (ops : DFSOpsP State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) :
    List State → ops.Aux → Option (Option (State × List State) × ops.Aux)
  | [], aux => some (none, aux)
  | q :: rest, aux =>
    match ops.getStatus aux q with
    | .unknown =>
      let (found?, aux') := dfsFromRootP ops succs edgeMarks expand aux q
      match found? with
      | some _ => some (found?, aux')
      | none => genericDFSGoP ops succs edgeMarks expand rest aux'
    | .dead | .live _ => genericDFSGoP ops succs edgeMarks expand rest aux
partial_fixpoint

def genericDFSP (ops : DFSOpsP State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) (roots : List State) (aux : ops.Aux) :
    Option (State × List State) × ops.Aux :=
  (genericDFSGoP ops succs edgeMarks expand roots aux).getD (none, aux)

/-! ## The Streett ops with the position -/

/-- One probe for a live state: the position comes back with the answer. -/
def liveStatusOfP (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State) (q : State) :
    DFSStatusP Nat :=
  match liveIndex[q]? with
  | some pos => .live pos
  | none => if dead.contains q then .dead else .unknown

/-- `streettUpdateF` with the target's live position given instead of looked up. -/
def streettUpdateP (numMarks : Nat) (aux : StreettAuxF State) (marks : Std.HashSet Nat) (dpos : Nat) :
    StreettAuxF State × Bool :=
  let ⟨live, liveIndex, dead, dstack, wit, wopts, pending, ls, lo, ws⟩ := aux
  match dstack.back? with
  | none => (⟨live, liveIndex, dead, dstack, wit, wopts, pending, ls, lo, ws⟩, false)
  | some (ll, acc) =>
    let top := (min ll dpos, acc ||| marksToBitmask marks ||| (1 <<< numMarks))
    (⟨live, liveIndex, dead, dstack.pop.push top, wit, wopts, pending, ls, lo, ws⟩, false)

@[expose, implicit_reducible] def streettOpsP [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (curRegions : Nat) : DFSOpsP State where
  Aux := StreettAuxF State
  Position := Nat
  initAux := streettInitAuxF
  sccHint := fun aux =>
    aux.witness.foldl (init := Std.HashSet.emptyWithCapacity aux.witness.size) fun h s => h.insert s
  numExplored := fun aux => aux.live.size + aux.dead.size
  getStatus := fun aux q => liveStatusOfP aux.liveIndex aux.dead q
  push := streettPushF
  update := streettUpdateP cs.numMarks
  pop := fun _succs _edgeMarks aux step => streettPopF cs curRegions aux step

/-! ## The easy facts -/

section EasyFacts
variable [LawfulBEq State] [LawfulHashable State]

theorem liveStatusOfP_forget (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State) (q : State) :
    (liveStatusOfP liveIndex dead q).forget = liveStatusOf liveIndex dead q := by
  unfold liveStatusOfP liveStatusOf
  cases h : liveIndex[q]? with
  | some pos => simp [DFSStatusP.forget, Std.HashMap.contains_eq_isSome_getElem?, h]
  | none =>
    by_cases hd : dead.contains q = true <;>
      simp [DFSStatusP.forget, Std.HashMap.contains_eq_isSome_getElem?, h, hd]

omit [LawfulBEq State] [LawfulHashable State] in
theorem liveStatusOfP_live (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State) (q : State)
    (pos : Nat) (h : liveStatusOfP liveIndex dead q = .live pos) : liveIndex[q]? = some pos := by
  unfold liveStatusOfP at h
  cases h' : liveIndex[q]? with
  | some p => rw [h'] at h; cases h; rfl
  | none =>
    rw [h'] at h
    by_cases hd : dead.contains q = true
    · rw [ite_eq_left hd] at h; cases h
    · rw [ite_eq_right hd] at h; cases h

theorem liveStatusOfP_live_getD (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State)
    (q : State) (pos : Nat) (h : liveStatusOfP liveIndex dead q = .live pos) :
    liveIndex.getD q 0 = pos := by
  rw [Std.HashMap.getD_eq_getD_getElem?, liveStatusOfP_live liveIndex dead q pos h]; rfl

end EasyFacts

omit [BEq State] [Hashable State] in
theorem streettUpdateP_eq_streettUpdateF [BEq State] [Hashable State] (numMarks : Nat)
    (aux : StreettAuxF State) (marks : Std.HashSet Nat) (d : State) :
    streettUpdateP numMarks aux marks (aux.liveIndex.getD d 0) = streettUpdateF numMarks aux marks d := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending, ls, lo, ws⟩ := aux
  rfl

/-! ## Drivers -/

section Drivers
variable [Inhabited State] [LawfulBEq State] [LawfulHashable State]

def streettRunP (cs : CompiledSpec State L) (curRegions : Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) (initialStates : List State) :
    Option (State × List State) × StreettAuxF State :=
  genericDFSP (streettOpsP cs curRegions) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
    expand initialStates (streettOpsP cs curRegions).initAux

def candidateRunP (cs : CompiledSpec State L)
    (regionExpand : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (c : Candidate State) : Option (State × List State) × StreettAuxF State :=
  streettRunP (cs.atBits c.regions) c.regions
    (fun s => filterExpand (regionExpand (c.region cs) s) c.states.contains) c.states.toList

-- Lean 4.32's module exporter needs the fixpoint body when inspecting partial_correctness.
@[expose] def pruneLoopP (cs : CompiledSpec State L)
    (regionExpand : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat) :
    Nat → List (Candidate State) →
      Option (Option (State × Array State × Array (Array State) × Array Nat × Candidate State) × Nat)
  | explored, [] => some (none, explored)
  | explored, c :: rest =>
    let (found?, aux) := candidateRunP cs regionExpand c
    let explored' := explored + aux.live.size + aux.dead.size
    match found? with
    | some (anchor, _) =>
      some (some (anchor, aux.witness, aux.witnessSuccs, aux.witnessOpts, c), explored')
    | none => pruneLoopP cs regionExpand explored' (aux.pending.toList ++ rest)
partial_fixpoint

@[expose] def streettCheckP (cs : CompiledSpec State L) (succs : State → Array State)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (regionExpand : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (initialStates : List State) : EmptinessResult State :=
  match streettRunP cs 0 expand initialStates with
  | (some (anchor, stem), aux) =>
    buildResult cs (memoGraph (witnessMemo aux.witness aux.witnessSuccs) succs) succs
      (cs.spec.regionMarks cs.restrict) initialStates aux.witness aux.witnessOpts anchor stem
      (aux.live.size + aux.dead.size)
  | (none, aux) =>
    match pruneLoopP cs regionExpand (aux.live.size + aux.dead.size) aux.pending.toList with
    | some (some (anchor, wit, ws, wopts, C), n) =>
      buildResult (cs.atBits C.regions) (memoGraph (witnessMemo wit ws) (C.graph cs cs.spec)) succs
        (cs.spec.regionMarks (C.region cs)) initialStates wit wopts anchor
        ((bfsFindPath aux.dead succs initialStates (· == anchor)).getD [anchor]) n
    | some (none, n) => .empty n
    | none => .empty (aux.live.size + aux.dead.size)

/-! ## The bridge: `streettCheckP` is `streettCheckF`

A lockstep of `dfsGoP` with `dfsGo` on the same aux and stack, in both directions since each driver is
a `partial_fixpoint` and the fallbacks have to agree on divergence too (as in `dfsGo_eq`). `push` and
`pop` are the same functions, `getStatus` agrees up to `forget`, and on a `.live pos` answer
`streettUpdateP … pos` is `streettUpdateF`, the four easy facts above. -/

theorem streettOpsP_getStatus_forget (cs : CompiledSpec State L) (cr : Nat) (aux : StreettAuxF State)
    (q : State) : ((streettOpsP cs cr).getStatus aux q).forget = (streettOpsF cs cr).getStatus aux q :=
  liveStatusOfP_forget aux.liveIndex aux.dead q

theorem streettOpsP_getStatus_live_of (cs : CompiledSpec State L) (cr : Nat) (aux : StreettAuxF State)
    (q : State) (h : (streettOpsF cs cr).getStatus aux q = .live) :
    ∃ pos, (streettOpsP cs cr).getStatus aux q = .live pos := by
  rw [← streettOpsP_getStatus_forget] at h
  cases hP : (streettOpsP cs cr).getStatus aux q with
  | dead => rw [hP] at h; cases h
  | live pos => exact ⟨pos, rfl⟩
  | unknown => rw [hP] at h; cases h

theorem streettOpsP_update_live (cs : CompiledSpec State L) (cr : Nat) (aux : StreettAuxF State)
    (m : Std.HashSet Nat) (d : State) (pos : Nat)
    (h : (streettOpsP cs cr).getStatus aux d = .live pos) :
    (streettOpsP cs cr).update aux m pos = (streettOpsF cs cr).update aux m d := by
  show streettUpdateP cs.numMarks aux m pos = streettUpdateF cs.numMarks aux m d
  rw [← streettUpdateP_eq_streettUpdateF, liveStatusOfP_live_getD aux.liveIndex aux.dead d pos h]

theorem dfsGoP_le (cs : CompiledSpec State L) (cr : Nat) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) :
    ∀ (aux : StreettAuxF State) (stk : List (DFSStep State Nat)) r,
      dfsGoP (streettOpsP cs cr) succs edgeMarks expand aux stk = some r →
      dfsGo (streettOpsF cs cr) succs edgeMarks expand aux stk = some r := by
  refine dfsGoP.partial_correctness (streettOpsP cs cr) succs edgeMarks expand
    (fun aux stk r => dfsGo (streettOpsF cs cr) succs edgeMarks expand aux stk = some r) ?_
  intro dfsGoP' ih aux stk r hr
  cases stk with
  | nil => rw [dfsGo.eq_def]; exact hr
  | cons step rest =>
    rw [dfsGo.eq_def]
    simp only []
    by_cases h : step.idx < step.succ.size
    · simp only [h, dite_true] at hr
      rw [dite_eq_left h]
      cases hgs : (streettOpsP cs cr).getStatus aux step.succ[step.idx] with
      | dead =>
        simp only [hgs] at hr
        have hgs' : (streettOpsF cs cr).getStatus aux step.succ[step.idx] = .dead := by
          rw [← streettOpsP_getStatus_forget, hgs]; rfl
        simp only [hgs']
        exact ih aux _ r hr
      | live dpos =>
        simp only [hgs] at hr
        have hgs' : (streettOpsF cs cr).getStatus aux step.succ[step.idx] = .live := by
          rw [← streettOpsP_getStatus_forget, hgs]; rfl
        simp only [hgs']
        have hupd := (streettOpsP_update_live cs cr aux (step.succMarks[step.idx]!) _ dpos hgs).symm
        rcases hu : (streettOpsP cs cr).update aux (step.succMarks[step.idx]!) dpos with ⟨aux', found⟩
        rw [hu] at hupd
        simp only [hu] at hr
        simp only [hupd]
        cases found with
        | true => exact hr
        | false => exact ih aux' _ r hr
      | unknown =>
        simp only [hgs] at hr
        have hgs' : (streettOpsF cs cr).getStatus aux step.succ[step.idx] = .unknown := by
          rw [← streettOpsP_getStatus_forget, hgs]; rfl
        simp only [hgs']
        rcases hpsh : (streettOpsP cs cr).push aux step.succ[step.idx] (step.succMarks[step.idx]!)
          with ⟨aux', pos'⟩
        simp only [hpsh] at hr
        have hpsh' : (streettOpsF cs cr).push aux step.succ[step.idx] (step.succMarks[step.idx]!)
            = (aux', pos') := hpsh
        simp only [hpsh']
        exact ih _ _ r hr
    · simp only [h, dite_false] at hr
      rw [dite_eq_right h]
      rcases hp : (streettOpsP cs cr).pop succs edgeMarks aux step with ⟨aux', found⟩
      simp only [hp] at hr
      have hp' : (streettOpsF cs cr).pop succs edgeMarks aux step = (aux', found) := hp
      simp only [hp']
      cases found with
      | true => exact hr
      | false => exact ih aux' rest r hr

theorem dfsGoF_le (cs : CompiledSpec State L) (cr : Nat) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) :
    ∀ (aux : StreettAuxF State) (stk : List (DFSStep State Nat)) r,
      dfsGo (streettOpsF cs cr) succs edgeMarks expand aux stk = some r →
      dfsGoP (streettOpsP cs cr) succs edgeMarks expand aux stk = some r := by
  refine dfsGo.partial_correctness (streettOpsF cs cr) succs edgeMarks expand
    (fun aux stk r => dfsGoP (streettOpsP cs cr) succs edgeMarks expand aux stk = some r) ?_
  intro dfsGo' ih aux stk r hr
  cases stk with
  | nil => rw [dfsGoP.eq_def]; exact hr
  | cons step rest =>
    rw [dfsGoP.eq_def]
    simp only []
    by_cases h : step.idx < step.succ.size
    · simp only [h, dite_true] at hr
      rw [dite_eq_left h]
      cases hgs : (streettOpsF cs cr).getStatus aux step.succ[step.idx] with
      | dead =>
        simp only [hgs] at hr
        have hgs' : (streettOpsP cs cr).getStatus aux step.succ[step.idx] = .dead := by
          have := streettOpsP_getStatus_forget cs cr aux step.succ[step.idx]
          rw [hgs] at this
          cases hP : (streettOpsP cs cr).getStatus aux step.succ[step.idx] <;> rw [hP] at this <;>
            first | rfl | cases this
        simp only [hgs']
        exact ih aux _ r hr
      | live =>
        simp only [hgs] at hr
        obtain ⟨dpos, hgs'⟩ := streettOpsP_getStatus_live_of cs cr aux step.succ[step.idx] hgs
        simp only [hgs']
        have hupd := streettOpsP_update_live cs cr aux (step.succMarks[step.idx]!) _ dpos hgs'
        rcases hu : (streettOpsF cs cr).update aux (step.succMarks[step.idx]!) step.succ[step.idx]
          with ⟨aux', found⟩
        rw [hu] at hupd
        simp only [hu] at hr
        simp only [hupd]
        cases found with
        | true => exact hr
        | false => exact ih aux' _ r hr
      | unknown =>
        simp only [hgs] at hr
        have hgs' : (streettOpsP cs cr).getStatus aux step.succ[step.idx] = .unknown := by
          have := streettOpsP_getStatus_forget cs cr aux step.succ[step.idx]
          rw [hgs] at this
          cases hP : (streettOpsP cs cr).getStatus aux step.succ[step.idx] <;> rw [hP] at this <;>
            first | rfl | cases this
        simp only [hgs']
        rcases hpsh : (streettOpsF cs cr).push aux step.succ[step.idx] (step.succMarks[step.idx]!)
          with ⟨aux', pos'⟩
        simp only [hpsh] at hr
        have hpsh' : (streettOpsP cs cr).push aux step.succ[step.idx] (step.succMarks[step.idx]!)
            = (aux', pos') := hpsh
        simp only [hpsh']
        exact ih _ _ r hr
    · simp only [h, dite_false] at hr
      rw [dite_eq_right h]
      rcases hp : (streettOpsF cs cr).pop succs edgeMarks aux step with ⟨aux', found⟩
      simp only [hp] at hr
      have hp' : (streettOpsP cs cr).pop succs edgeMarks aux step = (aux', found) := hp
      simp only [hp']
      cases found with
      | true => exact hr
      | false => exact ih aux' rest r hr

theorem dfsGoP_eq (cs : CompiledSpec State L) (cr : Nat) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (aux : StreettAuxF State) (stk : List (DFSStep State Nat)) :
    dfsGoP (streettOpsP cs cr) succs edgeMarks expand aux stk =
      dfsGo (streettOpsF cs cr) succs edgeMarks expand aux stk := by
  cases hP : dfsGoP (streettOpsP cs cr) succs edgeMarks expand aux stk with
  | none =>
    cases hF : dfsGo (streettOpsF cs cr) succs edgeMarks expand aux stk with
    | none => rfl
    | some r => rw [dfsGoF_le cs cr succs edgeMarks expand aux stk r hF] at hP; cases hP
  | some r => exact (dfsGoP_le cs cr succs edgeMarks expand aux stk r hP).symm

theorem dfsFromRootP_eq (cs : CompiledSpec State L) (cr : Nat) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (aux : StreettAuxF State) (q : State) :
    dfsFromRootP (streettOpsP cs cr) succs edgeMarks expand aux q =
      dfsFromRoot (streettOpsF cs cr) succs edgeMarks expand aux q := by
  unfold dfsFromRootP dfsFromRoot
  simp only [dfsGoP_eq]
  rfl

theorem genericDFSGoP_eq (cs : CompiledSpec State L) (cr : Nat) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) (roots : List State) :
    ∀ aux : StreettAuxF State,
      genericDFSGoP (streettOpsP cs cr) succs edgeMarks expand roots aux =
        genericDFSGo (streettOpsF cs cr) succs edgeMarks expand roots aux := by
  induction roots with
  | nil =>
    intro aux
    rw [genericDFSGoP.eq_def (streettOpsP cs cr), genericDFSGo.eq_def (streettOpsF cs cr)]
  | cons q rest ih =>
    intro aux
    rw [genericDFSGoP.eq_def (streettOpsP cs cr), genericDFSGo.eq_def (streettOpsF cs cr)]
    simp only []
    cases hgs : (streettOpsP cs cr).getStatus aux q with
    | dead =>
      have hgs' : (streettOpsF cs cr).getStatus aux q = .dead := by
        rw [← streettOpsP_getStatus_forget, hgs]; rfl
      simp only [hgs']
      exact ih aux
    | live pos =>
      have hgs' : (streettOpsF cs cr).getStatus aux q = .live := by
        rw [← streettOpsP_getStatus_forget, hgs]; rfl
      simp only [hgs']
      exact ih aux
    | unknown =>
      have hgs' : (streettOpsF cs cr).getStatus aux q = .unknown := by
        rw [← streettOpsP_getStatus_forget, hgs]; rfl
      simp only [hgs']
      rw [dfsFromRootP_eq]
      rcases hd : dfsFromRoot (streettOpsF cs cr) succs edgeMarks expand aux q with ⟨found?, aux'⟩
      cases found? with
      | some v => rfl
      | none => exact ih aux'

theorem genericDFSP_eq (cs : CompiledSpec State L) (cr : Nat) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) (roots : List State)
    (aux : StreettAuxF State) :
    genericDFSP (streettOpsP cs cr) succs edgeMarks expand roots aux =
      genericDFS (streettOpsF cs cr) succs edgeMarks expand roots aux := by
  unfold genericDFSP genericDFS
  rw [genericDFSGoP_eq]

theorem streettRunP_eq (cs : CompiledSpec State L) (cr : Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) (initialStates : List State) :
    streettRunP cs cr expand initialStates = streettRunF cs cr expand initialStates := by
  unfold streettRunP streettRunF
  exact genericDFSP_eq cs cr _ _ expand initialStates _

theorem candidateRunP_eq (cs : CompiledSpec State L)
    (regionExpand : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (c : Candidate State) :
    candidateRunP cs regionExpand c = candidateRunF cs regionExpand c := by
  unfold candidateRunP candidateRunF
  exact streettRunP_eq (cs.atBits c.regions) _ _ _

theorem pruneLoopP_le (cs : CompiledSpec State L)
    (regionExpand : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat) :
    ∀ n cands r, pruneLoopP cs regionExpand n cands = some r →
      pruneLoopF cs regionExpand n cands = some r := by
  refine pruneLoopP.partial_correctness cs regionExpand
    (fun n cands r => pruneLoopF cs regionExpand n cands = some r) ?_
  intro pruneLoopP' ih n cands r hr
  cases cands with
  | nil => rw [pruneLoopF.eq_def]; exact hr
  | cons c rest =>
    rw [pruneLoopF.eq_def]
    simp only [candidateRunP_eq] at hr
    simp only []
    rcases hc : candidateRunF cs regionExpand c with ⟨found?, aux⟩
    simp only [hc] at hr ⊢
    cases found? with
    | some v => exact hr
    | none => exact ih _ _ r hr

theorem pruneLoopF_le' (cs : CompiledSpec State L)
    (regionExpand : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat) :
    ∀ n cands r, pruneLoopF cs regionExpand n cands = some r →
      pruneLoopP cs regionExpand n cands = some r := by
  refine pruneLoopF.partial_correctness cs regionExpand
    (fun n cands r => pruneLoopP cs regionExpand n cands = some r) ?_
  intro pruneLoopF' ih n cands r hr
  cases cands with
  | nil => rw [pruneLoopP.eq_def]; exact hr
  | cons c rest =>
    rw [pruneLoopP.eq_def]
    simp only [candidateRunP_eq]
    rcases hc : candidateRunF cs regionExpand c with ⟨found?, aux⟩
    simp only [hc] at hr ⊢
    cases found? with
    | some v => exact hr
    | none => exact ih _ _ r hr

theorem pruneLoopP_eq (cs : CompiledSpec State L)
    (regionExpand : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (n : Nat) (cands : List (Candidate State)) :
    pruneLoopP cs regionExpand n cands = pruneLoopF cs regionExpand n cands := by
  cases hP : pruneLoopP cs regionExpand n cands with
  | none =>
    cases hF : pruneLoopF cs regionExpand n cands with
    | none => rfl
    | some r => rw [pruneLoopF_le' cs regionExpand n cands r hF] at hP; cases hP
  | some r => exact (pruneLoopP_le cs regionExpand n cands r hP).symm

/-- The position-carrying driver computes what `streettCheckF` computes. -/
theorem streettCheckP_eq (cs : CompiledSpec State L) (succs : State → Array State)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (regionExpand : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (initialStates : List State) :
    streettCheckP cs succs expand regionExpand initialStates =
      streettCheckF cs succs expand regionExpand initialStates := by
  unfold streettCheckP streettCheckF
  rw [streettRunP_eq]
  rcases streettRunF cs 0 expand initialStates with ⟨found?, aux⟩
  cases found? with
  | some v => rfl
  | none =>
    simp only []
    rw [pruneLoopP_eq]
    rfl

end Drivers

end Lasso
