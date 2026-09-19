/-
  The flush-enumeration contract shared by the lowlink-based refinements of `GenericDFS.lean`: the sets POP flushes as it
  closes frames are the maximal SCCs of the reachable subgraph, as `SCCEnumerationSound` asks.

  `TarjanSCC.lean` and `StreettPrune.lean` run the same lowlink discipline, PUSH opening a frame at the new live position,
  UPDATE lowering the innermost lowlink to a live target's position, and POP either closing the innermost frame and
  flushing the live stack above it or folding its lowlink into the parent. The enumeration is stated once over
  `LowlinkView`. A refinement stores none of what it flushes, so the flush sequence is named by running the search again
  through `enumOps`, a wrapper that records each closed frame beside the search state that closed it and never reports.

  Proof structure from [CCLMT18], whose stack, num, black and sccs are our `live`, `liveIndex`, `dead` and the recorded
  flushes, their gray set being the states on the driver's frame stack. `EnumWF` follows their `wf_env`, and their `dfs1`
  post-conditions characterising LOWLINK become invariants over the frame stack, stated over `ExploredEdge`.

  Defines:
  - `flushedSet`: the states POP is about to flush, the live stack from a position upwards
  - `LowlinkView`, `LowlinkLawful`: what a refinement exposes of its search state, and the discipline it obeys on that view
  - `enumOps`, `enumRun`, `enumSCCs`: the recording wrapper, its run, and the flushed sets that run recorded
  - `enumOpsFast`, `enumSCCsFast`: the same wrapper without the per-set snapshot, run by compiled code
  - `GrayFrame`, `ExploredEdge`: an open frame as the invariant reads it, and an edge the search has already taken
  - `SearchWF`, `EnumWF`: the invariant the search itself maintains, and its extension by what the wrapper has stored
  - `ReportedFrom`, `SearchOutcome`: what a run of the refinement itself leaves behind, reporting or not
  - `MonotoneAlong`, `RecordedAt`: a relation every operation moves forward along, and what each recorded flush looks
    like from a real run that never reports

  Proves:
  - `enumSCCs_sound`: the recorded sets are an `SCCEnumerationSound` enumeration
  - `enumSCCs_eq_enumSCCsFast` (`@[csimp]`): the snapshot-free run flushes the same sets
  - `enumWF_final`, `genericDFS_searchOutcome`: the invariants survive the recording run and, up to a reporting move, a
    run of the refinement itself
  - `enumOps_base_eq`: a run that never reports agrees with the recording run on the refinement's own state
  - `enumRun_recordedAt`: when the real run reports nothing, every recorded flush was a non-reporting closing POP of
    the real run at which the search invariant held
  - `enumSCCs_flushed`: each recorded set is the flush of the state recorded beside it
  - `SearchWF.close_flushed`, `SearchWF.close_acc_complete`: at a closing POP the flushed set is internally connected
    and closed up to `dead`, and the accumulator carries every mark inside it

  References:
  - [Tar72] Tarjan. Depth-first search and linear graph algorithms. SIAM J. Comput. 1(2), 1972.
  - [CCLMT18] Chen, Cohen, Lévy, Merz, Théry. Formal Proofs of Tarjan's Algorithm in Why3, Coq, and Isabelle.
    arXiv:1810.11979, 2018.
  - [RDKP13] Renault, Duret-Lutz, Kordon, Poitrenaud. Three SCC-based Emptiness Checks for Generalized Büchi
    Automata. LPAR-19, 2013.

  Sections:
  - The lowlink view
  - The recording wrapper
  - Snapshot-free recording
  - The run invariant
  - The enumeration contract
  - The reporting run
  - Recorded flushes
-/
import LTLLib.AbstractSpec.EmptinessCheck
import LTLLib.TGBABased.AbstractSpec.SCCTheory
import LTLLib.TGBABased.SCC.GenericDFS
import LTLLib.TGBABased.SCC.LiveStack

namespace LTLLib

universe u v w

variable {State : Type u} [BEq State] [Hashable State]

/-! ## The lowlink view -/

/-- The states POP is about to flush, which are exactly the live states from the closing frame upwards. -/
def flushedSet (live : Array State) (pos : Nat) : Std.HashSet State :=
  (live.extract pos live.size).foldl (init := Std.HashSet.emptyWithCapacity 0) fun acc s => acc.insert s

/-- What a lowlink-based refinement exposes of its own search state. -/
structure LowlinkView (ops : DFSOps State) where
  live : ops.Aux → Array State
  liveIndex : ops.Aux → Std.HashMap State Nat
  dead : ops.Aux → Std.HashSet State
  -- the frame stack's lowlink column, one entry per open frame, innermost last
  lowlinks : ops.Aux → Array Nat
  -- the frame stack's accumulator column, the marks seen on the frame's own component so far
  accs : ops.Aux → Array Nat
  -- the mask ored in at every internal edge, a spare bit where the refinement keeps one and `0` otherwise
  extraAcc : Nat
  -- a frame's `Position` read as the live-stack index PUSH gave it
  posNat : ops.Position → Nat

/-- Does this POP close its frame? Its lowlink having stayed at its own position makes the frame an SCC root. -/
def LowlinkView.closes {ops : DFSOps State} (V : LowlinkView ops) (aux : ops.Aux)
    (step : DFSStep State ops.Position) : Bool :=
  (V.lowlinks aux).back? == some (V.posNat step.pos)

/-- The discipline `TarjanSCC.lean` and `StreettPrune.lean` share, as laws on the view. -/
structure LowlinkLawful (ops : DFSOps State) (V : LowlinkView ops) : Prop where
  -- status is read off the triple alone
  status : ∀ aux q, ops.getStatus aux q = liveStatusOf (V.liveIndex aux) (V.dead aux) q
  -- PUSH appends the state and opens a frame whose lowlink is its own position
  push_live : ∀ aux q m, V.live (ops.push aux q m).1 = (V.live aux).push q
  push_liveIndex : ∀ aux q m,
    V.liveIndex (ops.push aux q m).1 = (V.liveIndex aux).insert q (V.live aux).size
  push_dead : ∀ aux q m, V.dead (ops.push aux q m).1 = V.dead aux
  push_lowlinks : ∀ aux q m, V.lowlinks (ops.push aux q m).1 = (V.lowlinks aux).push (V.live aux).size
  push_accs : ∀ aux q m, V.accs (ops.push aux q m).1 = (V.accs aux).push 0
  push_pos : ∀ aux q m, V.posNat (ops.push aux q m).2 = (V.live aux).size
  -- UPDATE lowers the innermost lowlink to the back-edge target's position and touches nothing else
  update_live : ∀ aux m d, V.live (ops.update aux m d).1 = V.live aux
  update_liveIndex : ∀ aux m d, V.liveIndex (ops.update aux m d).1 = V.liveIndex aux
  update_dead : ∀ aux m d, V.dead (ops.update aux m d).1 = V.dead aux
  -- guarded by an open frame, since with none the refinements leave the whole state alone
  update_lowlinks : ∀ aux m d ll, (V.lowlinks aux).back? = some ll →
    V.lowlinks (ops.update aux m d).1 =
      (V.lowlinks aux).pop.push (min ll ((V.liveIndex aux).getD d 0))
  -- UPDATE folds the back edge's own marks into the innermost accumulator, guarded the same way
  update_accs : ∀ aux m d acc, (V.accs aux).back? = some acc →
    V.accs (ops.update aux m d).1 = (V.accs aux).pop.push (acc ||| marksToBitmask m ||| V.extraAcc)
  -- POP at a closing frame flushes the live stack above it
  pop_close : ∀ succs edgeMarks aux step, V.closes aux step = true →
    (V.live (ops.pop succs edgeMarks aux step).1, V.liveIndex (ops.pop succs edgeMarks aux step).1,
        V.dead (ops.pop succs edgeMarks aux step).1) =
      liveFlush (V.live aux) (V.liveIndex aux) (V.dead aux) (V.posNat step.pos) ∧
      V.lowlinks (ops.pop succs edgeMarks aux step).1 = (V.lowlinks aux).pop ∧
      V.accs (ops.pop succs edgeMarks aux step).1 = (V.accs aux).pop
  -- POP at any other frame leaves the triple alone and folds the closing lowlink into the parent, if there is one
  pop_merge : ∀ succs edgeMarks aux step, V.closes aux step = false →
    V.live (ops.pop succs edgeMarks aux step).1 = V.live aux ∧
      V.liveIndex (ops.pop succs edgeMarks aux step).1 = V.liveIndex aux ∧
      V.dead (ops.pop succs edgeMarks aux step).1 = V.dead aux
  -- with no parent frame, at the outermost frame of a root's search, the closing lowlink is dropped
  pop_merge_lowlinks : ∀ succs edgeMarks aux step ll, V.closes aux step = false →
    (V.lowlinks aux).back? = some ll →
      V.lowlinks (ops.pop succs edgeMarks aux step).1 =
        match (V.lowlinks aux).pop.back? with
        | none => (V.lowlinks aux).pop
        | some pll => (V.lowlinks aux).pop.pop.push (min pll ll)
  -- the closing accumulator and the tree edge's own marks go the same way as the lowlink
  pop_merge_accs : ∀ succs edgeMarks aux step acc, V.closes aux step = false →
    (V.accs aux).back? = some acc →
      V.accs (ops.pop succs edgeMarks aux step).1 =
        match (V.accs aux).pop.back? with
        | none => (V.accs aux).pop
        | some pacc => (V.accs aux).pop.pop.push (pacc ||| step.acc ||| acc ||| V.extraAcc)
  -- the search starts with nothing touched and no frame open
  init_live : V.live ops.initAux = #[]
  init_dead : ∀ s, s ∉ V.dead ops.initAux
  init_lowlinks : V.lowlinks ops.initAux = #[]
  init_accs : V.accs ops.initAux = #[]
  init_status : ∀ q, ops.getStatus ops.initAux q = .unknown

/-! ## The recording wrapper -/

/-- The refinement's own state beside one entry per closed frame, each the set that frame flushed together with
the state that flushed it. -/
abbrev EnumAux (ops : DFSOps State) := ops.Aux × Array (Std.HashSet State × ops.Aux)

/-- The refinement's operations, recording every closed frame and never reporting. -/
def enumOps (ops : DFSOps State) (V : LowlinkView ops) : DFSOps State where
  Aux := EnumAux ops
  Position := ops.Position
  initAux := (ops.initAux, #[])
  getStatus := fun aux q => ops.getStatus aux.1 q
  push := fun aux q m =>
    let (base', pos) := ops.push aux.1 q m
    ((base', aux.2), pos)
  update := fun aux m d => (((ops.update aux.1 m d).1, aux.2), false)
  pop := fun succs edgeMarks aux step =>
    (((ops.pop succs edgeMarks aux.1 step).1,
      if V.closes aux.1 step then aux.2.push (flushedSet (V.live aux.1) (V.posNat step.pos), aux.1)
      else aux.2), false)
  sccHint := fun aux => ops.sccHint aux.1
  numExplored := fun aux => ops.numExplored aux.1

theorem enumOps_getStatus (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (aux : (enumOps ops V).Aux) (q : State) :
    (enumOps ops V).getStatus aux q = ops.getStatus aux.1 q := rfl

/-- The recording run over the whole graph. -/
def enumRun (ops : DFSOps State) (V : LowlinkView ops) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) :
    Array (Std.HashSet State × ops.Aux) :=
  (genericDFS (enumOps ops V) succs edgeMarks initialStates (enumOps ops V).initAux).2.2

/-- The sets that run flushed, in the order POP closed them. -/
def enumSCCs (ops : DFSOps State) (V : LowlinkView ops) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) :
    List (Std.HashSet State) :=
  (enumRun ops V succs edgeMarks initialStates).toList.map (·.1)

/-! ## Snapshot-free recording -/

/-- The recording wrapper without the snapshot beside each set, which compiled code runs so that POP updates the
refinement's state in place. -/
def enumOpsFast (ops : DFSOps State) (V : LowlinkView ops) : DFSOps State where
  Aux := ops.Aux × Array (Std.HashSet State)
  Position := ops.Position
  initAux := (ops.initAux, #[])
  getStatus := fun aux q => ops.getStatus aux.1 q
  push := fun aux q m =>
    let (base', pos) := ops.push aux.1 q m
    ((base', aux.2), pos)
  update := fun aux m d => (((ops.update aux.1 m d).1, aux.2), false)
  pop := fun succs edgeMarks aux step =>
    let sets := if V.closes aux.1 step then aux.2.push (flushedSet (V.live aux.1) (V.posNat step.pos)) else aux.2
    (((ops.pop succs edgeMarks aux.1 step).1, sets), false)
  sccHint := fun aux => ops.sccHint aux.1
  numExplored := fun aux => ops.numExplored aux.1

/-- The sets the snapshot-free run flushed, in the order POP closed them. -/
def enumSCCsFast (ops : DFSOps State) (V : LowlinkView ops) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) : List (Std.HashSet State) :=
  (genericDFS (enumOpsFast ops V) succs edgeMarks initialStates (enumOpsFast ops V).initAux).2.2.toList

/-- A recording state with its snapshots dropped. -/
def forgetSnapshots {ops : DFSOps State} {V : LowlinkView ops} (aux : (enumOps ops V).Aux) :
    (enumOpsFast ops V).Aux :=
  (aux.1, aux.2.map (·.1))

theorem enumOpsFast_getStatus (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops) (aux : (enumOps ops V).Aux)
    (q : State) : (enumOpsFast ops V).getStatus (forgetSnapshots aux) q = (enumOps ops V).getStatus aux q := rfl

theorem enumOpsFast_push (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops) (aux : (enumOps ops V).Aux) (q : State)
    (m : Std.HashSet Nat) :
    (enumOpsFast ops V).push (forgetSnapshots aux) q m =
      (forgetSnapshots ((enumOps ops V).push aux q m).1, ((enumOps ops V).push aux q m).2) := rfl

theorem enumOpsFast_update (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops) (aux : (enumOps ops V).Aux)
    (m : Std.HashSet Nat) (d : State) :
    (enumOpsFast ops V).update (forgetSnapshots aux) m d =
      (forgetSnapshots ((enumOps ops V).update aux m d).1, ((enumOps ops V).update aux m d).2) := rfl

theorem enumOpsFast_pop (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (aux : (enumOps ops V).Aux) (step : DFSStep State ops.Position) :
    (enumOpsFast ops V).pop succs edgeMarks (forgetSnapshots aux) step =
      (forgetSnapshots ((enumOps ops V).pop succs edgeMarks aux step).1,
        ((enumOps ops V).pop succs edgeMarks aux step).2) := by
  simp only [enumOpsFast, enumOps, forgetSnapshots]
  by_cases hc : V.closes aux.1 step = true <;> simp [hc, Array.map_push]

private theorem dfsGo_enumOpsFast_of_some (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat) :
    ∀ (aux : (enumOps ops V).Aux) (stack : List (DFSStep State ops.Position))
      (r : Option (State × List State) × (enumOps ops V).Aux),
      dfsGo (enumOps ops V) succs edgeMarks aux stack = some r →
      dfsGo (enumOpsFast ops V) succs edgeMarks (forgetSnapshots aux) stack = some (r.1, forgetSnapshots r.2) := by
  refine dfsGo.partial_correctness (enumOps ops V) succs edgeMarks
    (fun aux stack r => dfsGo (enumOpsFast ops V) succs edgeMarks (forgetSnapshots aux) stack =
      some (r.1, forgetSnapshots r.2)) ?_
  intro f ih aux stack r hr
  rw [dfsGo.eq_def]
  cases stack with
  | nil =>
    simp only [Option.some.injEq] at hr
    rw [← hr]
  | cons step rest =>
    by_cases hidx : step.idx < step.succ.size
    case neg =>
      simp only [hidx, dite_false, enumOpsFast_pop] at hr ⊢
      simp only [enumOps] at hr ⊢
      rcases hpop : ops.pop succs edgeMarks aux.1 step with ⟨aux'', found⟩
      simp only [hpop] at hr ⊢
      exact ih _ rest r hr
    case pos =>
      simp only [hidx, dite_true, enumOpsFast_getStatus, enumOpsFast_update, enumOpsFast_push] at hr ⊢
      simp only [enumOps] at hr ⊢
      cases hgs : ops.getStatus aux.1 step.succ[step.idx] with
      | dead =>
        simp only [hgs] at hr ⊢
        exact ih _ _ r hr
      | live =>
        simp only [hgs] at hr ⊢
        exact ih _ _ r hr
      | unknown =>
        simp only [hgs] at hr ⊢
        rcases hpsh : ops.push aux.1 step.succ[step.idx] (edgeMarks step.state step.succ[step.idx])
          with ⟨aux'', pos'⟩
        simp only [hpsh] at hr ⊢
        exact ih _ _ r hr

private theorem dfsGo_enumOps_of_fast_some (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat) :
    ∀ (b : (enumOpsFast ops V).Aux) (stack : List (DFSStep State ops.Position))
      (r' : Option (State × List State) × (enumOpsFast ops V).Aux),
      dfsGo (enumOpsFast ops V) succs edgeMarks b stack = some r' →
      ∀ aux : (enumOps ops V).Aux, forgetSnapshots aux = b →
        ∃ r, dfsGo (enumOps ops V) succs edgeMarks aux stack = some r := by
  refine dfsGo.partial_correctness (enumOpsFast ops V) succs edgeMarks
    (fun b stack _ => ∀ aux : (enumOps ops V).Aux, forgetSnapshots aux = b →
      ∃ r, dfsGo (enumOps ops V) succs edgeMarks aux stack = some r) ?_
  intro f ih b stack r' hr' aux hb
  subst hb
  rw [dfsGo.eq_def]
  cases stack with
  | nil => exact ⟨_, rfl⟩
  | cons step rest =>
    by_cases hidx : step.idx < step.succ.size
    case neg =>
      simp only [hidx, dite_false, enumOpsFast_pop] at hr' ⊢
      simp only [enumOps] at hr' ⊢
      rcases hpop : ops.pop succs edgeMarks aux.1 step with ⟨aux'', found⟩
      simp only [hpop] at hr' ⊢
      exact ih _ rest r' hr' _ rfl
    case pos =>
      simp only [hidx, dite_true, enumOpsFast_getStatus, enumOpsFast_update, enumOpsFast_push] at hr' ⊢
      simp only [enumOps] at hr' ⊢
      cases hgs : ops.getStatus aux.1 step.succ[step.idx] with
      | dead =>
        simp only [hgs] at hr' ⊢
        exact ih _ _ r' hr' _ rfl
      | live =>
        simp only [hgs] at hr' ⊢
        exact ih _ _ r' hr' _ rfl
      | unknown =>
        simp only [hgs] at hr' ⊢
        rcases hpsh : ops.push aux.1 step.succ[step.idx] (edgeMarks step.state step.succ[step.idx])
          with ⟨aux'', pos'⟩
        simp only [hpsh] at hr' ⊢
        exact ih _ _ r' hr' _ rfl

/-- The snapshot-free run steps exactly like the recording run, up to the dropped snapshots. -/
theorem dfsGo_enumOpsFast (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (aux : (enumOps ops V).Aux)
    (stack : List (DFSStep State ops.Position)) :
    dfsGo (enumOpsFast ops V) succs edgeMarks (forgetSnapshots aux) stack =
      (dfsGo (enumOps ops V) succs edgeMarks aux stack).map fun r => (r.1, forgetSnapshots r.2) := by
  rcases h : dfsGo (enumOps ops V) succs edgeMarks aux stack with _ | r
  · rcases h' : dfsGo (enumOpsFast ops V) succs edgeMarks (forgetSnapshots aux) stack with _ | r'
    · rfl
    · obtain ⟨r, hr⟩ := dfsGo_enumOps_of_fast_some ops V succs edgeMarks _ stack r' h' aux rfl
      rw [h] at hr
      cases hr
  · exact dfsGo_enumOpsFast_of_some ops V succs edgeMarks aux stack r h

theorem dfsFromRoot_enumOpsFast (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (aux : (enumOps ops V).Aux) (q0 : State) :
    dfsFromRoot (enumOpsFast ops V) succs edgeMarks (forgetSnapshots aux) q0 =
      ((dfsFromRoot (enumOps ops V) succs edgeMarks aux q0).1,
        forgetSnapshots (dfsFromRoot (enumOps ops V) succs edgeMarks aux q0).2) := by
  unfold dfsFromRoot
  rw [enumOpsFast_push]
  rcases hpsh : (enumOps ops V).push aux q0 (Std.HashSet.emptyWithCapacity 0) with ⟨aux', pos'⟩
  simp only
  rw [dfsGo_enumOpsFast]
  cases dfsGo (enumOps ops V) succs edgeMarks aux' [{ state := q0, pos := pos', acc := 0, succ := succs q0, idx := 0 }]
  <;> rfl

theorem genericDFSGo_enumOpsFast (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) :
    ∀ (roots : List State) (aux : (enumOps ops V).Aux),
      genericDFSGo (enumOpsFast ops V) succs edgeMarks roots (forgetSnapshots aux) =
        (genericDFSGo (enumOps ops V) succs edgeMarks roots aux).map fun r => (r.1, forgetSnapshots r.2) := by
  intro roots
  induction roots with
  | nil => intro aux; rw [genericDFSGo.eq_def, genericDFSGo.eq_def]; rfl
  | cons q rest ih =>
    intro aux
    rw [genericDFSGo.eq_def, genericDFSGo.eq_def]
    simp only
    rw [enumOpsFast_getStatus]
    cases (enumOps ops V).getStatus aux q with
    | dead => exact ih aux
    | live => exact ih aux
    | unknown =>
      simp only
      rw [dfsFromRoot_enumOpsFast]
      rcases hr : dfsFromRoot (enumOps ops V) succs edgeMarks aux q with ⟨found, aux'⟩
      cases found with
      | some x => rfl
      | none => exact ih aux'

/-- Compiled code runs the snapshot-free recording, which flushes the same sets. -/
@[csimp] theorem enumSCCs_eq_enumSCCsFast : @enumSCCs.{u,v,w} = @enumSCCsFast.{u,v,w} := by
  funext State _ _ ops V succs edgeMarks initialStates
  unfold enumSCCs enumRun enumSCCsFast genericDFS
  have hinit : (enumOpsFast ops V).initAux = forgetSnapshots (enumOps ops V).initAux := by
    simp [enumOpsFast, enumOps, forgetSnapshots]
  rw [hinit, genericDFSGo_enumOpsFast]
  cases genericDFSGo (enumOps ops V) succs edgeMarks initialStates (enumOps ops V).initAux with
  | none => simp [forgetSnapshots, enumOps]
  | some r => simp [forgetSnapshots, Array.toList_map]

/-! ## The run invariant -/

section RunInvariant
variable [Inhabited State]

/-- An open frame as the invariant reads it. -/
structure GrayFrame (State : Type u) where
  -- the gray state the frame was opened on
  state : State
  -- the live-stack index PUSH gave it
  pos : Nat
  -- how far the driver's scan of `succs state` has got
  idx : Nat
  -- the marks on the tree edge that opened the frame, as a bitmask
  acc : Nat

/-- The driver's open frames as the invariant reads them, innermost first. -/
def LowlinkView.grayOf {ops : DFSOps State} (V : LowlinkView ops)
    (stack : List (DFSStep State ops.Position)) : List (GrayFrame State) :=
  stack.map fun st => ⟨st.state, V.posNat st.pos, st.idx, st.acc⟩

/-- A lowlink column read innermost first, the column itself growing at its end. -/
def revGetD (arr : Array Nat) (k : Nat) : Nat := arr.toList.reverse.getD k 0

/-- Frame `k`'s own lowlink, innermost first. -/
def LowlinkView.lowlinkAt {ops : DFSOps State} (V : LowlinkView ops) (aux : ops.Aux) (k : Nat) : Nat :=
  revGetD (V.lowlinks aux) k

/-- Frame `k`'s own accumulator, innermost first. -/
def LowlinkView.accAt {ops : DFSOps State} (V : LowlinkView ops) (aux : ops.Aux) (k : Nat) : Nat :=
  revGetD (V.accs aux) k

/-- An edge the search has already taken, which is every edge out of a live state that is not an open frame,
and out of one that is, the prefix its cursor has covered. -/
def ExploredEdge (gray : List (GrayFrame State)) (succs : State → Array State) (s t : State) : Prop :=
  ∃ j, (succs s)[j]? = some t ∧ ∀ g ∈ gray, g.state = s → j < g.idx

omit [BEq State] [Hashable State] [Inhabited State] in
/-- An explored edge is an edge. -/
theorem ExploredEdge.mem {gray : List (GrayFrame State)} {succs : State → Array State} {s t : State}
    (h : ExploredEdge gray succs s t) : t ∈ succs s := by
  obtain ⟨j, hj, -⟩ := h
  obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hj
  exact heq ▸ Array.getElem_mem hlt

/-- Unblocked reachability. -/
abbrev Reaches (succs : State → Array State) (s t : State) : Prop :=
  PathTo succs (fun _ => False) s t

/-- The invariant the search itself maintains, the first six clauses of `wf_env` [CCLMT18, §3] together with the three
`dfs1` post-conditions that characterise LOWLINK, adapted to an explicit frame stack. -/
structure SearchWF (ops : DFSOps State) (V : LowlinkView ops) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) (aux : ops.Aux)
    (gray : List (GrayFrame State)) : Prop where
  -- [CCLMT18] `wf_num` and `simplelist`, the position map being exact rules out duplicates by itself
  liveWF : LiveWF (V.live aux) (V.liveIndex aux)
  -- [CCLMT18] `wf_color`, a state is live or dead but never both
  disjoint : ∀ s ∈ V.live aux, s ∉ V.dead aux
  -- nothing is touched that the search could not have got to
  touched_reachable : ∀ s, s ∈ V.live aux ∨ s ∈ V.dead aux → Reachable initialStates succs s
  -- [CCLMT18] `no_black_to_white` strengthened, a closed component reaches nothing outside `dead`
  dead_closed : ∀ s ∈ V.dead aux, ∀ t ∈ succs s, t ∈ V.dead aux
  -- an edge the search has taken landed on a state it had to touch, so nothing explored is still unknown
  explored_touched : ∀ s ∈ V.live aux, ∀ t, ExploredEdge gray succs s t →
    t ∈ V.live aux ∨ t ∈ V.dead aux
  -- [CCLMT18] `wf_env` clause 5, a live state reaches every live state above it
  live_reaches_above : ∀ i j, (hi : i < (V.live aux).size) → (hj : j < (V.live aux).size) → i ≤ j →
    (V.live aux)[i] = (V.live aux)[j] ∨ Reaches succs (V.live aux)[i] (V.live aux)[j]
  -- [CCLMT18] `wf_env` clause 6, every live state reaches a gray state sitting at or below it
  live_reaches_gray : ∀ i, (hi : i < (V.live aux).size) → ∃ g ∈ gray,
    g.pos ≤ i ∧ ((V.live aux)[i] = g.state ∨ Reaches succs (V.live aux)[i] g.state)
  -- one lowlink and one accumulator per open frame
  frames_length : (V.lowlinks aux).size = gray.length
  accs_length : (V.accs aux).size = gray.length
  -- each frame sits on its own live position
  frame_pos : ∀ g ∈ gray, g.pos < (V.live aux).size ∧ (V.live aux)[g.pos]! = g.state
  -- the frames are the spanning forest's current branch [CCLMT18, §2], each opened by a tree edge from the one below it
  gray_chain : ∀ k, (hk : k + 1 < gray.length) →
    ExploredEdge gray succs gray[k + 1].state gray[k].state
  -- each frame remembers the marks on the tree edge that opened it, which POP folds into its parent
  gray_acc : ∀ k, (hk : k + 1 < gray.length) →
    gray[k].acc = marksToBitmask (edgeMarks gray[k + 1].state gray[k].state)
  -- the frames climb the live stack strictly
  frames_mono : ∀ k l, (hk : k < gray.length) → (hl : l < gray.length) → k < l →
    gray[l].pos < gray[k].pos
  -- [CCLMT18] `dfs1` post-condition `n ≤ e'.num[x]`
  lowlink_le : ∀ k, (hk : k < gray.length) → V.lowlinkAt aux k ≤ gray[k].pos
  -- [CCLMT18] `dfs1` post-condition `n = +∞ ∨ num_of_reachable n x e'`
  lowlink_reaches : ∀ k, (hk : k < gray.length) → V.lowlinkAt aux k < (V.live aux).size ∧
    (V.lowlinkAt aux k = gray[k].pos ∨ Reaches succs gray[k].state (V.live aux)[V.lowlinkAt aux k]!)
  -- [CCLMT18] `dfs1` post-condition on `xedge_to`, over explored edges: an edge out of `gray[k]`'s span is bounded by
  -- the least lowlink from the innermost frame out to `k`
  lowlink_bound : ∀ k, (hk : k < gray.length) → ∀ i, (hi : i < (V.live aux).size) → gray[k].pos ≤ i →
    ∀ t, ExploredEdge gray succs (V.live aux)[i] t → ∀ pt, (V.liveIndex aux)[t]? = some pt →
      ∃ l ≤ k, V.lowlinkAt aux l ≤ pt
  -- [RDKP13] the accumulator is sound: every mark a frame carries sits on an explored edge with both ends inside the
  -- frame's own span and below every inner frame
  acc_sound : ∀ k, (hk : k < gray.length) → ∀ b, (V.accAt aux k).testBit b = true →
    ∃ u v pu pv, ExploredEdge gray succs u v ∧
      (V.liveIndex aux)[u]? = some pu ∧ (V.liveIndex aux)[v]? = some pv ∧
      gray[k].pos ≤ pu ∧ (∃ l ≤ k, V.lowlinkAt aux l ≤ pv) ∧
      (∀ l, (hl : l < k) → pu < gray[l].pos ∧ pv < gray[l].pos) ∧
      (V.extraAcc.testBit b = true ∨ b ∈ edgeMarks u v)
  -- [RDKP13] the accumulator is complete: every mark on an explored edge between live states is carried by the frame
  -- owning its source, unless the edge is the tree edge out of that frame, whose marks the frame above holds in its `acc`
  acc_complete : ∀ u v pu pv, ExploredEdge gray succs u v →
    (V.liveIndex aux)[u]? = some pu → (V.liveIndex aux)[v]? = some pv →
    ∀ b, (V.extraAcc.testBit b = true ∨ b ∈ edgeMarks u v) →
    ∃ l, ∃ hl : l < gray.length, gray[l].pos ≤ pu ∧ (∀ l', (hl' : l' < l) → pu < gray[l'].pos) ∧
      ((V.accAt aux l).testBit b = true ∨ ∃ j, ∃ _ : j + 1 = l, u = gray[l].state ∧ v = gray[j].state)

/-- The search invariant together with what the recording wrapper has stored, [CCLMT18] `wf_env` clause 7 split
into the two directions the enumeration contract asks for. -/
structure EnumWF (ops : DFSOps State) (V : LowlinkView ops) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) (aux : ops.Aux)
    (recorded : Array (Std.HashSet State × ops.Aux)) (gray : List (GrayFrame State)) : Prop
    extends SearchWF ops V succs edgeMarks initialStates aux gray where
  -- every recorded set is a completed component lying wholly inside `dead`
  recorded_sound : ∀ p ∈ recorded, (∀ s ∈ p.1, s ∈ V.dead aux) ∧ InternallyConnected succs p.1
  -- and every completed component inside `dead` is covered by one of them
  recorded_complete : ∀ D : Std.HashSet State, (∃ s, s ∈ D) → InternallyConnected succs D →
    (∀ s ∈ D, s ∈ V.dead aux) → ∃ p ∈ recorded, ∀ s ∈ D, s ∈ p.1

end RunInvariant

/-! ## The enumeration contract -/

variable [LawfulBEq State] [LawfulHashable State]

private theorem mem_foldl_insert (l : List State) (init : Std.HashSet State) (s : State) :
    s ∈ l.foldl (fun acc x => acc.insert x) init ↔ s ∈ init ∨ s ∈ l := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.mem_cons]
    have hins : ∀ x, x ∈ init.insert a ↔ x = a ∨ x ∈ init := by
      intro x
      rw [Std.HashSet.mem_insert]
      simp only [beq_iff_eq]
      exact ⟨fun hx => hx.imp Eq.symm id, fun hx => hx.imp Eq.symm id⟩
    rw [hins]
    tauto

/-- The set a closing POP flushes is exactly the live stack from that position upwards. -/
theorem mem_flushedSet (live : Array State) (pos : Nat) (s : State) :
    s ∈ flushedSet live pos ↔ ∃ i, ∃ _ : i < live.size, pos ≤ i ∧ live[i] = s := by
  have hbase : s ∈ flushedSet live pos ↔ s ∈ live.extract pos live.size := by
    rw [flushedSet, ← Array.foldl_toList, mem_foldl_insert]
    simp only [Std.HashSet.not_mem_emptyWithCapacity, false_or, Array.mem_toList_iff]
  rw [hbase]
  constructor
  · intro hm
    obtain ⟨j, hj, hjv⟩ := Array.getElem_of_mem hm
    rw [Array.size_extract] at hj
    refine ⟨pos + j, by omega, by omega, ?_⟩
    rw [← hjv, Array.getElem_extract]
  · rintro ⟨i, hi, hpi, rfl⟩
    have hj : i - pos < (live.extract pos live.size).size := by rw [Array.size_extract]; omega
    have hv : (live.extract pos live.size)[i - pos] = live[i] := by
      rw [Array.getElem_extract]
      congr 1
      omega
    rw [← hv]
    exact Array.getElem_mem hj

omit [LawfulBEq State] [LawfulHashable State] in
private theorem dfsGo_base_eq (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat) :
    ∀ (aux : (enumOps ops V).Aux) (stack : List (DFSStep State ops.Position))
      (r : Option (State × List State) × (enumOps ops V).Aux),
      dfsGo (enumOps ops V) succs edgeMarks aux stack = some r →
      ∀ r', dfsGo ops succs edgeMarks aux.1 stack = some r' → r'.1 = none →
        r.1 = none ∧ r.2.1 = r'.2 := by
  refine dfsGo.partial_correctness (enumOps ops V) succs edgeMarks
    (fun aux stack r => ∀ r', dfsGo ops succs edgeMarks aux.1 stack = some r' → r'.1 = none →
      r.1 = none ∧ r.2.1 = r'.2) ?_
  intro f ih aux stack r hr
  cases stack with
  | nil =>
    intro r' hr' _
    simp only [Option.some.injEq] at hr
    rw [dfsGo.eq_def] at hr'
    simp only [Option.some.injEq] at hr'
    rw [← hr, ← hr']
    exact ⟨rfl, rfl⟩
  | cons step rest =>
    intro r' hr' hnone'
    rw [dfsGo.eq_def] at hr'
    by_cases hidx : step.idx < step.succ.size
    case neg =>
      simp only [hidx, dite_false] at hr hr'
      rcases hpop : ops.pop succs edgeMarks aux.1 step with ⟨aux'', found⟩
      simp only [enumOps, hpop] at hr
      simp only [hpop] at hr'
      cases found with
      | true => simp only [Option.some.injEq] at hr'; rw [← hr'] at hnone'; exact absurd hnone' (by simp)
      | false => exact ih _ rest r hr r' hr' hnone'
    case pos =>
      simp only [hidx, dite_true] at hr hr'
      cases hgs : ops.getStatus aux.1 step.succ[step.idx] with
      | dead =>
        simp only [enumOps, hgs] at hr
        simp only [hgs] at hr'
        exact ih _ _ r hr r' hr' hnone'
      | live =>
        simp only [enumOps, hgs] at hr
        simp only [hgs] at hr'
        rcases hupd : ops.update aux.1 (edgeMarks step.state step.succ[step.idx])
            step.succ[step.idx] with ⟨aux'', found⟩
        simp only [hupd] at hr hr'
        cases found with
        | true =>
          simp only [if_true, Option.some.injEq] at hr'
          rw [← hr'] at hnone'; exact absurd hnone' (by simp)
        | false => exact ih _ _ r hr r' hr' hnone'
      | unknown =>
        simp only [enumOps, hgs] at hr
        simp only [hgs] at hr'
        exact ih _ _ r hr r' hr' hnone'

omit [LawfulBEq State] [LawfulHashable State] in
private theorem dfsFromRoot_eq (ops : DFSOps.{u,v,w} State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (aux : ops.Aux) (q0 : State) :
    dfsFromRoot ops succs edgeMarks aux q0 =
      (dfsGo ops succs edgeMarks (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1
        [{ state := q0, pos := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
           acc := 0, succ := succs q0, idx := 0 }]).getD
        (none, (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1) := rfl

/-- The wrapper inherits lawfulness from `ops`. -/
def enumLawful (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops) (L : LawfulDFSOps ops) :
    LawfulDFSOps (enumOps ops V) where
  WellFormed := fun aux => L.WellFormed aux.1
  wf_push := fun aux q m h hw => L.wf_push aux.1 q m h hw
  wf_update := fun aux m d hw => L.wf_update aux.1 m d hw
  wf_pop := fun succs edgeMarks aux step hw => L.wf_pop succs edgeMarks aux.1 step hw
  push_status := fun aux q m q' => L.push_status aux.1 q m q'
  update_status := fun aux m d q => L.update_status aux.1 m d q
  pop_status := fun succs edgeMarks aux step q hw => L.pop_status succs edgeMarks aux.1 step q hw

omit [LawfulHashable State] in
private theorem dfsFromRoot_base_eq (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs) (L : LawfulDFSOps ops)
    (aux : (enumOps ops V).Aux) (q0 : State) (hwf : L.WellFormed aux.1)
    (hq0status : ops.getStatus aux.1 q0 = .unknown) (hq0 : Reachable initialStates succs q0)
    (hnone : (dfsFromRoot ops succs edgeMarks aux.1 q0).1 = none) :
    (dfsFromRoot (enumOps ops V) succs edgeMarks aux q0).1 = none ∧
      (dfsFromRoot (enumOps ops V) succs edgeMarks aux q0).2.1 =
        (dfsFromRoot ops succs edgeMarks aux.1 q0).2 := by
  rw [dfsFromRoot_eq ops succs edgeMarks aux.1 q0] at hnone ⊢
  rw [dfsFromRoot_eq (enumOps ops V) succs edgeMarks aux q0]
  -- neither run diverges, so the two `getD` fallbacks never fire and the cross cases do not arise
  have hwne := dfsGo_ne_none (enumOps ops V) succs edgeMarks initialStates fr (enumLawful ops V L)
    ((enumOps ops V).push aux q0 (Std.HashSet.emptyWithCapacity 0)).1
    [{ state := q0, pos := ((enumOps ops V).push aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
       acc := 0, succ := succs q0, idx := 0 }]
    ((enumLawful ops V L).wf_push aux q0 _ hq0status hwf)
    (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; rfl)
    (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; exact hq0)
  have hune := dfsGo_ne_none ops succs edgeMarks initialStates fr L
    (ops.push aux.1 q0 (Std.HashSet.emptyWithCapacity 0)).1
    [{ state := q0, pos := (ops.push aux.1 q0 (Std.HashSet.emptyWithCapacity 0)).2,
       acc := 0, succ := succs q0, idx := 0 }]
    (L.wf_push aux.1 q0 _ hq0status hwf)
    (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; rfl)
    (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; exact hq0)
  obtain ⟨ru, hdg⟩ := Option.ne_none_iff_exists'.mp hune
  obtain ⟨rw', hdg'⟩ := Option.ne_none_iff_exists'.mp hwne
  rw [hdg] at hnone ⊢
  rw [hdg']
  simp only [Option.getD_some] at hnone ⊢
  exact dfsGo_base_eq ops V succs edgeMarks _ _ rw' hdg' ru hdg hnone

omit [LawfulHashable State] in
private theorem genericDFSGo_base_eq (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs) (L : LawfulDFSOps ops) :
    ∀ (roots : List State), (∀ q ∈ roots, Reachable initialStates succs q) →
      ∀ (aux : (enumOps ops V).Aux) rw' ru, L.WellFormed aux.1 →
        genericDFSGo (enumOps ops V) succs edgeMarks roots aux = some rw' →
        genericDFSGo ops succs edgeMarks roots aux.1 = some ru →
        ru.1 = none → rw'.1 = none ∧ rw'.2.1 = ru.2 := by
  intro roots
  induction roots with
  | nil =>
    intro _ aux rw' ru _ hw hu _
    rw [genericDFSGo.eq_def] at hw hu
    simp only [Option.some.injEq] at hw hu
    rw [← hw, ← hu]
    exact ⟨rfl, rfl⟩
  | cons q rest ih =>
    intro hroots aux rw' ru hwf hw hu hnone
    have hq : Reachable initialStates succs q := hroots q (by simp)
    have hrest : ∀ q' ∈ rest, Reachable initialStates succs q' :=
      fun q' hq' => hroots q' (by simp [hq'])
    rw [genericDFSGo.eq_def] at hw hu
    cases hst : ops.getStatus aux.1 q with
    | unknown =>
      simp only [enumOps_getStatus, hst] at hw
      simp only [hst] at hu
      cases hf : (dfsFromRoot ops succs edgeMarks aux.1 q).1 with
      | some x =>
        exfalso
        simp only [hf, Option.some.injEq] at hu
        rw [← hu] at hnone
        simp at hnone
      | none =>
        obtain ⟨hfw, hbase⟩ := dfsFromRoot_base_eq ops V succs edgeMarks initialStates fr L
          aux q hwf hst hq hf
        simp only [hf] at hu
        simp only [hfw] at hw
        refine ih hrest _ rw' ru ?_ hw (by rw [← hbase] at hu; exact hu) hnone
        rw [hbase]
        exact dfsFromRoot_wellFormed_total ops succs edgeMarks L aux.1 q hwf hst
    | dead =>
      simp only [enumOps_getStatus, hst] at hw
      simp only [hst] at hu
      exact ih hrest aux rw' ru hwf hw hu hnone
    | live =>
      simp only [enumOps_getStatus, hst] at hw
      simp only [hst] at hu
      exact ih hrest aux rw' ru hwf hw hu hnone

omit [LawfulHashable State] in
/-- A run that never reports agrees with the recording run on the refinement's own state. -/
theorem enumOps_base_eq (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs) (L : LawfulDFSOps ops)
    (hwf : L.WellFormed ops.initAux)
    (hnone : (genericDFS ops succs edgeMarks initialStates ops.initAux).1 = none) :
    (genericDFS (enumOps ops V) succs edgeMarks initialStates (enumOps ops V).initAux).2.1 =
      (genericDFS ops succs edgeMarks initialStates ops.initAux).2 := by
  unfold genericDFS at hnone ⊢
  obtain ⟨ru, hu⟩ := Option.ne_none_iff_exists'.mp
    (genericDFSGo_ne_none ops succs edgeMarks initialStates ops.initAux)
  obtain ⟨rw', hw⟩ := Option.ne_none_iff_exists'.mp
    (genericDFSGo_ne_none (enumOps ops V) succs edgeMarks initialStates (enumOps ops V).initAux)
  rw [hu] at hnone ⊢
  rw [hw]
  simp only [Option.getD_some] at hnone ⊢
  exact (genericDFSGo_base_eq ops V succs edgeMarks initialStates fr L initialStates
    (fun q hq => Reachable.base hq) (enumOps ops V).initAux rw' ru hwf hw hu hnone).2

/-- Every recorded entry is a closing POP's own flush, as an invariant on the recorded array alone. -/
def RecordedWF (ops : DFSOps State) (V : LowlinkView ops)
    (rec : Array (Std.HashSet State × ops.Aux)) : Prop :=
  ∀ p ∈ rec, ∃ step : DFSStep State ops.Position,
    V.closes p.2 step = true ∧ p.1 = flushedSet (V.live p.2) (V.posNat step.pos)

omit [LawfulBEq State] [LawfulHashable State] in
private theorem dfsGo_recorded (ops : DFSOps State) (V : LowlinkView ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat) :
    ∀ (aux : (enumOps ops V).Aux) (stack : List (DFSStep State (enumOps ops V).Position))
      (r : Option (State × List State) × (enumOps ops V).Aux),
      dfsGo (enumOps ops V) succs edgeMarks aux stack = some r →
      RecordedWF ops V aux.2 → RecordedWF ops V r.2.2 := by
  refine dfsGo.partial_correctness (enumOps ops V) succs edgeMarks
    (fun aux stack r => RecordedWF ops V aux.2 → RecordedWF ops V r.2.2) ?_
  intro dfsGo ih aux stack r hr
  cases stack with
  | nil =>
    intro h
    simp only [Option.some.injEq] at hr
    rw [← hr]
    exact h
  | cons step rest =>
    intro h
    by_cases hidx : step.idx < step.succ.size
    case neg =>
      simp only [hidx, dite_false] at hr
      -- POP never reports here, and the recorded array grows by at most the closing frame's flush
      refine ih _ rest r hr ?_
      by_cases hcl : V.closes aux.1 step
      · intro q hq
        rcases Array.mem_push.mp (by simpa [enumOps, hcl] using hq) with hq' | hq'
        · exact h q hq'
        · exact ⟨step, by simpa [hq'] using hcl, by simp [hq']⟩
      · simpa [enumOps, hcl] using h
    case pos =>
      simp only [hidx, dite_true] at hr
      cases hgs : (enumOps ops V).getStatus aux step.succ[step.idx] with
      | dead => simp only [hgs] at hr; exact ih aux _ r hr h
      | live =>
        simp only [hgs] at hr
        exact ih _ _ r (by simpa [enumOps] using hr) (by simpa [enumOps] using h)
      | unknown =>
        simp only [hgs] at hr
        exact ih _ _ r (by simpa [enumOps] using hr) (by simpa [enumOps] using h)

omit [LawfulBEq State] [LawfulHashable State] in
private theorem enum_getD (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (P : Option (State × List State) × (enumOps ops V).Aux → Prop)
    (o : Option (Option (State × List State) × (enumOps ops V).Aux)) (a : (enumOps ops V).Aux)
    (ha : P (none, a)) (hs : ∀ r, o = some r → P r) : P (o.getD (none, a)) := by
  cases o with
  | none => exact ha
  | some r => exact hs r rfl

omit [LawfulBEq State] [LawfulHashable State] in
private theorem dfsFromRoot_recorded (ops : DFSOps State) (V : LowlinkView ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (aux : (enumOps ops V).Aux) (q0 : State) (h : RecordedWF ops V aux.2) :
    RecordedWF ops V (dfsFromRoot (enumOps ops V) succs edgeMarks aux q0).2.2 := by
  unfold dfsFromRoot
  exact enum_getD ops V (fun r => RecordedWF ops V r.2.2) _ _ h
    (fun r hr => dfsGo_recorded ops V succs edgeMarks _ _ r hr h)

omit [LawfulBEq State] [LawfulHashable State] in
private theorem genericDFSGo_recorded (ops : DFSOps State) (V : LowlinkView ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat) :
    ∀ (roots : List State) (aux : (enumOps ops V).Aux) r,
      genericDFSGo (enumOps ops V) succs edgeMarks roots aux = some r →
      RecordedWF ops V aux.2 → RecordedWF ops V r.2.2 := by
  intro roots
  induction roots with
  | nil =>
    intro aux r hgo h
    rw [genericDFSGo.eq_def] at hgo
    simp only [Option.some.injEq] at hgo
    rw [← hgo]
    exact h
  | cons q rest ih =>
    intro aux r hgo h
    rw [genericDFSGo.eq_def] at hgo
    cases hst : (enumOps ops V).getStatus aux q with
    | unknown =>
      simp only [hst] at hgo
      have hrec := dfsFromRoot_recorded ops V succs edgeMarks aux q h
      cases hf : (dfsFromRoot (enumOps ops V) succs edgeMarks aux q).1 with
      | some x => simp only [hf, Option.some.injEq] at hgo; rw [← hgo]; exact hrec
      | none => simp only [hf] at hgo; exact ih _ r hgo hrec
    | dead => simp only [hst] at hgo; exact ih aux r hgo h
    | live => simp only [hst] at hgo; exact ih aux r hgo h

omit [LawfulBEq State] [LawfulHashable State] in
/-- Each recorded set is the flush of the state recorded beside it. -/
theorem enumSCCs_flushed (ops : DFSOps State) (V : LowlinkView ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (C : Std.HashSet State) (aux : ops.Aux)
    (h : (C, aux) ∈ enumRun ops V succs edgeMarks initialStates) :
    ∃ step : DFSStep State ops.Position, V.closes aux step = true ∧
      C = flushedSet (V.live aux) (V.posNat step.pos) := by
  have hinit : RecordedWF ops V (enumOps ops V).initAux.2 := by
    intro p hp; simp [enumOps] at hp
  unfold enumRun genericDFS at h
  cases hgo : genericDFSGo (enumOps ops V) succs edgeMarks initialStates (enumOps ops V).initAux with
  | none => rw [hgo] at h; simp only [Option.getD_none] at h; exact absurd h (by simp [enumOps])
  | some r =>
    rw [hgo] at h
    simp only [Option.getD_some] at h
    exact genericDFSGo_recorded ops V succs edgeMarks initialStates _ r hgo hinit (C, aux) h

omit [LawfulBEq State] [LawfulHashable State] in
private theorem dfsGo_enum_none (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat) :
    ∀ (aux : (enumOps ops V).Aux) (stack : List (DFSStep State ops.Position))
      (r : Option (State × List State) × (enumOps ops V).Aux),
      dfsGo (enumOps ops V) succs edgeMarks aux stack = some r → r.1 = none := by
  refine dfsGo.partial_correctness (enumOps ops V) succs edgeMarks (fun _ _ r => r.1 = none) ?_
  intro f ih aux stack r hr
  cases stack with
  | nil => simp only [Option.some.injEq] at hr; rw [← hr]
  | cons step rest =>
    by_cases hidx : step.idx < step.succ.size
    case neg => simp only [hidx, dite_false, enumOps] at hr; exact ih _ rest r hr
    case pos =>
      simp only [hidx, dite_true] at hr
      cases hgs : ops.getStatus aux.1 step.succ[step.idx] with
      | dead => simp only [enumOps_getStatus, hgs] at hr; exact ih _ _ r hr
      | live => simp only [enumOps, hgs] at hr; exact ih _ _ r hr
      | unknown => simp only [enumOps, hgs] at hr; exact ih _ _ r hr

omit [LawfulBEq State] [LawfulHashable State] in
private theorem dfsFromRoot_enum_none (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (aux : (enumOps ops V).Aux) (q0 : State) :
    (dfsFromRoot (enumOps ops V) succs edgeMarks aux q0).1 = none := by
  unfold dfsFromRoot
  exact enum_getD ops V (fun r => r.1 = none) _ _ rfl
    (fun r hr => dfsGo_enum_none ops V succs edgeMarks _ _ r hr)

omit [LawfulBEq State] [LawfulHashable State] in
private theorem genericDFSGo_enum_none (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat) :
    ∀ (roots : List State) (aux : (enumOps ops V).Aux) r,
      genericDFSGo (enumOps ops V) succs edgeMarks roots aux = some r → r.1 = none := by
  intro roots
  induction roots with
  | nil =>
    intro aux r hgo
    rw [genericDFSGo.eq_def] at hgo
    simp only [Option.some.injEq] at hgo
    rw [← hgo]
  | cons q rest ih =>
    intro aux r hgo
    rw [genericDFSGo.eq_def] at hgo
    cases hst : ops.getStatus aux.1 q with
    | unknown =>
      simp only [enumOps_getStatus, hst] at hgo
      rw [dfsFromRoot_enum_none ops V succs edgeMarks aux q] at hgo
      exact ih _ r hgo
    | dead => simp only [enumOps_getStatus, hst] at hgo; exact ih aux r hgo
    | live => simp only [enumOps_getStatus, hst] at hgo; exact ih aux r hgo

omit [LawfulBEq State] [LawfulHashable State] in
/-- The wrapper forces both reported `Bool`s to `false`, so the recording run explores everything. -/
theorem enumOps_never_reports (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) :
    (genericDFS (enumOps ops V) succs edgeMarks initialStates (enumOps ops V).initAux).1 = none := by
  unfold genericDFS
  obtain ⟨r, hgo⟩ := Option.ne_none_iff_exists'.mp
    (genericDFSGo_ne_none (enumOps ops V) succs edgeMarks initialStates (enumOps ops V).initAux)
  rw [hgo]
  exact genericDFSGo_enum_none ops V succs edgeMarks initialStates _ r hgo

omit [LawfulBEq State] [LawfulHashable State] in
/-- The lowlink column read innermost-first, peeling the frame `back?` names. -/
private theorem toList_reverse_of_back? {α} (arr : Array α) (x : α) (h : arr.back? = some x) :
    arr.toList.reverse = x :: arr.pop.toList.reverse := by
  obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.mp h
  simp

omit [LawfulBEq State] [LawfulHashable State] in
@[simp] private theorem revGetD_push_zero (arr : Array Nat) (x : Nat) :
    revGetD (arr.push x) 0 = x := by simp [revGetD]

omit [LawfulBEq State] [LawfulHashable State] in
@[simp] private theorem revGetD_push_succ (arr : Array Nat) (x k : Nat) :
    revGetD (arr.push x) (k + 1) = revGetD arr k := by simp [revGetD]

omit [LawfulBEq State] [LawfulHashable State] in
/-- The innermost entry of a column is its last one. -/
theorem revGetD_zero {arr : Array Nat} {x : Nat} (h : arr.back? = some x) :
    revGetD arr 0 = x := by simp [revGetD, toList_reverse_of_back? _ _ h]

omit [LawfulBEq State] [LawfulHashable State] in
private theorem revGetD_pop {arr : Array Nat} {x : Nat} (h : arr.back? = some x) (k : Nat) :
    revGetD arr.pop k = revGetD arr (k + 1) := by
  simp [revGetD, toList_reverse_of_back? _ _ h]

omit [BEq State] [Hashable State] [LawfulBEq State] [LawfulHashable State] in
/-- The frames are the spanning forest's current branch, so every one of them reaches the innermost [CCLMT18, §2]. -/
private theorem gray_reaches_head [Inhabited State] {succs : State → Array State}
    {g0 : GrayFrame State} {gray : List (GrayFrame State)}
    (hchain : ∀ k, (hk : k + 1 < (g0 :: gray).length) →
      (g0 :: gray)[k].state ∈ succs (g0 :: gray)[k + 1].state) :
    ∀ g ∈ g0 :: gray, g.state = g0.state ∨ Reaches succs g.state g0.state := by
  have key : ∀ k, (hk : k < (g0 :: gray).length) →
      (g0 :: gray)[k].state = g0.state ∨ Reaches succs (g0 :: gray)[k].state g0.state := by
    intro k
    induction k with
    | zero => intro _; exact Or.inl rfl
    | succ n ih =>
      intro hk
      have hstep : Reaches succs (g0 :: gray)[n + 1].state (g0 :: gray)[n].state :=
        PathTo.direct (hchain n hk)
      rcases ih (by omega) with heq | hr
      · exact Or.inr (by rw [← heq]; exact hstep)
      · exact Or.inr (PathTo.trans hstep hr)
  intro g hg
  obtain ⟨k, hk, hkg⟩ := List.getElem_of_mem hg
  rw [← hkg]
  exact key k hk

omit [BEq State] [Hashable State] [LawfulBEq State] [LawfulHashable State] in
/-- Bumping a frame's cursor moves neither its state nor its position. -/
private theorem bumped_getElem {f f' : GrayFrame State} {gray : List (GrayFrame State)}
    (hs : f'.state = f.state) (hp : f'.pos = f.pos) (ha : f'.acc = f.acc) (k : Nat)
    (hk : k < (f :: gray).length) :
    ((f' :: gray)[k]'(by simpa using hk)).state = ((f :: gray)[k]'hk).state ∧
      ((f' :: gray)[k]'(by simpa using hk)).pos = ((f :: gray)[k]'hk).pos ∧
      ((f' :: gray)[k]'(by simpa using hk)).acc = ((f :: gray)[k]'hk).acc := by
  rcases k with _ | k
  · exact ⟨hs, hp, ha⟩
  · simp

/-- The search invariant at the start: nothing touched and no frame open. -/
theorem searchWF_init [Inhabited State] (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (hlaw : LowlinkLawful ops V) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) :
    SearchWF ops V succs edgeMarks initialStates ops.initAux [] := by
  have hli : ∀ q : State, (V.liveIndex ops.initAux)[q]? = (none : Option Nat) := by
    intro q
    by_contra hc
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hc
    have h := hlaw.status ops.initAux q
    rw [hlaw.init_status q, liveStatusOf,
      if_pos (by rw [Std.HashMap.contains_eq_isSome_getElem?, hp]; rfl)] at h
    exact absurd h (by simp)
  have hsize : (V.live ops.initAux).size = 0 := by rw [hlaw.init_live]; rfl
  exact {
    liveWF := ⟨fun i hi => absurd hi (by omega),
      fun q p hp => absurd hp (by rw [hli q]; simp)⟩
    disjoint := fun s hs => absurd hs (by rw [hlaw.init_live]; simp)
    touched_reachable := fun s hs => by
      rcases hs with h | h
      · exact absurd h (by rw [hlaw.init_live]; simp)
      · exact absurd h (hlaw.init_dead s)
    dead_closed := fun s hs => absurd hs (hlaw.init_dead s)
    explored_touched := fun s hs => absurd hs (by rw [hlaw.init_live]; simp)
    live_reaches_above := fun i j hi => absurd hi (by omega)
    live_reaches_gray := fun i hi => absurd hi (by omega)
    frames_length := by rw [hlaw.init_lowlinks]; rfl
    accs_length := by rw [hlaw.init_accs]; rfl
    frame_pos := fun st hst => absurd hst (by simp)
    gray_chain := fun k hk => absurd hk (by simp)
    gray_acc := fun k hk => absurd hk (by simp)
    frames_mono := fun k l hk => absurd hk (by simp)
    lowlink_le := fun k hk => absurd hk (by simp)
    lowlink_reaches := fun k hk => absurd hk (by simp)
    lowlink_bound := fun k hk => absurd hk (by simp)
    acc_sound := fun k hk => absurd hk (by simp)
    acc_complete := fun u _ _ _ _ hu => by rw [hli u] at hu; simp at hu }

/-- The invariant at the start: nothing touched, no frame open, nothing recorded. -/
theorem enumWF_init [Inhabited State] (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (hlaw : LowlinkLawful ops V) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) :
    EnumWF ops V succs edgeMarks initialStates ops.initAux #[] [] where
  toSearchWF := searchWF_init ops V hlaw succs edgeMarks initialStates
  recorded_sound := fun p hp => absurd hp (by simp)
  recorded_complete := fun D hDne _ hDdead => by
    obtain ⟨s, hs⟩ := hDne
    exact absurd (hDdead s hs) (hlaw.init_dead s)

/-! ### The transitions

One `SearchWF` lemma per way the driver moves. Only a closing POP changes `dead`, so it is the only move with its own
`EnumWF` lemma. -/

/-- A dispatch onto a dead successor, which only bumps the innermost cursor. -/
theorem SearchWF.bump_step [Inhabited State] {ops : DFSOps.{u,v,w} State} {V : LowlinkView ops}
    (hlaw : LowlinkLawful ops V) {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    {aux : ops.Aux}
    {d src : State} {p idx a : Nat} {gray : List (GrayFrame State)}
    (hd : ops.getStatus aux d = .dead) (hedge : (succs src)[idx]? = some d)
    (h : SearchWF ops V succs edgeMarks initialStates aux (⟨src, p, idx, a⟩ :: gray)) :
    SearchWF ops V succs edgeMarks initialStates aux (⟨src, p, idx + 1, a⟩ :: gray) := by
  have hstat : liveStatusOf (V.liveIndex aux) (V.dead aux) d = .dead := by
    rw [← hlaw.status aux d]; exact hd
  have hnli : (V.liveIndex aux).contains d = false := by
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    rw [liveStatusOf, if_pos hc] at hstat
    exact absurd hstat (by simp)
  have hnone : (V.liveIndex aux)[d]? = none := by
    rcases hg : (V.liveIndex aux)[d]? with _ | pd
    · rfl
    · rw [Std.HashMap.contains_eq_isSome_getElem?, hg] at hnli
      simp at hnli
  have hdmem : d ∈ V.dead aux := by
    by_contra hc
    rw [liveStatusOf, if_neg (by simp [hnli]),
      if_neg (fun hcc => hc (Std.HashSet.mem_iff_contains.mpr hcc))] at hstat
    exact absurd hstat (by simp)
  have hexp : ∀ s t, ExploredEdge (⟨src, p, idx + 1, a⟩ :: gray) succs s t →
      ExploredEdge (⟨src, p, idx, a⟩ :: gray) succs s t ∨ (s = src ∧ t = d) := by
    rintro s t ⟨j, hj, hg⟩
    by_cases hs : s = src
    · subst hs
      have hjb : j < idx + 1 := hg _ (List.mem_cons_self ..) rfl
      rcases Nat.lt_or_ge j idx with hlt | hge
      · refine Or.inl ⟨j, hj, fun g hgm hgs => ?_⟩
        rcases List.mem_cons.mp hgm with rfl | hgm'
        · exact hlt
        · exact hg g (List.mem_cons_of_mem _ hgm') hgs
      · have hje : j = idx := by omega
        subst hje
        rw [hedge] at hj
        exact Or.inr ⟨rfl, (Option.some.inj hj).symm⟩
    · refine Or.inl ⟨j, hj, fun g hgm hgs => ?_⟩
      rcases List.mem_cons.mp hgm with rfl | hgm'
      · exact absurd hgs.symm hs
      · exact hg g (List.mem_cons_of_mem _ hgm') hgs
  have hexpmono : ∀ s t, ExploredEdge (⟨src, p, idx, a⟩ :: gray) succs s t →
      ExploredEdge (⟨src, p, idx + 1, a⟩ :: gray) succs s t := by
    rintro s t ⟨j, hj, hg⟩
    refine ⟨j, hj, fun g hgm hgs => ?_⟩
    rcases List.mem_cons.mp hgm with rfl | hgm'
    · have hb := hg _ (List.mem_cons_self ..) hgs
      simp only at hb ⊢
      omega
    · exact hg g (List.mem_cons_of_mem _ hgm') hgs
  refine {
    liveWF := h.liveWF, disjoint := h.disjoint, touched_reachable := h.touched_reachable
    dead_closed := h.dead_closed
    explored_touched := ?_
    live_reaches_above := h.live_reaches_above
    live_reaches_gray := ?_
    frames_length := h.frames_length
    accs_length := h.accs_length
    frame_pos := ?_, gray_chain := ?_, gray_acc := ?_, frames_mono := ?_
    lowlink_le := ?_, lowlink_reaches := ?_, lowlink_bound := ?_
    acc_sound := by
      intro k hk b hbit
      obtain ⟨u, v, pu, pv, he, hu, hv, hlo, hlow, hup, hmk⟩ := h.acc_sound k hk b hbit
      have hb1 := bumped_getElem (f := (⟨src, p, idx, a⟩ : GrayFrame State))
        (f' := (⟨src, p, idx + 1, a⟩ : GrayFrame State)) (gray := gray) rfl rfl rfl
      refine ⟨u, v, pu, pv, hexpmono _ _ he, hu, hv, ?_, hlow, ?_, hmk⟩
      · rw [(hb1 k hk).2.1]; exact hlo
      · intro l hl
        rw [(hb1 l (by simp at hk ⊢; omega)).2.1]
        exact hup l hl
    acc_complete := by
      intro u v pu pv he hu hv b hb
      have hb1 := bumped_getElem (f := (⟨src, p, idx, a⟩ : GrayFrame State))
        (f' := (⟨src, p, idx + 1, a⟩ : GrayFrame State)) (gray := gray) rfl rfl rfl
      rcases hexp u v he with he' | ⟨-, hvd⟩
      · obtain ⟨l, hl, hlo, hup, hacc⟩ := h.acc_complete u v pu pv he' hu hv b hb
        refine ⟨l, by simpa using hl, by rw [(hb1 l hl).2.1]; exact hlo, fun l' hl' => ?_, ?_⟩
        · rw [(hb1 l' (by omega)).2.1]; exact hup l' hl'
        · rcases hacc with hacc | ⟨j, hj, hu', hv'⟩
          · exact Or.inl hacc
          · exact Or.inr ⟨j, hj, by rw [(hb1 l hl).1]; exact hu', by rw [(hb1 j (by omega)).1]; exact hv'⟩
      · rw [hvd, hnone] at hv
        exact absurd hv (by simp)
  }
  · intro s hs t ht
    rcases hexp s t ht with ht' | ⟨-, rfl⟩
    · exact h.explored_touched s hs t ht'
    · exact Or.inr hdmem
  · intro i hi
    obtain ⟨g, hg, hgle, hgr⟩ := h.live_reaches_gray i hi
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact ⟨⟨src, p, idx + 1, a⟩, List.mem_cons_self .., hgle, hgr⟩
    · exact ⟨g, List.mem_cons_of_mem _ hg', hgle, hgr⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact h.frame_pos ⟨src, p, idx, a⟩ (List.mem_cons_self ..)
    · exact h.frame_pos g (List.mem_cons_of_mem _ hg')
  · intro k hk
    rcases k with _ | k
    · simpa using hexpmono _ _ (by simpa using h.gray_chain 0 hk)
    · simpa using hexpmono _ _ (by simpa using h.gray_chain (k + 1) hk)
  · intro k hk
    have hb0 := bumped_getElem (f := (⟨src, p, idx, a⟩ : GrayFrame State))
      (f' := (⟨src, p, idx + 1, a⟩ : GrayFrame State)) (gray := gray) rfl rfl rfl
    rw [(hb0 k (by simp at hk ⊢; omega)).2.2, (hb0 k (by simp at hk ⊢; omega)).1,
      (hb0 (k + 1) (by simp at hk ⊢; omega)).1]
    exact h.gray_acc k (by simp at hk ⊢; omega)
  · intro k l hk hl hkl
    rcases k with _ | k <;> rcases l with _ | l <;> simpa using h.frames_mono _ _ hk hl hkl
  · intro k hk
    rcases k with _ | k <;> simpa using h.lowlink_le _ hk
  · intro k hk
    rcases k with _ | k <;> simpa using h.lowlink_reaches _ hk
  · intro k hk i hi hle t ht pt hpt
    have hle' : (⟨src, p, idx, a⟩ :: gray)[k].pos ≤ i := by rcases k with _ | k <;> simpa using hle
    rcases hexp _ t ht with ht' | ⟨-, rfl⟩
    · exact h.lowlink_bound k hk i hi hle' t ht' pt hpt
    · rw [hnone] at hpt
      exact absurd hpt (by simp)

/-- UPDATE lowers the innermost lowlink to a live back-edge target, which only the lowlink clauses see. -/
theorem SearchWF.update_step [Inhabited State] {ops : DFSOps.{u,v,w} State} {V : LowlinkView ops}
    (hlaw : LowlinkLawful ops V) {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    {aux : ops.Aux} {m : Std.HashSet Nat}
    {d src : State} {p idx a : Nat} {gray : List (GrayFrame State)}
    (hd : ops.getStatus aux d = .live) (hedge : (succs src)[idx]? = some d)
    (hmarks : m = edgeMarks src d)
    (h : SearchWF ops V succs edgeMarks initialStates aux (⟨src, p, idx, a⟩ :: gray)) :
    SearchWF ops V succs edgeMarks initialStates (ops.update aux m d).1 (⟨src, p, idx + 1, a⟩ :: gray) := by
  have hsz : (V.lowlinks aux).size = gray.length + 1 := by rw [h.frames_length]; simp
  obtain ⟨ll, hll⟩ : ∃ ll, (V.lowlinks aux).back? = some ll := by
    rcases hb : (V.lowlinks aux).back? with _ | ll
    · rw [Array.back?_eq_none_iff] at hb; simp [hb] at hsz
    · exact ⟨ll, rfl⟩
  -- the back-edge target is live, so the position it contributes is a real live slot holding it
  have hdlive : (V.liveIndex aux).contains d = true := by
    have hs := hlaw.status aux d
    rw [hd, liveStatusOf] at hs
    by_cases hc : (V.liveIndex aux).contains d = true
    · exact hc
    · simp only [Bool.not_eq_true] at hc
      rw [hc] at hs
      simp at hs
      split at hs <;> simp at hs
  obtain ⟨pd, hpd⟩ : ∃ pd, (V.liveIndex aux)[d]? = some pd := by
    rw [Std.HashMap.contains_eq_isSome_getElem?] at hdlive
    exact Option.isSome_iff_exists.mp hdlive
  have hgetD : (V.liveIndex aux).getD d 0 = pd := by
    rw [Std.HashMap.getD_eq_getD_getElem?, hpd]; rfl
  obtain ⟨hpdlt, hpdval⟩ := h.liveWF.bwd d pd hpd
  have hdmem : d ∈ V.live aux := by
    rw [← hpdval, getElem!_pos (V.live aux) pd hpdlt]
    exact Array.getElem_mem hpdlt
  have hlive' : V.live (ops.update aux m d).1 = V.live aux := hlaw.update_live aux m d
  have hli' : V.liveIndex (ops.update aux m d).1 = V.liveIndex aux := hlaw.update_liveIndex aux m d
  have hdead' : V.dead (ops.update aux m d).1 = V.dead aux := hlaw.update_dead aux m d
  have hlow' : V.lowlinks (ops.update aux m d).1 = (V.lowlinks aux).pop.push (min ll pd) := by
    rw [hlaw.update_lowlinks aux m d ll hll, hgetD]
  -- the merge only lowers, and only the innermost
  have hmono : ∀ k, V.lowlinkAt (ops.update aux m d).1 k ≤ V.lowlinkAt aux k := by
    intro k
    rcases k with _ | k
    · simp only [LowlinkView.lowlinkAt, hlow', revGetD_push_zero, revGetD_zero hll]
      exact min_le_left _ _
    · simp only [LowlinkView.lowlinkAt, hlow', revGetD_push_succ, revGetD_pop hll]
      exact le_refl _
  have hzero : V.lowlinkAt (ops.update aux m d).1 0 = min ll pd := by
    simp [LowlinkView.lowlinkAt, hlow']
  have hsza : (V.accs aux).size = gray.length + 1 := by rw [h.accs_length]; simp
  obtain ⟨acc0, hacc0⟩ : ∃ a, (V.accs aux).back? = some a := by
    rcases hb : (V.accs aux).back? with _ | a
    · rw [Array.back?_eq_none_iff] at hb; simp [hb] at hsza
    · exact ⟨a, rfl⟩
  have hacc' : V.accs (ops.update aux m d).1
      = (V.accs aux).pop.push (acc0 ||| marksToBitmask m ||| V.extraAcc) :=
    hlaw.update_accs aux m d acc0 hacc0
  -- the only new edge is the one UPDATE just took
  have hexp : ∀ s t, ExploredEdge (⟨src, p, idx + 1, a⟩ :: gray) succs s t →
      ExploredEdge (⟨src, p, idx, a⟩ :: gray) succs s t ∨ (s = src ∧ t = d) := by
    rintro s t ⟨j, hj, hg⟩
    by_cases hs : s = src
    · subst hs
      have hjb : j < idx + 1 := hg _ (List.mem_cons_self ..) rfl
      rcases Nat.lt_or_ge j idx with hlt | hge
      · refine Or.inl ⟨j, hj, fun g hgm hgs => ?_⟩
        rcases List.mem_cons.mp hgm with rfl | hgm'
        · exact hlt
        · exact hg g (List.mem_cons_of_mem _ hgm') hgs
      · have hje : j = idx := by omega
        subst hje
        rw [hedge] at hj
        exact Or.inr ⟨rfl, (Option.some.inj hj).symm⟩
    · refine Or.inl ⟨j, hj, fun g hgm hgs => ?_⟩
      rcases List.mem_cons.mp hgm with rfl | hgm'
      · exact absurd hgs.symm hs
      · exact hg g (List.mem_cons_of_mem _ hgm') hgs
  have hexpmono : ∀ s t, ExploredEdge (⟨src, p, idx, a⟩ :: gray) succs s t →
      ExploredEdge (⟨src, p, idx + 1, a⟩ :: gray) succs s t := by
    rintro s t ⟨j, hj, hg⟩
    refine ⟨j, hj, fun g hgm hgs => ?_⟩
    rcases List.mem_cons.mp hgm with rfl | hgm'
    · have hb := hg _ (List.mem_cons_self ..) hgs
      simp only at hb ⊢
      omega
    · exact hg g (List.mem_cons_of_mem _ hgm') hgs
  have hmem : d ∈ succs src := by
    obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hedge
    exact heq ▸ Array.getElem_mem hlt
  have hinjU : ∀ x y, (hx : x < (V.live aux).size) → (hy : y < (V.live aux).size) →
      (V.live aux)[x] = (V.live aux)[y] → x = y := by
    intro x y hx hy hxy
    have h1 := h.liveWF.fwd x hx
    have h2 := h.liveWF.fwd y hy
    rw [hxy, h2] at h1
    exact (Option.some.inj h1).symm
  have hp1 : p < (V.live aux).size :=
    (h.frame_pos (⟨src, p, idx, a⟩ : GrayFrame State) (List.mem_cons_self ..)).1
  have hp2 : (V.live aux)[p]! = src :=
    (h.frame_pos (⟨src, p, idx, a⟩ : GrayFrame State) (List.mem_cons_self ..)).2
  have hpv : (V.live aux)[p]'hp1 = src := by
    rw [← hp2]; exact (getElem!_pos (V.live aux) p hp1).symm
  have hsrcpos : (V.liveIndex aux)[src]? = some p := by
    have hf := h.liveWF.fwd p hp1
    rwa [hpv] at hf
  have hgraysrcU : ∀ g ∈ gray, g.state ≠ src := by
    intro g hg heq
    obtain ⟨hg1, hg2⟩ := h.frame_pos g (List.mem_cons_of_mem _ hg)
    have hgv : (V.live aux)[g.pos]'hg1 = g.state := by
      rw [← hg2]; exact (getElem!_pos (V.live aux) g.pos hg1).symm
    have hge : g.pos = p := hinjU g.pos p hg1 hp1 (by rw [hgv, hpv, heq])
    obtain ⟨k, hk, hkg⟩ := List.getElem_of_mem hg
    have hm := h.frames_mono 0 (k + 1) (by simp) (by simp; omega) (by omega)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, hkg] at hm
    omega
  have hedgeexp : ExploredEdge (⟨src, p, idx + 1, a⟩ :: gray) succs src d := by
    refine ⟨idx, hedge, fun g hgm hgs => ?_⟩
    rcases List.mem_cons.mp hgm with rfl | hgm'
    · simp
    · exact absurd hgs (hgraysrcU g hgm')
  refine {
    liveWF := by rw [hlive', hli']; exact h.liveWF
    disjoint := by rw [hlive', hdead']; exact h.disjoint
    touched_reachable := by rw [hlive', hdead']; exact h.touched_reachable
    dead_closed := by rw [hdead']; exact h.dead_closed
    explored_touched := ?_
    live_reaches_above := by rw [hlive']; exact h.live_reaches_above
    live_reaches_gray := ?_
    frames_length := by rw [hlow', Array.size_push, Array.size_pop]; simp; omega
    accs_length := by rw [hacc', Array.size_push, Array.size_pop]; simp at hsza ⊢; omega
    frame_pos := ?_, gray_chain := ?_, gray_acc := ?_, frames_mono := ?_
    lowlink_le := ?_, lowlink_reaches := ?_, lowlink_bound := ?_
    acc_sound := by
      rw [hli']
      intro k hk b hbit
      have hb1 := bumped_getElem (f := (⟨src, p, idx, a⟩ : GrayFrame State))
        (f' := (⟨src, p, idx + 1, a⟩ : GrayFrame State)) (gray := gray) rfl rfl rfl
      rcases k with _ | k
      · have hacc0' : V.accAt (ops.update aux m d).1 0
            = acc0 ||| marksToBitmask m ||| V.extraAcc := by
          simp [LowlinkView.accAt, hacc']
        rw [hacc0'] at hbit
        simp only [Nat.testBit_or, Bool.or_eq_true] at hbit
        rcases hbit with (hbit | hbit) | hbit
        · obtain ⟨u, v, pu, pv, he, hu, hv, hlo, hlow, hup, hmk⟩ :=
            h.acc_sound 0 (by simp) b (by simpa [LowlinkView.accAt, revGetD_zero hacc0] using hbit)
          obtain ⟨l, hl, hlb⟩ := hlow
          exact ⟨u, v, pu, pv, hexpmono _ _ he, hu, hv, hlo,
            ⟨l, hl, le_trans (hmono l) hlb⟩, fun j hj => absurd hj (by omega), hmk⟩
        · exact ⟨src, d, p, pd, hedgeexp, hsrcpos, hpd, le_refl _,
            ⟨0, le_refl _, by rw [hzero]; exact min_le_right _ _⟩, fun l hl => absurd hl (by omega),
            Or.inr (by rw [← hmarks]; exact (testBit_marksToBitmask m b).mp hbit)⟩
        · exact ⟨src, d, p, pd, hedgeexp, hsrcpos, hpd, le_refl _,
            ⟨0, le_refl _, by rw [hzero]; exact min_le_right _ _⟩, fun l hl => absurd hl (by omega),
            Or.inl hbit⟩
      · have hacck : V.accAt (ops.update aux m d).1 (k + 1) = V.accAt aux (k + 1) := by
          simp only [LowlinkView.accAt, hacc', revGetD_push_succ, revGetD_pop hacc0]
        rw [hacck] at hbit
        obtain ⟨u, v, pu, pv, he, hu, hv, hlo, hlow, hup, hmk⟩ :=
          h.acc_sound (k + 1) hk b hbit
        obtain ⟨l, hl, hlb⟩ := hlow
        refine ⟨u, v, pu, pv, hexpmono _ _ he, hu, hv, ?_,
          ⟨l, hl, le_trans (hmono l) hlb⟩, ?_, hmk⟩
        · rw [(hb1 (k + 1) hk).2.1]; exact hlo
        · intro j hj
          rw [(hb1 j (by simp at hk ⊢; omega)).2.1]
          exact hup j hj
    acc_complete := by
      rw [hli']
      intro u v pu pv he hu hv b hb
      have hb1 := bumped_getElem (f := (⟨src, p, idx, a⟩ : GrayFrame State))
        (f' := (⟨src, p, idx + 1, a⟩ : GrayFrame State)) (gray := gray) rfl rfl rfl
      have hacc0' : V.accAt (ops.update aux m d).1 0 = acc0 ||| marksToBitmask m ||| V.extraAcc := by
        simp [LowlinkView.accAt, hacc']
      by_cases hsd : u = src ∧ v = d
      -- the edge UPDATE just took, carried by the innermost frame, which owns its source
      · obtain ⟨hus, hvd⟩ := hsd
        rw [hus] at hu
        rw [hus, hvd] at hb
        have hpu : pu = p := by rw [hsrcpos] at hu; exact (Option.some.inj hu).symm
        refine ⟨0, by simp, by simp [hpu], fun l' hl' => absurd hl' (by omega), Or.inl ?_⟩
        rw [hacc0']
        simp only [Nat.testBit_or, Bool.or_eq_true]
        rcases hb with hb | hb
        · exact Or.inr hb
        · exact Or.inl (Or.inr (by rw [hmarks]; exact (testBit_marksToBitmask _ b).mpr hb))
      · rcases hexp u v he with he' | hsd'
        · obtain ⟨l, hl, hlo, hup, hacc⟩ := h.acc_complete u v pu pv he' hu hv b hb
          refine ⟨l, by simpa using hl, by rw [(hb1 l hl).2.1]; exact hlo, fun l' hl' => ?_, ?_⟩
          · rw [(hb1 l' (by omega)).2.1]; exact hup l' hl'
          · rcases hacc with hacc | ⟨j, hj, hu', hv'⟩
            · refine Or.inl ?_
              rcases l with _ | l
              · rw [hacc0']
                rw [show V.accAt aux 0 = acc0 from revGetD_zero hacc0] at hacc
                simp [Nat.testBit_or, hacc]
              · have hacck : V.accAt (ops.update aux m d).1 (l + 1) = V.accAt aux (l + 1) := by
                  simp only [LowlinkView.accAt, hacc', revGetD_push_succ, revGetD_pop hacc0]
                rw [hacck]; exact hacc
            · exact Or.inr ⟨j, hj, by rw [(hb1 l hl).1]; exact hu', by rw [(hb1 j (by omega)).1]; exact hv'⟩
        · exact absurd hsd' hsd
  }
  · rw [hlive', hdead']
    intro s hs t ht
    rcases hexp s t ht with ht' | ⟨-, rfl⟩
    · exact h.explored_touched s hs t ht'
    · exact Or.inl hdmem
  · rw [hlive']
    intro i hi
    obtain ⟨g, hg, hgle, hgr⟩ := h.live_reaches_gray i hi
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact ⟨⟨src, p, idx + 1, a⟩, List.mem_cons_self .., hgle, hgr⟩
    · exact ⟨g, List.mem_cons_of_mem _ hg', hgle, hgr⟩
  · rw [hlive']
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact h.frame_pos ⟨src, p, idx, a⟩ (List.mem_cons_self ..)
    · exact h.frame_pos g (List.mem_cons_of_mem _ hg')
  · intro k hk
    rcases k with _ | k
    · simpa using hexpmono _ _ (by simpa using h.gray_chain 0 hk)
    · simpa using hexpmono _ _ (by simpa using h.gray_chain (k + 1) hk)
  · intro k hk
    have hb0 := bumped_getElem (f := (⟨src, p, idx, a⟩ : GrayFrame State))
      (f' := (⟨src, p, idx + 1, a⟩ : GrayFrame State)) (gray := gray) rfl rfl rfl
    rw [(hb0 k (by simp at hk ⊢; omega)).2.2, (hb0 k (by simp at hk ⊢; omega)).1,
      (hb0 (k + 1) (by simp at hk ⊢; omega)).1]
    exact h.gray_acc k (by simp at hk ⊢; omega)
  · intro k l hk hl hkl
    rcases k with _ | k <;> rcases l with _ | l <;> simpa using h.frames_mono _ _ hk hl hkl
  · intro k hk
    have hb := le_trans (hmono k) (h.lowlink_le k hk)
    rcases k with _ | k <;> simpa using hb
  · rw [hlive']
    intro k hk
    refine ⟨lt_of_le_of_lt (hmono k) (h.lowlink_reaches k hk).1, ?_⟩
    rcases k with _ | k
    · have h0 : V.lowlinkAt aux 0 = ll := revGetD_zero hll
      rcases Nat.le_total ll pd with hle | hle
      · rw [hzero, min_eq_left hle]
        have hr := (h.lowlink_reaches 0 hk).2
        rw [h0] at hr
        simpa using hr
      · rw [hzero, min_eq_right hle]
        exact Or.inr (by simp only [List.getElem_cons_zero]; rw [hpdval]; exact PathTo.direct hmem)
    · have hkk : V.lowlinkAt (ops.update aux m d).1 (k + 1) = V.lowlinkAt aux (k + 1) := by
        simp only [LowlinkView.lowlinkAt, hlow', revGetD_push_succ, revGetD_pop hll]
      rw [hkk]
      simpa using (h.lowlink_reaches (k + 1) hk).2
  · rw [hlive', hli']
    intro k hk i hi hle t ht pt hpt
    have hle' : (⟨src, p, idx, a⟩ :: gray)[k].pos ≤ i := by rcases k with _ | k <;> simpa using hle
    rcases hexp _ t ht with ht' | ⟨-, rfl⟩
    · obtain ⟨l, hlk, hlb⟩ := h.lowlink_bound k hk i hi hle' t ht' pt hpt
      exact ⟨l, hlk, le_trans (hmono l) hlb⟩
    · refine ⟨0, Nat.zero_le _, ?_⟩
      have hpteq : pt = pd := by rw [hpd] at hpt; exact (Option.some.inj hpt).symm
      rw [hzero, hpteq]
      exact min_le_right _ _

/-- PUSH opens a frame on a fresh state, the tree edge from the innermost frame carrying the reachability
clauses onto it. -/
theorem SearchWF.push_step [Inhabited State] {ops : DFSOps.{u,v,w} State} {V : LowlinkView ops}
    (hlaw : LowlinkLawful ops V) {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    {aux : ops.Aux} {m : Std.HashSet Nat}
    {d src : State} {p idx a : Nat} {gray : List (GrayFrame State)}
    (hd : ops.getStatus aux d = .unknown) (hedge : (succs src)[idx]? = some d)
    (hmarks : m = edgeMarks src d) (hdreach : Reachable initialStates succs d)
    (h : SearchWF ops V succs edgeMarks initialStates aux (⟨src, p, idx, a⟩ :: gray)) :
    SearchWF ops V succs edgeMarks initialStates (ops.push aux d m).1
      (⟨d, V.posNat (ops.push aux d m).2, 0, marksToBitmask m⟩ :: ⟨src, p, idx + 1, a⟩ :: gray) := by
  have hmem : d ∈ succs src := by
    obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hedge
    exact heq ▸ Array.getElem_mem hlt
  -- PUSH runs on an untouched state, so `d` is neither live nor dead
  have hstat : liveStatusOf (V.liveIndex aux) (V.dead aux) d = .unknown := by
    rw [← hlaw.status aux d]; exact hd
  have hli : (V.liveIndex aux).contains d = false := by
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    rw [liveStatusOf, if_pos hc] at hstat
    exact absurd hstat (by simp)
  have hnd : d ∉ V.dead aux := by
    intro hdd
    rw [liveStatusOf, if_neg (by simp [hli]), if_pos (Std.HashSet.mem_iff_contains.mp hdd)] at hstat
    exact absurd hstat (by simp)
  have hnl : ∀ i, (hi : i < (V.live aux).size) → (V.live aux)[i] ≠ d := by
    intro i hi heq
    have hf := h.liveWF.fwd i hi
    rw [heq] at hf
    rw [Std.HashMap.contains_eq_isSome_getElem?, hf] at hli
    simp at hli
  have hdmem : d ∉ V.live aux := by
    intro hdl
    obtain ⟨i, hi, hieq⟩ := Array.getElem_of_mem hdl
    exact hnl i hi hieq
  have hlive' : V.live (ops.push aux d m).1 = (V.live aux).push d := hlaw.push_live aux d m
  have hliveIdx' : V.liveIndex (ops.push aux d m).1 = (V.liveIndex aux).insert d (V.live aux).size :=
    hlaw.push_liveIndex aux d m
  have hdead' : V.dead (ops.push aux d m).1 = V.dead aux := hlaw.push_dead aux d m
  have hlow' : V.lowlinks (ops.push aux d m).1 = (V.lowlinks aux).push (V.live aux).size :=
    hlaw.push_lowlinks aux d m
  have hpos : V.posNat (ops.push aux d m).2 = (V.live aux).size := hlaw.push_pos aux d m
  have hll0 : V.lowlinkAt (ops.push aux d m).1 0 = (V.live aux).size := by
    simp [LowlinkView.lowlinkAt, hlow']
  have hllS : ∀ k, V.lowlinkAt (ops.push aux d m).1 (k + 1) = V.lowlinkAt aux k := by
    intro k; simp [LowlinkView.lowlinkAt, hlow']
  have hget : ∀ i, (hi : i < (V.live aux).size) → ((V.live aux).push d)[i]'(by simp; omega) = (V.live aux)[i] := by
    intro i hi; simp [Array.getElem_push, hi]
  have hget! : ∀ i, i < (V.live aux).size → ((V.live aux).push d)[i]! = (V.live aux)[i]! := by
    intro i hi
    rw [getElem!_pos _ i (by simp; omega), getElem!_pos _ i hi]
    simp [Array.getElem_push, hi]
  have hbump := bumped_getElem (f := (⟨src, p, idx, a⟩ : GrayFrame State))
    (f' := (⟨src, p, idx + 1, a⟩ : GrayFrame State)) (gray := gray) rfl rfl rfl
  have hinj : ∀ x y, (hx : x < (V.live aux).size) → (hy : y < (V.live aux).size) →
      (V.live aux)[x] = (V.live aux)[y] → x = y := by
    intro x y hx hy hxy
    have h1 := h.liveWF.fwd x hx
    have h2 := h.liveWF.fwd y hy
    rw [hxy, h2] at h1
    exact (Option.some.inj h1).symm
  -- no other open frame sits on `src`, since frames sit on distinct live positions
  have hgraysrc : ∀ g ∈ gray, g.state ≠ src := by
    intro g hg heq
    obtain ⟨hg1, hg2⟩ := h.frame_pos g (List.mem_cons_of_mem _ hg)
    have hp1 : p < (V.live aux).size :=
      (h.frame_pos (⟨src, p, idx, a⟩ : GrayFrame State) (List.mem_cons_self ..)).1
    have hp2 : (V.live aux)[p]! = src :=
      (h.frame_pos (⟨src, p, idx, a⟩ : GrayFrame State) (List.mem_cons_self ..)).2
    have hgv : (V.live aux)[g.pos]'hg1 = g.state := by
      rw [← hg2]; exact (getElem!_pos (V.live aux) g.pos hg1).symm
    have hpv : (V.live aux)[p]'hp1 = src := by
      rw [← hp2]; exact (getElem!_pos (V.live aux) p hp1).symm
    have : g.pos = p := hinj g.pos p hg1 hp1 (by rw [hgv, hpv, heq])
    obtain ⟨k, hk, hkg⟩ := List.getElem_of_mem hg
    have hm := h.frames_mono 0 (k + 1) (by simp) (by simp; omega) (by omega)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, hkg] at hm
    omega
  have hsrclive : src ∈ V.live aux := by
    have hp1 : p < (V.live aux).size :=
      (h.frame_pos (⟨src, p, idx, a⟩ : GrayFrame State) (List.mem_cons_self ..)).1
    have hp2 : (V.live aux)[p]! = src :=
      (h.frame_pos (⟨src, p, idx, a⟩ : GrayFrame State) (List.mem_cons_self ..)).2
    rw [← hp2, getElem!_pos (V.live aux) p hp1]
    exact Array.getElem_mem hp1
  have hdsrc : d ≠ src := fun hc => hdmem (hc ▸ hsrclive)
  have hexppush : ∀ s t, s ≠ d → ExploredEdge (⟨src, p, idx, a⟩ :: gray) succs s t →
      ExploredEdge (⟨d, V.posNat (ops.push aux d m).2, 0, marksToBitmask m⟩ ::
        ⟨src, p, idx + 1, a⟩ :: gray) succs s t := by
    rintro s t hsd ⟨j, hj, hg⟩
    refine ⟨j, hj, fun g hgm hgs => ?_⟩
    rcases List.mem_cons.mp hgm with rfl | hgm'
    · exact absurd hgs.symm hsd
    · rcases List.mem_cons.mp hgm' with rfl | hgm''
      · have hb := hg _ (List.mem_cons_self ..) hgs
        simp only at hb ⊢
        omega
      · exact hg g (List.mem_cons_of_mem _ hgm'') hgs
  -- the tree edge, along which every live state reaches the state PUSH opens
  have hreach_d : ∀ i, (hi : i < (V.live aux).size) →
      (V.live aux)[i] = d ∨ Reaches succs (V.live aux)[i] d := by
    intro i hi
    obtain ⟨g, hg, -, hgr⟩ := h.live_reaches_gray i hi
    have hgd : Reaches succs g.state d := by
      rcases gray_reaches_head (fun k hk => (h.gray_chain k hk).mem) g hg with heq | hr
      · rw [heq]; exact PathTo.direct hmem
      · exact PathTo.trans hr (PathTo.direct hmem)
    rcases hgr with heq | hr
    · exact Or.inr (by rw [heq]; exact hgd)
    · exact Or.inr (PathTo.trans hr hgd)
  -- PUSH takes the tree edge and opens a frame that has scanned nothing
  have hexp : ∀ s t, ExploredEdge (⟨d, V.posNat (ops.push aux d m).2, 0, marksToBitmask m⟩ ::
        ⟨src, p, idx + 1, a⟩ :: gray) succs s t →
      ExploredEdge (⟨src, p, idx, a⟩ :: gray) succs s t ∨ (s = src ∧ t = d) := by
    rintro s t ⟨j, hj, hg⟩
    by_cases hs : s = src
    · subst hs
      have hjb : j < idx + 1 := hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) rfl
      rcases Nat.lt_or_ge j idx with hlt | hge
      · refine Or.inl ⟨j, hj, fun g hgm hgs => ?_⟩
        rcases List.mem_cons.mp hgm with rfl | hgm'
        · exact hlt
        · exact hg g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hgm')) hgs
      · have hje : j = idx := by omega
        subst hje
        rw [hedge] at hj
        exact Or.inr ⟨rfl, (Option.some.inj hj).symm⟩
    · refine Or.inl ⟨j, hj, fun g hgm hgs => ?_⟩
      rcases List.mem_cons.mp hgm with rfl | hgm'
      · exact absurd hgs.symm hs
      · exact hg g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hgm')) hgs
  have hexpd : ∀ t, ¬ ExploredEdge (⟨d, V.posNat (ops.push aux d m).2, 0, marksToBitmask m⟩ ::
      ⟨src, p, idx + 1, a⟩ :: gray) succs d t := by
    rintro t ⟨j, -, hg⟩
    exact absurd (hg _ (List.mem_cons_self ..) rfl) (by simp)
  refine {
    liveWF := by rw [hlive', hliveIdx']; exact h.liveWF.push hli
    disjoint := ?_, touched_reachable := ?_
    dead_closed := by rw [hdead']; exact h.dead_closed
    explored_touched := ?_, live_reaches_above := ?_, live_reaches_gray := ?_
    frames_length := by rw [hlow', Array.size_push, h.frames_length]; simp
    accs_length := by rw [hlaw.push_accs aux d m, Array.size_push, h.accs_length]; simp
    frame_pos := ?_, gray_chain := ?_, gray_acc := ?_, frames_mono := ?_
    lowlink_le := ?_, lowlink_reaches := ?_, lowlink_bound := ?_
    acc_sound := by
      rw [hliveIdx']
      intro k hk b hbit
      rcases k with _ | k
      · exfalso
        have hz : V.accAt (ops.push aux d m).1 0 = 0 := by
          simp [LowlinkView.accAt, hlaw.push_accs aux d m]
        rw [hz] at hbit
        simp at hbit
      · have hacck : V.accAt (ops.push aux d m).1 (k + 1) = V.accAt aux k := by
          simp [LowlinkView.accAt, hlaw.push_accs aux d m]
        rw [hacck] at hbit
        obtain ⟨u, v, pu, pv, he, hu, hv, hlo, hlow, hup, hmk⟩ :=
          h.acc_sound k (by simp at hk ⊢; omega) b hbit
        obtain ⟨hult, huval⟩ := h.liveWF.bwd u pu hu
        obtain ⟨hvlt, hvval⟩ := h.liveWF.bwd v pv hv
        have hune : u ≠ d := by
          intro hc
          exact hnl pu hult (by rw [← getElem!_pos (V.live aux) pu hult, huval]; exact hc)
        have hvne : v ≠ d := by
          intro hc
          exact hnl pv hvlt (by rw [← getElem!_pos (V.live aux) pv hvlt, hvval]; exact hc)
        obtain ⟨l, hl, hlb⟩ := hlow
        refine ⟨u, v, pu, pv, hexppush _ _ hune he, ?_, ?_, ?_,
          ⟨l + 1, by omega, by rw [hllS l]; exact hlb⟩, ?_, hmk⟩
        · rwa [Std.HashMap.getElem?_insert, if_neg (by simpa using Ne.symm hune)]
        · rwa [Std.HashMap.getElem?_insert, if_neg (by simpa using Ne.symm hvne)]
        · simp only [List.getElem_cons_succ]
          rw [(hbump k (by simp at hk ⊢; omega)).2.1]
          exact hlo
        · intro j hj
          rcases j with _ | j
          · simp only [List.getElem_cons_zero, hpos]
            exact ⟨hult, hvlt⟩
          · simp only [List.getElem_cons_succ]
            rw [(hbump j (by simp at hk hj ⊢; omega)).2.1]
            exact hup j (by omega)
    acc_complete := by
      rw [hliveIdx']
      intro u v pu pv he hu hv b hb
      by_cases hud : u = d
      · subst hud; exact absurd he (hexpd v)
      have hu' : (V.liveIndex aux)[u]? = some pu := by
        rwa [Std.HashMap.getElem?_insert, if_neg (by simpa using Ne.symm hud)] at hu
      obtain ⟨hpult, hpuval⟩ := h.liveWF.bwd u pu hu'
      rcases hexp u v he with he' | ⟨hus, hvd⟩
      · -- an edge taken earlier, whose owner moves up one frame
        have hvd : v ≠ d := by
          rintro rfl
          have hul : u ∈ V.live aux := by
            rw [← hpuval, getElem!_pos (V.live aux) pu hpult]; exact Array.getElem_mem hpult
          rcases h.explored_touched u hul _ he' with hl | hdd
          · exact hdmem hl
          · exact hnd hdd
        have hv' : (V.liveIndex aux)[v]? = some pv := by
          rwa [Std.HashMap.getElem?_insert, if_neg (by simpa using Ne.symm hvd)] at hv
        obtain ⟨l, hl, hlo, hup, hacc⟩ := h.acc_complete u v pu pv he' hu' hv' b hb
        refine ⟨l + 1, by simp at hl ⊢; omega, ?_, fun l' hl' => ?_, ?_⟩
        · simp only [List.getElem_cons_succ]; rw [(hbump l hl).2.1]; exact hlo
        · rcases l' with _ | l'
          · simp only [List.getElem_cons_zero, hpos]; exact hpult
          · simp only [List.getElem_cons_succ]
            rw [(hbump l' (by simp at hl ⊢; omega)).2.1]
            exact hup l' (by omega)
        · rcases hacc with hacc | ⟨j, hj, hu'', hv''⟩
          · refine Or.inl ?_
            have hacck : V.accAt (ops.push aux d m).1 (l + 1) = V.accAt aux l := by
              simp [LowlinkView.accAt, hlaw.push_accs aux d m]
            rw [hacck]; exact hacc
          · refine Or.inr ⟨j + 1, by omega, ?_, ?_⟩
            · simp only [List.getElem_cons_succ]; rw [(hbump l hl).1]; exact hu''
            · simp only [List.getElem_cons_succ]; rw [(hbump j (by simp at hl ⊢; omega)).1]; exact hv''
      · -- the tree edge PUSH just took, owned by the frame it was taken from
        have hp1 : p < (V.live aux).size :=
          (h.frame_pos (⟨src, p, idx, a⟩ : GrayFrame State) (List.mem_cons_self ..)).1
        have hp2 : (V.live aux)[p]! = src :=
          (h.frame_pos (⟨src, p, idx, a⟩ : GrayFrame State) (List.mem_cons_self ..)).2
        have hf := h.liveWF.fwd p hp1
        rw [← getElem!_pos (V.live aux) p hp1, hp2, ← hus, hu'] at hf
        have hpu : pu = p := Option.some.inj hf
        refine ⟨1, by simp, ?_, fun l' hl' => ?_, Or.inr ⟨0, rfl, by simp [hus], by simp [hvd]⟩⟩
        · simp only [List.getElem_cons_succ, List.getElem_cons_zero]; omega
        · obtain rfl : l' = 0 := by omega
          simp only [List.getElem_cons_zero, hpos]; exact hpult
  }
  · rw [hlive', hdead']
    intro s hs
    rcases Array.mem_push.mp hs with hs' | rfl
    · exact h.disjoint s hs'
    · exact hnd
  · rw [hlive', hdead']
    intro s hs
    rcases hs with hs | hs
    · rcases Array.mem_push.mp hs with hs' | rfl
      · exact h.touched_reachable s (Or.inl hs')
      · exact hdreach
    · exact h.touched_reachable s (Or.inr hs)
  · rw [hlive', hdead']
    intro s hs t ht
    by_cases hsd : s = d
    · exact absurd (hsd ▸ ht) (hexpd t)
    · have hs' : s ∈ V.live aux := by
        rcases Array.mem_push.mp hs with hs'' | rfl
        · exact hs''
        · exact absurd rfl hsd
      rcases hexp s t ht with ht' | ⟨-, rfl⟩
      · rcases h.explored_touched s hs' t ht' with hl | hdd
        · exact Or.inl (Array.mem_push.mpr (Or.inl hl))
        · exact Or.inr hdd
      · exact Or.inl (Array.mem_push.mpr (Or.inr rfl))
  · rw [hlive']
    intro i j hi hj hij
    simp only [Array.size_push] at hi hj
    by_cases hjn : j = (V.live aux).size
    · subst hjn
      by_cases hin : i = (V.live aux).size
      · subst hin; exact Or.inl rfl
      · have hi' : i < (V.live aux).size := by omega
        rw [hget i hi', show ((V.live aux).push d)[(V.live aux).size] = d by simp]
        exact hreach_d i hi'
    · have hj' : j < (V.live aux).size := by omega
      have hi' : i < (V.live aux).size := by omega
      rw [hget i hi', hget j hj']
      exact h.live_reaches_above i j hi' hj' hij
  · rw [hlive']
    intro i hi
    simp only [Array.size_push] at hi
    by_cases hin : i = (V.live aux).size
    · subst hin
      exact ⟨⟨d, V.posNat (ops.push aux d m).2, 0, marksToBitmask m⟩, List.mem_cons_self .., by simp [hpos],
        Or.inl (by simp)⟩
    · have hi' : i < (V.live aux).size := by omega
      obtain ⟨g, hg, hgle, hgr⟩ := h.live_reaches_gray i hi'
      rw [hget i hi']
      rcases List.mem_cons.mp hg with rfl | hg'
      · exact ⟨⟨src, p, idx + 1, a⟩, List.mem_cons_of_mem _ (List.mem_cons_self ..), hgle, hgr⟩
      · exact ⟨g, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg'), hgle, hgr⟩
  · rw [hlive']
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact ⟨by simp [hpos], by simp [hpos]⟩
    · obtain ⟨h1, h2⟩ : g.pos < (V.live aux).size ∧ (V.live aux)[g.pos]! = g.state := by
        rcases List.mem_cons.mp hg' with rfl | hg3
        · exact h.frame_pos ⟨src, p, idx, a⟩ (List.mem_cons_self ..)
        · exact h.frame_pos g (List.mem_cons_of_mem _ hg3)
      exact ⟨by simp; omega, by rw [hget! g.pos h1]; exact h2⟩
  · intro k hk
    rcases k with _ | k
    · refine ⟨idx, hedge, fun g hgm hgs => ?_⟩
      rcases List.mem_cons.mp hgm with rfl | hgm'
      · exact absurd hgs hdsrc
      · rcases List.mem_cons.mp hgm' with rfl | hgm''
        · simp
        · exact absurd hgs (hgraysrc g hgm'')
    · have hkold : k + 1 < ((⟨src, p, idx, a⟩ : GrayFrame State) :: gray).length := by
        simp at hk ⊢; omega
      have hkold0 : k < ((⟨src, p, idx, a⟩ : GrayFrame State) :: gray).length := by omega
      set g' := ((⟨src, p, idx, a⟩ : GrayFrame State) :: gray)[k + 1]'hkold with hg'def
      have hst : g'.state ≠ d := by
        intro hc
        obtain ⟨hg1, hg2⟩ := h.frame_pos g' (List.getElem_mem hkold)
        exact hnl g'.pos hg1 (by rw [← hc, ← hg2]; exact (getElem!_pos (V.live aux) g'.pos hg1).symm)
      have hc := hexppush _ _ hst (h.gray_chain k hkold)
      simp only [List.getElem_cons_succ]
      rw [(hbump k hkold0).1]
      simpa using hc
  · intro k hk
    rcases k with _ | k
    · simp [hmarks]
    · simp only [List.getElem_cons_succ]
      rw [(hbump k (by simp at hk ⊢; omega)).2.2, (hbump k (by simp at hk ⊢; omega)).1]
      simpa using h.gray_acc k (by simp at hk ⊢; omega)
  · intro k l hk hl hkl
    rcases k with _ | k
    · rcases l with _ | l
      · omega
      · simp only [List.getElem_cons_zero, List.getElem_cons_succ, hpos]
        rw [(hbump l (by simpa using hl)).2.1]
        exact (h.frame_pos _ (List.getElem_mem _)).1
    · rcases l with _ | l
      · omega
      · simp only [List.getElem_cons_succ]
        rw [(hbump l (by simpa using hl)).2.1, (hbump k (by simpa using hk)).2.1]
        exact h.frames_mono k l (by simpa using hk) (by simpa using hl) (by omega)
  · intro k hk
    rcases k with _ | k
    · simp [hll0, hpos]
    · rw [hllS k]
      simp only [List.getElem_cons_succ]
      rw [(hbump k (by simpa using hk)).2.1]
      exact h.lowlink_le k (by simpa using hk)
  · rw [hlive']
    intro k hk
    rcases k with _ | k
    · exact ⟨by simp [hll0], Or.inl (by simp [hll0, hpos])⟩
    · obtain ⟨h1, h2⟩ := h.lowlink_reaches k (by simpa using hk)
      rw [hllS k]
      refine ⟨by simp; omega, ?_⟩
      simp only [List.getElem_cons_succ]
      rw [(hbump k (by simpa using hk)).1, (hbump k (by simpa using hk)).2.1, hget! _ h1]
      exact h2
  · rw [hlive', hliveIdx']
    intro k hk i hi hle t ht pt hpt
    simp only [Array.size_push] at hi
    by_cases hin : i = (V.live aux).size
    · subst hin
      exact absurd (by simpa using ht) (hexpd t)
    have hi' : i < (V.live aux).size := by omega
    rw [hget i hi'] at ht
    rcases hexp _ t ht with ht' | ⟨-, rfl⟩
    · have htne : t ≠ d := by
        rintro rfl
        rcases h.explored_touched _ (Array.getElem_mem hi') t ht' with hl | hdd
        · exact hdmem hl
        · exact hnd hdd
      have hpt' : (V.liveIndex aux)[t]? = some pt := by
        rwa [Std.HashMap.getElem?_insert, if_neg (by simpa using Ne.symm htne)] at hpt
      rcases k with _ | k
      · exfalso
        simp only [List.getElem_cons_zero, hpos] at hle
        omega
      · simp only [List.getElem_cons_succ] at hle
        rw [(hbump k (by simpa using hk)).2.1] at hle
        obtain ⟨l, hlk, hlb⟩ := h.lowlink_bound k (by simpa using hk) i hi' hle t ht' pt hpt'
        exact ⟨l + 1, by omega, by rw [hllS l]; exact hlb⟩
    · refine ⟨0, Nat.zero_le _, ?_⟩
      rw [hll0]
      have hpteq : pt = (V.live aux).size := by
        rw [Std.HashMap.getElem?_insert, if_pos (by simp)] at hpt
        exact (Option.some.inj hpt).symm
      omega

omit [LawfulBEq State] [LawfulHashable State] in
private theorem SearchWF.pos_lt_head [Inhabited State] {ops : DFSOps.{u,v,w} State} {V : LowlinkView ops}
    {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    {aux : ops.Aux} {f : GrayFrame State} {gray : List (GrayFrame State)}
    (h : SearchWF ops V succs edgeMarks initialStates aux (f :: gray)) : ∀ g ∈ gray, g.pos < f.pos := by
  intro g hg
  obtain ⟨k, hk, hkg⟩ := List.getElem_of_mem hg
  have hm := h.frames_mono 0 (k + 1) (by simp) (by simp; omega) (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, hkg] at hm
  exact hm

omit [LawfulBEq State] [LawfulHashable State] in
/-- At a closing POP every edge out of the flushed range has been explored, the closing frame by its own cursor and
everything above it by having been popped already. -/
theorem SearchWF.close_explored [Inhabited State] {ops : DFSOps.{u,v,w} State} {V : LowlinkView ops}
    {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    {aux : ops.Aux} {step : DFSStep State ops.Position} {gray : List (GrayFrame State)}
    (hsucc : step.succ = succs step.state) (hidx : ¬ step.idx < step.succ.size)
    (h : SearchWF ops V succs edgeMarks initialStates aux
      (⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: gray)) :
    ∀ i, (hi : i < (V.live aux).size) → V.posNat step.pos ≤ i → ∀ t ∈ succs (V.live aux)[i],
      ExploredEdge (⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: gray) succs (V.live aux)[i] t := by
  have hposlt : V.posNat step.pos < (V.live aux).size :=
    (h.frame_pos ⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ (List.mem_cons_self ..)).1
  have hposval : (V.live aux)[V.posNat step.pos]! = step.state :=
    (h.frame_pos ⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ (List.mem_cons_self ..)).2
  have hstepmem : (V.live aux)[V.posNat step.pos]'hposlt = step.state := by
    rw [← hposval]; exact (getElem!_pos (V.live aux) (V.posNat step.pos) hposlt).symm
  have hgraylt : ∀ g ∈ gray, g.pos < V.posNat step.pos := h.pos_lt_head
  intro i hi hpi t ht
  obtain ⟨j, hj, hjv⟩ := Array.getElem_of_mem ht
  refine ⟨j, by rw [Array.getElem?_eq_some_iff]; exact ⟨hj, hjv⟩, fun g hgm hgs => ?_⟩
  rcases List.mem_cons.mp hgm with rfl | hgm'
  · simp only at hgs
    have hieq : i = V.posNat step.pos := h.liveWF.inj hi hposlt (by rw [hstepmem, hgs])
    subst hieq
    rw [hstepmem, ← hsucc] at hj
    show j < step.idx
    omega
  · exfalso
    obtain ⟨hg1, hg2⟩ := h.frame_pos g (List.mem_cons_of_mem _ hgm')
    have hgval : (V.live aux)[g.pos]'hg1 = g.state := by
      rw [← hg2]; exact (getElem!_pos (V.live aux) g.pos hg1).symm
    have heq : g.pos = i := h.liveWF.inj hg1 hi (hgval.trans hgs)
    have := hgraylt g hgm'
    omega

/-- At a closing POP the flushed set is internally connected and every edge out of it stays inside it or lands in
`dead`. -/
theorem SearchWF.close_flushed [Inhabited State] {ops : DFSOps.{u,v,w} State} {V : LowlinkView ops}
    {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    {aux : ops.Aux} {step : DFSStep State ops.Position} {gray : List (GrayFrame State)}
    (hsucc : step.succ = succs step.state) (hidx : ¬ step.idx < step.succ.size)
    (hclose : V.closes aux step = true)
    (h : SearchWF ops V succs edgeMarks initialStates aux
      (⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: gray)) :
    (∀ x ∈ flushedSet (V.live aux) (V.posNat step.pos), ∀ y ∈ succs x,
      y ∈ flushedSet (V.live aux) (V.posNat step.pos) ∨ y ∈ V.dead aux) ∧
    InternallyConnected succs (flushedSet (V.live aux) (V.posNat step.pos)) := by
  have hclose' : (V.lowlinks aux).back? = some (V.posNat step.pos) := by
    rw [LowlinkView.closes] at hclose
    exact beq_iff_eq.mp hclose
  have hll0 : V.lowlinkAt aux 0 = V.posNat step.pos := revGetD_zero hclose'
  have hposlt : V.posNat step.pos < (V.live aux).size :=
    (h.frame_pos ⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ (List.mem_cons_self ..)).1
  have hposval : (V.live aux)[V.posNat step.pos]! = step.state :=
    (h.frame_pos ⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ (List.mem_cons_self ..)).2
  have hstepmem : (V.live aux)[V.posNat step.pos]'hposlt = step.state := by
    rw [← hposval]; exact (getElem!_pos (V.live aux) (V.posNat step.pos) hposlt).symm
  have hinj : ∀ a b, (ha : a < (V.live aux).size) → (hb : b < (V.live aux).size) →
      (V.live aux)[a] = (V.live aux)[b] → a = b := fun _ _ ha hb hab => h.liveWF.inj ha hb hab
  have hgraylt : ∀ g ∈ gray, g.pos < V.posNat step.pos := h.pos_lt_head
  have hfull := h.close_explored hsucc hidx
  -- [CCLMT18] the closing test, read through `lowlink_bound`: nothing above the frame reaches below it
  have hbound : ∀ i, (hi : i < (V.live aux).size) → V.posNat step.pos ≤ i → ∀ t ∈ succs (V.live aux)[i],
      t ∈ V.dead aux ∨ ∃ pt, (V.liveIndex aux)[t]? = some pt ∧ V.posNat step.pos ≤ pt := by
    intro i hi hpi t ht
    have hexpl := hfull i hi hpi t ht
    rcases h.explored_touched _ (Array.getElem_mem hi) t hexpl with hlv | hdd
    · obtain ⟨jt, hjt, hjtv⟩ := Array.getElem_of_mem hlv
      have hpt : (V.liveIndex aux)[t]? = some jt := by rw [← hjtv]; exact h.liveWF.fwd jt hjt
      obtain ⟨l, hl0, hlb⟩ := h.lowlink_bound 0 (by simp) i hi (by simpa using hpi) t hexpl jt hpt
      have hl : l = 0 := by omega
      subst hl
      rw [hll0] at hlb
      exact Or.inr ⟨jt, hpt, hlb⟩
    · exact Or.inl hdd
  have hmemF : ∀ s, s ∈ flushedSet (V.live aux) (V.posNat step.pos) ↔
      ∃ i, ∃ _ : i < (V.live aux).size, V.posNat step.pos ≤ i ∧ (V.live aux)[i] = s :=
    fun s => mem_flushedSet _ _ s
  have hFout : ∀ x ∈ flushedSet (V.live aux) (V.posNat step.pos), ∀ y ∈ succs x,
      y ∈ flushedSet (V.live aux) (V.posNat step.pos) ∨ y ∈ V.dead aux := by
    intro x hx y hy
    obtain ⟨i, hi, hpi, rfl⟩ := (hmemF x).mp hx
    rcases hbound i hi hpi y hy with hdd | ⟨pt, hpt, hptge⟩
    · exact Or.inr hdd
    · obtain ⟨hltp, hval⟩ := h.liveWF.bwd y pt hpt
      rw [getElem!_pos (V.live aux) pt hltp] at hval
      exact Or.inl ((hmemF y).mpr ⟨pt, hltp, hptge, hval⟩)
  have hFdisj : ∀ x ∈ flushedSet (V.live aux) (V.posNat step.pos), x ∉ V.dead aux := by
    intro x hx
    obtain ⟨i, hi, -, rfl⟩ := (hmemF x).mp hx
    exact h.disjoint _ (Array.getElem_mem hi)
  have hDclosed : ∀ x ∈ V.dead aux, ∀ y ∈ succs x, y ∈ V.dead aux := h.dead_closed
  have hstay : ∀ x, x ∈ flushedSet (V.live aux) (V.posNat step.pos) ∨ x ∈ V.dead aux →
      ∀ y, Reaches succs x y →
        y ∈ flushedSet (V.live aux) (V.posNat step.pos) ∨ y ∈ V.dead aux := by
    intro x hx y hr
    exact hr.closed
      (P := fun z => z ∈ flushedSet (V.live aux) (V.posNat step.pos) ∨ z ∈ V.dead aux) hx
      (fun a ha b hb => by
      rcases ha with ha | ha
      · exact hFout a ha b hb
      · exact Or.inr (hDclosed a ha b hb))
  -- clause 6 restricted to the flushed span can only name the closing frame, a deeper one being unreachable
  have hxpos : ∀ i, (hi : i < (V.live aux).size) → V.posNat step.pos ≤ i →
      (V.live aux)[i] = step.state ∨ Reaches succs (V.live aux)[i] step.state := by
    intro i hi hpi
    obtain ⟨g, hg, hgle, hgr⟩ := h.live_reaches_gray i hi
    rcases List.mem_cons.mp hg with rfl | hg'
    · simpa using hgr
    · exfalso
      obtain ⟨hg1, hg2⟩ := h.frame_pos g (List.mem_cons_of_mem _ hg')
      have hglt := hgraylt g hg'
      have hgval : (V.live aux)[g.pos]'hg1 = g.state := by
        rw [← hg2]; exact (getElem!_pos (V.live aux) g.pos hg1).symm
      have hgnotF : g.state ∉ flushedSet (V.live aux) (V.posNat step.pos) := by
        intro hmem
        obtain ⟨j, hj, hpj, hjv⟩ := (hmemF _).mp hmem
        have : j = g.pos := hinj j g.pos hj hg1 (by rw [hjv, ← hgval])
        omega
      have hgnotD : g.state ∉ V.dead aux := by
        rw [← hgval]
        exact h.disjoint _ (Array.getElem_mem hg1)
      have hin : (V.live aux)[i] ∈ flushedSet (V.live aux) (V.posNat step.pos) :=
        (hmemF _).mpr ⟨i, hi, hpi, rfl⟩
      rcases hgr with heq | hr
      · exact hgnotF (heq ▸ hin)
      · rcases hstay _ (Or.inl hin) _ hr with hc | hc
        · exact hgnotF hc
        · exact hgnotD hc
  have hconn : InternallyConnected succs (flushedSet (V.live aux) (V.posNat step.pos)) := by
    intro s hs t ht
    obtain ⟨i, hi, hpi, rfl⟩ := (hmemF s).mp hs
    obtain ⟨j, hj, hpj, rfl⟩ := (hmemF t).mp ht
    by_cases hij : i = j
    · subst hij; exact Or.inl rfl
    refine Or.inr (pathTo_within hFout hDclosed hFdisj ?_ hs ht)
    have h2 : step.state = (V.live aux)[j] ∨ Reaches succs step.state (V.live aux)[j] := by
      rcases h.live_reaches_above (V.posNat step.pos) j hposlt hj hpj with he | hr
      · exact Or.inl (by rw [← hstepmem]; exact he)
      · exact Or.inr (by rw [← hstepmem]; exact hr)
    rcases hxpos i hi hpi with he1 | hr1
    · rcases h2 with he2 | hr2
      · exact absurd (hinj i j hi hj (he1.trans he2)) hij
      · rw [he1]; exact hr2
    · rcases h2 with he2 | hr2
      · rw [← he2]; exact hr1
      · exact PathTo.trans hr1 hr2
  exact ⟨hFout, hconn⟩

/-- At a closing POP the accumulator carries the marks of every edge inside the flushed set, and the extra mask as
soon as there is one such edge. -/
theorem SearchWF.close_acc_complete [Inhabited State] {ops : DFSOps.{u,v,w} State} {V : LowlinkView ops}
    {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    {aux : ops.Aux} {step : DFSStep State ops.Position} {gray : List (GrayFrame State)}
    (hsucc : step.succ = succs step.state) (hidx : ¬ step.idx < step.succ.size)
    (h : SearchWF ops V succs edgeMarks initialStates aux
      (⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: gray)) :
    ∀ u ∈ flushedSet (V.live aux) (V.posNat step.pos), ∀ v ∈ flushedSet (V.live aux) (V.posNat step.pos),
      v ∈ succs u → ∀ b, (V.extraAcc.testBit b = true ∨ b ∈ edgeMarks u v) →
        (V.accAt aux 0).testBit b = true := by
  intro u hu v hv huv b hb
  obtain ⟨i, hi, hpi, rfl⟩ := (mem_flushedSet _ _ u).mp hu
  obtain ⟨j, hj, -, rfl⟩ := (mem_flushedSet _ _ v).mp hv
  obtain ⟨l, hl, -, hup, hacc⟩ := h.acc_complete _ _ i j (h.close_explored hsucc hidx i hi hpi _ huv)
    (h.liveWF.fwd i hi) (h.liveWF.fwd j hj) b hb
  -- the source sits at or above the closing frame, so that frame owns it
  rcases l with _ | l
  · rcases hacc with hacc | ⟨j', hj', -⟩
    · exact hacc
    · exact absurd hj' (by omega)
  · have h0 : i < V.posNat step.pos := hup 0 (by omega)
    omega

/-- POP at a closing frame flushes the live stack above it into `dead`. -/
theorem SearchWF.popClose_step [Inhabited State] {ops : DFSOps.{u,v,w} State} {V : LowlinkView ops}
    (hlaw : LowlinkLawful ops V) {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    {aux : ops.Aux}
    {step : DFSStep State ops.Position} {gray : List (GrayFrame State)}
    (hsucc : step.succ = succs step.state) (hidx : ¬ step.idx < step.succ.size)
    (hclose : V.closes aux step = true)
    (h : SearchWF ops V succs edgeMarks initialStates aux
      (⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: gray)) :
    SearchWF ops V succs edgeMarks initialStates (ops.pop succs edgeMarks aux step).1 gray := by
  have hclose' : (V.lowlinks aux).back? = some (V.posNat step.pos) := by
    rw [LowlinkView.closes] at hclose
    exact beq_iff_eq.mp hclose
  have hll0 : V.lowlinkAt aux 0 = V.posNat step.pos := revGetD_zero hclose'
  have hposlt : V.posNat step.pos < (V.live aux).size :=
    (h.frame_pos ⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ (List.mem_cons_self ..)).1
  have hinj : ∀ a b, (ha : a < (V.live aux).size) → (hb : b < (V.live aux).size) →
      (V.live aux)[a] = (V.live aux)[b] → a = b := fun _ _ ha hb hab => h.liveWF.inj ha hb hab
  have hgraylt : ∀ g ∈ gray, g.pos < V.posNat step.pos := h.pos_lt_head
  -- the frame POP closes has scanned every successor, so dropping it adds no explored edge
  have hexp : ∀ s t, ExploredEdge gray succs s t →
      ExploredEdge (⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: gray) succs s t := by
    rintro s t ⟨j, hj, hg⟩
    refine ⟨j, hj, fun g hgm hgs => ?_⟩
    rcases List.mem_cons.mp hgm with rfl | hgm'
    · simp only at hgs
      subst hgs
      obtain ⟨hjlt, -⟩ := Array.getElem?_eq_some_iff.mp hj
      rw [← hsucc] at hjlt
      show j < step.idx
      omega
    · exact hg g hgm' hgs
  have hexpdrop : ∀ s t,
      ExploredEdge (⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: gray) succs s t →
        ExploredEdge gray succs s t := by
    rintro s t ⟨j, hj, hg⟩
    exact ⟨j, hj, fun g hgm hgs => hg g (List.mem_cons_of_mem _ hgm) hgs⟩
  obtain ⟨hFout, -⟩ := h.close_flushed hsucc hidx hclose
  -- the flush itself
  obtain ⟨htriple, hlowpop, haccpop⟩ := hlaw.pop_close succs edgeMarks aux step hclose
  have hlive' : V.live (ops.pop succs edgeMarks aux step).1
      = (liveFlush (V.live aux) (V.liveIndex aux) (V.dead aux) (V.posNat step.pos)).1 :=
    congrArg Prod.fst htriple
  have hli' : V.liveIndex (ops.pop succs edgeMarks aux step).1
      = (liveFlush (V.live aux) (V.liveIndex aux) (V.dead aux) (V.posNat step.pos)).2.1 :=
    congrArg (fun p => p.2.1) htriple
  have hdead' : V.dead (ops.pop succs edgeMarks aux step).1
      = (liveFlush (V.live aux) (V.liveIndex aux) (V.dead aux) (V.posNat step.pos)).2.2 :=
    congrArg (fun p => p.2.2) htriple
  have hsizeL : (liveFlush (V.live aux) (V.liveIndex aux) (V.dead aux) (V.posNat step.pos)).1.size
      = V.posNat step.pos :=
    liveFlush_size _ _ _ _ (le_of_lt hposlt)
  have hgetlt' : ∀ i, (hi : i < V.posNat step.pos) →
      (liveFlush (V.live aux) (V.liveIndex aux) (V.dead aux)
        (V.posNat step.pos)).1[i]'(by rw [hsizeL]; omega) = (V.live aux)[i]'(by omega) := by
    intro i hi
    rw [← getElem!_pos _ i (by rw [hsizeL]; omega), ← getElem!_pos (V.live aux) i (by omega)]
    exact liveFlush_getElem!_lt (V.posNat step.pos) _ _ _ i hi
  have hdeadmono : ∀ q ∈ V.dead aux,
      q ∈ (liveFlush (V.live aux) (V.liveIndex aux) (V.dead aux) (V.posNat step.pos)).2.2 :=
    fun q hq => liveFlush_dead_mono _ _ _ _ q hq
  have hdeadge : ∀ i, V.posNat step.pos ≤ i → i < (V.live aux).size →
      (V.live aux)[i]! ∈
        (liveFlush (V.live aux) (V.liveIndex aux) (V.dead aux) (V.posNat step.pos)).2.2 :=
    fun i h1 h2 => liveFlush_dead_of_ge _ _ _ _ i h1 h2
  have hdeador : ∀ q ∈ (liveFlush (V.live aux) (V.liveIndex aux) (V.dead aux)
        (V.posNat step.pos)).2.2,
      q ∈ V.dead aux ∨ ∃ p, V.posNat step.pos ≤ p ∧ p < (V.live aux).size ∧ (V.live aux)[p]! = q :=
    fun q hq => liveFlush_dead_or_old _ _ _ _ q hq
  have htouched : ∀ s, s ∈ V.live aux ∨ s ∈ V.dead aux →
      s ∈ (liveFlush (V.live aux) (V.liveIndex aux) (V.dead aux) (V.posNat step.pos)).1 ∨
        s ∈ (liveFlush (V.live aux) (V.liveIndex aux) (V.dead aux) (V.posNat step.pos)).2.2 :=
    fun s hs => liveFlush_touched_mono _ _ _ _ s hs
  obtain ⟨accb, haccb⟩ : ∃ x, (V.accs aux).back? = some x := by
    have hszb : (V.accs aux).size = gray.length + 1 := by rw [h.accs_length]; simp
    rcases hb : (V.accs aux).back? with _ | x
    · rw [Array.back?_eq_none_iff] at hb; simp [hb] at hszb
    · exact ⟨x, rfl⟩
  -- a live state below the closing position keeps its index through the flush
  have hsurv : ∀ (w : State) (pw : Nat), (V.liveIndex aux)[w]? = some pw → pw < V.posNat step.pos →
      (liveFlush (V.live aux) (V.liveIndex aux) (V.dead aux) (V.posNat step.pos)).2.1[w]?
        = some pw := by
    intro w pw hw hlt
    obtain ⟨hwlt, hwval⟩ := h.liveWF.bwd w pw hw
    have hlt' : pw < (liveFlush (V.live aux) (V.liveIndex aux) (V.dead aux)
        (V.posNat step.pos)).1.size := by rw [hsizeL]; exact hlt
    have hf := (LiveWF.flush (dead := V.dead aux) (V.posNat step.pos) h.liveWF).fwd pw hlt'
    rw [hgetlt' pw hlt] at hf
    rw [getElem!_pos (V.live aux) pw hwlt] at hwval
    rwa [hwval] at hf
  have hpopAt : ∀ k, V.lowlinkAt (ops.pop succs edgeMarks aux step).1 k = V.lowlinkAt aux (k + 1) := by
    intro k
    simp only [LowlinkView.lowlinkAt, hlowpop]
    exact revGetD_pop hclose' k
  refine {
    liveWF := by rw [hlive', hli']; exact LiveWF.flush (V.posNat step.pos) h.liveWF
    disjoint := ?_, touched_reachable := ?_, dead_closed := ?_, explored_touched := ?_
    live_reaches_above := ?_, live_reaches_gray := ?_
    frames_length := by rw [hlowpop, Array.size_pop, h.frames_length]; simp
    accs_length := by rw [haccpop, Array.size_pop, h.accs_length]; simp
    frame_pos := ?_, gray_chain := ?_, gray_acc := ?_, frames_mono := ?_
    lowlink_le := ?_, lowlink_reaches := ?_, lowlink_bound := ?_
    acc_sound := by
      simp only [hli']
      intro k hk b hbit
      have hacck : V.accAt (ops.pop succs edgeMarks aux step).1 k = V.accAt aux (k + 1) := by
        simp only [LowlinkView.accAt, haccpop]
        exact revGetD_pop haccb k
      rw [hacck] at hbit
      obtain ⟨u, v, pu, pv, he, hu, hv, hlo, hlow, hup, hmk⟩ :=
        h.acc_sound (k + 1) (by simpa using hk) b hbit
      obtain ⟨hpu0, hpv0⟩ := hup 0 (by omega)
      simp only [List.getElem_cons_zero] at hpu0 hpv0
      obtain ⟨l, hl, hlb⟩ := hlow
      have hlpos : 1 ≤ l := by
        rcases Nat.eq_zero_or_pos l with hl0 | hl0
        · exfalso; rw [hl0, hll0] at hlb; omega
        · exact hl0
      refine ⟨u, v, pu, pv, hexpdrop _ _ he, hsurv u pu hu hpu0, hsurv v pv hv hpv0, ?_,
        ⟨l - 1, by omega, ?_⟩, ?_, hmk⟩
      · simpa using hlo
      · rw [hpopAt (l - 1), show l - 1 + 1 = l from by omega]
        exact hlb
      · intro j hj
        simpa using hup (j + 1) (by omega)
    acc_complete := by
      simp only [hli']
      intro u v pu pv he hu hv b hb
      -- a state still live after the flush sat below the closing position, at the same index
      have hold : ∀ (w : State) (pw : Nat), (liveFlush (V.live aux) (V.liveIndex aux) (V.dead aux)
          (V.posNat step.pos)).2.1[w]? = some pw →
          (V.liveIndex aux)[w]? = some pw ∧ pw < V.posNat step.pos := by
        intro w pw hw
        obtain ⟨hlt, hval⟩ := (LiveWF.flush (dead := V.dead aux) (V.posNat step.pos) h.liveWF).bwd w pw hw
        rw [hsizeL] at hlt
        rw [liveFlush_getElem!_lt (V.posNat step.pos) _ _ _ pw hlt] at hval
        refine ⟨?_, hlt⟩
        rw [← hval, getElem!_pos (V.live aux) pw (by omega)]
        exact h.liveWF.fwd pw (by omega)
      obtain ⟨hu', hpulo⟩ := hold u pu hu
      obtain ⟨hv', hpvlo⟩ := hold v pv hv
      obtain ⟨l, hl, hlo, hup, hacc⟩ := h.acc_complete u v pu pv (hexp _ _ he) hu' hv' b hb
      rcases l with _ | l
      · exact absurd (show V.posNat step.pos ≤ pu from hlo) (by omega)
      · refine ⟨l, by simpa using hl, by simpa using hlo,
          fun l' hl' => by simpa using hup (l' + 1) (by omega), ?_⟩
        rcases hacc with hacc | ⟨j, hj, hu'', hv''⟩
        · refine Or.inl ?_
          have hacck : V.accAt (ops.pop succs edgeMarks aux step).1 l = V.accAt aux (l + 1) := by
            simp only [LowlinkView.accAt, haccpop]
            exact revGetD_pop haccb l
          rw [hacck]; exact hacc
        · rcases j with _ | j
          · -- a tree edge into the closing frame ends at a flushed state
            exfalso
            have hxpos : (V.liveIndex aux)[step.state]? = some (V.posNat step.pos) := by
              have hf := h.liveWF.fwd _ hposlt
              rwa [← getElem!_pos (V.live aux) _ hposlt,
                (h.frame_pos ⟨step.state, V.posNat step.pos, step.idx, step.acc⟩
                  (List.mem_cons_self ..)).2] at hf
            have hvx : v = step.state := hv''
            rw [hvx, hxpos] at hv'
            have := Option.some.inj hv'
            omega
          · obtain rfl : l = j + 1 := by omega
            exact Or.inr ⟨j, rfl, by simpa using hu'', by simpa using hv''⟩
  }
  · rw [hlive', hdead']
    intro s hs hsd
    obtain ⟨i, hi, hiv⟩ := Array.getElem_of_mem hs
    have hip : i < V.posNat step.pos := by rw [hsizeL] at hi; exact hi
    have hval : (V.live aux)[i]'(by omega) = s := by rw [← hiv, hgetlt' i hip]
    rcases hdeador s hsd with hdd | ⟨q, hq1, hq2, hq3⟩
    · exact h.disjoint s (by rw [← hval]; exact Array.getElem_mem _) hdd
    · rw [getElem!_pos (V.live aux) q hq2] at hq3
      have : q = i := hinj q i hq2 (by omega) (by rw [hq3, hval])
      omega
  · rw [hlive', hdead']
    intro s hs
    apply h.touched_reachable s
    rcases hs with hs | hs
    · obtain ⟨i, hi, hiv⟩ := Array.getElem_of_mem hs
      have hip : i < V.posNat step.pos := by rw [hsizeL] at hi; exact hi
      exact Or.inl (by rw [← hiv, hgetlt' i hip]; exact Array.getElem_mem _)
    · rcases hdeador s hs with hdd | ⟨q, hq1, hq2, hq3⟩
      · exact Or.inr hdd
      · refine Or.inl ?_
        rw [← hq3, getElem!_pos (V.live aux) q hq2]
        exact Array.getElem_mem hq2
  · rw [hdead']
    intro s hs t ht
    rcases hdeador s hs with hdd | ⟨q, hq1, hq2, hq3⟩
    · exact hdeadmono t (h.dead_closed s hdd t ht)
    · rw [getElem!_pos (V.live aux) q hq2] at hq3
      rcases hFout s ((mem_flushedSet _ _ s).mpr ⟨q, hq2, hq1, hq3⟩) t ht with htF | hdd
      · obtain ⟨i, hi, hpi, rfl⟩ := (mem_flushedSet _ _ t).mp htF
        rw [← getElem!_pos (V.live aux) i hi]
        exact hdeadge i hpi hi
      · exact hdeadmono t hdd
  · rw [hlive', hdead']
    intro s hs t ht
    obtain ⟨i, hi, hiv⟩ := Array.getElem_of_mem hs
    have hip : i < V.posNat step.pos := by rw [hsizeL] at hi; exact hi
    have hval : (V.live aux)[i]'(by omega) = s := by rw [← hiv, hgetlt' i hip]
    have hsl : s ∈ V.live aux := by rw [← hval]; exact Array.getElem_mem _
    rcases h.explored_touched s hsl t (hexp s t ht) with hlv | hdd
    · exact htouched t (Or.inl hlv)
    · exact Or.inr (hdeadmono t hdd)
  · rw [hlive']
    intro i j hi hj hij
    rw [hsizeL] at hi hj
    rw [hgetlt' i hi, hgetlt' j hj]
    exact h.live_reaches_above i j (by omega) (by omega) hij
  · rw [hlive']
    intro i hi
    rw [hsizeL] at hi
    obtain ⟨g, hg, hgle, hgr⟩ := h.live_reaches_gray i (by omega)
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact absurd hgle (by simp; omega)
    · exact ⟨g, hg', hgle, by rw [hgetlt' i hi]; exact hgr⟩
  · rw [hlive']
    intro g hg
    obtain ⟨hg1, hg2⟩ := h.frame_pos g (List.mem_cons_of_mem _ hg)
    have hglt := hgraylt g hg
    refine ⟨by rw [hsizeL]; exact hglt, ?_⟩
    rw [liveFlush_getElem!_lt (V.posNat step.pos) _ _ _ g.pos hglt]
    exact hg2
  · intro k hk
    exact hexpdrop _ _ (by simpa using h.gray_chain (k + 1) (by simpa using hk))
  · intro k hk
    simpa using h.gray_acc (k + 1) (by simpa using hk)
  · intro k l hk hl hkl
    simpa using h.frames_mono (k + 1) (l + 1) (by simpa using hk) (by simpa using hl) (by omega)
  · intro k hk
    rw [hpopAt k]
    simpa using h.lowlink_le (k + 1) (by simpa using hk)
  · rw [hlive']
    intro k hk
    have hle := h.lowlink_le (k + 1) (by simpa using hk)
    simp only [List.getElem_cons_succ] at hle
    have hglt := hgraylt _ (List.getElem_mem (show k < gray.length by simpa using hk))
    have hlt : V.lowlinkAt aux (k + 1) < V.posNat step.pos := by omega
    obtain ⟨-, h2⟩ := h.lowlink_reaches (k + 1) (by simpa using hk)
    rw [hpopAt k]
    refine ⟨by rw [hsizeL]; exact hlt, ?_⟩
    rw [liveFlush_getElem!_lt (V.posNat step.pos) _ _ _ _ hlt]
    simpa using h2
  · rw [hlive', hli']
    intro k hk i hi hle t ht pt hpt
    rw [hsizeL] at hi
    obtain ⟨hptlt, hptval⟩ :=
      (LiveWF.flush (dead := V.dead aux) (V.posNat step.pos) h.liveWF).bwd t pt hpt
    rw [hsizeL] at hptlt
    rw [liveFlush_getElem!_lt (V.posNat step.pos) _ _ _ pt hptlt] at hptval
    have hpt' : (V.liveIndex aux)[t]? = some pt := by
      rw [← hptval, getElem!_pos (V.live aux) pt (by omega)]
      exact h.liveWF.fwd pt (by omega)
    rw [hgetlt' i hi] at ht
    have hkk : k + 1 < (⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: gray).length := by
      simp at hk ⊢; omega
    have hle' : ((⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: gray)[k + 1]'hkk).pos ≤ i := by
      simpa using hle
    obtain ⟨l, hlk, hlb⟩ := h.lowlink_bound (k + 1) hkk i (by omega) hle' t (hexp _ t ht) pt hpt'
    rcases l with _ | l
    · rw [hll0] at hlb; omega
    · exact ⟨l, by omega, by rw [hpopAt l]; exact hlb⟩

omit [LawfulBEq State] [LawfulHashable State] in
/-- POP at any other frame folds its lowlink into the parent and records nothing. -/
theorem SearchWF.popMerge_step [Inhabited State] {ops : DFSOps.{u,v,w} State} {V : LowlinkView ops}
    (hlaw : LowlinkLawful ops V) {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    {aux : ops.Aux}
    {step : DFSStep State ops.Position} {gray : List (GrayFrame State)}
    (hsucc : step.succ = succs step.state) (hidx : ¬ step.idx < step.succ.size)
    (hclose : V.closes aux step = false)
    (h : SearchWF ops V succs edgeMarks initialStates aux
      (⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: gray)) :
    SearchWF ops V succs edgeMarks initialStates (ops.pop succs edgeMarks aux step).1 gray := by
  have hsz : (V.lowlinks aux).size = gray.length + 1 := by rw [h.frames_length]; simp
  obtain ⟨ll, hll⟩ : ∃ ll, (V.lowlinks aux).back? = some ll := by
    rcases hb : (V.lowlinks aux).back? with _ | ll
    · rw [Array.back?_eq_none_iff] at hb; simp [hb] at hsz
    · exact ⟨ll, rfl⟩
  have hll0 : V.lowlinkAt aux 0 = ll := revGetD_zero hll
  have hsza : (V.accs aux).size = gray.length + 1 := by rw [h.accs_length]; simp
  obtain ⟨acc0, hacc0⟩ : ∃ a, (V.accs aux).back? = some a := by
    rcases hb : (V.accs aux).back? with _ | a
    · rw [Array.back?_eq_none_iff] at hb; simp [hb] at hsza
    · exact ⟨a, rfl⟩
  have haccm := hlaw.pop_merge_accs succs edgeMarks aux step acc0 hclose hacc0
  -- the frame POP closes has scanned every successor, so dropping it adds no explored edge
  have hexp : ∀ s t, ExploredEdge gray succs s t →
      ExploredEdge (⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: gray) succs s t := by
    rintro s t ⟨j, hj, hg⟩
    refine ⟨j, hj, fun g hgm hgs => ?_⟩
    rcases List.mem_cons.mp hgm with rfl | hgm'
    · simp only at hgs
      subst hgs
      obtain ⟨hjlt, -⟩ := Array.getElem?_eq_some_iff.mp hj
      rw [← hsucc] at hjlt
      show j < step.idx
      omega
    · exact hg g hgm' hgs
  have hexpdrop : ∀ s t,
      ExploredEdge (⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: gray) succs s t →
        ExploredEdge gray succs s t := by
    rintro s t ⟨j, hj, hg⟩
    exact ⟨j, hj, fun g hgm hgs => hg g (List.mem_cons_of_mem _ hgm) hgs⟩
  -- the frame is not closing, so its lowlink already points strictly below it
  have hne : ll ≠ V.posNat step.pos := by
    intro heq
    rw [LowlinkView.closes, hll, heq] at hclose
    simp at hclose
  have hllle : ll ≤ V.posNat step.pos := by
    have hb := h.lowlink_le 0 (by simp)
    rw [hll0] at hb
    simpa using hb
  obtain ⟨hlllt, hreach⟩ := h.lowlink_reaches 0 (by simp)
  rw [hll0] at hlllt hreach
  have hxreach : Reaches succs step.state ((V.live aux)[ll]'hlllt) := by
    rcases hreach with heq | hr
    · exact absurd (by simpa using heq) hne
    · rw [getElem!_pos (V.live aux) ll hlllt] at hr
      simpa using hr
  -- clause 6 survives losing the closed frame: route a lost witness through that frame's own lowlink
  have hgray6 : ∀ i, (hi : i < (V.live aux).size) → ∃ g ∈ gray,
      g.pos ≤ i ∧ ((V.live aux)[i] = g.state ∨ Reaches succs (V.live aux)[i] g.state) := by
    intro i hi
    obtain ⟨g, hg, hgi, hgr⟩ := h.live_reaches_gray i hi
    rcases List.mem_cons.mp hg with rfl | hg'
    · obtain ⟨g', hg'mem, hg'll, hg'r⟩ := h.live_reaches_gray ll hlllt
      have hg'gray : g' ∈ gray := by
        rcases List.mem_cons.mp hg'mem with rfl | hh
        · exact absurd hg'll (by simp; omega)
        · exact hh
      have hxg : Reaches succs step.state g'.state := by
        rcases hg'r with heq | hr
        · rw [← heq]; exact hxreach
        · exact PathTo.trans hxreach hr
      refine ⟨g', hg'gray, by simp at hgi ⊢; omega, Or.inr ?_⟩
      rcases hgr with heq | hr
      · rw [heq]; exact hxg
      · exact PathTo.trans hr hxg
    · exact ⟨g, hg', hgi, hgr⟩
  obtain ⟨hlive', hli', hdead'⟩ := hlaw.pop_merge succs edgeMarks aux step hclose
  have hlow' := hlaw.pop_merge_lowlinks succs edgeMarks aux step ll hclose hll
  rcases hpb : (V.lowlinks aux).pop.back? with _ | pll
  · -- no parent frame, so this was the outermost one and `gray` is empty
    rw [hpb] at hlow'
    have hpz : (V.lowlinks aux).pop.size = 0 := by
      rw [Array.back?_eq_none_iff] at hpb; simp [hpb]
    have hgnil : gray = [] := by
      rw [Array.size_pop] at hpz
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hgnil
    exact {
      liveWF := by rw [hlive', hli']; exact h.liveWF
      disjoint := by rw [hlive', hdead']; exact h.disjoint
      touched_reachable := by rw [hlive', hdead']; exact h.touched_reachable
      dead_closed := by rw [hdead']; exact h.dead_closed
      explored_touched := by
        rw [hlive', hdead']
        exact fun s hs t ht => h.explored_touched s hs t (hexp s t ht)
      live_reaches_above := by rw [hlive']; exact h.live_reaches_above
      live_reaches_gray := by rw [hlive']; exact hgray6
      frames_length := by rw [hlow']; simpa using hpz
      accs_length := by
        have hp0 : (V.accs aux).pop.size = 0 := by
          rw [Array.size_pop]; simp at hsza; omega
        have hpb2 : (V.accs aux).pop.back? = none := by
          rcases hb2 : (V.accs aux).pop.back? with _ | x
          · rfl
          · obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hb2
            rw [hys] at hp0; simp at hp0
        rw [hpb2] at haccm
        rw [haccm, hp0]
        simp
      frame_pos := fun g hg => absurd hg (by simp)
      gray_chain := fun k hk => absurd hk (by simp)
      gray_acc := fun k hk => absurd hk (by simp)
      frames_mono := fun k l hk => absurd hk (by simp)
      lowlink_le := fun k hk => absurd hk (by simp)
      lowlink_reaches := fun k hk => absurd hk (by simp)
      lowlink_bound := fun k hk => absurd hk (by simp)
      acc_sound := fun k hk => absurd hk (by simp)
      acc_complete := by
        rw [hli']
        intro u _ pu _ _ hu
        obtain ⟨g, hg, -⟩ := hgray6 pu (h.liveWF.bwd u pu hu).1
        simp at hg
    }
  · -- a parent frame takes the merge, exactly as UPDATE does
    rw [hpb] at hlow'
    have hpge : 1 ≤ (V.lowlinks aux).pop.size := by
      obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.mp hpb
      rw [hys]; simp
    obtain ⟨y, gray'', hgy⟩ : ∃ y gray'', gray = y :: gray'' := by
      rcases gray with _ | ⟨y, gray''⟩
      · exfalso; rw [Array.size_pop] at hpge; simp at hsz; omega
      · exact ⟨y, gray'', rfl⟩
    subst hgy
    have hpll : V.lowlinkAt aux 1 = pll := by
      show revGetD (V.lowlinks aux) 1 = pll
      rw [← revGetD_pop hll 0]
      exact revGetD_zero hpb
    have hnew0 : V.lowlinkAt (ops.pop succs edgeMarks aux step).1 0 = min pll ll := by
      simp [LowlinkView.lowlinkAt, hlow']
    have hnewS : ∀ k, V.lowlinkAt (ops.pop succs edgeMarks aux step).1 (k + 1)
        = V.lowlinkAt aux (k + 2) := by
      intro k
      simp only [LowlinkView.lowlinkAt, hlow', revGetD_push_succ, revGetD_pop hpb, revGetD_pop hll]
    have hpllle : pll ≤ y.pos := by
      have hb := h.lowlink_le 1 (by simp)
      rw [hpll] at hb
      simpa using hb
    have hxy : step.state ∈ succs y.state := by
      simpa using (h.gray_chain 0 (by simp)).mem
    obtain ⟨pacc0, hpb2⟩ : ∃ x, (V.accs aux).pop.back? = some x := by
      rcases hb2 : (V.accs aux).pop.back? with _ | x
      · exfalso
        have hp0 : (V.accs aux).pop.size = 0 := by
          rw [Array.back?_eq_none_iff] at hb2; simp [hb2]
        rw [Array.size_pop] at hp0; simp at hsza; omega
      · exact ⟨x, rfl⟩
    rw [hpb2] at haccm
    refine {
      liveWF := by rw [hlive', hli']; exact h.liveWF
      disjoint := by rw [hlive', hdead']; exact h.disjoint
      touched_reachable := by rw [hlive', hdead']; exact h.touched_reachable
      dead_closed := by rw [hdead']; exact h.dead_closed
      explored_touched := by
        rw [hlive', hdead']
        exact fun s hs t ht => h.explored_touched s hs t (hexp s t ht)
      live_reaches_above := by rw [hlive']; exact h.live_reaches_above
      live_reaches_gray := by rw [hlive']; exact hgray6
      frames_length := by
        rw [hlow', Array.size_push, Array.size_pop, Array.size_pop]
        simp at hsz ⊢; omega
      accs_length := by
        rw [haccm, Array.size_push, Array.size_pop, Array.size_pop]
        simp at hsza ⊢; omega
      frame_pos := ?_, gray_chain := ?_, gray_acc := ?_, frames_mono := ?_
      lowlink_le := ?_, lowlink_reaches := ?_, lowlink_bound := ?_
      acc_sound := by
        simp only [hli']
        intro k hk b hbit
        · have hyp1 : y.pos < (V.live aux).size :=
            (h.frame_pos y (List.mem_cons_of_mem _ (List.mem_cons_self ..))).1
          have hyp2 : (V.live aux)[y.pos]! = y.state :=
            (h.frame_pos y (List.mem_cons_of_mem _ (List.mem_cons_self ..))).2
          have hypos : (V.liveIndex aux)[y.state]? = some y.pos := by
            have hf := h.liveWF.fwd y.pos hyp1
            rwa [← getElem!_pos (V.live aux) y.pos hyp1, hyp2] at hf
          have hxp1 : V.posNat step.pos < (V.live aux).size :=
            (h.frame_pos _ (List.mem_cons_self ..)).1
          have hxp2 : (V.live aux)[V.posNat step.pos]! = step.state :=
            (h.frame_pos _ (List.mem_cons_self ..)).2
          have hxpos : (V.liveIndex aux)[step.state]? = some (V.posNat step.pos) := by
            have hf := h.liveWF.fwd (V.posNat step.pos) hxp1
            rwa [← getElem!_pos (V.live aux) _ hxp1, hxp2] at hf
          have htree : ExploredEdge (y :: gray'') succs y.state step.state :=
            hexpdrop _ _ (by simpa using h.gray_chain 0 (by simp))
          have htreeacc : step.acc = marksToBitmask (edgeMarks y.state step.state) := by
            simpa using h.gray_acc 0 (by simp)
          have hmintree : min pll ll ≤ V.posNat step.pos :=
            le_trans (min_le_right _ _) hllle
          rcases k with _ | k
          · have hnewA : V.accAt (ops.pop succs edgeMarks aux step).1 0
                = pacc0 ||| step.acc ||| acc0 ||| V.extraAcc := by
              simp [LowlinkView.accAt, haccm]
            rw [hnewA] at hbit
            simp only [Nat.testBit_or, Bool.or_eq_true] at hbit
            have haccA0 : V.accAt aux 0 = acc0 := revGetD_zero hacc0
            have haccA1 : V.accAt aux 1 = pacc0 := by
              show revGetD (V.accs aux) 1 = pacc0
              rw [← revGetD_pop hacc0 0]
              exact revGetD_zero hpb2
            rcases hbit with ((hbit | hbit) | hbit) | hbit
            · obtain ⟨u, v, pu, pv, he, hu, hv, hlo, hlow, hup, hmk⟩ :=
                h.acc_sound 1 (by simp) b (by rw [haccA1]; exact hbit)
              obtain ⟨l, hl, hlb⟩ := hlow
              refine ⟨u, v, pu, pv, hexpdrop _ _ he, hu, hv, by simpa using hlo,
                ⟨0, le_refl _, ?_⟩, fun j hj => absurd hj (by omega), hmk⟩
              rw [hnew0]
              rcases Nat.eq_zero_or_pos l with rfl | hl0
              · rw [hll0] at hlb; exact le_trans (min_le_right _ _) hlb
              · have hl1 : l = 1 := by omega
                subst hl1
                rw [hpll] at hlb
                exact le_trans (min_le_left _ _) hlb
            · exact ⟨y.state, step.state, y.pos, V.posNat step.pos, htree, hypos, hxpos,
                by simp, ⟨0, le_refl _, by rw [hnew0]; exact hmintree⟩,
                fun j hj => absurd hj (by omega),
                Or.inr (by rw [htreeacc] at hbit; exact (testBit_marksToBitmask _ b).mp hbit)⟩
            · obtain ⟨u, v, pu, pv, he, hu, hv, hlo, hlow, hup, hmk⟩ :=
                h.acc_sound 0 (by simp) b (by rw [haccA0]; exact hbit)
              obtain ⟨l, hl, hlb⟩ := hlow
              have hl0 : l = 0 := by omega
              subst hl0
              rw [hll0] at hlb
              have hym := h.frames_mono 0 1 (by simp) (by simp) (by omega)
              simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hym hlo
              refine ⟨u, v, pu, pv, hexpdrop _ _ he, hu, hv, by simp; omega,
                ⟨0, le_refl _, by rw [hnew0]; exact le_trans (min_le_right _ _) hlb⟩,
                fun j hj => absurd hj (by omega), hmk⟩
            · exact ⟨y.state, step.state, y.pos, V.posNat step.pos, htree, hypos, hxpos,
                by simp, ⟨0, le_refl _, by rw [hnew0]; exact hmintree⟩,
                fun j hj => absurd hj (by omega), Or.inl hbit⟩
          · have hnewA : V.accAt (ops.pop succs edgeMarks aux step).1 (k + 1)
                = V.accAt aux (k + 2) := by
              simp only [LowlinkView.accAt, haccm, revGetD_push_succ, revGetD_pop hpb2,
                revGetD_pop hacc0]
            rw [hnewA] at hbit
            obtain ⟨u, v, pu, pv, he, hu, hv, hlo, hlow, hup, hmk⟩ :=
              h.acc_sound (k + 2) (by simpa using hk) b hbit
            obtain ⟨l, hl, hlb⟩ := hlow
            refine ⟨u, v, pu, pv, hexpdrop _ _ he, hu, hv, by simpa using hlo, ?_, ?_, hmk⟩
            · rcases l with _ | l
              · rw [hll0] at hlb
                exact ⟨0, Nat.zero_le _, by rw [hnew0]; exact le_trans (min_le_right _ _) hlb⟩
              · rcases l with _ | l
                · rw [hpll] at hlb
                  exact ⟨0, Nat.zero_le _, by rw [hnew0]; exact le_trans (min_le_left _ _) hlb⟩
                · exact ⟨l + 1, by omega, by rw [hnewS l]; exact hlb⟩
            · intro j hj
              simpa using hup (j + 1) (by omega)
      acc_complete := by
        simp only [hli']
        intro u v pu pv he hu hv b hb
        have haccA0 : V.accAt aux 0 = acc0 := revGetD_zero hacc0
        have haccA1 : V.accAt aux 1 = pacc0 := by
          show revGetD (V.accs aux) 1 = pacc0
          rw [← revGetD_pop hacc0 0]
          exact revGetD_zero hpb2
        have hnewA0 : V.accAt (ops.pop succs edgeMarks aux step).1 0
            = pacc0 ||| step.acc ||| acc0 ||| V.extraAcc := by
          simp [LowlinkView.accAt, haccm]
        have htreeacc : step.acc = marksToBitmask (edgeMarks y.state step.state) := by
          simpa using h.gray_acc 0 (by simp)
        have hym := h.frames_mono 0 1 (by simp) (by simp) (by omega)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hym
        obtain ⟨l, hl, hlo, hup, hacc⟩ := h.acc_complete u v pu pv (hexp _ _ he) hu hv b hb
        rcases l with _ | _ | l
        · -- owned by the merged frame, which folds into its parent
          refine ⟨0, by simp, ?_, fun l' hl' => absurd hl' (by omega), Or.inl ?_⟩
          · show y.pos ≤ pu
            have : V.posNat step.pos ≤ pu := hlo
            omega
          · rcases hacc with hacc | ⟨j, hj, -⟩
            · rw [hnewA0]
              rw [haccA0] at hacc
              simp [Nat.testBit_or, hacc]
            · exact absurd hj (by omega)
        · refine ⟨0, by simp, hlo, fun l' hl' => absurd hl' (by omega), Or.inl ?_⟩
          rw [hnewA0]
          rcases hacc with hacc | ⟨j, hj, hu', hv'⟩
          · rw [haccA1] at hacc
            simp [Nat.testBit_or, hacc]
          · -- the tree edge into the merged frame, whose marks that frame still held
            obtain rfl : j = 0 := by omega
            have hu0 : u = y.state := hu'
            have hv0 : v = step.state := hv'
            subst hu0 hv0
            simp only [Nat.testBit_or, Bool.or_eq_true]
            rcases hb with hb | hb
            · exact Or.inr hb
            · exact Or.inl (Or.inl (Or.inr (by rw [htreeacc]; exact (testBit_marksToBitmask _ b).mpr hb)))
        · have hnewAS : V.accAt (ops.pop succs edgeMarks aux step).1 (l + 1) = V.accAt aux (l + 2) := by
            simp only [LowlinkView.accAt, haccm, revGetD_push_succ, revGetD_pop hpb2, revGetD_pop hacc0]
          refine ⟨l + 1, by simpa using hl, by simpa using hlo,
            fun l' hl' => by simpa using hup (l' + 1) (by omega), ?_⟩
          rcases hacc with hacc | ⟨j, hj, hu', hv'⟩
          · exact Or.inl (by rw [hnewAS]; exact hacc)
          · obtain rfl : j = l + 1 := by omega
            exact Or.inr ⟨l, rfl, by simpa using hu', by simpa using hv'⟩
    }
    · intro g hg
      rw [hlive']
      exact h.frame_pos g (List.mem_cons_of_mem _ hg)
    · intro k hk
      exact hexpdrop _ _ (by simpa using h.gray_chain (k + 1) (by simpa using hk))
    · intro k hk
      simpa using h.gray_acc (k + 1) (by simpa using hk)
    · intro k l hk hl hkl
      simpa using h.frames_mono (k + 1) (l + 1) (by simpa using hk) (by simpa using hl) (by omega)
    · intro k hk
      rcases k with _ | k
      · rw [hnew0]
        simpa using le_trans (min_le_left pll ll) hpllle
      · rw [hnewS k]
        simpa using h.lowlink_le (k + 2) (by simpa using hk)
    · rw [hlive']
      intro k hk
      rcases k with _ | k
      · refine ⟨by rw [hnew0]; exact lt_of_le_of_lt (min_le_right _ _) hlllt, ?_⟩
        rw [hnew0]
        rcases Nat.le_total pll ll with hle | hle
        · rw [min_eq_left hle]
          have hr := (h.lowlink_reaches 1 (by simp)).2
          rw [hpll] at hr
          simpa using hr
        · rw [min_eq_right hle]
          refine Or.inr ?_
          simp only [List.getElem_cons_zero]
          rw [getElem!_pos (V.live aux) ll hlllt]
          exact PathTo.trans (PathTo.direct hxy) hxreach
      · rw [hnewS k]
        obtain ⟨h1, h2⟩ := h.lowlink_reaches (k + 2) (by simpa using hk)
        exact ⟨h1, by simpa using h2⟩
    · rw [hlive', hli']
      intro k hk i hi hle t ht pt hpt
      have hkk : k + 1 < (⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: y :: gray'').length := by
        simp at hk ⊢; omega
      have hle' : ((⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: y :: gray'')[k + 1]'hkk).pos ≤ i := by
        simpa using hle
      obtain ⟨l, hlk, hlb⟩ := h.lowlink_bound (k + 1) hkk i hi hle' t (hexp _ t ht) pt hpt
      rcases l with _ | l
      · rw [hll0] at hlb
        exact ⟨0, Nat.zero_le _, by rw [hnew0]; exact le_trans (min_le_right _ _) hlb⟩
      · rcases l with _ | l
        · rw [hpll] at hlb
          exact ⟨0, Nat.zero_le _, by rw [hnew0]; exact le_trans (min_le_left _ _) hlb⟩
        · exact ⟨l + 1, by omega, by rw [hnewS l]; exact hlb⟩

/-- PUSH on a fresh root, where no frame is open and the live stack is empty. -/
theorem SearchWF.pushRoot_step [Inhabited State] {ops : DFSOps.{u,v,w} State} {V : LowlinkView ops}
    (hlaw : LowlinkLawful ops V) {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    {aux : ops.Aux} {m : Std.HashSet Nat}
    {q0 : State} (hq0 : ops.getStatus aux q0 = .unknown)
    (hq0reach : Reachable initialStates succs q0)
    (h : SearchWF ops V succs edgeMarks initialStates aux []) :
    SearchWF ops V succs edgeMarks initialStates (ops.push aux q0 m).1
      [⟨q0, V.posNat (ops.push aux q0 m).2, 0, 0⟩] := by
  -- no frame is open, so clause 6 has no witness to offer and the live stack must already be empty
  have hempty : (V.live aux).size = 0 := by
    by_contra hne
    obtain ⟨g, hg, -⟩ := h.live_reaches_gray 0 (by omega)
    exact absurd hg (by simp)
  have hstat : liveStatusOf (V.liveIndex aux) (V.dead aux) q0 = .unknown := by
    rw [← hlaw.status aux q0]; exact hq0
  have hli : (V.liveIndex aux).contains q0 = false := by
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    rw [liveStatusOf, if_pos hc] at hstat
    exact absurd hstat (by simp)
  have hnd : q0 ∉ V.dead aux := by
    intro hd
    rw [liveStatusOf, if_neg (by simp [hli]),
      if_pos (Std.HashSet.mem_iff_contains.mp hd)] at hstat
    exact absurd hstat (by simp)
  have hlive' : V.live (ops.push aux q0 m).1 = (V.live aux).push q0 := hlaw.push_live aux q0 m
  have hsize' : (V.live (ops.push aux q0 m).1).size = 1 := by
    rw [hlive', Array.size_push, hempty]
  have hpos : V.posNat (ops.push aux q0 m).2 = 0 := by rw [hlaw.push_pos, hempty]
  have hdead' : V.dead (ops.push aux q0 m).1 = V.dead aux := hlaw.push_dead aux q0 m
  have hget0 : ∀ (hi : 0 < (V.live (ops.push aux q0 m).1).size),
      (V.live (ops.push aux q0 m).1)[0] = q0 := by
    intro hi
    have hz : (V.live (ops.push aux q0 m).1)[0]
        = ((V.live aux).push q0)[0]'(by rw [← hlive']; exact hi) := by simp only [hlive']
    rw [hz]
    simp [Array.getElem_push, hempty]
  have hget0! : (V.live (ops.push aux q0 m).1)[0]! = q0 := by
    rw [hlive']
    have h0 : (0 : Nat) = (V.live aux).size := hempty.symm
    rw [h0, Array.getElem!_push_eq]
  have hll0 : V.lowlinkAt (ops.push aux q0 m).1 0 = 0 := by
    simp [LowlinkView.lowlinkAt, hlaw.push_lowlinks aux q0 m, hempty]
  refine {
    liveWF := ?_, disjoint := ?_, touched_reachable := ?_
    dead_closed := by rw [hdead']; exact h.dead_closed
    explored_touched := ?_, live_reaches_above := ?_, live_reaches_gray := ?_
    frames_length := ?_
    accs_length := by
      rw [hlaw.push_accs aux q0 m, Array.size_push]
      have hz : (V.accs aux).size = 0 := by rw [h.accs_length]; rfl
      simp [hz]
    frame_pos := ?_
    gray_chain := fun k hk => absurd hk (by simp)
    gray_acc := fun k hk => absurd hk (by simp)
    frames_mono := fun k l hk hl hkl => absurd hkl (by simp at hk hl; omega)
    lowlink_le := ?_, lowlink_reaches := ?_, lowlink_bound := ?_
    acc_sound := by
      intro k hk b hbit
      exfalso
      have hz : V.accAt (ops.push aux q0 m).1 0 = 0 := by
        simp [LowlinkView.accAt, hlaw.push_accs aux q0 m]
      have hk0 : k = 0 := by simp at hk; omega
      subst hk0
      rw [hz] at hbit
      simp at hbit
    acc_complete := by
      rw [hlaw.push_liveIndex aux q0 m]
      rintro u v pu pv ⟨j, -, hg⟩ hu
      by_cases hqu : q0 = u
      · exact absurd (hg _ (List.mem_cons_self ..) hqu) (by simp)
      · rw [Std.HashMap.getElem?_insert, if_neg (by simpa using hqu)] at hu
        have := (h.liveWF.bwd u pu hu).1
        omega
  }
  · rw [hlive', hlaw.push_liveIndex aux q0 m]; exact h.liveWF.push hli
  · intro s hs
    rw [hdead']
    rw [hlive', Array.mem_push] at hs
    rcases hs with hs | rfl
    · exact h.disjoint s hs
    · exact hnd
  · intro s hs
    rcases hs with hs | hs
    · rw [hlive', Array.mem_push] at hs
      rcases hs with hs | rfl
      · exact h.touched_reachable s (Or.inl hs)
      · exact hq0reach
    · exact h.touched_reachable s (Or.inr (hdead' ▸ hs))
  · rintro s hs t ⟨j, -, hg⟩
    have hsq : s = q0 := by
      rw [hlive', Array.mem_push] at hs
      rcases hs with hs | rfl
      · obtain ⟨i, hi, -⟩ := Array.getElem_of_mem hs
        omega
      · rfl
    exact absurd (hg _ (List.mem_cons_self ..) hsq.symm) (by simp)
  · intro i j hi hj hij
    have hi0 : i = 0 := by rw [hsize'] at hi; omega
    have hj0 : j = 0 := by rw [hsize'] at hj; omega
    subst hi0; subst hj0
    exact Or.inl rfl
  · intro i hi
    have hi0 : i = 0 := by rw [hsize'] at hi; omega
    subst hi0
    exact ⟨⟨q0, V.posNat (ops.push aux q0 m).2, 0, 0⟩, by simp, by simp [hpos], Or.inl (hget0 hi)⟩
  · rw [hlaw.push_lowlinks aux q0 m, Array.size_push]
    have hz : (V.lowlinks aux).size = 0 := by rw [h.frames_length]; rfl
    simp [hz]
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    exact ⟨by show V.posNat (ops.push aux q0 m).2 < _; rw [hpos, hsize']; omega,
      by show (V.live (ops.push aux q0 m).1)[V.posNat (ops.push aux q0 m).2]! = q0
         rw [hpos]; exact hget0!⟩
  · intro k hk
    have hk0 : k = 0 := by simp at hk; omega
    subst hk0
    simp [hll0, hpos]
  · intro k hk
    have hk0 : k = 0 := by simp at hk; omega
    subst hk0
    exact ⟨by rw [hll0, hsize']; omega, Or.inl (by show V.lowlinkAt _ 0 = V.posNat _; rw [hll0, hpos])⟩
  · rintro k hk i hi hle t ⟨j, -, hg⟩ pt hpt
    have hi0 : i = 0 := by rw [hsize'] at hi; omega
    subst hi0
    rw [hget0 hi] at hg
    exact absurd (hg _ (List.mem_cons_self ..) rfl) (by simp)

omit [LawfulBEq State] [LawfulHashable State] in
/-- A move that leaves `dead` alone and records nothing keeps the recorded clauses. -/
theorem EnumWF.of_dead_eq [Inhabited State] {ops : DFSOps.{u,v,w} State} {V : LowlinkView ops}
    {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    {aux aux' : ops.Aux} {recorded : Array (Std.HashSet State × ops.Aux)} {gray gray' : List (GrayFrame State)}
    (h : EnumWF ops V succs edgeMarks initialStates aux recorded gray)
    (h' : SearchWF ops V succs edgeMarks initialStates aux' gray') (hdead : V.dead aux' = V.dead aux) :
    EnumWF ops V succs edgeMarks initialStates aux' recorded gray' where
  toSearchWF := h'
  recorded_sound := by rw [hdead]; exact h.recorded_sound
  recorded_complete := by rw [hdead]; exact h.recorded_complete

/-- POP at a closing frame records a completed SCC, maximal since `dead` grows by a whole component and never
by part of one. -/
theorem EnumWF.popClose_step [Inhabited State] {ops : DFSOps.{u,v,w} State} {V : LowlinkView ops}
    (hlaw : LowlinkLawful ops V) {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    {aux : ops.Aux} {recorded : Array (Std.HashSet State × ops.Aux)}
    {step : DFSStep State ops.Position} {gray : List (GrayFrame State)}
    (hsucc : step.succ = succs step.state) (hidx : ¬ step.idx < step.succ.size)
    (hclose : V.closes aux step = true)
    (h : EnumWF ops V succs edgeMarks initialStates aux recorded
      (⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: gray)) :
    EnumWF ops V succs edgeMarks initialStates (ops.pop succs edgeMarks aux step).1
      (recorded.push (flushedSet (V.live aux) (V.posNat step.pos), aux)) gray := by
  obtain ⟨hFout, hconn⟩ := h.toSearchWF.close_flushed hsucc hidx hclose
  have hdead' : V.dead (ops.pop succs edgeMarks aux step).1
      = (liveFlush (V.live aux) (V.liveIndex aux) (V.dead aux) (V.posNat step.pos)).2.2 :=
    congrArg (fun p => p.2.2) (hlaw.pop_close succs edgeMarks aux step hclose).1
  have hsccsub : ∀ (D : Std.HashSet State) (a b : State), b ∈ sccSuccs succs D a → b ∈ succs a := by
    intro D a b hb
    simp only [sccSuccs] at hb
    exact (Array.mem_filter.mp hb).1
  refine { toSearchWF := SearchWF.popClose_step hlaw hsucc hidx hclose h.toSearchWF,
           recorded_sound := ?_, recorded_complete := ?_ }
  · rw [hdead']
    intro pr hpr
    rcases Array.mem_push.mp hpr with hpr' | rfl
    · obtain ⟨hsub, hc⟩ := h.recorded_sound pr hpr'
      exact ⟨fun s hs => liveFlush_dead_mono _ _ _ _ s (hsub s hs), hc⟩
    · refine ⟨fun s hs => ?_, hconn⟩
      obtain ⟨i, hi, hpi, rfl⟩ := (mem_flushedSet _ _ s).mp hs
      rw [← getElem!_pos (V.live aux) i hi]
      exact liveFlush_dead_of_ge _ _ _ _ i hpi hi
  · rw [hdead']
    intro D hDne hDconn hDdead
    by_cases hall : ∀ s ∈ D, s ∈ V.dead aux
    · obtain ⟨pr, hpr, hsub⟩ := h.recorded_complete D hDne hDconn hall
      exact ⟨pr, Array.mem_push.mpr (Or.inl hpr), hsub⟩
    · push_neg at hall
      obtain ⟨s0, hs0D, hs0nd⟩ := hall
      have hs0F : s0 ∈ flushedSet (V.live aux) (V.posNat step.pos) := by
        rcases liveFlush_dead_or_old _ _ _ _ s0 (hDdead s0 hs0D) with hdd | ⟨q, hq1, hq2, hq3⟩
        · exact absurd hdd hs0nd
        · rw [getElem!_pos (V.live aux) q hq2] at hq3
          exact (mem_flushedSet _ _ s0).mpr ⟨q, hq2, hq1, hq3⟩
      -- nothing reachable from the flushed set leaves it or `dead`
      have hstay : ∀ y, Reaches succs s0 y →
          y ∈ flushedSet (V.live aux) (V.posNat step.pos) ∨ y ∈ V.dead aux := fun y hr =>
        hr.closed (P := fun z => z ∈ flushedSet (V.live aux) (V.posNat step.pos) ∨ z ∈ V.dead aux)
          (Or.inl hs0F) (fun a ha b hb => by
            rcases ha with ha | ha
            · exact hFout a ha b hb
            · exact Or.inr (h.dead_closed a ha b hb))
      refine ⟨_, Array.mem_push.mpr (Or.inr rfl), fun u hu => ?_⟩
      rcases hDconn s0 hs0D u hu with heq | hpath
      · exact heq ▸ hs0F
      · rcases hstay u (PathTo.mono_succs (hsccsub D) hpath) with hc | hc
        · exact hc
        · exfalso
          refine hs0nd ?_
          rcases hDconn u hu s0 hs0D with heq | hback
          · exact heq ▸ hc
          · exact (PathTo.mono_succs (hsccsub D) hback).closed hc h.dead_closed

/-! ### Preservation across the run -/

private theorem dfsGo_enumWF [Inhabited State] (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (hlaw : LowlinkLawful ops V) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) :
    ∀ (aux : (enumOps ops V).Aux) (stack : List (DFSStep State ops.Position))
      (r : Option (State × List State) × (enumOps ops V).Aux),
      dfsGo (enumOps ops V) succs edgeMarks aux stack = some r →
      (∀ st ∈ stack, st.succ = succs st.state) →
      (∀ st ∈ stack, Reachable initialStates succs st.state) →
      EnumWF ops V succs edgeMarks initialStates aux.1 aux.2 (V.grayOf stack) →
      EnumWF ops V succs edgeMarks initialStates r.2.1 r.2.2 [] := by
  refine dfsGo.partial_correctness (enumOps ops V) succs edgeMarks
    (fun aux stack r => (∀ st ∈ stack, st.succ = succs st.state) →
      (∀ st ∈ stack, Reachable initialStates succs st.state) →
      EnumWF ops V succs edgeMarks initialStates aux.1 aux.2 (V.grayOf stack) →
      EnumWF ops V succs edgeMarks initialStates r.2.1 r.2.2 []) ?_
  intro f ih aux stack r hr
  cases stack with
  | nil =>
    intro _ _ hwf
    simp only [Option.some.injEq] at hr
    rw [← hr]
    exact hwf
  | cons step rest =>
    intro hsucc hreach hwf
    have hsucc' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
        st.succ = succs st.state := by
      intro st hst
      rcases List.mem_cons.mp hst with rfl | hst'
      · exact hsucc step (by simp)
      · exact hsucc st (List.mem_cons_of_mem _ hst')
    have hreach' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
        Reachable initialStates succs st.state := by
      intro st hst
      rcases List.mem_cons.mp hst with rfl | hst'
      · exact hreach step (by simp)
      · exact hreach st (List.mem_cons_of_mem _ hst')
    by_cases hidx : step.idx < step.succ.size
    case neg =>
      simp only [hidx, dite_false] at hr
      by_cases hcl : V.closes aux.1 step
      · simp only [enumOps, hcl, if_true] at hr
        exact ih _ rest r hr (fun st hst => hsucc st (List.mem_cons_of_mem _ hst))
          (fun st hst => hreach st (List.mem_cons_of_mem _ hst))
          (EnumWF.popClose_step hlaw (hsucc step (by simp)) hidx hcl hwf)
      · simp only [enumOps, hcl] at hr
        exact ih _ rest r hr (fun st hst => hsucc st (List.mem_cons_of_mem _ hst))
          (fun st hst => hreach st (List.mem_cons_of_mem _ hst))
          (hwf.of_dead_eq
            (SearchWF.popMerge_step hlaw (hsucc step (by simp)) hidx (by simpa using hcl) hwf.toSearchWF)
            (hlaw.pop_merge _ _ _ _ (by simpa using hcl)).2.2)
    case pos =>
      simp only [hidx, dite_true] at hr
      have hd : step.succ[step.idx] ∈ succs step.state := by
        rw [← hsucc step (by simp)]; exact Array.getElem_mem hidx
      have hedge : (succs step.state)[step.idx]? = some step.succ[step.idx] := by
        rw [← hsucc step (by simp)]; exact Array.getElem?_eq_getElem hidx
      cases hgs : ops.getStatus aux.1 step.succ[step.idx] with
      | dead =>
        simp only [enumOps_getStatus, hgs] at hr
        exact ih aux _ r hr hsucc' hreach'
          (hwf.of_dead_eq (SearchWF.bump_step hlaw hgs hedge hwf.toSearchWF) rfl)
      | live =>
        simp only [enumOps, hgs] at hr
        exact ih _ _ r hr hsucc' hreach'
          (hwf.of_dead_eq (SearchWF.update_step hlaw hgs hedge rfl hwf.toSearchWF) (hlaw.update_dead _ _ _))
      | unknown =>
        simp only [enumOps, hgs] at hr
        refine ih _ _ r hr ?_ ?_ ?_
        · intro st hst
          rcases List.mem_cons.mp hst with rfl | hst'
          · rfl
          · exact hsucc' st hst'
        · intro st hst
          rcases List.mem_cons.mp hst with rfl | hst'
          · exact Reachable.step (hreach step (by simp)) hd
          · exact hreach' st hst'
        · exact hwf.of_dead_eq (SearchWF.push_step hlaw hgs hedge rfl
            (Reachable.step (hreach step (by simp)) hd) hwf.toSearchWF) (hlaw.push_dead _ _ _)

private theorem dfsFromRoot_enumWF [Inhabited State] (ops : DFSOps.{u,v,w} State)
    (V : LowlinkView ops) (hlaw : LowlinkLawful ops V) (L : LawfulDFSOps ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs)
    (aux : (enumOps ops V).Aux) (q0 : State) (hwfL : L.WellFormed aux.1)
    (hq0status : ops.getStatus aux.1 q0 = .unknown) (hq0 : Reachable initialStates succs q0)
    (hwf : EnumWF ops V succs edgeMarks initialStates aux.1 aux.2 []) :
    EnumWF ops V succs edgeMarks initialStates (dfsFromRoot (enumOps ops V) succs edgeMarks aux q0).2.1
      (dfsFromRoot (enumOps ops V) succs edgeMarks aux q0).2.2 [] := by
  rw [dfsFromRoot_eq (enumOps ops V) succs edgeMarks aux q0]
  obtain ⟨r, hdg⟩ := Option.ne_none_iff_exists'.mp
    (dfsGo_ne_none (enumOps ops V) succs edgeMarks initialStates fr (enumLawful ops V L)
      ((enumOps ops V).push aux q0 (Std.HashSet.emptyWithCapacity 0)).1
      [{ state := q0, pos := ((enumOps ops V).push aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
         acc := 0, succ := succs q0, idx := 0 }]
      ((enumLawful ops V L).wf_push aux q0 _ hq0status hwfL)
      (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; rfl)
      (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; exact hq0))
  rw [hdg]
  simp only [Option.getD_some]
  refine dfsGo_enumWF ops V hlaw succs edgeMarks initialStates _ _ r hdg
    (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; rfl)
    (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; exact hq0) ?_
  exact hwf.of_dead_eq (SearchWF.pushRoot_step hlaw hq0status hq0 hwf.toSearchWF) (hlaw.push_dead _ _ _)

private theorem genericDFSGo_enumWF [Inhabited State] (ops : DFSOps.{u,v,w} State)
    (V : LowlinkView ops) (hlaw : LowlinkLawful ops V) (L : LawfulDFSOps ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs) :
    ∀ (roots : List State), (∀ q ∈ roots, Reachable initialStates succs q) →
      ∀ (aux : (enumOps ops V).Aux) r, L.WellFormed aux.1 →
        genericDFSGo (enumOps ops V) succs edgeMarks roots aux = some r →
        EnumWF ops V succs edgeMarks initialStates aux.1 aux.2 [] →
        EnumWF ops V succs edgeMarks initialStates r.2.1 r.2.2 [] := by
  intro roots
  induction roots with
  | nil =>
    intro _ aux r _ hgo hwf
    rw [genericDFSGo.eq_def] at hgo
    simp only [Option.some.injEq] at hgo
    rw [← hgo]
    exact hwf
  | cons q rest ih =>
    intro hroots aux r hwfL hgo hwf
    have hq : Reachable initialStates succs q := hroots q (by simp)
    have hrest : ∀ q' ∈ rest, Reachable initialStates succs q' :=
      fun q' hq' => hroots q' (by simp [hq'])
    rw [genericDFSGo.eq_def] at hgo
    cases hst : ops.getStatus aux.1 q with
    | unknown =>
      simp only [enumOps_getStatus, hst] at hgo
      have hstep := dfsFromRoot_enumWF ops V hlaw L succs edgeMarks initialStates fr aux q
        hwfL hst hq hwf
      have hwfL' : L.WellFormed (dfsFromRoot (enumOps ops V) succs edgeMarks aux q).2.1 :=
        dfsFromRoot_wellFormed_total (enumOps ops V) succs edgeMarks (enumLawful ops V L) aux q
          hwfL hst
      cases hf : (dfsFromRoot (enumOps ops V) succs edgeMarks aux q).1 with
      | some x => simp only [hf, Option.some.injEq] at hgo; rw [← hgo]; exact hstep
      | none => simp only [hf] at hgo; exact ih hrest _ r hwfL' hgo hstep
    | dead => simp only [enumOps_getStatus, hst] at hgo; exact ih hrest aux r hwfL hgo hwf
    | live => simp only [enumOps_getStatus, hst] at hgo; exact ih hrest aux r hwfL hgo hwf

/-- The invariant survives the whole recording run, which finishes with no frame left open. -/
theorem enumWF_final [Inhabited State] (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (hlaw : LowlinkLawful ops V) (L : LawfulDFSOps ops) (hwf0 : L.WellFormed ops.initAux)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs) :
    EnumWF ops V succs edgeMarks initialStates
      (genericDFS (enumOps ops V) succs edgeMarks initialStates (enumOps ops V).initAux).2.1
      (genericDFS (enumOps ops V) succs edgeMarks initialStates (enumOps ops V).initAux).2.2 [] := by
  unfold genericDFS
  obtain ⟨r, hgo⟩ := Option.ne_none_iff_exists'.mp
    (genericDFSGo_ne_none (enumOps ops V) succs edgeMarks initialStates (enumOps ops V).initAux)
  rw [hgo]
  simp only [Option.getD_some]
  exact genericDFSGo_enumWF ops V hlaw L succs edgeMarks initialStates fr initialStates
    (fun q hq => Reachable.base hq) (enumOps ops V).initAux r hwf0 hgo
    (enumWF_init ops V hlaw succs edgeMarks initialStates)

/-- The flushes enumerate the maximal SCCs reachable from `initialStates`, trivial ones included. -/
theorem enumSCCs_sound [Inhabited State] (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (hlaw : LowlinkLawful ops V) (L : LawfulDFSOps ops) (hwf0 : L.WellFormed ops.initAux)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs) :
    SCCEnumerationSound initialStates succs (enumSCCs ops V succs edgeMarks initialStates) := by
  have hwf := enumWF_final ops V hlaw L hwf0 succs edgeMarks initialStates fr
  set fin := (genericDFS (enumOps ops V) succs edgeMarks initialStates (enumOps ops V).initAux).2
    with hfin
  -- with no frame open there is no gray state left, so clause 6 forces the live stack empty
  have hlive : (V.live fin.1).size = 0 := by
    by_contra hne
    obtain ⟨st, hst, -⟩ := hwf.live_reaches_gray 0 (by omega)
    exact absurd hst (by simp)
  -- so everything the search touched is dead
  have htouched : ∀ s, ops.getStatus fin.1 s ≠ .unknown → s ∈ V.dead fin.1 := by
    intro s hs
    rw [hlaw.status fin.1 s, liveStatusOf] at hs
    have hnl : (V.liveIndex fin.1).contains s = false := by
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      obtain ⟨p, hp⟩ : ∃ p, (V.liveIndex fin.1)[s]? = some p := by
        rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
        exact Option.isSome_iff_exists.mp hc
      have := (hwf.liveWF.bwd s p hp).1
      omega
    simp only [hnl, Bool.false_eq_true, if_false] at hs
    by_cases hd : (V.dead fin.1).contains s = true
    · exact Std.HashSet.mem_iff_contains.mpr hd
    · simp [hd] at hs
  have hmem : ∀ C, C ∈ enumSCCs ops V succs edgeMarks initialStates → ∃ a, (C, a) ∈ fin.2 := by
    intro C hC
    simp only [enumSCCs, enumRun, List.mem_map] at hC
    obtain ⟨q, hq, rfl⟩ := hC
    exact ⟨q.2, by simpa using hq⟩
  refine ⟨?_, ?_, ?_⟩
  · intro C hC s hs
    obtain ⟨a, ha⟩ := hmem C hC
    exact hwf.touched_reachable s (Or.inr ((hwf.recorded_sound (C, a) ha).1 s hs))
  · intro C hC
    obtain ⟨a, ha⟩ := hmem C hC
    exact (hwf.recorded_sound (C, a) ha).2
  · intro D hDne hDconn hDreach
    have hexpl := genericDFS_returns_none_fully_explored (enumOps ops V) succs edgeMarks
      (enumLawful ops V L) (Reachable initialStates succs)
      (fun aux q hq hw hu => dfsGo_ne_none (enumOps ops V) succs edgeMarks initialStates fr
        (enumLawful ops V L) _ _ ((enumLawful ops V L).wf_push aux q _ hu hw)
        (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; rfl)
        (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; exact hq))
      initialStates (fun q hq => Reachable.base hq)
      (genericDFSGo_ne_none (enumOps ops V) succs edgeMarks initialStates _)
      hwf0 (fun q => hlaw.init_status q)
      (enumOps_never_reports ops V succs edgeMarks initialStates)
    obtain ⟨q, hq, hsub⟩ := hwf.recorded_complete D hDne hDconn
      (fun s hs => htouched s (hexpl s (hDreach s hs)))
    refine ⟨q.1, ?_, hsub⟩
    simp only [enumSCCs, enumRun, List.mem_map]
    exact ⟨q, by simpa using hq, rfl⟩

/-! ## The reporting run

The search invariant over a run of the refinement itself rather than the recording wrapper. A run that reports
stops at the reporting UPDATE or POP, so what it leaves behind is the invariant just before that move. -/

/-- The search state a report was made from, the invariant holding just before the reporting move at the frame
the report names as its anchor. -/
def ReportedFrom [Inhabited State] (ops : DFSOps State) (V : LowlinkView ops) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) (aux' : ops.Aux)
    (anchor : State) : Prop :=
  ∃ (aux : ops.Aux) (step : DFSStep State ops.Position) (gray : List (GrayFrame State)),
    SearchWF ops V succs edgeMarks initialStates aux
      (⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: gray) ∧
    step.succ = succs step.state ∧ step.state = anchor ∧
    -- POP reported on a fully scanned frame
    ((¬ step.idx < step.succ.size ∧ ops.pop succs edgeMarks aux step = (aux', true)) ∨
    -- or UPDATE reported on the frame's next edge, whose target is live
      ∃ d, (succs step.state)[step.idx]? = some d ∧ ops.getStatus aux d = .live ∧
        ops.update aux (edgeMarks step.state d) d = (aux', true))

/-- What a run of the refinement leaves behind, the invariant with no frame open when nothing is reported. -/
def SearchOutcome [Inhabited State] (ops : DFSOps State) (V : LowlinkView ops) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (r : Option (State × List State) × ops.Aux) : Prop :=
  (r.1 = none → SearchWF ops V succs edgeMarks initialStates r.2 []) ∧
  ∀ anchor stem, r.1 = some (anchor, stem) → ReportedFrom ops V succs edgeMarks initialStates r.2 anchor

private theorem dfsGo_searchOutcome [Inhabited State] (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (hlaw : LowlinkLawful ops V) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) :
    ∀ (aux : ops.Aux) (stack : List (DFSStep State ops.Position))
      (r : Option (State × List State) × ops.Aux),
      dfsGo ops succs edgeMarks aux stack = some r →
      (∀ st ∈ stack, st.succ = succs st.state) →
      (∀ st ∈ stack, Reachable initialStates succs st.state) →
      SearchWF ops V succs edgeMarks initialStates aux (V.grayOf stack) →
      SearchOutcome ops V succs edgeMarks initialStates r := by
  refine dfsGo.partial_correctness ops succs edgeMarks
    (fun aux stack r => (∀ st ∈ stack, st.succ = succs st.state) →
      (∀ st ∈ stack, Reachable initialStates succs st.state) →
      SearchWF ops V succs edgeMarks initialStates aux (V.grayOf stack) →
      SearchOutcome ops V succs edgeMarks initialStates r) ?_
  intro f ih aux stack r hr
  cases stack with
  | nil =>
    intro _ _ hwf
    simp only [Option.some.injEq] at hr
    rw [← hr]
    exact ⟨fun _ => hwf, fun _ _ h => by simp at h⟩
  | cons step rest =>
    intro hsucc hreach hwf
    have hstepsucc : step.succ = succs step.state := hsucc step (by simp)
    have hsucc' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
        st.succ = succs st.state := by
      intro st hst
      rcases List.mem_cons.mp hst with rfl | hst'
      · exact hstepsucc
      · exact hsucc st (List.mem_cons_of_mem _ hst')
    have hreach' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
        Reachable initialStates succs st.state := by
      intro st hst
      rcases List.mem_cons.mp hst with rfl | hst'
      · exact hreach step (by simp)
      · exact hreach st (List.mem_cons_of_mem _ hst')
    by_cases hidx : step.idx < step.succ.size
    case neg =>
      simp only [hidx, dite_false] at hr
      rcases hpop : ops.pop succs edgeMarks aux step with ⟨aux', _ | _⟩
      · simp only [hpop] at hr
        have hp1 : (ops.pop succs edgeMarks aux step).1 = aux' := by rw [hpop]
        refine ih aux' rest r hr (fun st hst => hsucc st (List.mem_cons_of_mem _ hst))
          (fun st hst => hreach st (List.mem_cons_of_mem _ hst)) ?_
        rw [← hp1]
        by_cases hcl : V.closes aux step
        · exact SearchWF.popClose_step hlaw hstepsucc hidx hcl hwf
        · exact SearchWF.popMerge_step hlaw hstepsucc hidx (by simpa using hcl) hwf
      · simp only [hpop, Option.some.injEq] at hr
        rw [← hr]
        refine ⟨fun h => by simp at h, fun anchor stem heq => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        exact ⟨aux, step, V.grayOf rest, hwf, hstepsucc, heq.1, Or.inl ⟨hidx, hpop⟩⟩
    case pos =>
      simp only [hidx, dite_true] at hr
      have hd : step.succ[step.idx] ∈ succs step.state := by
        rw [← hstepsucc]; exact Array.getElem_mem hidx
      have hedge : (succs step.state)[step.idx]? = some step.succ[step.idx] := by
        rw [← hstepsucc]; exact Array.getElem?_eq_getElem hidx
      cases hgs : ops.getStatus aux step.succ[step.idx] with
      | dead =>
        simp only [hgs] at hr
        exact ih aux _ r hr hsucc' hreach' (SearchWF.bump_step hlaw hgs hedge hwf)
      | live =>
        rcases hupd : ops.update aux (edgeMarks step.state step.succ[step.idx]) step.succ[step.idx]
          with ⟨aux', _ | _⟩
        · simp only [hgs, hupd, Bool.false_eq_true, ↓reduceIte] at hr
          have hu1 : (ops.update aux (edgeMarks step.state step.succ[step.idx]) step.succ[step.idx]).1
              = aux' := by rw [hupd]
          refine ih aux' _ r hr hsucc' hreach' ?_
          rw [← hu1]
          exact SearchWF.update_step hlaw hgs hedge rfl hwf
        · simp only [hgs, hupd, ↓reduceIte, Option.some.injEq] at hr
          rw [← hr]
          refine ⟨fun h => by simp at h, fun anchor stem heq => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          exact ⟨aux, step, V.grayOf rest, hwf, hstepsucc, heq.1, Or.inr ⟨_, hedge, hgs, hupd⟩⟩
      | unknown =>
        rcases hpush : ops.push aux step.succ[step.idx] (edgeMarks step.state step.succ[step.idx])
          with ⟨aux', pos'⟩
        simp only [hgs, hpush] at hr
        have hstep := SearchWF.push_step hlaw hgs hedge rfl (Reachable.step (hreach step (by simp)) hd) hwf
        rw [hpush] at hstep
        refine ih _ _ r hr ?_ ?_ hstep
        · intro st hst
          rcases List.mem_cons.mp hst with rfl | hst'
          · rfl
          · exact hsucc' st hst'
        · intro st hst
          rcases List.mem_cons.mp hst with rfl | hst'
          · exact Reachable.step (hreach step (by simp)) hd
          · exact hreach' st hst'

private theorem dfsFromRoot_searchOutcome [Inhabited State] (ops : DFSOps.{u,v,w} State)
    (V : LowlinkView ops) (hlaw : LowlinkLawful ops V) (L : LawfulDFSOps ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs)
    (aux : ops.Aux) (q0 : State) (hwfL : L.WellFormed aux)
    (hq0status : ops.getStatus aux q0 = .unknown) (hq0 : Reachable initialStates succs q0)
    (hwf : SearchWF ops V succs edgeMarks initialStates aux []) :
    SearchOutcome ops V succs edgeMarks initialStates (dfsFromRoot ops succs edgeMarks aux q0) := by
  rw [dfsFromRoot_eq ops succs edgeMarks aux q0]
  obtain ⟨r, hdg⟩ := Option.ne_none_iff_exists'.mp
    (dfsGo_ne_none ops succs edgeMarks initialStates fr L
      (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1
      [{ state := q0, pos := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
         acc := 0, succ := succs q0, idx := 0 }]
      (L.wf_push aux q0 _ hq0status hwfL)
      (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; rfl)
      (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; exact hq0))
  rw [hdg]
  simp only [Option.getD_some]
  exact dfsGo_searchOutcome ops V hlaw succs edgeMarks initialStates _ _ r hdg
    (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; rfl)
    (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; exact hq0)
    (SearchWF.pushRoot_step hlaw hq0status hq0 hwf)

private theorem genericDFSGo_searchOutcome [Inhabited State] (ops : DFSOps.{u,v,w} State)
    (V : LowlinkView ops) (hlaw : LowlinkLawful ops V) (L : LawfulDFSOps ops)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs) :
    ∀ (roots : List State), (∀ q ∈ roots, Reachable initialStates succs q) →
      ∀ (aux : ops.Aux) r, L.WellFormed aux →
        genericDFSGo ops succs edgeMarks roots aux = some r →
        SearchWF ops V succs edgeMarks initialStates aux [] →
        SearchOutcome ops V succs edgeMarks initialStates r := by
  intro roots
  induction roots with
  | nil =>
    intro _ aux r _ hgo hwf
    rw [genericDFSGo.eq_def] at hgo
    simp only [Option.some.injEq] at hgo
    rw [← hgo]
    exact ⟨fun _ => hwf, fun _ _ h => by simp at h⟩
  | cons q rest ih =>
    intro hroots aux r hwfL hgo hwf
    have hq : Reachable initialStates succs q := hroots q (by simp)
    have hrest : ∀ q' ∈ rest, Reachable initialStates succs q' :=
      fun q' hq' => hroots q' (by simp [hq'])
    rw [genericDFSGo.eq_def] at hgo
    cases hst : ops.getStatus aux q with
    | unknown =>
      simp only [hst] at hgo
      have hstep := dfsFromRoot_searchOutcome ops V hlaw L succs edgeMarks initialStates fr aux q
        hwfL hst hq hwf
      have hwfL' : L.WellFormed (dfsFromRoot ops succs edgeMarks aux q).2 :=
        dfsFromRoot_wellFormed_total ops succs edgeMarks L aux q hwfL hst
      cases hf : (dfsFromRoot ops succs edgeMarks aux q).1 with
      | some x =>
        simp only [hf, Option.some.injEq] at hgo
        rw [← hgo]
        have hpair : dfsFromRoot ops succs edgeMarks aux q = (some x, (dfsFromRoot ops succs edgeMarks aux q).2) :=
          Prod.ext hf rfl
        rw [hpair] at hstep
        exact hstep
      | none => simp only [hf] at hgo; exact ih hrest _ r hwfL' hgo (hstep.1 hf)
    | dead => simp only [hst] at hgo; exact ih hrest aux r hwfL hgo hwf
    | live => simp only [hst] at hgo; exact ih hrest aux r hwfL hgo hwf

/-- A run of the refinement leaves the search invariant behind, with no frame open when nothing is reported, and
holding just before the reporting move otherwise. -/
theorem genericDFS_searchOutcome [Inhabited State] (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (hlaw : LowlinkLawful ops V) (L : LawfulDFSOps ops) (hwf0 : L.WellFormed ops.initAux)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs) :
    SearchOutcome ops V succs edgeMarks initialStates
      (genericDFS ops succs edgeMarks initialStates ops.initAux) := by
  unfold genericDFS
  obtain ⟨r, hgo⟩ := Option.ne_none_iff_exists'.mp
    (genericDFSGo_ne_none ops succs edgeMarks initialStates ops.initAux)
  rw [hgo]
  simp only [Option.getD_some]
  exact genericDFSGo_searchOutcome ops V hlaw L succs edgeMarks initialStates fr initialStates
    (fun q hq => Reachable.base hq) ops.initAux r hwf0 hgo
    (searchWF_init ops V hlaw succs edgeMarks initialStates)

/-! ## Recorded flushes

Every flush of the recording run is, for a real run that never reports, a closing POP of the real run taken with the
search invariant holding and without reporting. -/

/-- A relation every operation of the refinement moves forward along, such as a queue that only grows. -/
structure MonotoneAlong (ops : DFSOps State) (R : ops.Aux → ops.Aux → Prop) : Prop where
  refl : ∀ a, R a a
  trans : ∀ a b c, R a b → R b c → R a c
  push : ∀ a q m, R a (ops.push a q m).1
  update : ∀ a m d, R a (ops.update a m d).1
  pop : ∀ succs edgeMarks a step, R a (ops.pop succs edgeMarks a step).1

/-- Every recorded flush was made at a closing POP the search invariant held at and which did not report, and the
run has since moved on from that POP along `R` to `cur`. -/
def RecordedAt [Inhabited State] (ops : DFSOps State) (V : LowlinkView ops) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (R : ops.Aux → ops.Aux → Prop) (recorded : Array (Std.HashSet State × ops.Aux)) (cur : ops.Aux) : Prop :=
  ∀ p ∈ recorded, ∃ (step : DFSStep State ops.Position) (gray : List (GrayFrame State)),
    SearchWF ops V succs edgeMarks initialStates p.2
      (⟨step.state, V.posNat step.pos, step.idx, step.acc⟩ :: gray) ∧
    step.succ = succs step.state ∧ ¬ step.idx < step.succ.size ∧ V.closes p.2 step = true ∧
    p.1 = flushedSet (V.live p.2) (V.posNat step.pos) ∧
    (ops.pop succs edgeMarks p.2 step).2 = false ∧ R (ops.pop succs edgeMarks p.2 step).1 cur

omit [LawfulBEq State] [LawfulHashable State] in
private theorem RecordedAt.mono [Inhabited State] {ops : DFSOps State} {V : LowlinkView ops}
    {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    {R : ops.Aux → ops.Aux → Prop} (hR : MonotoneAlong ops R) {recorded : Array (Std.HashSet State × ops.Aux)}
    {cur cur' : ops.Aux} (h : RecordedAt ops V succs edgeMarks initialStates R recorded cur) (hc : R cur cur') :
    RecordedAt ops V succs edgeMarks initialStates R recorded cur' := by
  intro p hp
  obtain ⟨step, gray, h1, h2, h3, h4, h5, h6, h7⟩ := h p hp
  exact ⟨step, gray, h1, h2, h3, h4, h5, h6, hR.trans _ _ _ h7 hc⟩

private theorem dfsGo_recordedAt [Inhabited State] (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (hlaw : LowlinkLawful ops V) {R : ops.Aux → ops.Aux → Prop} (hR : MonotoneAlong ops R)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) :
    ∀ (aux : (enumOps ops V).Aux) (stack : List (DFSStep State ops.Position))
      (r : Option (State × List State) × (enumOps ops V).Aux),
      dfsGo (enumOps ops V) succs edgeMarks aux stack = some r →
      (∀ r', dfsGo ops succs edgeMarks aux.1 stack = some r' → r'.1 = none) →
      (∀ st ∈ stack, st.succ = succs st.state) →
      (∀ st ∈ stack, Reachable initialStates succs st.state) →
      SearchWF ops V succs edgeMarks initialStates aux.1 (V.grayOf stack) →
      RecordedAt ops V succs edgeMarks initialStates R aux.2 aux.1 →
      RecordedAt ops V succs edgeMarks initialStates R r.2.2 r.2.1 := by
  refine dfsGo.partial_correctness (enumOps ops V) succs edgeMarks
    (fun aux stack r => (∀ r', dfsGo ops succs edgeMarks aux.1 stack = some r' → r'.1 = none) →
      (∀ st ∈ stack, st.succ = succs st.state) →
      (∀ st ∈ stack, Reachable initialStates succs st.state) →
      SearchWF ops V succs edgeMarks initialStates aux.1 (V.grayOf stack) →
      RecordedAt ops V succs edgeMarks initialStates R aux.2 aux.1 →
      RecordedAt ops V succs edgeMarks initialStates R r.2.2 r.2.1) ?_
  intro f ih aux stack r hr
  cases stack with
  | nil =>
    intro _ _ _ _ hrec
    simp only [Option.some.injEq] at hr
    rw [← hr]
    exact hrec
  | cons step rest =>
    intro hreal hsucc hreach hwf hrec
    have hstepsucc : step.succ = succs step.state := hsucc step (by simp)
    have hsucc' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
        st.succ = succs st.state := by
      intro st hst
      rcases List.mem_cons.mp hst with rfl | hst'
      · exact hstepsucc
      · exact hsucc st (List.mem_cons_of_mem _ hst')
    have hreach' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
        Reachable initialStates succs st.state := by
      intro st hst
      rcases List.mem_cons.mp hst with rfl | hst'
      · exact hreach step (by simp)
      · exact hreach st (List.mem_cons_of_mem _ hst')
    by_cases hidx : step.idx < step.succ.size
    case neg =>
      simp only [hidx, dite_false] at hr
      rcases hpop : ops.pop succs edgeMarks aux.1 step with ⟨aux'', _ | _⟩
      · have hp1 : (ops.pop succs edgeMarks aux.1 step).1 = aux'' := by rw [hpop]
        -- the real run takes the same POP and carries on from the same state
        have hreal' : ∀ r', dfsGo ops succs edgeMarks (ops.pop succs edgeMarks aux.1 step).1 rest = some r' →
            r'.1 = none := by
          intro r' h
          refine hreal r' ?_
          rw [dfsGo.eq_def]
          simp only [hidx, dite_false, hpop]
          rwa [hp1] at h
        by_cases hcl : V.closes aux.1 step
        · simp only [enumOps, hcl, if_true] at hr
          refine ih _ rest r hr hreal' (fun st hst => hsucc st (List.mem_cons_of_mem _ hst))
            (fun st hst => hreach st (List.mem_cons_of_mem _ hst))
            (SearchWF.popClose_step hlaw hstepsucc hidx hcl hwf) ?_
          intro p hp
          rcases Array.mem_push.mp hp with hp' | rfl
          · exact hrec.mono hR (hR.pop succs edgeMarks aux.1 step) p hp'
          · exact ⟨step, V.grayOf rest, hwf, hstepsucc, hidx, hcl, rfl,
              by show (ops.pop succs edgeMarks aux.1 step).2 = false; rw [hpop], hR.refl _⟩
        · simp only [enumOps, hcl] at hr
          exact ih _ rest r hr hreal' (fun st hst => hsucc st (List.mem_cons_of_mem _ hst))
            (fun st hst => hreach st (List.mem_cons_of_mem _ hst))
            (SearchWF.popMerge_step hlaw hstepsucc hidx (by simpa using hcl) hwf)
            (hrec.mono hR (hR.pop succs edgeMarks aux.1 step))
      -- a reporting POP would have made the real run report
      · have hx : dfsGo ops succs edgeMarks aux.1 (step :: rest) =
            some (some (step.state, ((step :: rest).map (·.state)).reverse), aux'') := by
          rw [dfsGo.eq_def]
          simp only [hidx, dite_false, hpop]
          rfl
        exact absurd (hreal _ hx) (by simp)
    case pos =>
      simp only [hidx, dite_true] at hr
      have hd : step.succ[step.idx] ∈ succs step.state := by
        rw [← hstepsucc]; exact Array.getElem_mem hidx
      have hedge : (succs step.state)[step.idx]? = some step.succ[step.idx] := by
        rw [← hstepsucc]; exact Array.getElem?_eq_getElem hidx
      cases hgs : ops.getStatus aux.1 step.succ[step.idx] with
      | dead =>
        simp only [enumOps_getStatus, hgs] at hr
        refine ih aux _ r hr (fun r' h => hreal r' ?_) hsucc' hreach' (SearchWF.bump_step hlaw hgs hedge hwf) hrec
        rw [dfsGo.eq_def]
        simp only [hidx, dite_true, hgs]
        exact h
      | live =>
        simp only [enumOps, hgs] at hr
        rcases hupd : ops.update aux.1 (edgeMarks step.state step.succ[step.idx]) step.succ[step.idx]
          with ⟨aux'', _ | _⟩
        · have hu1 : (ops.update aux.1 (edgeMarks step.state step.succ[step.idx]) step.succ[step.idx]).1
              = aux'' := by rw [hupd]
          refine ih _ _ r hr (fun r' h => hreal r' ?_) hsucc' hreach'
            (SearchWF.update_step hlaw hgs hedge rfl hwf) (hrec.mono hR (hR.update _ _ _))
          rw [dfsGo.eq_def]
          simp only [hidx, dite_true, hgs, hupd, Bool.false_eq_true, ↓reduceIte]
          rwa [hu1] at h
        -- a reporting UPDATE would have made the real run report
        · have hx : dfsGo ops succs edgeMarks aux.1 (step :: rest) =
              some (some (step.state,
                ((({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest).map (·.state)).reverse),
                aux'') := by
            rw [dfsGo.eq_def]
            simp only [hidx, dite_true, hgs, hupd, ↓reduceIte]
          exact absurd (hreal _ hx) (by simp)
      | unknown =>
        rcases hpush : ops.push aux.1 step.succ[step.idx] (edgeMarks step.state step.succ[step.idx])
          with ⟨aux'', pos'⟩
        simp only [enumOps, hgs, hpush] at hr
        have hstep := SearchWF.push_step hlaw hgs hedge rfl (Reachable.step (hreach step (by simp)) hd) hwf
        rw [hpush] at hstep
        have hmono := hR.push aux.1 step.succ[step.idx] (edgeMarks step.state step.succ[step.idx])
        rw [hpush] at hmono
        refine ih _ _ r hr (fun r' h => hreal r' ?_) ?_ ?_ hstep (hrec.mono hR hmono)
        · rw [dfsGo.eq_def]
          simp only [hidx, dite_true, hgs, hpush]
          exact h
        · intro st hst
          rcases List.mem_cons.mp hst with rfl | hst'
          · rfl
          · exact hsucc' st hst'
        · intro st hst
          rcases List.mem_cons.mp hst with rfl | hst'
          · exact Reachable.step (hreach step (by simp)) hd
          · exact hreach' st hst'

private theorem dfsFromRoot_recordedAt [Inhabited State] (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (hlaw : LowlinkLawful ops V) {R : ops.Aux → ops.Aux → Prop} (hR : MonotoneAlong ops R)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (aux : (enumOps ops V).Aux) (q0 : State)
    (hq0status : ops.getStatus aux.1 q0 = .unknown) (hq0 : Reachable initialStates succs q0)
    (hnone : (dfsFromRoot ops succs edgeMarks aux.1 q0).1 = none)
    (hwf : SearchWF ops V succs edgeMarks initialStates aux.1 [])
    (hrec : RecordedAt ops V succs edgeMarks initialStates R aux.2 aux.1) :
    RecordedAt ops V succs edgeMarks initialStates R (dfsFromRoot (enumOps ops V) succs edgeMarks aux q0).2.2
      (dfsFromRoot (enumOps ops V) succs edgeMarks aux q0).2.1 := by
  rw [dfsFromRoot_eq ops succs edgeMarks aux.1 q0] at hnone
  rw [dfsFromRoot_eq (enumOps ops V) succs edgeMarks aux q0]
  have hmono := hR.push aux.1 q0 (Std.HashSet.emptyWithCapacity 0)
  cases hdg : dfsGo (enumOps ops V) succs edgeMarks
      ((enumOps ops V).push aux q0 (Std.HashSet.emptyWithCapacity 0)).1
      [{ state := q0, pos := ((enumOps ops V).push aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
         acc := 0, succ := succs q0, idx := 0 }] with
  | none =>
    simp only [Option.getD_none]
    exact hrec.mono hR hmono
  | some r =>
    simp only [Option.getD_some]
    refine dfsGo_recordedAt ops V hlaw hR succs edgeMarks initialStates _ _ r hdg ?_
      (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; rfl)
      (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; exact hq0)
      (SearchWF.pushRoot_step hlaw hq0status hq0 hwf) (hrec.mono hR hmono)
    intro r' h
    have h' : dfsGo ops succs edgeMarks (ops.push aux.1 q0 (Std.HashSet.emptyWithCapacity 0)).1
        [{ state := q0, pos := (ops.push aux.1 q0 (Std.HashSet.emptyWithCapacity 0)).2,
           acc := 0, succ := succs q0, idx := 0 }] = some r' := h
    rw [h'] at hnone
    exact hnone

private theorem genericDFSGo_recordedAt [Inhabited State] (ops : DFSOps.{u,v,w} State)
    (V : LowlinkView ops) (hlaw : LowlinkLawful ops V) (L : LawfulDFSOps ops)
    {R : ops.Aux → ops.Aux → Prop} (hR : MonotoneAlong ops R)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs) :
    ∀ (roots : List State), (∀ q ∈ roots, Reachable initialStates succs q) →
      ∀ (aux : (enumOps ops V).Aux) rw' ru, L.WellFormed aux.1 →
        genericDFSGo (enumOps ops V) succs edgeMarks roots aux = some rw' →
        genericDFSGo ops succs edgeMarks roots aux.1 = some ru → ru.1 = none →
        EnumWF ops V succs edgeMarks initialStates aux.1 aux.2 [] →
        RecordedAt ops V succs edgeMarks initialStates R aux.2 aux.1 →
        RecordedAt ops V succs edgeMarks initialStates R rw'.2.2 rw'.2.1 := by
  intro roots
  induction roots with
  | nil =>
    intro _ aux rw' ru _ hw _ _ _ hrec
    rw [genericDFSGo.eq_def] at hw
    simp only [Option.some.injEq] at hw
    rw [← hw]
    exact hrec
  | cons q rest ih =>
    intro hroots aux rw' ru hwfL hw hu hnone hwf hrec
    have hq : Reachable initialStates succs q := hroots q (by simp)
    have hrest : ∀ q' ∈ rest, Reachable initialStates succs q' :=
      fun q' hq' => hroots q' (by simp [hq'])
    rw [genericDFSGo.eq_def] at hw hu
    cases hst : ops.getStatus aux.1 q with
    | unknown =>
      simp only [enumOps_getStatus, hst] at hw
      simp only [hst] at hu
      cases hf : (dfsFromRoot ops succs edgeMarks aux.1 q).1 with
      | some x =>
        exfalso
        simp only [hf, Option.some.injEq] at hu
        rw [← hu] at hnone
        simp at hnone
      | none =>
        obtain ⟨hfw, hbase⟩ := dfsFromRoot_base_eq ops V succs edgeMarks initialStates fr L
          aux q hwfL hst hq hf
        have hrec' := dfsFromRoot_recordedAt ops V hlaw hR succs edgeMarks initialStates aux q hst hq hf
          hwf.toSearchWF hrec
        have hwf' := dfsFromRoot_enumWF ops V hlaw L succs edgeMarks initialStates fr aux q hwfL hst hq hwf
        simp only [hf] at hu
        simp only [hfw] at hw
        refine ih hrest _ rw' ru ?_ hw (by rw [← hbase] at hu; exact hu) hnone hwf' hrec'
        rw [hbase]
        exact dfsFromRoot_wellFormed_total ops succs edgeMarks L aux.1 q hwfL hst
    | dead =>
      simp only [enumOps_getStatus, hst] at hw
      simp only [hst] at hu
      exact ih hrest aux rw' ru hwfL hw hu hnone hwf hrec
    | live =>
      simp only [enumOps_getStatus, hst] at hw
      simp only [hst] at hu
      exact ih hrest aux rw' ru hwfL hw hu hnone hwf hrec

/-- When the real run reports nothing, every flush the recording run made was a closing POP of the real run at which
the search invariant held and which did not report, and the real run finished `R`-ahead of it. -/
theorem enumRun_recordedAt [Inhabited State] (ops : DFSOps.{u,v,w} State) (V : LowlinkView ops)
    (hlaw : LowlinkLawful ops V) (L : LawfulDFSOps ops) (hwf0 : L.WellFormed ops.initAux)
    {R : ops.Aux → ops.Aux → Prop} (hR : MonotoneAlong ops R)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (initialStates : List State) (fr : FiniteReach initialStates succs)
    (hnone : (genericDFS ops succs edgeMarks initialStates ops.initAux).1 = none) :
    RecordedAt ops V succs edgeMarks initialStates R (enumRun ops V succs edgeMarks initialStates)
      (genericDFS ops succs edgeMarks initialStates ops.initAux).2 := by
  unfold enumRun
  unfold genericDFS at hnone ⊢
  obtain ⟨ru, hu⟩ := Option.ne_none_iff_exists'.mp
    (genericDFSGo_ne_none ops succs edgeMarks initialStates ops.initAux)
  obtain ⟨rw', hw⟩ := Option.ne_none_iff_exists'.mp
    (genericDFSGo_ne_none (enumOps ops V) succs edgeMarks initialStates (enumOps ops V).initAux)
  rw [hu] at hnone ⊢
  rw [hw]
  simp only [Option.getD_some] at hnone ⊢
  have heq := (genericDFSGo_base_eq ops V succs edgeMarks initialStates fr L initialStates
    (fun q hq => Reachable.base hq) (enumOps ops V).initAux rw' ru hwf0 hw hu hnone).2
  rw [← heq]
  exact genericDFSGo_recordedAt ops V hlaw L hR succs edgeMarks initialStates fr initialStates
    (fun q hq => Reachable.base hq) (enumOps ops V).initAux rw' ru hwf0 hw hu hnone
    (enumWF_init ops V hlaw succs edgeMarks initialStates) (fun p hp => by simp [enumOps] at hp)

end LTLLib
