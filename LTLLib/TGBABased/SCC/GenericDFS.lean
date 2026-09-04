/-
  Algorithm 1, a generic DFS skeleton parameterized by abstract PUSH/POP/GET_STATUS/UPDATE operations.
  `TarjanSCC.lean`/`DijkstraSCC.lean`/`GabowSCC.lean` each refine this by instantiating those four operations.
  Also defines generic witness extraction (`checkWithWitness`), shared by every refinement.

  Renault, Duret-Lutz, Kordon, Poitrenaud, "Three SCC-based Emptiness Checks for Generalized
  Büchi Automata" (LPAR-19, 2013).

  Input: A TGBA A = ⟨Q, q0, δ, F, f⟩
    states Q, initial state q0, transition relation δ, acceptance-mark set F,
    and f : δ → 2^F mapping each transition to the acceptance marks it carries.

  struct Step { acc : 2^F, pos : Position, succ : 2^δ }
  struct Transition { src : Q, dst : Q }
  dfs : stack of ⟨Step⟩

  Position pos ← PUSH(q0)
  dfs.push(⟨∅, pos, successors(q0)⟩)
  while ¬dfs.isEmpty()
    Step step ← dfs.top()
    if step.succ ≠ ∅
      Transition t ← pick one from step.succ
      switch GET_STATUS(t.dst) do
        case DEAD
          skip
        case LIVE
          UPDATE(f(t), t.dst)
        case UNKNOWN
          pos ← PUSH(t.dst)
          dfs.push(⟨f(t), pos, successors(t.dst)⟩)
    else
      dfs.pop()
      POP(step)

  Operations specialized by each refinement:
  - GET_STATUS: returns the status of a state (DEAD/LIVE/UNKNOWN).
  - PUSH: called for any newly visited state, marks it LIVE.
  - UPDATE: called on every back-edge (a transition to a LIVE state), detects a transition closing a cycle.
  - POP: called on every backtrack. When the last state of an SCC is popped (its "root", which may depend on
    visitation order), POP must mark every state in that SCC DEAD. It may also report a closed accepting cycle,
    for algorithms whose merge is lazy enough that UPDATE alone cannot always tell. Only Tarjan's does, it merges
    into the immediate parent frame on backtrack, whereas Dijkstra's and Gabow's merge eagerly inside UPDATE.

  Lean encoding notes:
  - `Transition.src` is always the owning `Step`'s own state, so `Step` carries an explicit `state` field rather
    than storing `src` on each pending successor, and `f(t)` is then just `edgeMarks step.state d`.
  - `dfs` is private to the generic driver here, not shared global state as in the paper, so `push` also takes the
    incoming transition's marks and `pop` takes the popped step's own `Position`. Whatever a refinement needs
    mirrored from `Step` it keeps in its own `Aux`, updated in lockstep with the driver's stack pushes and pops.

  `dfsGo` and `genericDFSGo` are `partial_fixpoint` definitions, where a `none` result denotes divergence.
  `dfsGo_ne_none`/`genericDFSGo_ne_none` rule that out, so the search terminates.

  Witness extraction (`checkWithWitness`): the search returns `some (anchor, stem)` with `stem` already a real
  path, and `ops.sccHint` supplies a known accepting subset that `WitnessExtraction.lean` rebuilds a cycle from.

  Sections:
  - Generic DFS operations
  - Generic DFS driver
  - Generic status-transition reachability
  - Witness-check driver
  - Termination
  - Witness-check correctness
-/

import Std
import LTLLib.AbstractSpec.EmptinessCheck
import LTLLib.TGBABased.SCC.WitnessExtraction

namespace LTLLib

/-! ## Generic DFS operations -/

inductive DFSStatus where
  | dead    -- All successors of the SCC it belongs to have been visited
  | live
  | unknown -- Not yet explored by DFS
deriving BEq, Repr, Inhabited

/-- The four operations (getStatus, PUSH, UPDATE, POP) a concrete SCC-based emptiness check must provide.  -/
structure DFSOps (State : Type u) [BEq State] [Hashable State] where
  Aux : Type v      -- Refinement's private search state
  Position : Type w -- What `PUSH` returns per state
  initAux : Aux

  getStatus : Aux → State → DFSStatus
  push : Aux → State → Std.HashSet Nat → Aux × Position -- `marks` are the incoming transition's acceptance marks (`f(t)`, `∅` for a root state).
  update : Aux → Std.HashSet Nat → State → Aux × Bool -- Reports whether the back-edge found a counterexample
  pop : Aux → Position → Aux × Bool -- reports whether backtracking closed an accepting cycle (Only Tarjan can do that)

  sccHint : Aux → Std.HashSet State -- A known, accepting SCC, but not necessarily maximal (Alg. may return early).
  numExplored : Aux → Nat -- Exists only for reporting to the user

/-- A frame on the generic DFS stack. Read bottom-to-top the stack is always a path from an initial
state to wherever the search is. `dfsGo` reads it off directly as the `.nonEmpty` stem. -/
structure DFSStep (State : Type u) (Position : Type w) where
  state : State
  pos : Position  -- what this frame's own `push` call returned
  acc : Std.HashSet Nat  -- unused by Dijkstra/Gabow (own `dfsInfo`/`dfs[r].acc` mirror instead), Tarjan's POP needs it
  -- `succ[idx..]` are the still-unexplored outgoing states, kept as `succs state` itself so a push allocates nothing extra
  succ : Array State
  idx : Nat

/-- A state list running backwards: each entry is a successor of the next, and the last is initial. -/
def RevPathFrom {State : Type u} (initialStates : List State) (succs : State → Array State)
    (l : List State) : Prop :=
  (∀ i, (hi : i + 1 < l.length) → l[i] ∈ succs l[i + 1]) ∧
  ∀ (h : l ≠ []), l.getLast h ∈ initialStates

/-- The driver stack read top-down, each frame's state a successor of the one below it and the outermost an
initial state. Preserved by every `dfsGo` step. -/
def DFSStackChain {State : Type u} {P : Type w} (initialStates : List State)
    (succs : State → Array State) (stack : List (DFSStep State P)) : Prop :=
  RevPathFrom initialStates succs (stack.map (·.state))

theorem RevPathFrom.tail {State : Type u} {initialStates : List State} {succs : State → Array State}
    {a : State} {l : List State} (h : RevPathFrom initialStates succs (a :: l)) :
    RevPathFrom initialStates succs l := by
  refine ⟨fun i hi => ?_, fun hne => ?_⟩
  · simpa using h.1 (i + 1) (by simp only [List.length_cons]; omega)
  · have := h.2 (by simp)
    rwa [List.getLast_cons hne] at this

theorem RevPathFrom.cons {State : Type u} {initialStates : List State} {succs : State → Array State}
    {a : State} {l : List State} (hne : l ≠ []) (hstep : a ∈ succs (l.head hne))
    (h : RevPathFrom initialStates succs l) : RevPathFrom initialStates succs (a :: l) := by
  refine ⟨fun i hi => ?_, fun _ => ?_⟩
  · cases i with
    | zero =>
      simpa [List.getElem_cons_zero, List.getElem_cons_succ, List.head_eq_getElem] using hstep
    | succ i' => simpa using h.1 i' (by simp only [List.length_cons] at hi; omega)
  · rw [List.getLast_cons hne]; exact h.2 hne

/-- Reversed, the stack is a forward path from an initial state to the top frame's state. -/
theorem RevPathFrom.stem {State : Type u} {initialStates : List State} {succs : State → Array State}
    {l : List State} (h : RevPathFrom initialStates succs l) (hne : l ≠ []) :
    ∃ hs : l.reverse ≠ [], l.reverse.head hs ∈ initialStates ∧
      (∀ i, (hi : i + 1 < l.reverse.length) → l.reverse[i + 1] ∈ succs (l.reverse[i])) ∧
      l.reverse.getLast hs = l.head hne := by
  refine ⟨by simpa using hne, ?_, fun i hi => ?_, by rw [List.getLast_reverse]⟩
  · rw [List.head_reverse]; exact h.2 hne
  · rw [List.length_reverse] at hi
    rw [List.getElem_reverse, List.getElem_reverse]
    have heq : l.length - 1 - (i + 1) + 1 = l.length - 1 - i := by omega
    have hmem := h.1 (l.length - 1 - (i + 1)) (by omega)
    simp only [heq] at hmem
    exact hmem

variable {State : Type u} [BEq State] [Hashable State]

/-- What a `DFSOps` refinement must satisfy for the generic theorems to apply. Deliberately holds neither `sccHint`'s
contract nor `pop_confirms_no_accepting_scc`, both need driver-level context no `Aux`-only `Prop` can see. -/
structure LawfulDFSOps {State : Type u} [BEq State] [Hashable State] (ops : DFSOps State) where
  -- a well-formedness predicate on the refinement's own `Aux`, preserved by all three operations
  WellFormed : ops.Aux → Prop
  wf_push : ∀ aux q marks, ops.getStatus aux q = .unknown → WellFormed aux →
    WellFormed (ops.push aux q marks).1
  wf_update : ∀ aux marks d, WellFormed aux → WellFormed (ops.update aux marks d).1
  wf_pop : ∀ aux pos, WellFormed aux → WellFormed (ops.pop aux pos).1
  -- `PUSH` marks its target live and touches nothing else
  push_status : ∀ aux q marks q', ops.getStatus (ops.push aux q marks).1 q' =
    if q' == q then .live else ops.getStatus aux q'
  -- `UPDATE` is pure bookkeeping
  update_status : ∀ aux marks d q, ops.getStatus (ops.update aux marks d).1 q = ops.getStatus aux q
  -- `POP` only ever promotes live states to dead
  pop_status : ∀ aux pos q, WellFormed aux →
    ops.getStatus (ops.pop aux pos).1 q = ops.getStatus aux q ∨
    (ops.getStatus aux q = .live ∧ ops.getStatus (ops.pop aux pos).1 q = .dead)

/-! ## Generic DFS driver -/

/-- Inner loop: drain the DFS stack from a single root, per Algorithm 1's `while ¬dfs.isEmpty()` loop.

On finding a cycle it returns `some (anchor, stem)`, the current stack root to `anchor`,
with `anchor` the closing back-edge's source, or the state receiving the merged info when `POP` reports. -/
def dfsGo (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) :
    ops.Aux → List (DFSStep State ops.Position) → Option (Option (State × List State) × ops.Aux)
  | aux, [] => some (none, aux)
  | aux, step :: rest =>
    if h : step.idx < step.succ.size then
      let d := step.succ[step.idx]
      let dfs' := { step with idx := step.idx + 1 } :: rest
      match ops.getStatus aux d with
      | .dead => dfsGo ops succs edgeMarks aux dfs'
      | .live =>
        let (aux', found) := ops.update aux (edgeMarks step.state d) d
        if found then
          let stem := (dfs'.map (·.state)).reverse
          some (some (step.state, stem), aux')
        else dfsGo ops succs edgeMarks aux' dfs'
      | .unknown =>
        let marks := edgeMarks step.state d
        let (aux', pos') := ops.push aux d marks
        let newStep : DFSStep State ops.Position :=
          { state := d, pos := pos', acc := marks, succ := succs d, idx := 0 }
        dfsGo ops succs edgeMarks aux' (newStep :: dfs')
    else
      let (aux', found) := ops.pop aux step.pos
      -- `rest = []` means `step` was this root's outermost frame, which has no parent to merge into and so is
      -- always its own SCC's root, never taking POP's found-reporting branch.
      match found, rest with
      | true, newTop :: _ => some (some (newTop.state, (rest.map (·.state)).reverse), aux')
      | _, _ => dfsGo ops succs edgeMarks aux' rest
partial_fixpoint -- The outer `Option` is never actually `none` (`dfsGo_ne_none`), proving Termination.

/-- Run the generic DFS from a single fresh root, per Algorithm 1's lines 5-6. -/
def dfsFromRoot (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (aux : ops.Aux) (q0 : State) :
    Option (State × List State) × ops.Aux :=
  let (aux', pos') := ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)
  let step : DFSStep State ops.Position :=
    { state := q0, pos := pos', acc := Std.HashSet.emptyWithCapacity 0,
      succ := succs q0, idx := 0 }
  -- The `getD` fallback is unreachable (`dfsGo_ne_none`), it keeps this total.
  (dfsGo ops succs edgeMarks aux' [step]).getD (none, aux')

/-- Outer loop over initial states, sharing search state across roots. -/
def genericDFSGo (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) :
    List State → ops.Aux → Option (Option (State × List State) × ops.Aux)
  | [], aux => some (none, aux)
  | q :: rest, aux =>
    match ops.getStatus aux q with
    | .unknown =>
      let (found?, aux') := dfsFromRoot ops succs edgeMarks aux q
      match found? with
      | some _ => some (found?, aux') -- Exit immediately on first counter example
      | none => genericDFSGo ops succs edgeMarks rest aux'
    | .dead | .live => genericDFSGo ops succs edgeMarks rest aux -- skipped, earlier root's search already touched it
partial_fixpoint -- Outer option is never none (`genericDFSGo_ne_none`), proving Termination.

def genericDFS (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (roots : List State) (aux : ops.Aux) :
    Option (State × List State) × ops.Aux :=
  (genericDFSGo ops succs edgeMarks roots aux).getD (none, aux)

/-! ## Generic status-transition reachability

Not a `LawfulDFSOps` field: whether a state ever got pushed, and why it is reachable,
is knowledge only `dfsGo`'s own recursion has, not `DFSOps`'s `Aux`-level operations.
Proved once here, generically. -/

private theorem stackReach_cons {succs : State → Array State} {initialStates : List State}
    {ops : DFSOps State} {hd : DFSStep State ops.Position} {tl : List (DFSStep State ops.Position)}
    (hhd : Reachable initialStates succs hd.state)
    (htl : ∀ st ∈ tl, Reachable initialStates succs st.state) :
    ∀ st ∈ hd :: tl, Reachable initialStates succs st.state := by
  intro st hst
  rcases List.mem_cons.mp hst with rfl | hst
  · exact hhd
  · exact htl st hst

private theorem stackSucc_cons {succs : State → Array State} {ops : DFSOps State}
    {hd : DFSStep State ops.Position} {tl : List (DFSStep State ops.Position)}
    (hhd : ∀ x ∈ hd.succ, x ∈ succs hd.state)
    (htl : ∀ st ∈ tl, ∀ x ∈ st.succ, x ∈ succs st.state) :
    ∀ st ∈ hd :: tl, ∀ x ∈ st.succ, x ∈ succs st.state := by
  intro st hst
  rcases List.mem_cons.mp hst with rfl | hst
  · exact hhd
  · exact htl st hst

/-- Whatever newly becomes non-`unknown` during a `dfsGo` run is reachable (given stack and succs are faithful). -/
theorem dfsGo_touched_reachable [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (hpush : ∀ aux q marks q', ops.getStatus (ops.push aux q marks).1 q' =
      if q' == q then .live else ops.getStatus aux q')
    (hupdate : ∀ aux marks d q, ops.getStatus (ops.update aux marks d).1 q = ops.getStatus aux q)
    (hpop : ∀ aux pos q, ops.getStatus (ops.pop aux pos).1 q = ops.getStatus aux q ∨
      (ops.getStatus aux q = .live ∧ ops.getStatus (ops.pop aux pos).1 q = .dead)) :
    ∀ aux (stack : List (DFSStep State ops.Position)) (r : Option (State × List State) × ops.Aux),
    dfsGo ops succs edgeMarks aux stack = some r →
    (∀ st ∈ stack, Reachable initialStates succs st.state) →
    (∀ st ∈ stack, ∀ x ∈ st.succ, x ∈ succs st.state) →
    ∀ s, ops.getStatus r.2 s ≠ .unknown →
      ops.getStatus aux s ≠ .unknown ∨ Reachable initialStates succs s := by
  refine dfsGo.partial_correctness ops succs edgeMarks
    (fun aux stack r =>
      (∀ st ∈ stack, Reachable initialStates succs st.state) →
      (∀ st ∈ stack, ∀ x ∈ st.succ, x ∈ succs st.state) →
      ∀ s, ops.getStatus r.2 s ≠ .unknown →
        ops.getStatus aux s ≠ .unknown ∨ Reachable initialStates succs s) ?_
  intro dfsGo ih aux stack r hr
  cases stack with
  | nil =>
    intro _ _ s hstatus
    simp only [Option.some.injEq] at hr
    rw [← hr] at hstatus
    exact Or.inl hstatus
  | cons step rest =>
  intro hreach hsuccInv s hstatus
  have hstepReach : Reachable initialStates succs step.state := hreach step (by simp)
  have hrestReach : ∀ st ∈ rest, Reachable initialStates succs st.state :=
    fun st hst => hreach st (List.mem_cons_of_mem _ hst)
  have hstepSucc : ∀ x ∈ step.succ, x ∈ succs step.state := hsuccInv step (by simp)
  have hrestSucc : ∀ st ∈ rest, ∀ x ∈ st.succ, x ∈ succs st.state :=
    fun st hst => hsuccInv st (List.mem_cons_of_mem _ hst)
  by_cases h : step.idx < step.succ.size
  case neg =>
    simp only [h, dite_false] at hr
    rcases hpopeq : ops.pop aux step.pos with ⟨aux', found⟩
    simp only [hpopeq] at hr
    cases found with
    | true =>
      cases rest with
      | nil =>
        simp only at hr
        rcases ih aux' [] r hr (by simp) (by simp) s hstatus with h1 | h1
        · rcases hpop aux step.pos s with h2 | ⟨h2, h3⟩
          · rw [hpopeq] at h2
            simp only at h2
            rw [h2] at h1
            exact Or.inl h1
          · exact Or.inl (by rw [h2]; simp)
        · exact Or.inr h1
      | cons newTop tail =>
        simp only [Option.some.injEq] at hr
        have hr2 : r.2 = aux' := by rw [← hr]
        have hstatus' : ops.getStatus aux' s ≠ .unknown := hr2 ▸ hstatus
        rcases hpop aux step.pos s with h1 | ⟨h1, h2⟩
        · rw [hpopeq] at h1
          simp only at h1
          rw [h1] at hstatus'
          exact Or.inl hstatus'
        · exact Or.inl (by rw [h1]; simp)
    | false =>
      simp only at hr
      rcases ih aux' rest r hr hrestReach hrestSucc s hstatus with h1 | h1
      · rcases hpop aux step.pos s with h2 | ⟨h2, h3⟩
        · rw [hpopeq] at h2
          simp only at h2
          rw [h2] at h1
          exact Or.inl h1
        · exact Or.inl (by rw [h2]; simp)
      · exact Or.inr h1
  case pos =>
  simp only [h, dite_true] at hr
  set d := step.succ[step.idx] with hd_def
  have hdReach : Reachable initialStates succs d :=
    Reachable.step hstepReach (hstepSucc _ (Array.getElem_mem h))
  have hdfs'Reach := stackReach_cons (succs := succs) (initialStates := initialStates)
    (hd := ({ step with idx := step.idx + 1 } : DFSStep State ops.Position)) (tl := rest)
    hstepReach hrestReach
  have hdfs'Succ := stackSucc_cons (succs := succs)
    (hd := ({ step with idx := step.idx + 1 } : DFSStep State ops.Position)) (tl := rest)
    hstepSucc hrestSucc
  cases hgs : ops.getStatus aux d with
  | dead =>
    simp only [hgs] at hr
    exact ih aux _ r hr hdfs'Reach hdfs'Succ s hstatus
  | live =>
    simp only [hgs] at hr
    rcases hupdeq : ops.update aux (edgeMarks step.state d) d with ⟨aux', found⟩
    simp only [hupdeq] at hr
    have haux'1 : (ops.update aux (edgeMarks step.state d) d).1 = aux' := congrArg Prod.fst hupdeq
    have hueq : ops.getStatus aux' s = ops.getStatus aux s := haux'1 ▸ hupdate aux (edgeMarks step.state d) d s
    by_cases hf : found = true
    · simp only [hf, if_true, Option.some.injEq] at hr
      rw [← hr] at hstatus
      simp only at hstatus
      rw [hueq] at hstatus
      exact Or.inl hstatus
    · simp only [hf] at hr
      rcases ih aux' _ r hr hdfs'Reach hdfs'Succ s hstatus with h1 | h1
      · rw [hueq] at h1
        exact Or.inl h1
      · exact Or.inr h1
  | unknown =>
    simp only [hgs] at hr
    rcases hpsheq : ops.push aux d (edgeMarks step.state d) with ⟨aux', pos'⟩
    simp only [hpsheq] at hr
    set hnewStep : DFSStep State ops.Position :=
      { state := d, pos := pos', acc := edgeMarks step.state d, succ := succs d, idx := 0 } with hnewStep_def
    have hnewReach := stackReach_cons (succs := succs) (initialStates := initialStates)
      (hd := hnewStep) (tl := ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest)
      hdReach hdfs'Reach
    have hnewSucc := stackSucc_cons (succs := succs)
      (hd := hnewStep) (tl := ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest)
      (fun x hx => hx) hdfs'Succ
    have haux'2 : (ops.push aux d (edgeMarks step.state d)).1 = aux' := congrArg Prod.fst hpsheq
    have hpeq : ops.getStatus aux' s = if s == d then .live else ops.getStatus aux s :=
      haux'2 ▸ hpush aux d (edgeMarks step.state d) s
    rcases ih aux' _ r hr hnewReach hnewSucc s hstatus with h1 | h1
    · rw [hpeq] at h1
      by_cases hsd : s == d
      · right
        have hse : s = d := by simpa using hsd
        rw [hse]
        exact hdReach
      · simp only [hsd] at h1
        exact Or.inl h1
    · exact Or.inr h1

/-- Status only ever moves forward along `dfsGo`'s recursion, never back to `.unknown`. -/
theorem dfsGo_status_monotone (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (L : LawfulDFSOps ops) :
    ∀ aux (stack : List (DFSStep State ops.Position)) (r : Option (State × List State) × ops.Aux),
    dfsGo ops succs edgeMarks aux stack = some r →
    L.WellFormed aux →
    ∀ s, ops.getStatus aux s ≠ .unknown → ops.getStatus r.2 s ≠ .unknown := by
  refine dfsGo.partial_correctness ops succs edgeMarks
    (fun aux stack r => L.WellFormed aux → ∀ s, ops.getStatus aux s ≠ .unknown → ops.getStatus r.2 s ≠ .unknown) ?_
  intro dfsGo ih aux stack r hr
  cases stack with
  | nil =>
    simp only [Option.some.injEq] at hr
    intro _ s hs
    rw [← hr]
    exact hs
  | cons step rest =>
  intro hwf
  by_cases h : step.idx < step.succ.size
  case neg =>
    simp only [h, dite_false] at hr
    rcases hpopeq : ops.pop aux step.pos with ⟨aux', found⟩
    simp only [hpopeq] at hr
    have L.pop_status' : ∀ s, ops.getStatus aux s ≠ .unknown → ops.getStatus aux' s ≠ .unknown := by
      intro s hs
      rcases L.pop_status aux step.pos s hwf with h1 | ⟨h1, h2⟩
      · rw [hpopeq] at h1; simp only at h1; rw [h1]; exact hs
      · rw [hpopeq] at h2; simp only at h2; rw [h2]; simp
    have haux'0 : (ops.pop aux step.pos).1 = aux' := congrArg Prod.fst hpopeq
    have hwf' : L.WellFormed aux' := haux'0 ▸ L.wf_pop aux step.pos hwf
    cases found with
    | true =>
      cases rest with
      | nil =>
        simp only at hr
        intro s hs
        exact ih aux' [] r hr hwf' s (L.pop_status' s hs)
      | cons newTop tail =>
        simp only [Option.some.injEq] at hr
        intro s hs
        have hr2 : r.2 = aux' := by rw [← hr]
        rw [hr2]; exact L.pop_status' s hs
    | false =>
      simp only at hr
      intro s hs
      exact ih aux' rest r hr hwf' s (L.pop_status' s hs)
  case pos =>
  simp only [h, dite_true] at hr
  set d := step.succ[step.idx]
  cases hgs : ops.getStatus aux d with
  | dead =>
    simp only [hgs] at hr
    exact ih aux _ r hr hwf
  | live =>
    simp only [hgs] at hr
    rcases hupdeq : ops.update aux (edgeMarks step.state d) d with ⟨aux', found⟩
    simp only [hupdeq] at hr
    have haux'1 : (ops.update aux (edgeMarks step.state d) d).1 = aux' := congrArg Prod.fst hupdeq
    have hueq : ∀ s, ops.getStatus aux' s = ops.getStatus aux s :=
      fun s => haux'1 ▸ L.update_status aux (edgeMarks step.state d) d s
    have hwf' : L.WellFormed aux' := haux'1 ▸ L.wf_update aux (edgeMarks step.state d) d hwf
    by_cases hf : found = true
    · simp only [hf, if_true, Option.some.injEq] at hr
      intro s hs
      rw [← hr]
      simp only
      rw [hueq]
      exact hs
    · simp only [hf] at hr
      intro s hs
      have := ih aux' _ r hr hwf' s (by rw [hueq]; exact hs)
      exact this
  | unknown =>
    simp only [hgs] at hr
    rcases hpsheq : ops.push aux d (edgeMarks step.state d) with ⟨aux', pos'⟩
    simp only [hpsheq] at hr
    have haux'2 : (ops.push aux d (edgeMarks step.state d)).1 = aux' := congrArg Prod.fst hpsheq
    have hpeq : ∀ s, ops.getStatus aux' s = if s == d then .live else ops.getStatus aux s :=
      fun s => haux'2 ▸ L.push_status aux d (edgeMarks step.state d) s
    have hwf' : L.WellFormed aux' := haux'2 ▸ L.wf_push aux d (edgeMarks step.state d) hgs hwf
    intro s hs
    refine ih aux' _ r hr hwf' s ?_
    rw [hpeq]
    by_cases hsd : s == d
    · simp [hsd]
    · simp only [hsd]; exact hs

/-- `dfsGo_touched_reachable` specialized to `dfsFromRoot`'s own call shape. -/
theorem dfsFromRoot_touched_reachable [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (hpush : ∀ aux q marks q', ops.getStatus (ops.push aux q marks).1 q' =
      if q' == q then .live else ops.getStatus aux q')
    (hupdate : ∀ aux marks d q, ops.getStatus (ops.update aux marks d).1 q = ops.getStatus aux q)
    (hpop : ∀ aux pos q, ops.getStatus (ops.pop aux pos).1 q = ops.getStatus aux q ∨
      (ops.getStatus aux q = .live ∧ ops.getStatus (ops.pop aux pos).1 q = .dead))
    (aux : ops.Aux) (q0 : State) (hq0 : Reachable initialStates succs q0) (s : State)
    (hstatus : ops.getStatus (dfsFromRoot ops succs edgeMarks aux q0).2 s ≠ .unknown) :
    ops.getStatus aux s ≠ .unknown ∨ Reachable initialStates succs s := by
  unfold dfsFromRoot at hstatus
  rw [show ops.push aux q0 (Std.HashSet.emptyWithCapacity 0) =
      ((ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1, (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2)
      from rfl] at hstatus
  simp only at hstatus
  set aux' := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1 with haux'
  set step : DFSStep State ops.Position :=
    { state := q0, pos := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
      acc := Std.HashSet.emptyWithCapacity 0, succ := succs q0, idx := 0 } with hstep
  have hpeq : ops.getStatus aux' s = if s == q0 then .live else ops.getStatus aux s := by
    rw [haux']
    exact hpush aux q0 (Std.HashSet.emptyWithCapacity 0) s
  have hresolve : ops.getStatus aux' s ≠ .unknown → ops.getStatus aux s ≠ .unknown ∨ Reachable initialStates succs s := by
    intro h1
    rw [hpeq] at h1
    by_cases hsq : s == q0
    · right
      have hse : s = q0 := by simpa using hsq
      rw [hse]; exact hq0
    · simp only [hsq] at h1
      exact Or.inl h1
  cases hdg : dfsGo ops succs edgeMarks aux' [step] with
  | none =>
    rw [hdg] at hstatus
    simp only [Option.getD_none] at hstatus
    exact hresolve hstatus
  | some r =>
    rw [hdg] at hstatus
    simp only [Option.getD_some] at hstatus
    have hstackReach : ∀ st ∈ [step], Reachable initialStates succs st.state := by
      intro st hst
      simp only [List.mem_singleton] at hst
      rw [hst, hstep]
      exact hq0
    have hstackSucc : ∀ st ∈ [step], ∀ x ∈ st.succ, x ∈ succs st.state := by
      intro st hst
      simp only [List.mem_singleton] at hst
      rw [hst, hstep]
      exact fun x hx => hx
    rcases dfsGo_touched_reachable ops succs edgeMarks initialStates hpush hupdate hpop
      aux' [step] r hdg hstackReach hstackSucc s hstatus with h1 | h1
    · exact hresolve h1
    · exact Or.inr h1

/-- The reported `stem` is a path from an initial state to the reported anchor. -/
theorem dfsGo_stem_path [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) :
    ∀ aux (stack : List (DFSStep State ops.Position)) r,
    dfsGo ops succs edgeMarks aux stack = some r →
    (∀ st ∈ stack, st.succ = succs st.state) →
    DFSStackChain initialStates succs stack →
    ∀ anchor stem, r.1 = some (anchor, stem) →
      ∃ hs : stem ≠ [], stem.head hs ∈ initialStates ∧
        (∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs (stem[i])) ∧
        stem.getLast hs = anchor := by
  refine dfsGo.partial_correctness ops succs edgeMarks
    (fun aux stack r =>
      (∀ st ∈ stack, st.succ = succs st.state) →
      DFSStackChain initialStates succs stack →
      ∀ anchor stem, r.1 = some (anchor, stem) →
        ∃ hs : stem ≠ [], stem.head hs ∈ initialStates ∧
          (∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs (stem[i])) ∧
          stem.getLast hs = anchor) ?_
  intro go ih aux stack r hr
  cases stack with
  | nil =>
    simp only [Option.some.injEq] at hr
    intro _ _ _ _ heq
    rw [← hr] at heq
    exact absurd heq (by simp)
  | cons step rest =>
  intro hsucceq hchain
  have hstepSucc : step.succ = succs step.state := hsucceq step (by simp)
  have hchainBump : DFSStackChain initialStates succs
      (({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest) := by
    simpa [DFSStackChain] using hchain
  have hsucceqBump : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
      st.succ = succs st.state := by
    intro st hst
    rcases List.mem_cons.mp hst with rfl | hst
    · exact hstepSucc
    · exact hsucceq st (List.mem_cons_of_mem _ hst)
  by_cases h : step.idx < step.succ.size
  case pos =>
    simp only [h, dite_true] at hr
    set d := step.succ[step.idx] with hd_def
    have hdSucc : d ∈ succs step.state := hstepSucc ▸ Array.getElem_mem h
    cases hgs : ops.getStatus aux d with
    | dead => simp only [hgs] at hr; exact ih aux _ r hr hsucceqBump hchainBump
    | live =>
      simp only [hgs] at hr
      rcases hupdeq : ops.update aux (edgeMarks step.state d) d with ⟨aux', found⟩
      simp only [hupdeq] at hr
      by_cases hf : found = true
      -- the closing back-edge's own frame is the anchor, and the live stack is the stem
      · simp only [hf, if_true, Option.some.injEq] at hr
        intro anchor stem heq
        rw [← hr] at heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨hs, hhead, hpath, hlast⟩ := hchainBump.stem (by simp)
        rw [← heq.2]
        exact ⟨hs, hhead, hpath, by rw [hlast, ← heq.1]; simp⟩
      · simp only [hf] at hr; exact ih aux' _ r hr hsucceqBump hchainBump
    | unknown =>
      simp only [hgs] at hr
      rcases L.push_status : ops.push aux d (edgeMarks step.state d) with ⟨aux', pos'⟩
      simp only [L.push_status] at hr
      refine ih aux' _ r hr ?_ ?_
      · intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · rfl
        · exact hsucceqBump st hst
      · exact hchainBump.cons (by simp) (by simpa using hdSucc)
  case neg =>
    simp only [h, dite_false] at hr
    rcases hpopeq : ops.pop aux step.pos with ⟨aux', found⟩
    simp only [hpopeq] at hr
    have hchainTail : DFSStackChain initialStates succs rest := hchain.tail
    have hsucceqTail : ∀ st ∈ rest, st.succ = succs st.state :=
      fun st hst => hsucceq st (List.mem_cons_of_mem _ hst)
    cases hf : found with
    | false => simp only [hf] at hr; exact ih aux' rest r hr hsucceqTail hchainTail
    | true =>
      cases hrest : rest with
      | nil => simp only [hf, hrest] at hr; exact ih aux' [] r hr (by simp) (by simp [DFSStackChain, RevPathFrom])
      -- POP reported it: the popped frame is gone, so the new top of the stack anchors the stem
      | cons newTop rest' =>
        simp only [hf, hrest, Option.some.injEq] at hr
        intro anchor stem heq
        rw [← hr] at heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨hs, hhead, hpath, hlast⟩ :=
          (show DFSStackChain initialStates succs (newTop :: rest') from hrest ▸ hchainTail).stem (by simp)
        rw [← heq.2]
        exact ⟨hs, hhead, hpath, by rw [hlast, ← heq.1]; simp⟩

/-- One-hop closure: once a `dfsGo` run completes with no cycle found, any state already non-`unknown` and no longer
on the stack has every one of its `succs` non-`unknown` too. -/
theorem dfsGo_closed [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (L : LawfulDFSOps ops) :
    ∀ aux (stack : List (DFSStep State ops.Position)) (r : Option (State × List State) × ops.Aux),
    dfsGo ops succs edgeMarks aux stack = some r →
    r.1 = none →
    L.WellFormed aux →
    (∀ st ∈ stack, st.succ = succs st.state) →
    (∀ st ∈ stack, ∀ x ∈ (st.succ.toList.take st.idx), ops.getStatus aux x ≠ .unknown) →
    (∀ t, ops.getStatus aux t ≠ .unknown → (∀ st ∈ stack, st.state ≠ t) →
      ∀ x ∈ succs t, ops.getStatus aux x ≠ .unknown) →
    ∀ t, ops.getStatus r.2 t ≠ .unknown → ∀ x ∈ succs t, ops.getStatus r.2 x ≠ .unknown := by
  refine dfsGo.partial_correctness ops succs edgeMarks
    (fun aux stack r => r.1 = none → L.WellFormed aux →
      (∀ st ∈ stack, st.succ = succs st.state) →
      (∀ st ∈ stack, ∀ x ∈ (st.succ.toList.take st.idx), ops.getStatus aux x ≠ .unknown) →
      (∀ t, ops.getStatus aux t ≠ .unknown → (∀ st ∈ stack, st.state ≠ t) →
        ∀ x ∈ succs t, ops.getStatus aux x ≠ .unknown) →
      ∀ t, ops.getStatus r.2 t ≠ .unknown → ∀ x ∈ succs t, ops.getStatus r.2 x ≠ .unknown) ?_
  intro dfsGo ih aux stack r hr
  cases stack with
  | nil =>
    simp only [Option.some.injEq] at hr
    intro _ _ _ _ hClosed t ht x hx
    rw [← hr] at ht
    have h1 := hClosed t ht (by simp) x hx
    rw [← hr]
    exact h1
  | cons step rest =>
  intro hnone hwf hsucceq hprefix hClosed
  have hstepSuccEq : step.succ = succs step.state := hsucceq step (by simp)
  have hrestSuccEq : ∀ st ∈ rest, st.succ = succs st.state :=
    fun st hst => hsucceq st (List.mem_cons_of_mem _ hst)
  have hstepPrefix : ∀ x ∈ (step.succ.toList.take step.idx), ops.getStatus aux x ≠ .unknown :=
    hprefix step (by simp)
  have hrestPrefix : ∀ st ∈ rest, ∀ x ∈ (st.succ.toList.take st.idx), ops.getStatus aux x ≠ .unknown :=
    fun st hst => hprefix st (List.mem_cons_of_mem _ hst)
  by_cases h : step.idx < step.succ.size
  case pos =>
    simp only [h, dite_true] at hr
    set d := step.succ[step.idx] with hd_def
    have hdTake : step.succ.toList.take (step.idx + 1) = step.succ.toList.take step.idx ++ [d] := by
      rw [List.take_add_one]; congr 1; simp [hd_def]
    cases hgs : ops.getStatus aux d with
    | dead =>
      simp only [hgs] at hr
      have hSuccEq' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
          st.succ = succs st.state := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · exact hstepSuccEq
        · exact hrestSuccEq st hst
      have hPrefix' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
          ∀ x ∈ (st.succ.toList.take st.idx), ops.getStatus aux x ≠ .unknown := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · show ∀ x ∈ step.succ.toList.take (step.idx + 1), ops.getStatus aux x ≠ .unknown
          rw [hdTake]
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hstepPrefix x hx
          · simp only [List.mem_singleton] at hx
            rw [hx]; exact hgs ▸ (by simp)
        · exact hrestPrefix st hst
      have hClosed' : ∀ t, ops.getStatus aux t ≠ .unknown →
          (∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest, st.state ≠ t) →
          ∀ x ∈ succs t, ops.getStatus aux x ≠ .unknown := by
        intro t ht hexcl x hx
        refine hClosed t ht ?_ x hx
        intro st hst
        rcases List.mem_cons.mp hst with heq | hst
        · rw [heq]; exact hexcl { step with idx := step.idx + 1 } (by simp)
        · exact hexcl _ (List.mem_cons_of_mem _ hst)
      exact ih aux _ r hr hnone hwf hSuccEq' hPrefix' hClosed'
    | live =>
      simp only [hgs] at hr
      rcases hupdeq : ops.update aux (edgeMarks step.state d) d with ⟨aux', found⟩
      simp only [hupdeq] at hr
      have haux'1 : (ops.update aux (edgeMarks step.state d) d).1 = aux' := congrArg Prod.fst hupdeq
      have hueq : ∀ s, ops.getStatus aux' s = ops.getStatus aux s :=
        fun s => haux'1 ▸ L.update_status aux (edgeMarks step.state d) d s
      by_cases hf : found = true
      · exfalso
        simp only [hf, if_true, Option.some.injEq] at hr
        rw [← hr] at hnone
        simp at hnone
      · simp only [hf] at hr
        have hwf' : L.WellFormed aux' := haux'1 ▸ L.wf_update aux (edgeMarks step.state d) d hwf
        have hSuccEq' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
            st.succ = succs st.state := by
          intro st hst
          rcases List.mem_cons.mp hst with rfl | hst
          · exact hstepSuccEq
          · exact hrestSuccEq st hst
        have hPrefix' : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
            ∀ x ∈ (st.succ.toList.take st.idx), ops.getStatus aux' x ≠ .unknown := by
          intro st hst
          rcases List.mem_cons.mp hst with rfl | hst
          · show ∀ x ∈ step.succ.toList.take (step.idx + 1), ops.getStatus aux' x ≠ .unknown
            rw [hdTake]
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · simp only [hueq]; exact hstepPrefix x hx
            · simp only [List.mem_singleton] at hx
              rw [hx]; simp only [hueq]; simp [hgs]
          · simp only [hueq]; exact hrestPrefix st hst
        have hClosed' : ∀ t, ops.getStatus aux' t ≠ .unknown →
            (∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest, st.state ≠ t) →
            ∀ x ∈ succs t, ops.getStatus aux' x ≠ .unknown := by
          intro t ht hexcl x hx
          simp only [hueq] at ht
          simp only [hueq]
          refine hClosed t ht ?_ x hx
          intro st hst
          rcases List.mem_cons.mp hst with heq | hst
          · rw [heq]; exact hexcl { step with idx := step.idx + 1 } (by simp)
          · exact hexcl _ (List.mem_cons_of_mem _ hst)
        exact ih aux' _ r hr hnone hwf' hSuccEq' hPrefix' hClosed'
    | unknown =>
      simp only [hgs] at hr
      rcases hpsheq : ops.push aux d (edgeMarks step.state d) with ⟨aux', pos'⟩
      simp only [hpsheq] at hr
      have haux'2 : (ops.push aux d (edgeMarks step.state d)).1 = aux' := congrArg Prod.fst hpsheq
      have hpeq : ∀ s, ops.getStatus aux' s = if s == d then .live else ops.getStatus aux s :=
        fun s => haux'2 ▸ L.push_status aux d (edgeMarks step.state d) s
      have hwf' : L.WellFormed aux' := haux'2 ▸ L.wf_push aux d (edgeMarks step.state d) hgs hwf
      set newStep : DFSStep State ops.Position :=
        { state := d, pos := pos', acc := edgeMarks step.state d, succ := succs d, idx := 0 } with hnewStep_def
      have hSuccEq' : ∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
          st.succ = succs st.state := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · rw [hnewStep_def]
        · rcases List.mem_cons.mp hst with rfl | hst
          · exact hstepSuccEq
          · exact hrestSuccEq st hst
      have hPrefix' : ∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
          ∀ x ∈ (st.succ.toList.take st.idx), ops.getStatus aux' x ≠ .unknown := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · rw [hnewStep_def]; simp
        · rcases List.mem_cons.mp hst with rfl | hst
          · show ∀ x ∈ step.succ.toList.take (step.idx + 1), ops.getStatus aux' x ≠ .unknown
            rw [hdTake]
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · have hxne : x ≠ d := by
                intro hxeq; rw [hxeq] at hx; exact hstepPrefix d hx hgs
              simp only [hpeq, beq_iff_eq, hxne, if_false]
              exact hstepPrefix x hx
            · simp only [List.mem_singleton] at hx
              rw [hx]; simp only [hpeq]; simp
          · intro x hx
            simp only [hpeq]
            have hxne : x ≠ d := by
              intro hxeq; rw [hxeq] at hx; exact hrestPrefix st hst d hx hgs
            simp only [beq_iff_eq, hxne, if_false]
            exact hrestPrefix st hst x hx
      have hClosed' : ∀ t, ops.getStatus aux' t ≠ .unknown →
          (∀ st ∈ newStep :: ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
            st.state ≠ t) →
          ∀ x ∈ succs t, ops.getStatus aux' x ≠ .unknown := by
        intro t ht hexcl x hx
        by_cases htd : t == d
        · exfalso
          have hteq : t = d := by simpa using htd
          have hns : newStep.state = t := by rw [hnewStep_def]; exact hteq.symm
          exact (hexcl newStep (by simp)) hns
        · simp only [hpeq, htd] at ht
          have hxeq : ops.getStatus aux x ≠ .unknown := hClosed t ht (by
            intro st hst
            by_cases hstd : st = step
            · rw [hstd]
              exact hexcl { step with idx := step.idx + 1 } (by simp)
            · have hst' : st ∈ rest := by
                rcases List.mem_cons.mp hst with heq | hst'
                · exact absurd heq hstd
                · exact hst'
              exact hexcl st (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hst'))) x hx
          simp only [hpeq]
          by_cases hxd : x == d
          · simp [hxd]
          · simp only [hxd]; exact hxeq
      exact ih aux' _ r hr hnone hwf' hSuccEq' hPrefix' hClosed'
  case neg =>
    simp only [h, dite_false] at hr
    rcases hpopeq : ops.pop aux step.pos with ⟨aux', found⟩
    simp only [hpopeq] at hr
    have L.pop_status' : ∀ q, ops.getStatus aux q ≠ .unknown → ops.getStatus aux' q ≠ .unknown := by
      intro q hq
      rcases L.pop_status aux step.pos q hwf with h1 | ⟨h1, h2⟩
      · rw [hpopeq] at h1; simp only at h1; rw [h1]; exact hq
      · rw [hpopeq] at h2; simp only at h2; rw [h2]; simp
    have L.pop_status'' : ∀ q, ops.getStatus aux' q ≠ .unknown → ops.getStatus aux q ≠ .unknown := by
      intro q hq
      rcases L.pop_status aux step.pos q hwf with h1 | ⟨h1, h2⟩
      · rw [hpopeq] at h1; simp only at h1; rw [← h1]; exact hq
      · rw [hpopeq] at h2; simp only at h2; rw [h1]; simp
    have haux'0 : (ops.pop aux step.pos).1 = aux' := congrArg Prod.fst hpopeq
    have hwf' : L.WellFormed aux' := haux'0 ▸ L.wf_pop aux step.pos hwf
    have hcrux : ∀ x ∈ succs step.state, ops.getStatus aux' x ≠ .unknown := by
      have hidxge : step.succ.size ≤ step.idx := Nat.le_of_not_lt h
      have hfull : step.succ.toList.take step.idx = step.succ.toList := by
        apply List.take_of_length_le; simpa using hidxge
      have h1 := hstepPrefix
      rw [hfull] at h1
      intro x hx
      apply L.pop_status'
      apply h1
      rw [← hstepSuccEq] at hx
      simpa using hx
    cases found with
    | true =>
      cases rest with
      | nil =>
        simp only at hr
        have hClosed' : ∀ t, ops.getStatus aux' t ≠ .unknown →
            (∀ st ∈ ([] : List (DFSStep State ops.Position)), st.state ≠ t) →
            ∀ x ∈ succs t, ops.getStatus aux' x ≠ .unknown := by
          intro t ht _ x hx
          by_cases hts : t = step.state
          · rw [hts] at hx; exact hcrux x hx
          · refine L.pop_status' x (hClosed t (L.pop_status'' t ht) ?_ x hx)
            intro st hst
            simp only [List.mem_singleton] at hst
            rw [hst]
            exact fun heq => hts heq.symm
        exact ih aux' [] r hr hnone hwf' (by simp) (by simp) hClosed'
      | cons newTop tail =>
        exfalso
        simp only [Option.some.injEq] at hr
        rw [← hr] at hnone
        simp at hnone
    | false =>
      simp only at hr
      have hPrefix' : ∀ st ∈ rest, ∀ x ∈ (st.succ.toList.take st.idx), ops.getStatus aux' x ≠ .unknown := by
        intro st hst x hx
        exact L.pop_status' x (hrestPrefix st hst x hx)
      have hClosed' : ∀ t, ops.getStatus aux' t ≠ .unknown → (∀ st ∈ rest, st.state ≠ t) →
          ∀ x ∈ succs t, ops.getStatus aux' x ≠ .unknown := by
        intro t ht hexcl x hx
        by_cases hts : t = step.state
        · rw [hts] at hx; exact hcrux x hx
        · exact L.pop_status' x (hClosed t (L.pop_status'' t ht) (fun st hst => by
            by_cases hse : st = step
            · rw [hse]; exact fun heq => hts heq.symm
            · have hst' : st ∈ rest := by
                rcases List.mem_cons.mp hst with heq | hst'
                · exact absurd heq hse
                · exact hst'
              exact hexcl st hst') x hx)
      exact ih aux' rest r hr hnone hwf' hrestSuccEq hPrefix' hClosed'

/-- `dfsGo_closed` specialized to `dfsFromRoot`'s own call shape, with `q0` being `.unknown`. -/
theorem dfsFromRoot_closed [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (L : LawfulDFSOps ops)
    (aux : ops.Aux) (q0 : State) (hwf : L.WellFormed aux) (hq0 : ops.getStatus aux q0 = .unknown)
    (hClosed0 : ∀ t, ops.getStatus aux t ≠ .unknown → ∀ x ∈ succs t, ops.getStatus aux x ≠ .unknown)
    -- Taken as a hypothesis so this stays generic over `ops`, refinements discharge it via `dfsGo_ne_none`.
    (hReal : dfsGo ops succs edgeMarks (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1
      [({ state := q0, pos := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
          acc := Std.HashSet.emptyWithCapacity 0, succ := succs q0, idx := 0 } :
        DFSStep State ops.Position)] ≠ none)
    (hnone : (dfsFromRoot ops succs edgeMarks aux q0).1 = none) :
    ∀ t, ops.getStatus (dfsFromRoot ops succs edgeMarks aux q0).2 t ≠ .unknown →
      ∀ x ∈ succs t, ops.getStatus (dfsFromRoot ops succs edgeMarks aux q0).2 x ≠ .unknown := by
  unfold dfsFromRoot at hnone ⊢
  rw [show ops.push aux q0 (Std.HashSet.emptyWithCapacity 0) =
      ((ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1, (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2)
      from rfl] at hnone ⊢
  simp only at hnone ⊢
  set aux' := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1 with haux'
  set step : DFSStep State ops.Position :=
    { state := q0, pos := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
      acc := Std.HashSet.emptyWithCapacity 0, succ := succs q0, idx := 0 } with hstep
  have hwf' : L.WellFormed aux' := by
    rw [haux']; exact L.wf_push aux q0 (Std.HashSet.emptyWithCapacity 0) hq0 hwf
  have hpeq : ∀ s, ops.getStatus aux' s = if s == q0 then .live else ops.getStatus aux s := by
    rw [haux']; exact L.push_status aux q0 (Std.HashSet.emptyWithCapacity 0)
  have hClosed0' : ∀ t, ops.getStatus aux' t ≠ .unknown → (∀ st ∈ [step], st.state ≠ t) →
      ∀ x ∈ succs t, ops.getStatus aux' x ≠ .unknown := by
    intro t ht hexcl x hx
    have htq : t ≠ q0 := fun heq => hexcl step (by simp) (by rw [hstep]; exact heq.symm)
    simp only [hpeq, beq_iff_eq, htq, if_false] at ht
    have hxeq : ops.getStatus aux x ≠ .unknown := hClosed0 t ht x hx
    rw [hpeq]
    by_cases hxq : x == q0
    · simp [hxq]
    · simp only [hxq]; exact hxeq
  cases hdg : dfsGo ops succs edgeMarks aux' [step] with
  | none => exact absurd hdg hReal
  | some r =>
    simp only [hdg, Option.getD_some] at hnone ⊢
    have hsucceq : ∀ st ∈ [step], st.succ = succs st.state := by
      intro st hst; simp only [List.mem_singleton] at hst; rw [hst, hstep]
    have hprefix : ∀ st ∈ [step], ∀ x ∈ (st.succ.toList.take st.idx), ops.getStatus aux' x ≠ .unknown := by
      intro st hst; simp only [List.mem_singleton] at hst; rw [hst, hstep]; simp
    exact dfsGo_closed ops succs edgeMarks L
      aux' [step] r hdg hnone hwf' hsucceq hprefix hClosed0'

/-- `L.WellFormed` is preserved by a full `dfsGo` run. -/
theorem dfsGo_wellFormed (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (L : LawfulDFSOps ops) :
    ∀ aux (stack : List (DFSStep State ops.Position)) (r : Option (State × List State) × ops.Aux),
    dfsGo ops succs edgeMarks aux stack = some r → L.WellFormed aux → L.WellFormed r.2 := by
  refine dfsGo.partial_correctness ops succs edgeMarks
    (fun aux stack r => L.WellFormed aux → L.WellFormed r.2) ?_
  intro dfsGo ih aux stack r hr
  cases stack with
  | nil =>
    simp only [Option.some.injEq] at hr
    intro hwf; rw [← hr]; exact hwf
  | cons step rest =>
  intro hwf
  by_cases h : step.idx < step.succ.size
  case pos =>
    simp only [h, dite_true] at hr
    set d := step.succ[step.idx]
    cases hgs : ops.getStatus aux d with
    | dead => simp only [hgs] at hr; exact ih aux _ r hr hwf
    | live =>
      simp only [hgs] at hr
      rcases hupdeq : ops.update aux (edgeMarks step.state d) d with ⟨aux', found⟩
      simp only [hupdeq] at hr
      have haux'1 : (ops.update aux (edgeMarks step.state d) d).1 = aux' := congrArg Prod.fst hupdeq
      have hwf' : L.WellFormed aux' := haux'1 ▸ L.wf_update aux (edgeMarks step.state d) d hwf
      by_cases hf : found = true
      · simp only [hf, if_true, Option.some.injEq] at hr; rw [← hr]; exact hwf'
      · simp only [hf] at hr; exact ih aux' _ r hr hwf'
    | unknown =>
      simp only [hgs] at hr
      rcases hpsheq : ops.push aux d (edgeMarks step.state d) with ⟨aux', pos'⟩
      simp only [hpsheq] at hr
      have haux'2 : (ops.push aux d (edgeMarks step.state d)).1 = aux' := congrArg Prod.fst hpsheq
      have hwf' : L.WellFormed aux' := haux'2 ▸ L.wf_push aux d (edgeMarks step.state d) hgs hwf
      exact ih aux' _ r hr hwf'
  case neg =>
    simp only [h, dite_false] at hr
    rcases hpopeq : ops.pop aux step.pos with ⟨aux', found⟩
    simp only [hpopeq] at hr
    have haux'0 : (ops.pop aux step.pos).1 = aux' := congrArg Prod.fst hpopeq
    have hwf' : L.WellFormed aux' := haux'0 ▸ L.wf_pop aux step.pos hwf
    cases found with
    | true =>
      cases rest with
      | nil => simp only at hr; exact ih aux' [] r hr hwf'
      | cons newTop tail => simp only [Option.some.injEq] at hr; rw [← hr]; exact hwf'
    | false => simp only at hr; exact ih aux' rest r hr hwf'

theorem dfsFromRoot_wellFormed [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (L : LawfulDFSOps ops)
    (aux : ops.Aux) (q0 : State) (hwf : L.WellFormed aux) (hq0 : ops.getStatus aux q0 = .unknown)
    (hReal : dfsGo ops succs edgeMarks (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1
      [({ state := q0, pos := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
          acc := Std.HashSet.emptyWithCapacity 0, succ := succs q0, idx := 0 } :
        DFSStep State ops.Position)] ≠ none) :
    L.WellFormed (dfsFromRoot ops succs edgeMarks aux q0).2 := by
  unfold dfsFromRoot
  rw [show ops.push aux q0 (Std.HashSet.emptyWithCapacity 0) =
      ((ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1, (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2)
      from rfl]
  simp only
  set aux' := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1 with haux'
  set step : DFSStep State ops.Position :=
    { state := q0, pos := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
      acc := Std.HashSet.emptyWithCapacity 0, succ := succs q0, idx := 0 } with hstep
  have hwf' : L.WellFormed aux' := by
    rw [haux']; exact L.wf_push aux q0 (Std.HashSet.emptyWithCapacity 0) hq0 hwf
  cases hdg : dfsGo ops succs edgeMarks aux' [step] with
  | none => exact absurd hdg hReal
  | some r =>
    simp only [Option.getD_some]
    exact dfsGo_wellFormed ops succs edgeMarks L
      aux' [step] r hdg hwf'

theorem dfsFromRoot_status_monotone [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (L : LawfulDFSOps ops)
    (aux : ops.Aux) (q0 : State) (hwf : L.WellFormed aux) (hq0 : ops.getStatus aux q0 = .unknown)
    (hReal : dfsGo ops succs edgeMarks (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1
      [({ state := q0, pos := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
          acc := Std.HashSet.emptyWithCapacity 0, succ := succs q0, idx := 0 } :
        DFSStep State ops.Position)] ≠ none) :
    ∀ s, ops.getStatus aux s ≠ .unknown →
      ops.getStatus (dfsFromRoot ops succs edgeMarks aux q0).2 s ≠ .unknown := by
  unfold dfsFromRoot
  rw [show ops.push aux q0 (Std.HashSet.emptyWithCapacity 0) =
      ((ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1, (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2)
      from rfl]
  simp only
  set aux' := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1 with haux'
  set step : DFSStep State ops.Position :=
    { state := q0, pos := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
      acc := Std.HashSet.emptyWithCapacity 0, succ := succs q0, idx := 0 } with hstep
  have hpeq : ∀ s, ops.getStatus aux' s = if s == q0 then .live else ops.getStatus aux s := by
    rw [haux']; exact L.push_status aux q0 (Std.HashSet.emptyWithCapacity 0)
  have hwf' : L.WellFormed aux' := by
    rw [haux']; exact L.wf_push aux q0 (Std.HashSet.emptyWithCapacity 0) hq0 hwf
  intro s hs
  have hs' : ops.getStatus aux' s ≠ .unknown := by
    rw [hpeq]; by_cases hsq : s == q0
    · simp [hsq]
    · simp only [hsq]; exact hs
  cases hdg : dfsGo ops succs edgeMarks aux' [step] with
  | none => exact absurd hdg hReal
  | some r =>
    simp only [Option.getD_some]
    exact dfsGo_status_monotone ops succs edgeMarks L aux' [step] r hdg hwf' s hs'

theorem dfsFromRoot_root_touched [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (L : LawfulDFSOps ops)
    (aux : ops.Aux) (q0 : State) (hwf : L.WellFormed aux) (hq0 : ops.getStatus aux q0 = .unknown)
    (hReal : dfsGo ops succs edgeMarks (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1
      [({ state := q0, pos := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
          acc := Std.HashSet.emptyWithCapacity 0, succ := succs q0, idx := 0 } :
        DFSStep State ops.Position)] ≠ none) :
    ops.getStatus (dfsFromRoot ops succs edgeMarks aux q0).2 q0 ≠ .unknown := by
  unfold dfsFromRoot
  rw [show ops.push aux q0 (Std.HashSet.emptyWithCapacity 0) =
      ((ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1, (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2)
      from rfl]
  simp only
  set aux' := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).1 with haux'
  set step : DFSStep State ops.Position :=
    { state := q0, pos := (ops.push aux q0 (Std.HashSet.emptyWithCapacity 0)).2,
      acc := Std.HashSet.emptyWithCapacity 0, succ := succs q0, idx := 0 } with hstep
  have hpeq : ∀ s, ops.getStatus aux' s = if s == q0 then .live else ops.getStatus aux s := by
    rw [haux']; exact L.push_status aux q0 (Std.HashSet.emptyWithCapacity 0)
  have hwf' : L.WellFormed aux' := by
    rw [haux']; exact L.wf_push aux q0 (Std.HashSet.emptyWithCapacity 0) hq0 hwf
  have hs' : ops.getStatus aux' q0 ≠ .unknown := by rw [hpeq]; simp
  cases hdg : dfsGo ops succs edgeMarks aux' [step] with
  | none => exact absurd hdg hReal
  | some r =>
    simp only [Option.getD_some]
    exact dfsGo_status_monotone ops succs edgeMarks L aux' [step] r hdg hwf' q0 hs'

/-- Multi-root chaining of `dfsGo_closed` over the outer loop, one root at a time. -/
theorem genericDFSGo_closed [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (L : LawfulDFSOps ops)
    (P : State → Prop)
    (hReal : ∀ aux q, P q → L.WellFormed aux → ops.getStatus aux q = .unknown →
      dfsGo ops succs edgeMarks (ops.push aux q (Std.HashSet.emptyWithCapacity 0)).1
        [({ state := q, pos := (ops.push aux q (Std.HashSet.emptyWithCapacity 0)).2,
            acc := Std.HashSet.emptyWithCapacity 0, succ := succs q, idx := 0 } :
          DFSStep State ops.Position)] ≠ none) :
    ∀ (roots : List State) aux (r : Option (State × List State) × ops.Aux),
    genericDFSGo ops succs edgeMarks roots aux = some r →
    (∀ q ∈ roots, P q) →
    r.1 = none →
    L.WellFormed aux →
    (∀ t, ops.getStatus aux t ≠ .unknown → ∀ x ∈ succs t, ops.getStatus aux x ≠ .unknown) →
    L.WellFormed r.2 ∧ (∀ t, ops.getStatus r.2 t ≠ .unknown → ∀ x ∈ succs t, ops.getStatus r.2 x ≠ .unknown) := by
  refine genericDFSGo.partial_correctness ops succs edgeMarks
    (fun roots aux r => (∀ q ∈ roots, P q) → r.1 = none → L.WellFormed aux →
      (∀ t, ops.getStatus aux t ≠ .unknown → ∀ x ∈ succs t, ops.getStatus aux x ≠ .unknown) →
      L.WellFormed r.2 ∧ (∀ t, ops.getStatus r.2 t ≠ .unknown → ∀ x ∈ succs t, ops.getStatus r.2 x ≠ .unknown)) ?_
  intro genericDFSGo ih roots aux r hr
  cases roots with
  | nil =>
    simp only [Option.some.injEq] at hr
    intro _ _ hwf hClosed
    rw [← hr]; exact ⟨hwf, hClosed⟩
  | cons q rest =>
  intro hrootsP hnone hwf hClosed
  have hrestP : ∀ q' ∈ rest, P q' := fun q' hq' => hrootsP q' (List.mem_cons_of_mem _ hq')
  cases hgs : ops.getStatus aux q with
  | dead =>
    simp only [hgs] at hr
    exact ih rest aux r hr hrestP hnone hwf hClosed
  | live =>
    simp only [hgs] at hr
    exact ih rest aux r hr hrestP hnone hwf hClosed
  | unknown =>
    simp only [hgs] at hr
    rcases hdfr : dfsFromRoot ops succs edgeMarks aux q with ⟨found?, aux'⟩
    simp only [hdfr] at hr
    have haux'eq : (dfsFromRoot ops succs edgeMarks aux q).2 = aux' := by rw [hdfr]
    cases hf : found? with
    | some val =>
      exfalso
      simp only [hf, Option.some.injEq] at hr
      rw [← hr] at hnone
      simp at hnone
    | none =>
      simp only [hf] at hr
      have hReal' := hReal aux q (hrootsP q (by simp)) hwf hgs
      have hdfrnone : (dfsFromRoot ops succs edgeMarks aux q).1 = none := by
        rw [hdfr]; exact hf
      have hwf' : L.WellFormed aux' :=
        haux'eq ▸ dfsFromRoot_wellFormed ops succs edgeMarks L
          aux q hwf hgs hReal'
      have hClosed' : ∀ t, ops.getStatus aux' t ≠ .unknown → ∀ x ∈ succs t, ops.getStatus aux' x ≠ .unknown :=
        haux'eq ▸ dfsFromRoot_closed ops succs edgeMarks L aux q hwf hgs hClosed hReal' hdfrnone
      exact ih rest aux' r hr hrestP hnone hwf' hClosed'

theorem genericDFSGo_status_monotone [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (L : LawfulDFSOps ops)
    (P : State → Prop)
    (hReal : ∀ aux q, P q → L.WellFormed aux → ops.getStatus aux q = .unknown →
      dfsGo ops succs edgeMarks (ops.push aux q (Std.HashSet.emptyWithCapacity 0)).1
        [({ state := q, pos := (ops.push aux q (Std.HashSet.emptyWithCapacity 0)).2,
            acc := Std.HashSet.emptyWithCapacity 0, succ := succs q, idx := 0 } :
          DFSStep State ops.Position)] ≠ none) :
    ∀ (roots : List State) aux (r : Option (State × List State) × ops.Aux),
    genericDFSGo ops succs edgeMarks roots aux = some r →
    (∀ q ∈ roots, P q) →
    L.WellFormed aux →
    ∀ s, ops.getStatus aux s ≠ .unknown → ops.getStatus r.2 s ≠ .unknown := by
  refine genericDFSGo.partial_correctness ops succs edgeMarks
    (fun roots aux r => (∀ q ∈ roots, P q) → L.WellFormed aux →
      ∀ s, ops.getStatus aux s ≠ .unknown → ops.getStatus r.2 s ≠ .unknown) ?_
  intro genericDFSGo ih roots aux r hr
  cases roots with
  | nil =>
    simp only [Option.some.injEq] at hr
    intro _ _ s hs
    rw [← hr]; exact hs
  | cons q rest =>
  intro hrootsP hwf
  have hrestP : ∀ q' ∈ rest, P q' := fun q' hq' => hrootsP q' (List.mem_cons_of_mem _ hq')
  cases hgs : ops.getStatus aux q with
  | dead =>
    simp only [hgs] at hr
    exact ih rest aux r hr hrestP hwf
  | live =>
    simp only [hgs] at hr
    exact ih rest aux r hr hrestP hwf
  | unknown =>
    simp only [hgs] at hr
    rcases hdfr : dfsFromRoot ops succs edgeMarks aux q with ⟨found?, aux'⟩
    simp only [hdfr] at hr
    have haux'eq : (dfsFromRoot ops succs edgeMarks aux q).2 = aux' := by rw [hdfr]
    have hReal' := hReal aux q (hrootsP q (by simp)) hwf hgs
    have hwf' : L.WellFormed aux' :=
      haux'eq ▸ dfsFromRoot_wellFormed ops succs edgeMarks L
        aux q hwf hgs hReal'
    have hmono' : ∀ s, ops.getStatus aux s ≠ .unknown → ops.getStatus aux' s ≠ .unknown :=
      haux'eq ▸ dfsFromRoot_status_monotone ops succs edgeMarks L aux q hwf hgs hReal'
    cases hf : found? with
    | some val =>
      simp only [hf, Option.some.injEq] at hr
      intro s hs
      have hr2 : r.2 = aux' := by rw [← hr]
      rw [hr2]; exact hmono' s hs
    | none =>
      simp only [hf] at hr
      intro s hs
      exact ih rest aux' r hr hrestP hwf' s (hmono' s hs)

/-- `dfsGo_closed` lifted through `genericDFS`'s outer `Option` wrapper. -/
theorem genericDFS_closed [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (L : LawfulDFSOps ops)
    (P : State → Prop)
    (hReal : ∀ aux q, P q → L.WellFormed aux → ops.getStatus aux q = .unknown →
      dfsGo ops succs edgeMarks (ops.push aux q (Std.HashSet.emptyWithCapacity 0)).1
        [({ state := q, pos := (ops.push aux q (Std.HashSet.emptyWithCapacity 0)).2,
            acc := Std.HashSet.emptyWithCapacity 0, succ := succs q, idx := 0 } :
          DFSStep State ops.Position)] ≠ none)
    (roots : List State) (aux : ops.Aux) (hrootsP : ∀ q ∈ roots, P q)
    (hReal2 : genericDFSGo ops succs edgeMarks roots aux ≠ none)
    (hnone : (genericDFS ops succs edgeMarks roots aux).1 = none)
    (hwf : L.WellFormed aux)
    (hClosed : ∀ t, ops.getStatus aux t ≠ .unknown → ∀ x ∈ succs t, ops.getStatus aux x ≠ .unknown) :
    L.WellFormed (genericDFS ops succs edgeMarks roots aux).2 ∧
      ∀ t, ops.getStatus (genericDFS ops succs edgeMarks roots aux).2 t ≠ .unknown →
        ∀ x ∈ succs t, ops.getStatus (genericDFS ops succs edgeMarks roots aux).2 x ≠ .unknown := by
  unfold genericDFS at hnone ⊢
  cases hdg : genericDFSGo ops succs edgeMarks roots aux with
  | none => exact absurd hdg hReal2
  | some r =>
    simp only [hdg, Option.getD_some] at hnone ⊢
    exact genericDFSGo_closed ops succs edgeMarks L P hReal roots aux r hdg hrootsP hnone hwf hClosed

theorem genericDFS_status_monotone [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (L : LawfulDFSOps ops)
    (P : State → Prop)
    (hReal : ∀ aux q, P q → L.WellFormed aux → ops.getStatus aux q = .unknown →
      dfsGo ops succs edgeMarks (ops.push aux q (Std.HashSet.emptyWithCapacity 0)).1
        [({ state := q, pos := (ops.push aux q (Std.HashSet.emptyWithCapacity 0)).2,
            acc := Std.HashSet.emptyWithCapacity 0, succ := succs q, idx := 0 } :
          DFSStep State ops.Position)] ≠ none)
    (roots : List State) (aux : ops.Aux) (hrootsP : ∀ q ∈ roots, P q)
    (hReal2 : genericDFSGo ops succs edgeMarks roots aux ≠ none)
    (hwf : L.WellFormed aux) :
    ∀ s, ops.getStatus aux s ≠ .unknown →
      ops.getStatus (genericDFS ops succs edgeMarks roots aux).2 s ≠ .unknown := by
  unfold genericDFS
  cases hdg : genericDFSGo ops succs edgeMarks roots aux with
  | none => exact absurd hdg hReal2
  | some r =>
    simp only [Option.getD_some]
    exact genericDFSGo_status_monotone ops succs edgeMarks L P hReal roots aux r hdg hrootsP hwf

omit [BEq State] [Hashable State] in
/-- One-hop closure transported along an arbitrary `succs`-path. -/
theorem closed_pathTo {aux : State → DFSStatus} {succs : State → Array State}
    (hClosed : ∀ t, aux t ≠ .unknown → ∀ x ∈ succs t, aux x ≠ .unknown) :
    ∀ {s t}, PathTo succs (fun _ => False) s t → aux s ≠ .unknown → aux t ≠ .unknown := by
  intro s t hpath
  induction hpath with
  | direct ht => intro hs; exact hClosed _ hs _ ht
  | through hmid _ _ ih => intro hs; exact ih (hClosed _ hs _ hmid)

/-- Every root is non-`.unknown` by the time the whole search completes, whether it was skipped or searched. -/
theorem genericDFS_roots_touched [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (L : LawfulDFSOps ops)
    (P : State → Prop)
    (hReal : ∀ aux q, P q → L.WellFormed aux → ops.getStatus aux q = .unknown →
      dfsGo ops succs edgeMarks (ops.push aux q (Std.HashSet.emptyWithCapacity 0)).1
        [({ state := q, pos := (ops.push aux q (Std.HashSet.emptyWithCapacity 0)).2,
            acc := Std.HashSet.emptyWithCapacity 0, succ := succs q, idx := 0 } :
          DFSStep State ops.Position)] ≠ none) :
    ∀ (roots : List State) aux (r : Option (State × List State) × ops.Aux),
    genericDFSGo ops succs edgeMarks roots aux = some r →
    (∀ q ∈ roots, P q) →
    r.1 = none →
    L.WellFormed aux →
    (∀ q ∈ roots, ops.getStatus r.2 q ≠ .unknown) ∧
      (∀ s, ops.getStatus aux s ≠ .unknown → ops.getStatus r.2 s ≠ .unknown) := by
  refine genericDFSGo.partial_correctness ops succs edgeMarks
    (fun roots aux r => (∀ q ∈ roots, P q) → r.1 = none → L.WellFormed aux →
      (∀ q ∈ roots, ops.getStatus r.2 q ≠ .unknown) ∧
        (∀ s, ops.getStatus aux s ≠ .unknown → ops.getStatus r.2 s ≠ .unknown)) ?_
  intro go ih roots aux r hr
  cases roots with
  | nil =>
    simp only [Option.some.injEq] at hr
    intro _ _ _
    refine ⟨fun q hq => by simp at hq, fun s hs => ?_⟩
    rw [← hr]; exact hs
  | cons q0 rest =>
  intro hrootsP hnone hwf
  have hrestP : ∀ q' ∈ rest, P q' := fun q' hq' => hrootsP q' (List.mem_cons_of_mem _ hq')
  cases hgs : ops.getStatus aux q0 with
  | dead =>
    simp only [hgs] at hr
    obtain ⟨ihroots, ihmono⟩ := ih rest aux r hr hrestP hnone hwf
    refine ⟨fun q' hq' => ?_, ihmono⟩
    rcases List.mem_cons.mp hq' with heq | hq''
    · rw [heq]; exact ihmono q0 (by simp [hgs])
    · exact ihroots q' hq''
  | live =>
    simp only [hgs] at hr
    obtain ⟨ihroots, ihmono⟩ := ih rest aux r hr hrestP hnone hwf
    refine ⟨fun q' hq' => ?_, ihmono⟩
    rcases List.mem_cons.mp hq' with heq | hq''
    · rw [heq]; exact ihmono q0 (by simp [hgs])
    · exact ihroots q' hq''
  | unknown =>
    simp only [hgs] at hr
    rcases hdfr : dfsFromRoot ops succs edgeMarks aux q0 with ⟨found?, aux'⟩
    simp only [hdfr] at hr
    have haux'eq : (dfsFromRoot ops succs edgeMarks aux q0).2 = aux' := by rw [hdfr]
    have hReal' := hReal aux q0 (hrootsP q0 (by simp)) hwf hgs
    have hq0touched : ops.getStatus aux' q0 ≠ .unknown :=
      haux'eq ▸ dfsFromRoot_root_touched ops succs edgeMarks L aux q0 hwf hgs hReal'
    have hstepMono : ∀ s, ops.getStatus aux s ≠ .unknown → ops.getStatus aux' s ≠ .unknown :=
      haux'eq ▸ dfsFromRoot_status_monotone ops succs edgeMarks L aux q0 hwf hgs hReal'
    cases hf : found? with
    | some val =>
      exfalso
      simp only [hf, Option.some.injEq] at hr
      rw [← hr] at hnone
      simp at hnone
    | none =>
      simp only [hf] at hr
      have hwf' : L.WellFormed aux' :=
        haux'eq ▸ dfsFromRoot_wellFormed ops succs edgeMarks L
          aux q0 hwf hgs hReal'
      obtain ⟨ihroots, ihmono⟩ := ih rest aux' r hr hrestP hnone hwf'
      refine ⟨fun q' hq' => ?_, fun s hs => ihmono s (hstepMono s hs)⟩
      rcases List.mem_cons.mp hq' with heq | hq''
      · rw [heq]; exact ihmono q0 hq0touched
      · exact ihroots q' hq''

/-- Once `genericDFS` finishes over every root with no counterexample, every reachable state is non-`.unknown`. -/
theorem genericDFS_returns_none_fully_explored [LawfulBEq State] (ops : DFSOps State)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (L : LawfulDFSOps ops)
    (P : State → Prop)
    (hReal : ∀ aux q, P q → L.WellFormed aux → ops.getStatus aux q = .unknown →
      dfsGo ops succs edgeMarks (ops.push aux q (Std.HashSet.emptyWithCapacity 0)).1
        [({ state := q, pos := (ops.push aux q (Std.HashSet.emptyWithCapacity 0)).2,
            acc := Std.HashSet.emptyWithCapacity 0, succ := succs q, idx := 0 } :
          DFSStep State ops.Position)] ≠ none)
    (initialStates : List State) (hrootsP : ∀ q ∈ initialStates, P q)
    (hReal2 : genericDFSGo ops succs edgeMarks initialStates ops.initAux ≠ none)
    (hwf0 : L.WellFormed ops.initAux)
    (hinit0 : ∀ q, ops.getStatus ops.initAux q = .unknown)
    (hnone : (genericDFS ops succs edgeMarks initialStates ops.initAux).1 = none) :
    ∀ s, Reachable initialStates succs s →
      ops.getStatus (genericDFS ops succs edgeMarks initialStates ops.initAux).2 s ≠ .unknown := by
  set auxFinal := (genericDFS ops succs edgeMarks initialStates ops.initAux).2 with hauxFinal
  have hClosed : ∀ t, ops.getStatus auxFinal t ≠ .unknown → ∀ x ∈ succs t, ops.getStatus auxFinal x ≠ .unknown :=
    (genericDFS_closed ops succs edgeMarks L
      P hReal initialStates ops.initAux hrootsP hReal2 hnone hwf0 (fun t ht => absurd (hinit0 t) ht)).2
  have hrootsTouched : ∀ q ∈ initialStates, ops.getStatus auxFinal q ≠ .unknown := by
    rw [hauxFinal]
    unfold genericDFS at hnone ⊢
    cases hdg : genericDFSGo ops succs edgeMarks initialStates ops.initAux with
    | none => exact absurd hdg hReal2
    | some r =>
      simp only [Option.getD_some]
      simp only [hdg, Option.getD_some] at hnone
      exact (genericDFS_roots_touched ops succs edgeMarks L P hReal initialStates ops.initAux r hdg hrootsP hnone hwf0).1
  intro s hs
  induction hs with
  | base hi => exact hrootsTouched _ hi
  | step hprev hstep ih => exact hClosed _ ih _ hstep

/-! ## Witness-check driver -/

/-- Run `ops`'s search to decide emptiness, then on `.nonEmpty` rebuild the cycle by plain graph BFS restricted
to the accepting SCC `ops.sccHint` hands back. The stem comes from the search's own stack. -/
def checkWithWitness [LawfulBEq State] [LawfulHashable State] (ops : DFSOps State)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat)
    (initialStates : List State) : EmptinessResult State :=
  let (found?, aux) := genericDFS ops succs edgeMarks initialStates ops.initAux
  match found? with
  | none => .empty (ops.numExplored aux)
  | some (anchor, stem) =>
    let scc := ops.sccHint aux
    let sccSuccsMap : Std.HashMap State (Array State) :=
      scc.toList.foldl (init := {}) fun m s => m.insert s ((succs s).filter scc.contains)
    let sccSuccs' : State → Array State := fun s =>
      match sccSuccsMap[s]? with
      | some a => a
      -- None branch never actually taken (it is same as `SCCTheory.sccSuccs` for correctness)
      | none => (succs s).filter scc.contains
    -- Every BFS is confined to the scc, so the scc is the finite domain `stitchCycleAt` termination proof requires
    let cycle := stitchCycleAt scc sccSuccs' edgeMarks numMarks anchor
    match cycle with
    | [] => .empty (ops.numExplored aux)
    | _ => .nonEmpty stem (anchor :: cycle)

/-- Contract `checkWithWitness`'s correctness requires (kept out of `LawfulDFSOps` since this constrains driver-level results rather than `Aux` operations).
A reported `(anchor, stem)` comes with a sccHint that really is an accepting SCC containing `anchor` with a real path `stem` into it from an initial state. -/
def SccHintSound [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat) (initialStates : List State) : Prop :=
  ∀ anchor stem,
    (genericDFS ops succs edgeMarks initialStates ops.initAux).1 = some (anchor, stem) →
    InternallyConnected succs (ops.sccHint (genericDFS ops succs edgeMarks initialStates ops.initAux).2) ∧
    AcceptingMarks succs edgeMarks numMarks
      (ops.sccHint (genericDFS ops succs edgeMarks initialStates ops.initAux).2) ∧
    anchor ∈ ops.sccHint (genericDFS ops succs edgeMarks initialStates ops.initAux).2 ∧
    ∃ hs : stem ≠ [], stem.head hs ∈ initialStates ∧
      (∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs (stem[i])) ∧
      stem.getLast hs = anchor

/-! ## Termination -/

/-- The reachable states still to be discovered, finite by `FiniteReach` (Unreachable unknown set may be infinite).-/
def unexploredSet (ops : DFSOps State) (succs : State → Array State) (initialStates : List State)
    (aux : ops.Aux) : Set State :=
  {s | Reachable initialStates succs s ∧ ops.getStatus aux s = .unknown}

theorem unexploredSet_finite (ops : DFSOps State) (succs : State → Array State)
    (initialStates : List State) (fr : FiniteReach initialStates succs) (aux : ops.Aux) :
    (unexploredSet ops succs initialStates aux).Finite :=
  fr.subset (fun _ hs => hs.1)

/-- First component of `dfsGo`'s lexicographic measure `(unexploredCard, stack.length, stackPending)`. -/
noncomputable def unexploredCard (ops : DFSOps State) (succs : State → Array State)
    (initialStates : List State) (fr : FiniteReach initialStates succs) (aux : ops.Aux) : Nat :=
  (unexploredSet_finite ops succs initialStates fr aux).toFinset.card

theorem unexploredCard_lt_of_subset (ops : DFSOps State) (succs : State → Array State)
    (initialStates : List State) (fr : FiniteReach initialStates succs) {aux aux' : ops.Aux}
    (hsub : unexploredSet ops succs initialStates aux' ⊆ unexploredSet ops succs initialStates aux)
    {d : State} (hd : d ∈ unexploredSet ops succs initialStates aux)
    (hd' : d ∉ unexploredSet ops succs initialStates aux') :
    unexploredCard ops succs initialStates fr aux' < unexploredCard ops succs initialStates fr aux :=
  Finset.card_lt_card (by
    rw [Finset.ssubset_iff_of_subset (Set.Finite.toFinset_subset_toFinset.mpr hsub)]
    exact ⟨d, (Set.Finite.mem_toFinset _).mpr hd, fun hc => hd' ((Set.Finite.mem_toFinset _).mp hc)⟩)

theorem unexploredCard_eq_of_eq (ops : DFSOps State) (succs : State → Array State)
    (initialStates : List State) (fr : FiniteReach initialStates succs) {aux aux' : ops.Aux}
    (heq : unexploredSet ops succs initialStates aux' = unexploredSet ops succs initialStates aux) :
    unexploredCard ops succs initialStates fr aux' = unexploredCard ops succs initialStates fr aux := by
  unfold unexploredCard
  congr 1
  simp only [heq]

/-- `push` removes exactly its own target from the unknown set, so the count strictly decreases whenever target was both reachable and still unknown. -/
theorem unexploredCard_push [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (initialStates : List State) (fr : FiniteReach initialStates succs)
    (hpush : ∀ aux q marks q', ops.getStatus (ops.push aux q marks).1 q' =
      if q' == q then .live else ops.getStatus aux q')
    (aux : ops.Aux) (q : State) (marks : Std.HashSet Nat)
    (hq : ops.getStatus aux q = .unknown) (hqreach : Reachable initialStates succs q) :
    unexploredCard ops succs initialStates fr (ops.push aux q marks).1 <
      unexploredCard ops succs initialStates fr aux := by
  refine unexploredCard_lt_of_subset ops succs initialStates fr (d := q) ?_ ⟨hqreach, hq⟩ ?_
  · rintro s ⟨hr, hs⟩
    refine ⟨hr, ?_⟩
    rw [hpush aux q marks s] at hs
    split at hs
    · exact absurd hs (by simp)
    · exact hs
  · rintro ⟨-, hc⟩
    rw [hpush aux q marks q] at hc
    simp at hc

/-- `update` never moves any state's status, so the unknown set is untouched. -/
theorem unexploredSet_update (ops : DFSOps State) (succs : State → Array State)
    (initialStates : List State)
    (hupdate : ∀ aux marks d q, ops.getStatus (ops.update aux marks d).1 q = ops.getStatus aux q)
    (aux : ops.Aux) (marks : Std.HashSet Nat) (d : State) :
    unexploredSet ops succs initialStates (ops.update aux marks d).1 =
      unexploredSet ops succs initialStates aux := by
  ext s; simp only [unexploredSet, Set.mem_setOf_eq, hupdate]

/-- `pop` only ever moves states from live to dead, which leaves the unknown set alone. -/
theorem unexploredSet_pop (ops : DFSOps State) (succs : State → Array State)
    (initialStates : List State) (WellFormed : ops.Aux → Prop)
    (hpop : ∀ aux pos q, WellFormed aux → ops.getStatus (ops.pop aux pos).1 q = ops.getStatus aux q ∨
      (ops.getStatus aux q = .live ∧ ops.getStatus (ops.pop aux pos).1 q = .dead))
    (aux : ops.Aux) (pos : ops.Position) (hwf : WellFormed aux) :
    unexploredSet ops succs initialStates (ops.pop aux pos).1 =
      unexploredSet ops succs initialStates aux := by
  ext s
  simp only [unexploredSet, Set.mem_setOf_eq]
  rcases hpop aux pos s hwf with h | ⟨h1, h2⟩
  · rw [h]
  · rw [h1, h2]; simp

/-- Third component of `dfsGo`'s measure `(unexploredCard, stack.length, stackPending)`. -/
def stackPending {P : Type w} (stack : List (DFSStep State P)) : Nat :=
  (stack.map fun st => st.succ.size - st.idx).sum

omit [BEq State] [Hashable State] in
theorem stackPending_cons {P : Type w} (st : DFSStep State P) (rest : List (DFSStep State P)) :
    stackPending (st :: rest) = (st.succ.size - st.idx) + stackPending rest := by
  simp [stackPending]

omit [BEq State] [Hashable State] in
/-- Dispatching one successor strictly reduces what the stack owes. -/
theorem stackPending_bump {P : Type w} (st : DFSStep State P) (rest : List (DFSStep State P))
    (h : st.idx < st.succ.size) :
    stackPending (({ st with idx := st.idx + 1 } : DFSStep State P) :: rest) < stackPending (st :: rest) := by
  rw [stackPending_cons, stackPending_cons]
  simp only []
  omega

/-- The outer loop always returns a real answer, its recursion being structural on the root list. -/
theorem genericDFSGo_ne_none (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) :
    ∀ (roots : List State) (aux : ops.Aux), genericDFSGo ops succs edgeMarks roots aux ≠ none := by
  intro roots
  induction roots with
  | nil => intro aux; rw [genericDFSGo.eq_def]; simp
  | cons q rest ih =>
    intro aux
    rw [genericDFSGo.eq_def]
    cases hgs : ops.getStatus aux q with
    | dead => simpa only [hgs] using ih aux
    | live => simpa only [hgs] using ih aux
    | unknown =>
      simp only [hgs]
      rcases hdfr : dfsFromRoot ops succs edgeMarks aux q with ⟨found?, aux'⟩
      cases found? with
      | some val => simp
      | none => simpa using ih aux'

/-- `dfsGo` always returns a real answer, so the search terminates. The measure is the lexicographic triple
`(unexploredCard, stack.length, stackPending)`, `PUSH` shrinking the first, `POP` the second, any other dispatch the third. -/
theorem dfsGo_ne_none [LawfulBEq State] (ops : DFSOps State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (fr : FiniteReach initialStates succs) (L : LawfulDFSOps ops) :
    ∀ aux (stack : List (DFSStep State ops.Position)), L.WellFormed aux →
    (∀ st ∈ stack, st.succ = succs st.state) →
    (∀ st ∈ stack, Reachable initialStates succs st.state) →
    dfsGo ops succs edgeMarks aux stack ≠ none := by
  suffices H : ∀ n1 n2 n3 aux (stack : List (DFSStep State ops.Position)),
      unexploredCard ops succs initialStates fr aux = n1 → stack.length = n2 → stackPending stack = n3 →
      L.WellFormed aux → (∀ st ∈ stack, st.succ = succs st.state) →
      (∀ st ∈ stack, Reachable initialStates succs st.state) →
      dfsGo ops succs edgeMarks aux stack ≠ none by
    exact fun aux stack hwf hs hr => H _ _ _ aux stack rfl rfl rfl hwf hs hr
  intro n1
  induction n1 using Nat.strong_induction_on with
  | _ n1 ih1 =>
  intro n2
  induction n2 using Nat.strong_induction_on with
  | _ n2 ih2 =>
  intro n3
  induction n3 using Nat.strong_induction_on with
  | _ n3 ih3 =>
  intro aux stack h1 h2 h3 hwf hsucc hreach
  subst h1; subst h2; subst h3
  cases stack with
  | nil => rw [dfsGo.eq_def]; simp
  | cons step rest =>
    have hstepSucc : step.succ = succs step.state := hsucc step (by simp)
    have hstepReach : Reachable initialStates succs step.state := hreach step (by simp)
    rw [dfsGo.eq_def]
    simp only []
    by_cases h : step.idx < step.succ.size
    · rw [dif_pos h]
      set d := step.succ[step.idx] with hd_def
      have hdSucc : d ∈ succs step.state := hstepSucc ▸ Array.getElem_mem h
      have hdReach : Reachable initialStates succs d := .step hstepReach hdSucc
      have hbumpSucc : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
          st.succ = succs st.state := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · exact hstepSucc
        · exact hsucc st (List.mem_cons_of_mem _ hst)
      have hbumpReach : ∀ st ∈ ({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest,
          Reachable initialStates succs st.state := by
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · exact hstepReach
        · exact hreach st (List.mem_cons_of_mem _ hst)
      have hbumpLen : (({ step with idx := step.idx + 1 } : DFSStep State ops.Position) :: rest).length
          = (step :: rest).length := by simp
      cases hgs : ops.getStatus aux d with
      -- dispatched, `aux` untouched: only the pending count moves
      | dead =>
        exact ih3 _ (stackPending_bump step rest h) aux _ rfl hbumpLen rfl hwf hbumpSucc hbumpReach
      | live =>
        by_cases hf : (ops.update aux (edgeMarks step.state d) d).2 = true
        · rw [if_pos hf]; simp
        · rw [if_neg hf]
          have hcard : unexploredCard ops succs initialStates fr
              (ops.update aux (edgeMarks step.state d) d).1 =
              unexploredCard ops succs initialStates fr aux :=
            unexploredCard_eq_of_eq ops succs initialStates fr
              (unexploredSet_update ops succs initialStates L.update_status aux (edgeMarks step.state d) d)
          exact ih3 _ (stackPending_bump step rest h) _ _ hcard hbumpLen rfl
            (L.wf_update aux (edgeMarks step.state d) d hwf) hbumpSucc hbumpReach
      -- a fresh state leaves the unknown set, the only branch that shrinks the first component
      | unknown =>
        refine ih1 _ (unexploredCard_push ops succs initialStates fr L.push_status aux d
          (edgeMarks step.state d) hgs hdReach) _ _ _ _ rfl rfl rfl
          (L.wf_push aux d (edgeMarks step.state d) hgs hwf) ?_ ?_
        · intro st hst
          rcases List.mem_cons.mp hst with rfl | hst
          · rfl
          · exact hbumpSucc st hst
        · intro st hst
          rcases List.mem_cons.mp hst with rfl | hst
          · exact hdReach
          · exact hbumpReach st hst
    -- backtracking: the stack shrinks, and `pop` never touches the unknown set
    · rw [dif_neg h]
      have hcard : unexploredCard ops succs initialStates fr (ops.pop aux step.pos).1 =
          unexploredCard ops succs initialStates fr aux :=
        unexploredCard_eq_of_eq ops succs initialStates fr
          (unexploredSet_pop ops succs initialStates L.WellFormed L.pop_status aux step.pos hwf)
      have hrec : dfsGo ops succs edgeMarks (ops.pop aux step.pos).1 rest ≠ none :=
        ih2 _ (by simp) _ _ rest hcard rfl rfl (L.wf_pop aux step.pos hwf)
          (fun st hst => hsucc st (List.mem_cons_of_mem _ hst))
          (fun st hst => hreach st (List.mem_cons_of_mem _ hst))
      cases hf : (ops.pop aux step.pos).2 with
      | true =>
        cases rest with
        | nil => simpa using hrec
        | cons newTop rest' => simp
      | false => simpa using hrec

/-! ## Witness-check correctness -/

private theorem foldl_insert_getElem?_eq [LawfulBEq State] [LawfulHashable State]
    (f : State → Array State) :
    ∀ (l : List State) (init : Std.HashMap State (Array State)),
      (∀ s v, init[s]? = some v → v = f s) →
      ∀ s v, (l.foldl (fun m x => m.insert x (f x)) init)[s]? = some v → v = f s := by
  intro l
  induction l with
  | nil => intro init hinit s v h; exact hinit s v h
  | cons a t ih =>
    intro init hinit s v h
    refine ih (init.insert a (f a)) (fun s' v' h' => ?_) s v h
    rw [Std.HashMap.getElem?_insert] at h'
    split at h'
    · rename_i hbeq
      rw [← Option.some.inj h', (beq_iff_eq.mp hbeq)]
    · exact hinit s' v' h'

theorem checkWithWitness_sccSuccs_eq [LawfulBEq State] [LawfulHashable State]
    (succs : State → Array State) (scc : Std.HashSet State) :
    (fun s => match (scc.toList.foldl (init := ({} : Std.HashMap State (Array State)))
                 fun m x => m.insert x ((succs x).filter scc.contains))[s]? with
              | some a => a
              | none => (succs s).filter scc.contains) = sccSuccs succs scc := by
  funext s
  rcases hm : (scc.toList.foldl (init := ({} : Std.HashMap State (Array State)))
      fun m x => m.insert x ((succs x).filter scc.contains))[s]? with _ | v
  · rw [hm]; rfl
  · rw [hm]
    exact foldl_insert_getElem?_eq (fun x => (succs x).filter scc.contains) scc.toList {}
      (by intro s' v' h'; simp at h') s v hm

/-- Soundness of `.nonEmpty`: the returned `stem`/`loop.tail` are literally some `TAcceptingCycle`'s own fields. -/
theorem checkWithWitness_nonEmpty_valid [LawfulBEq State] [LawfulHashable State] (ops : DFSOps State)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat)
    (initialStates : List State)
    (hsound : SccHintSound ops succs edgeMarks numMarks initialStates)
    {stem loop : List State}
    (h : checkWithWitness ops succs edgeMarks numMarks initialStates = .nonEmpty stem loop) :
    ∃ ac : TAcceptingCycle initialStates succs edgeMarks numMarks, ac.stem = stem ∧ ac.cycle = loop.tail := by
  unfold checkWithWitness at h
  rcases hgd : genericDFS ops succs edgeMarks initialStates ops.initAux with ⟨found?, aux⟩
  simp only [hgd] at h
  cases hf : found? with
  | none => rw [hf] at h; simp at h
  | some val =>
    obtain ⟨anchor, stem'⟩ := val
    rw [hf] at h
    obtain ⟨hconn, hcov, hanchor, hs, hhead, hpath, hlast⟩ :=
      hsound anchor stem' (by rw [hgd, hf])
    rw [hgd] at hconn hcov hanchor
    obtain ⟨ac, hstemeq, hcycleeq⟩ :=
      stitchCycleAt_toTAcceptingCycle hconn hcov hanchor hs hhead hpath hlast
    simp only [checkWithWitness_sccSuccs_eq succs (ops.sccHint aux)] at h
    rw [← hcycleeq] at h
    split at h
    · rename_i hnil
      exact absurd (hnil ▸ ac.cycle_nonempty) (by simp)
    · simp only [EmptinessResult.nonEmpty.injEq] at h
      exact ⟨ac, hstemeq.trans h.1, by rw [← h.2]; simp⟩

/-- `.empty` is only ever returned when the search itself found nothing, `hsound` rules out the `cycle = []` fallback. -/
theorem checkWithWitness_empty_of_none [LawfulBEq State] [LawfulHashable State] (ops : DFSOps State)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat)
    (initialStates : List State)
    (hsound : SccHintSound ops succs edgeMarks numMarks initialStates)
    {n : Nat} (h : checkWithWitness ops succs edgeMarks numMarks initialStates = .empty n) :
    (genericDFS ops succs edgeMarks initialStates ops.initAux).1 = none := by
  unfold checkWithWitness at h
  rcases hgd : genericDFS ops succs edgeMarks initialStates ops.initAux with ⟨found?, aux⟩
  simp only [hgd] at h
  cases hf : found? with
  | none => rfl
  | some val =>
    exfalso
    obtain ⟨anchor, stem'⟩ := val
    rw [hf] at h
    obtain ⟨hconn, hcov, hanchor, hs, hhead, hpath, hlast⟩ :=
      hsound anchor stem' (by rw [hgd, hf])
    rw [hgd] at hconn hcov hanchor
    obtain ⟨ac, -, hcycleeq⟩ :=
      stitchCycleAt_toTAcceptingCycle hconn hcov hanchor hs hhead hpath hlast
    simp only [checkWithWitness_sccSuccs_eq succs (ops.sccHint aux)] at h
    rw [← hcycleeq] at h
    split at h
    · rename_i hnil
      exact absurd (hnil ▸ ac.cycle_nonempty) (by simp)
    · simp at h

end LTLLib
