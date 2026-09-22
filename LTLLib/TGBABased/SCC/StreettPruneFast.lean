/-
  The Streett prune's fast path: the scan reads option bits that the expansion carried, instead of
  asking the spec's region predicates once per (edge, option). `EdgeLabels.md` §13.20 (the executable),
  §13.21 (the sweep), §13.22 (the proof).

  What it changes, and only this. The proved `streettPop` closes an SCC by re-deriving its internal
  edges from `succs` and then evaluating every option's region and marks on each edge through
  `cs.regions`/`cs.optMarks`, each of which is a full `regionSuccs` — one `sysSucc` plus one `sysLabel`
  in Veil — to answer a membership question about a source whose steps the DFS had already computed.
  §13.16 measured that at 25 of 66 Veil callbacks on BcastFolklore's CorrLtl, in a route that is 93 %
  Veil. Here every frame's `succ` and `succOpts` are retained at its live position when it is popped,
  and the scan folds the retained bits. The search makes no callback outside `expand`.

  Defines:
  - `CompiledSpec.letterBits`: one letter's packed option bits, in the layout `DFSStep.succOpts` uses
  - `StreettAuxF`: `StreettAux` plus the retained per-live-state successors and bits
  - `streettPushF`/`streettUpdateF`/`streettPopF`, `streettOpsF`: the refinement
  - `scanFrameF`: `scanFrame` over retained data
  - `streettRunF`, `candidateRunF`, `pruneLoopF`, `streettCheckF`: the drivers, mirroring the proved ones
    line for line except where they read retained data

  Proves — the fast route *is* the proved route, so every theorem of `StreettPrune.lean` transfers
  through one rewrite (`modelCheckPruneSplit_eq` in `Fairness/FairRouter.lean`):
  - `CompiledSpec.edgeBits`, defined through `scanOptionsAt`, and its bit lemmas
  - `scanFrameF_eq_scanFrame`: the retained scan is the callback scan, bit by bit
  - `InvF` and the lockstep of PUSH/UPDATE/POP (`streettPopF_spec`), then `dfsGo_lockstep` in both
    directions, `dfsGo_eq`, `dfsFromRoot_eq`, `genericDFSGo_eq`, `genericDFS_eq`, `streettRunF_eq`
  - `candidateRunF_eq`, `pruneLoopF_eq`, and `streettCheckF_eq`: the top-level equality

  `Tests/StreettPruneFast.lean` keeps the 200-case differential test that stood in for this proof while
  the route was benchmarked; it is now a cross-check of the executable against the theorem.
-/
import LTLLib.TGBABased.SCC.StreettPrune

namespace LTLLib

variable {State : Type u} {L : Type w} [BEq State] [Hashable State]

/-! ## A letter's option bits

`DFSStep.succOpts` packs one `Nat` per edge: bit `o` (for `o < numOptions`) says option `o`'s region
admits the edge, and bit `numOptions + optMarkBase[o] + j` says its mark `j` is carried by an in-region
realization of it. That is `cs.regions[o]` and `cs.optMarks[o][j]` read on the edge — exactly what
`scanOptionsAt` folds — so the scan's accumulators become `regionAlive &&& bits` and
`marksSeen ||| (bits >>> numOptions)`. -/

private def markBitsAt (gs : Array (L → Bool)) (l : L) (base j acc : Nat) : Nat :=
  if h : j < gs.size then
    markBitsAt gs l base (j + 1) (if gs[j] l then acc ||| (1 <<< (base + j)) else acc)
  else acc
termination_by gs.size - j

private def letterBitsFrom (cs : CompiledSpec State L) (l : L) (o acc : Nat) : Nat :=
  if h : o < cs.letterOptions.size then
    let opt := cs.letterOptions[o]
    -- a mark counts only on a realization that is also in-region: `StreettOption.onEdges` conjoins the
    -- region into each mark predicate, and this is that conjunction read on one letter
    let acc' :=
      if opt.region l then
        markBitsAt opt.marks l (cs.numOptions + cs.optMarkBase[o]!) 0 (acc ||| (1 <<< o))
      else acc
    letterBitsFrom cs l (o + 1) acc'
  else acc
termination_by cs.letterOptions.size - o

/-- The option bits one letter contributes to an edge that reads it. An edge with several realizations
takes the `|||` of theirs, which is the existential `contains` of `StreettOption.onEdges`. Pure: the
options' predicates are Boolean formulas over the letter, and nothing here enters the system. -/
def CompiledSpec.letterBits (cs : CompiledSpec State L) (l : L) : Nat := letterBitsFrom cs l 0 0

/-! ## The search state

`StreettAux` with two more arrays, indexed by live position like `live` itself. They are filled at POP,
not PUSH: in `dfsGo` `push` runs *before* the frame's `expand`, and POP is the first operation handed the
whole frame. Pops are LIFO, so when a frame closes an SCC every position above it has already been popped
and stashed, and the scan reads a complete component.

Memory: the arrays hold references to `succ`/`succOpts` arrays that `expand` allocated anyway and that
the proved route frees at POP; here they live until their SCC is flushed. On one large SCC that is the
edges of the SCC rather than its states. No allocation is added — the two pushes per frame store a
shared empty literal. -/
structure StreettAuxF (State : Type u) [BEq State] [Hashable State] where
  live : Array State
  liveIndex : Std.HashMap State Nat
  dead : Std.HashSet State
  dstack : Array (Nat × Nat)
  witness : Array State
  witnessOpts : Array Nat
  pending : Array (Candidate State)
  -- `liveSuccs[i]` is `(expand live[i]).1` once `live[i]` has been popped, `#[]` before. What the proved
  -- route's `internalEdges succs` re-derived through one callback per SCC state (§13.16's 5).
  liveSuccs : Array (Array State)
  -- `liveOpts[i]` is `(expand live[i]).2.2`, parallel to `liveSuccs[i]` — or `#[]` when the spec has no
  -- options. What `cs.regions`/`cs.optMarks` re-derived through one callback per (edge, option)
  -- evaluation (§13.16's 20).
  liveOpts : Array (Array Nat)
  -- §13.26: the retained successor arrays of the reported witness, `witnessSuccs[k]` belonging to
  -- `witness[k]` — the slice of `liveSuccs` the accepting POP would otherwise drop. The report reads
  -- them through `memoGraph` instead of calling the candidate's graph once per witness state, which
  -- was one callback pair plus a region filter per witness state, 27 % of a `fails` row on `servers`.
  witnessSuccs : Array (Array State)

def streettInitAuxF : StreettAuxF State where
  live := #[]
  liveIndex := Std.HashMap.emptyWithCapacity 0
  dead := Std.HashSet.emptyWithCapacity 0
  dstack := #[]
  witness := #[]
  witnessOpts := #[]
  pending := #[]
  liveSuccs := #[]
  liveOpts := #[]
  witnessSuccs := #[]

/-! ## The scan over retained data

`scanFrame cs succs live lo` is `scanLetters` over `internalEdges succs (sccSetOf live lo) (live[lo..])`.
The retained arrays give the same edges in the same order — `liveSuccs[i]` *is* `succs live[i]` by
`ExpandCoherent` — and membership in the closing SCC is `liveIndex[t] ≥ lo`, so the per-scan `sccSetOf`
hash set is not built either. `&&&`/`|||` are idempotent and monotone, so checking `scanLabels`'s early
exit once per state rather than once per edge changes nothing. -/

/-- Do the entries of `os` at successor indices `k ..< n` all equal `b`? A state-labelled system gives
every out-edge of a state the same bits (`optBitsFor`'s shared-letter branch), and `&&&`/`|||` are
idempotent, so once one internal edge of such a state has been folded the rest of its edges cannot
change the masks. Deciding this costs one `Nat` comparison per edge and no hashing; acting on it saves
a hash lookup with a deep state equality per edge — 17 % of the default route on `servers`
(`EdgeLabels.md` §13.25). -/
private def sameBitsFrom (os : Array Nat) (n k b : Nat) : Bool :=
  if h : k < n then (os[k]! == b) && sameBitsFrom os n (k + 1) b else true
termination_by n - k

private def scanEdgesF (liveIndex : Std.HashMap State Nat) (lo shift : Nat)
    (ss : Array State) (os : Array Nat) (uniform : Bool) (k ra ms : Nat) : Nat × Nat :=
  if h : k < ss.size then
    match liveIndex[ss[k]]? with
    | some j =>
      if lo ≤ j then
        -- `os[k]!` panics on a payload that is not parallel to `ss`: a caller handing this route an
        -- expansion without bits is a bug that must not degrade silently into "no option holds"
        let bits := os[k]!
        -- under `uniform` every later edge of this state carries `bits` too, and the masks are idempotent
        if uniform then (ra &&& bits, ms ||| (bits >>> shift))
        else scanEdgesF liveIndex lo shift ss os uniform (k + 1) (ra &&& bits) (ms ||| (bits >>> shift))
      else scanEdgesF liveIndex lo shift ss os uniform (k + 1) ra ms
    | none => scanEdgesF liveIndex lo shift ss os uniform (k + 1) ra ms
  else (ra, ms)
termination_by ss.size - k

private def scanLiveF (cs : CompiledSpec State L) (liveIndex : Std.HashMap State Nat)
    (lsuccs : Array (Array State)) (lopts : Array (Array Nat)) (lo fullMarks i ra ms : Nat) :
    Nat × Nat :=
  if h : i < lsuccs.size then
    -- `scanLabels`'s early exit: nothing left to clear and nothing left to set. With no options at all
    -- this fires before any payload is read, which is what lets the no-option payload be empty.
    if ra == 0 && ms == fullMarks then (ra, ms)
    else
      let (ra', ms') := scanEdgesF liveIndex lo cs.numOptions lsuccs[i] lopts[i]!
        (sameBitsFrom lopts[i]! lsuccs[i].size 0 (lopts[i]!)[0]!) 0 ra ms
      scanLiveF cs liveIndex lsuccs lopts lo fullMarks (i + 1) ra' ms'
  else (ra, ms)
termination_by lsuccs.size - i

/-- `scanFrame` on retained data: the two masks over the closing SCC's internal edges, no callback. -/
def scanFrameF (cs : CompiledSpec State L) (liveIndex : Std.HashMap State Nat)
    (lsuccs : Array (Array State)) (lopts : Array (Array Nat)) (lo : Nat) : Nat × Nat :=
  scanLiveF cs liveIndex lsuccs lopts lo ((1 <<< cs.numOptMarks) - 1) lo ((1 <<< cs.numOptions) - 1) 0

/-! ## PUSH, UPDATE and POP

Copies of the proved operations with the two retained arrays threaded through. Destructured rather than
`{ aux with … }` for the same reason as there: in-place updates. -/

def streettPushF (aux : StreettAuxF State) (q : State) (_marks : Std.HashSet Nat) :
    StreettAuxF State × Nat :=
  let ⟨live, liveIndex, dead, dstack, wit, wopts, pending, ls, lo, ws⟩ := aux
  let pos := live.size
  (⟨live.push q, liveIndex.insert q pos, dead, dstack.push (pos, 0), wit, wopts, pending,
    ls.push #[], lo.push #[], ws⟩, pos)

def streettUpdateF (numMarks : Nat) (aux : StreettAuxF State) (marks : Std.HashSet Nat) (d : State) :
    StreettAuxF State × Bool :=
  let ⟨live, liveIndex, dead, dstack, wit, wopts, pending, ls, lo, ws⟩ := aux
  match dstack.back? with
  | none => (⟨live, liveIndex, dead, dstack, wit, wopts, pending, ls, lo, ws⟩, false)
  | some (ll, acc) =>
    let top := (min ll (liveIndex.getD d 0), acc ||| marksToBitmask marks ||| (1 <<< numMarks))
    (⟨live, liveIndex, dead, dstack.pop.push top, wit, wopts, pending, ls, lo, ws⟩, false)

/-- POP. The frame's expansion is stashed at its position first, so that when this frame closes an SCC
the scan sees its own edges too; the stash is dropped with the states by `shrink` wherever the proved
route calls `liveFlush`. -/
def streettPopF [Inhabited State] (cs : CompiledSpec State L) (curRegions : Nat)
    (aux : StreettAuxF State) (step : DFSStep State Nat) : StreettAuxF State × Bool :=
  let ⟨live, liveIndex, dead, dstack0, wit, wopts, pending, ls0, lo0, ws⟩ := aux
  let ls := ls0.setIfInBounds step.pos step.succ
  let lo := lo0.setIfInBounds step.pos step.succOpts
  match dstack0.back? with
  | none => (⟨live, liveIndex, dead, dstack0, wit, wopts, pending, ls, lo, ws⟩, false)
  | some (ll, acc) =>
    let dstack := dstack0.pop
    if ll = step.pos then
      if acc != fullAccMask cs.numMarks then
        let (live', liveIndex', dead') := liveFlush live liveIndex dead step.pos
        (⟨live', liveIndex', dead', dstack, wit, wopts, pending,
          ls.shrink step.pos, lo.shrink step.pos, ws⟩, false)
      else
        let (regionAlive, marksSeen) := scanFrameF cs liveIndex ls lo step.pos
        match firstUnsatisfied cs regionAlive marksSeen with
        | none =>
          let wit' := live.extract step.pos live.size
          -- the witness's successors, the same slice of the retained arrays (§13.26)
          let ws' := ls.extract step.pos live.size
          let wopts' := selectedOptions cs regionAlive marksSeen
          let (live', liveIndex', dead') := liveFlush live liveIndex dead step.pos
          (⟨live', liveIndex', dead', dstack, wit', wopts', pending,
            ls.shrink step.pos, lo.shrink step.pos, ws'⟩, true)
        | some liveOpts =>
          let pending' := liveOpts.foldl (init := pending) fun ps o =>
            let C : Candidate State := ⟨sccSetOf live step.pos, curRegions ||| (1 <<< o)⟩
            if C.states.isEmpty || curRegions.testBit o then ps else ps.push C
          let (live', liveIndex', dead') := liveFlush live liveIndex dead step.pos
          (⟨live', liveIndex', dead', dstack, wit, wopts, pending',
            ls.shrink step.pos, lo.shrink step.pos, ws⟩, false)
    else
      match dstack.back? with
      | none => (⟨live, liveIndex, dead, dstack, wit, wopts, pending, ls, lo, ws⟩, false)
      | some (pll, pacc) =>
        let merged := (min pll ll, pacc ||| step.acc ||| acc ||| (1 <<< cs.numMarks))
        (⟨live, liveIndex, dead, dstack.pop.push merged, wit, wopts, pending, ls, lo, ws⟩, false)

/-! ## The `DFSOps` instance and the drivers -/

def streettOpsF [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (curRegions : Nat) : DFSOps State where
  Aux := StreettAuxF State
  Position := Nat
  initAux := streettInitAuxF
  sccHint := fun aux =>
    aux.witness.foldl (init := Std.HashSet.emptyWithCapacity aux.witness.size) fun h s => h.insert s
  numExplored := fun aux => aux.live.size + aux.dead.size
  getStatus := fun aux q => liveStatusOf aux.liveIndex aux.dead q
  push := streettPushF
  update := streettUpdateF cs.numMarks
  -- `succs`/`edgeMarks` are not consulted: the frame carries everything POP needs
  pop := fun _succs _edgeMarks aux step => streettPopF cs curRegions aux step

section Drivers
variable [Inhabited State] [LawfulBEq State] [LawfulHashable State]

/-- One search. `dfsGo` hands `succs`/`edgeMarks` to `ops.pop` and nowhere else, and this `pop` ignores
them, so they are stubbed here: by construction the search expands through `expand` alone. -/
def streettRunF (cs : CompiledSpec State L) (curRegions : Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) (initialStates : List State) :
    Option (State × List State) × StreettAuxF State :=
  genericDFS (streettOpsF cs curRegions) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
    expand initialStates (streettOpsF cs curRegions).initAux

/-- A candidate's search: the region-restricted expansion *with bits*, filtered to its states in lockstep
as `Candidate.expand` does. -/
def candidateRunF (cs : CompiledSpec State L)
    (regionExpand : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (c : Candidate State) : Option (State × List State) × StreettAuxF State :=
  streettRunF cs c.regions (fun s => filterExpand (regionExpand (c.region cs) s) c.states.contains)
    c.states.toList

/-- `pruneLoop` for the fast path. -/
def pruneLoopF (cs : CompiledSpec State L)
    (regionExpand : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat) :
    Nat → List (Candidate State) →
      Option (Option (State × Array State × Array (Array State) × Array Nat × Candidate State) × Nat)
  | explored, [] => some (none, explored)
  | explored, c :: rest =>
    let (found?, aux) := candidateRunF cs regionExpand c
    let explored' := explored + aux.live.size + aux.dead.size
    match found? with
    | some (anchor, _) =>
      some (some (anchor, aux.witness, aux.witnessSuccs, aux.witnessOpts, c), explored')
    | none => pruneLoopF cs regionExpand explored' (aux.pending.toList ++ rest)
partial_fixpoint -- terminating for the reason `pruneLoop` is

/-- The retained witness successors as a lookup for the report. §13.26 -/
def witnessMemo (wit : Array State) (ws : Array (Array State)) : Std.HashMap State (Array State) :=
  (List.range wit.size).foldl (init := Std.HashMap.emptyWithCapacity wit.size) fun m k =>
    m.insert wit[k]! ws[k]!

/-- The report's graph: the memo, falling back to `g` off the witness. Equal to `g` as a function whenever
the memo is correct (`memoGraph_eq`), which is all `streettCheckF_eq` needs; `witnessCycle` only asks
about witness states, so the fallback is never taken. -/
def memoGraph (memo : Std.HashMap State (Array State)) (g : State → Array State) : State → Array State :=
  fun s => match memo[s]? with
    | some ss => ss
    | none => g s

/-- `streettCheck` for the fast path. `succs` and `edgeMarks` are used only at report time — the stem's
BFS, the cycle's rebuild and the lasso validation — never by a search. `regionExpand` is the spec's
restricted expansion *with bits*, which the candidate searches walk. -/
def streettCheckF (cs : CompiledSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (regionExpand : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (initialStates : List State) : EmptinessResult State :=
  match streettRunF cs 0 expand initialStates with
  | (some (anchor, stem), aux) =>
    buildResult cs (memoGraph (witnessMemo aux.witness aux.witnessSuccs) succs) succs edgeMarks
      initialStates aux.witness aux.witnessOpts anchor stem (aux.live.size + aux.dead.size)
  | (none, aux) =>
    match pruneLoopF cs regionExpand (aux.live.size + aux.dead.size) aux.pending.toList with
    | some (some (anchor, wit, ws, wopts, C), n) =>
      buildResult cs (memoGraph (witnessMemo wit ws) (C.graph cs cs.spec)) succs edgeMarks
        initialStates wit wopts anchor
        ((bfsFindPath aux.dead succs initialStates (· == anchor)).getD [anchor]) n
    | some (none, n) => .empty n
    | none => .empty (aux.live.size + aux.dead.size)

end Drivers

/-! ## Proof, part 1: the retained scan is the callback scan

`scanFrame` folds `scanOptionsAt` over the closing SCC's internal edges; `scanFrameF` folds
`(· &&& bits, · ||| (bits >>> numOptions))` over the retained ones. Both results are characterised bit
by bit — the callback scan's characterisation is `scanLabels_fst_testBit`/`scanLabels_snd_testBit`, in
`StreettPrune.lean` — and the two agree when the retained bits are `edgeBits`, the scan's own reading of
one edge packed the way `DFSStep.succOpts` packs it. -/

section ScanProof

/-- One edge's packed bits, defined *through* `scanOptionsAt` — from the full region mask and no marks,
the marks shifted above the regions — so that the scan's own `testBit` lemmas apply to it unchanged. -/
def CompiledSpec.edgeBits (cs : CompiledSpec State L) (lab : State × State) : Nat :=
  (scanOptionsAt cs lab 0 ((1 <<< cs.numOptions) - 1) 0).1 |||
    ((scanOptionsAt cs lab 0 ((1 <<< cs.numOptions) - 1) 0).2 <<< cs.numOptions)

omit [Hashable State] in
theorem CompiledSpec.edgeBits_testBit_lt (cs : CompiledSpec State L) (lab : State × State)
    {b : Nat} (hb : b < cs.numOptions) :
    (cs.edgeBits lab).testBit b = true ↔ cs.regions[b]! lab = true := by
  rw [CompiledSpec.edgeBits, Nat.testBit_or, Nat.testBit_shiftLeft]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, scanOptionsAt_fst_testBit]
  simp [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, hb, Nat.not_le.mpr hb]

omit [Hashable State] in
theorem CompiledSpec.edgeBits_testBit_ge (cs : CompiledSpec State L) (hwf : cs.WF)
    (lab : State × State) (b : Nat) :
    (cs.edgeBits lab).testBit (cs.numOptions + b) = true ↔
      ∃ p, p < cs.numOptions ∧ ∃ k, k < (cs.optMarks[p]!).size ∧
        cs.optMarkBase[p]! + k = b ∧ (cs.optMarks[p]!)[k]! lab = true := by
  rw [CompiledSpec.edgeBits, Nat.testBit_or, Nat.testBit_shiftLeft]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, scanOptionsAt_fst_testBit,
    scanOptionsAt_snd_testBit cs hwf]
  simp [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

omit [Hashable State] in
/-- No edge carries a mark bit at or above `numOptMarks`: what makes the scan's early exit lossless. -/
theorem CompiledSpec.edgeBits_testBit_ge_false (cs : CompiledSpec State L) (hwf : cs.WF)
    (lab : State × State) {b : Nat} (hb : cs.numOptMarks ≤ b) :
    (cs.edgeBits lab).testBit (cs.numOptions + b) = false := by
  by_contra h
  obtain ⟨p, hp, k, hk, hbk, _⟩ := (cs.edgeBits_testBit_ge hwf lab b).mp (by simpa using h)
  have := hwf.bit_lt hp hk
  omega

/-- `t` lies in the SCC closing at `lo`, as the retained scan decides it. -/
private def InSccF (liveIndex : Std.HashMap State Nat) (lo : Nat) (t : State) : Prop :=
  ∃ j, liveIndex[t]? = some j ∧ lo ≤ j

private theorem sameBitsFrom_eq_true (os : Array Nat) (n b : Nat) :
    ∀ m k, n - k = m → (sameBitsFrom os n k b = true ↔ ∀ k', k ≤ k' → k' < n → os[k']! = b) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro k hm
  rw [sameBitsFrom]
  by_cases hk : k < n
  · simp only [hk, dite_true, Bool.and_eq_true, beq_iff_eq]
    rw [ih (n - (k + 1)) (by omega) (k + 1) rfl]
    constructor
    · rintro ⟨h0, hrest⟩ k' hkk' hk'
      rcases Nat.eq_or_lt_of_le hkk' with rfl | hlt
      · exact h0
      · exact hrest k' hlt hk'
    · intro h
      exact ⟨h k (Nat.le_refl _) hk, fun k' hkk' hk' => h k' (Nat.le_of_succ_le hkk') hk'⟩
  · simp only [hk, dite_false, true_iff]
    intro k' hkk' hk'; omega

private theorem scanEdgesF_fst_testBit (liveIndex : Std.HashMap State Nat) (lo shift : Nat)
    (ss : Array State) (os : Array Nat) (b : Nat) (uniform : Bool)
    (huni : uniform = true → ∀ k', k' < ss.size → os[k']! = os[0]!) :
    ∀ n k ra ms, ss.size - k = n →
      ((scanEdgesF liveIndex lo shift ss os uniform k ra ms).1.testBit b = true ↔
        ra.testBit b = true ∧ ∀ k', k ≤ k' → (hk' : k' < ss.size) →
          InSccF liveIndex lo ss[k'] → (os[k']!).testBit b = true) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k ra ms hn
  rw [scanEdgesF]
  by_cases hk : k < ss.size
  · simp only [hk, dite_true]
    have hrec : ∀ ra' ms', (scanEdgesF liveIndex lo shift ss os uniform (k + 1) ra' ms').1.testBit b = true ↔
        ra'.testBit b = true ∧ ∀ k', k + 1 ≤ k' → (hk' : k' < ss.size) →
          InSccF liveIndex lo ss[k'] → (os[k']!).testBit b = true :=
      fun ra' ms' => ih (ss.size - (k + 1)) (by omega) (k + 1) ra' ms' rfl
    cases hm : liveIndex[ss[k]]? with
    | none =>
      rw [hrec]
      have hno : ¬ InSccF liveIndex lo ss[k] := by rintro ⟨j, hj, _⟩; rw [hm] at hj; cases hj
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun k' hkk' hk' hin => ?_⟩
        rcases Nat.eq_or_lt_of_le hkk' with rfl | hlt
        · exact absurd hin hno
        · exact h2 k' hlt hk' hin
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun k' hkk' hk' hin => h2 k' (Nat.le_of_succ_le hkk') hk' hin⟩
    | some j =>
      by_cases hj : lo ≤ j
      · simp only [hj, if_true]
        have hyes : InSccF liveIndex lo ss[k] := ⟨j, hm, hj⟩
        by_cases hu : uniform = true
        · -- the early exit: every later edge of this state carries `os[k]!`
          simp only [hu, if_true]
          rw [Nat.testBit_and, Bool.and_eq_true]
          constructor
          · rintro ⟨h1, hb'⟩
            refine ⟨h1, fun k' _ hk' _ => ?_⟩
            rw [huni hu k' hk', ← huni hu k hk]; exact hb'
          · rintro ⟨h1, h2⟩
            exact ⟨h1, h2 k (Nat.le_refl _) hk hyes⟩
        · rw [if_neg hu]
          rw [hrec, Nat.testBit_and, Bool.and_eq_true]
          constructor
          · rintro ⟨⟨h1, hb'⟩, h2⟩
            refine ⟨h1, fun k' hkk' hk' hin => ?_⟩
            rcases Nat.eq_or_lt_of_le hkk' with rfl | hlt
            · exact hb'
            · exact h2 k' hlt hk' hin
          · rintro ⟨h1, h2⟩
            exact ⟨⟨h1, h2 k (Nat.le_refl _) hk hyes⟩,
              fun k' hkk' hk' hin => h2 k' (Nat.le_of_succ_le hkk') hk' hin⟩
      · simp only [hj, if_false]
        rw [hrec]
        have hno : ¬ InSccF liveIndex lo ss[k] := by
          rintro ⟨j', hj', hlo⟩; rw [hm] at hj'; cases hj'; exact hj hlo
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun k' hkk' hk' hin => ?_⟩
          rcases Nat.eq_or_lt_of_le hkk' with rfl | hlt
          · exact absurd hin hno
          · exact h2 k' hlt hk' hin
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun k' hkk' hk' hin => h2 k' (Nat.le_of_succ_le hkk') hk' hin⟩
  · simp only [hk, dite_false]
    constructor
    · intro h; exact ⟨h, fun k' hkk' hk' _ => absurd hk' (by omega)⟩
    · exact fun h => h.1

private theorem scanEdgesF_snd_testBit (liveIndex : Std.HashMap State Nat) (lo shift : Nat)
    (ss : Array State) (os : Array Nat) (b : Nat) (uniform : Bool)
    (huni : uniform = true → ∀ k', k' < ss.size → os[k']! = os[0]!) :
    ∀ n k ra ms, ss.size - k = n →
      ((scanEdgesF liveIndex lo shift ss os uniform k ra ms).2.testBit b = true ↔
        ms.testBit b = true ∨ ∃ k', k ≤ k' ∧ ∃ hk' : k' < ss.size,
          InSccF liveIndex lo ss[k'] ∧ (os[k']!).testBit (shift + b) = true) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k ra ms hn
  rw [scanEdgesF]
  by_cases hk : k < ss.size
  · simp only [hk, dite_true]
    have hrec : ∀ ra' ms', (scanEdgesF liveIndex lo shift ss os uniform (k + 1) ra' ms').2.testBit b = true ↔
        ms'.testBit b = true ∨ ∃ k', k + 1 ≤ k' ∧ ∃ hk' : k' < ss.size,
          InSccF liveIndex lo ss[k'] ∧ (os[k']!).testBit (shift + b) = true :=
      fun ra' ms' => ih (ss.size - (k + 1)) (by omega) (k + 1) ra' ms' rfl
    cases hm : liveIndex[ss[k]]? with
    | none =>
      rw [hrec]
      have hno : ¬ InSccF liveIndex lo ss[k] := by rintro ⟨j, hj, _⟩; rw [hm] at hj; cases hj
      constructor
      · rintro (h | ⟨k', hkk', hk', hin, hbit⟩)
        · exact Or.inl h
        · exact Or.inr ⟨k', Nat.le_of_succ_le hkk', hk', hin, hbit⟩
      · rintro (h | ⟨k', hkk', hk', hin, hbit⟩)
        · exact Or.inl h
        · rcases Nat.eq_or_lt_of_le hkk' with rfl | hlt
          · exact absurd hin hno
          · exact Or.inr ⟨k', hlt, hk', hin, hbit⟩
    | some j =>
      by_cases hj : lo ≤ j
      · simp only [hj, if_true]
        have hyes : InSccF liveIndex lo ss[k] := ⟨j, hm, hj⟩
        by_cases hu : uniform = true
        · -- the early exit, as in `scanEdgesF_fst_testBit`
          simp only [hu, if_true]
          rw [Nat.testBit_or, Nat.testBit_shiftRight, Bool.or_eq_true]
          constructor
          · rintro (h | hb')
            · exact Or.inl h
            · exact Or.inr ⟨k, Nat.le_refl _, hk, hyes, hb'⟩
          · rintro (h | ⟨k', _, hk', _, hbit⟩)
            · exact Or.inl h
            · refine Or.inr ?_
              rw [huni hu k hk, ← huni hu k' hk']; exact hbit
        · rw [if_neg hu]
          rw [hrec, Nat.testBit_or, Nat.testBit_shiftRight, Bool.or_eq_true]
          constructor
          · rintro ((h | hb') | ⟨k', hkk', hk', hin, hbit⟩)
            · exact Or.inl h
            · exact Or.inr ⟨k, Nat.le_refl _, hk, hyes, hb'⟩
            · exact Or.inr ⟨k', Nat.le_of_succ_le hkk', hk', hin, hbit⟩
          · rintro (h | ⟨k', hkk', hk', hin, hbit⟩)
            · exact Or.inl (Or.inl h)
            · rcases Nat.eq_or_lt_of_le hkk' with rfl | hlt
              · exact Or.inl (Or.inr hbit)
              · exact Or.inr ⟨k', hlt, hk', hin, hbit⟩
      · simp only [hj, if_false]
        rw [hrec]
        have hno : ¬ InSccF liveIndex lo ss[k] := by
          rintro ⟨j', hj', hlo⟩; rw [hm] at hj'; cases hj'; exact hj hlo
        constructor
        · rintro (h | ⟨k', hkk', hk', hin, hbit⟩)
          · exact Or.inl h
          · exact Or.inr ⟨k', Nat.le_of_succ_le hkk', hk', hin, hbit⟩
        · rintro (h | ⟨k', hkk', hk', hin, hbit⟩)
          · exact Or.inl h
          · rcases Nat.eq_or_lt_of_le hkk' with rfl | hlt
            · exact absurd hin hno
            · exact Or.inr ⟨k', hlt, hk', hin, hbit⟩
  · simp only [hk, dite_false]
    constructor
    · exact Or.inl
    · rintro (h | ⟨k', _, hk', _, _⟩)
      · exact h
      · exact absurd hk' (by omega)

private theorem scanLiveF_fst_testBit (cs : CompiledSpec State L) (liveIndex : Std.HashMap State Nat)
    (lsuccs : Array (Array State)) (lopts : Array (Array Nat)) (lo fullMarks b : Nat) :
    ∀ n i ra ms, lsuccs.size - i = n →
      ((scanLiveF cs liveIndex lsuccs lopts lo fullMarks i ra ms).1.testBit b = true ↔
        ra.testBit b = true ∧ ∀ j, i ≤ j → (hj : j < lsuccs.size) → ∀ k, (hk : k < lsuccs[j].size) →
          InSccF liveIndex lo lsuccs[j][k] → (lopts[j]![k]!).testBit b = true) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i ra ms hn
  rw [scanLiveF]
  by_cases hi : i < lsuccs.size
  · simp only [hi, dite_true]
    by_cases hexit : (ra == 0 && ms == fullMarks) = true
    · rw [if_pos hexit]
      simp only [Bool.and_eq_true, beq_iff_eq] at hexit
      simp [hexit.1]
    · rw [if_neg hexit]
      have huni : sameBitsFrom lopts[i]! lsuccs[i].size 0 (lopts[i]!)[0]! = true →
          ∀ k', k' < lsuccs[i].size → (lopts[i]!)[k']! = (lopts[i]!)[0]! :=
        fun hu k' hk' => (sameBitsFrom_eq_true _ _ _ _ 0 rfl).mp hu k' (Nat.zero_le _) hk'
      rcases hs : scanEdgesF liveIndex lo cs.numOptions lsuccs[i] lopts[i]!
        (sameBitsFrom lopts[i]! lsuccs[i].size 0 (lopts[i]!)[0]!) 0 ra ms with ⟨ra', ms'⟩
      simp only []
      rw [ih (lsuccs.size - (i + 1)) (by omega) (i + 1) ra' ms' rfl]
      have h1 := scanEdgesF_fst_testBit liveIndex lo cs.numOptions lsuccs[i] lopts[i]! b _ huni _ 0 ra ms rfl
      rw [hs] at h1
      simp only [] at h1
      rw [h1]
      constructor
      · rintro ⟨⟨hra, hcur⟩, hrest⟩
        refine ⟨hra, fun j hij hj k hk hin => ?_⟩
        rcases Nat.eq_or_lt_of_le hij with rfl | hlt
        · exact hcur k (Nat.zero_le _) hk hin
        · exact hrest j hlt hj k hk hin
      · rintro ⟨hra, hall⟩
        exact ⟨⟨hra, fun k _ hk hin => hall i (Nat.le_refl _) hi k hk hin⟩,
          fun j hij hj k hk hin => hall j (Nat.le_of_succ_le hij) hj k hk hin⟩
  · simp only [hi, dite_false]
    constructor
    · intro h; exact ⟨h, fun j _ hj => absurd hj (by omega)⟩
    · exact fun h => h.1

private theorem scanLiveF_snd_testBit (cs : CompiledSpec State L) (liveIndex : Std.HashMap State Nat)
    (lsuccs : Array (Array State)) (lopts : Array (Array Nat)) (lo m b : Nat)
    (hbound : ∀ j, lo ≤ j → (hj : j < lsuccs.size) → ∀ k, (hk : k < lsuccs[j].size) → ∀ b', m ≤ b' →
      (lopts[j]![k]!).testBit (cs.numOptions + b') = false) :
    ∀ n i ra ms, lo ≤ i → lsuccs.size - i = n →
      ((scanLiveF cs liveIndex lsuccs lopts lo ((1 <<< m) - 1) i ra ms).2.testBit b = true ↔
        ms.testBit b = true ∨ ∃ j, i ≤ j ∧ ∃ hj : j < lsuccs.size, ∃ k, ∃ hk : k < lsuccs[j].size,
          InSccF liveIndex lo lsuccs[j][k] ∧ (lopts[j]![k]!).testBit (cs.numOptions + b) = true) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i ra ms hloi hn
  rw [scanLiveF]
  by_cases hi : i < lsuccs.size
  · simp only [hi, dite_true]
    by_cases hexit : (ra == 0 && ms == (1 <<< m) - 1) = true
    · rw [if_pos hexit]
      simp only [Bool.and_eq_true, beq_iff_eq] at hexit
      rw [hexit.2]
      constructor
      · exact Or.inl
      · rintro (h | ⟨j, hij, hj, k, hk, _, hbit⟩)
        · exact h
        · by_cases hbm : b < m
          · simp [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, hbm]
          · rw [hbound j (by omega) hj k hk b (Nat.le_of_not_lt hbm)] at hbit; cases hbit
    · rw [if_neg hexit]
      have huni : sameBitsFrom lopts[i]! lsuccs[i].size 0 (lopts[i]!)[0]! = true →
          ∀ k', k' < lsuccs[i].size → (lopts[i]!)[k']! = (lopts[i]!)[0]! :=
        fun hu k' hk' => (sameBitsFrom_eq_true _ _ _ _ 0 rfl).mp hu k' (Nat.zero_le _) hk'
      rcases hs : scanEdgesF liveIndex lo cs.numOptions lsuccs[i] lopts[i]!
        (sameBitsFrom lopts[i]! lsuccs[i].size 0 (lopts[i]!)[0]!) 0 ra ms with ⟨ra', ms'⟩
      simp only []
      rw [ih (lsuccs.size - (i + 1)) (by omega) (i + 1) ra' ms' (by omega) rfl]
      have h2 := scanEdgesF_snd_testBit liveIndex lo cs.numOptions lsuccs[i] lopts[i]! b _ huni _ 0 ra ms rfl
      rw [hs] at h2
      simp only [] at h2
      rw [h2]
      constructor
      · rintro ((h | ⟨k, _, hk, hin, hbit⟩) | ⟨j, hij, hj, k, hk, hin, hbit⟩)
        · exact Or.inl h
        · exact Or.inr ⟨i, Nat.le_refl _, hi, k, hk, hin, hbit⟩
        · exact Or.inr ⟨j, Nat.le_of_succ_le hij, hj, k, hk, hin, hbit⟩
      · rintro (h | ⟨j, hij, hj, k, hk, hin, hbit⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.eq_or_lt_of_le hij with rfl | hlt
          · exact Or.inl (Or.inr ⟨k, Nat.zero_le _, hk, hin, hbit⟩)
          · exact Or.inr ⟨j, hlt, hj, k, hk, hin, hbit⟩
  · simp only [hi, dite_false]
    constructor
    · exact Or.inl
    · rintro (h | ⟨j, _, hj, _⟩)
      · exact h
      · exact absurd hj (by omega)

/-- The retained scan's membership test is the flushed range read as a set. -/
private theorem inSccF_iff [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {live : Array State} {liveIndex : Std.HashMap State Nat}
    (hlwf : LiveWF live liveIndex) (lo : Nat) (t : State) :
    InSccF liveIndex lo t ↔ t ∈ sccSetOf live lo := by
  rw [sccSetOf, mem_sccSet, List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨j, hj, hlo⟩
    obtain ⟨hjlt, hje⟩ := hlwf.bwd t j hj
    refine ⟨j - lo, by simp only [Array.length_toList]; omega, ?_⟩
    have hidx : lo + (j - lo) = j := by omega
    simp only [hidx, Array.getElem_toList]
    rw [← hje, getElem!_pos live j hjlt]
  · rintro ⟨j', hj', hje⟩
    have hlt : lo + j' < live.size := by simp only [Array.length_toList] at hj'; omega
    refine ⟨lo + j', ?_, by omega⟩
    have := hlwf.fwd (lo + j') hlt
    rw [Array.getElem_toList] at hje
    rw [← hje]; exact this

/-- The callback scan's edge list, read as a universal statement over the retained arrays. -/
private theorem internalEdges_forall_iff [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {succs : State → Array State}
    {live : Array State} {liveIndex : Std.HashMap State Nat} {lsuccs : Array (Array State)} {lo : Nat}
    (hlwf : LiveWF live liveIndex) (h1 : lsuccs.size = live.size)
    (hret : ∀ i, lo ≤ i → (hi : i < live.size) → lsuccs[i]! = succs live[i])
    (P : State × State → Prop) :
    (∀ e ∈ internalEdges succs (sccSetOf live lo) (live.toList.drop lo), P e) ↔
      ∀ j, lo ≤ j → (hj : j < lsuccs.size) → ∀ k, (hk : k < lsuccs[j].size) →
        InSccF liveIndex lo lsuccs[j][k] → P (live[j]'(h1 ▸ hj), lsuccs[j][k]) := by
  constructor
  · intro h j hlo hj k hk hin
    have hjl : j < live.size := h1 ▸ hj
    have hs : lsuccs[j] = succs live[j] := by rw [← getElem!_pos lsuccs j hj]; exact hret j hlo hjl
    refine h _ (mem_internalEdges.mpr ⟨?_, ?_, (inSccF_iff hlwf lo _).mp hin⟩)
    · show live[j] ∈ live.toList.drop lo
      rw [List.mem_drop_iff_getElem]
      refine ⟨j - lo, by simp only [Array.length_toList]; omega, ?_⟩
      have hidx : lo + (j - lo) = j := by omega
      simp only [hidx, Array.getElem_toList]
    · show lsuccs[j][k] ∈ succs live[j]
      rw [← hs]; exact Array.getElem_mem hk
  · intro h e he
    obtain ⟨e1, e2⟩ := e
    obtain ⟨hmem, hsucc, hB⟩ := mem_internalEdges.mp he
    simp only [] at hmem hsucc hB
    rw [List.mem_drop_iff_getElem] at hmem
    obtain ⟨j', hj', hje⟩ := hmem
    have hlt : lo + j' < live.size := by simp only [Array.length_toList] at hj'; omega
    rw [Array.getElem_toList] at hje
    subst hje
    have hjs : lo + j' < lsuccs.size := h1 ▸ hlt
    have hs : lsuccs[lo + j'] = succs live[lo + j'] := by
      rw [← getElem!_pos lsuccs _ hjs]; exact hret _ (Nat.le_add_right _ _) hlt
    rw [← hs] at hsucc
    obtain ⟨k, hk, hke⟩ := Array.mem_iff_getElem.mp hsucc
    subst hke
    exact h (lo + j') (Nat.le_add_right _ _) hjs k hk ((inSccF_iff hlwf lo _).mpr hB)

/-- The same, existentially. -/
private theorem internalEdges_exists_iff [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {succs : State → Array State}
    {live : Array State} {liveIndex : Std.HashMap State Nat} {lsuccs : Array (Array State)} {lo : Nat}
    (hlwf : LiveWF live liveIndex) (h1 : lsuccs.size = live.size)
    (hret : ∀ i, lo ≤ i → (hi : i < live.size) → lsuccs[i]! = succs live[i])
    (P : State × State → Prop) :
    (∃ e ∈ internalEdges succs (sccSetOf live lo) (live.toList.drop lo), P e) ↔
      ∃ j, lo ≤ j ∧ ∃ hj : j < lsuccs.size, ∃ k, ∃ hk : k < lsuccs[j].size,
        InSccF liveIndex lo lsuccs[j][k] ∧ P (live[j]'(h1 ▸ hj), lsuccs[j][k]) := by
  constructor
  · rintro ⟨⟨e1, e2⟩, he, hP⟩
    obtain ⟨hmem, hsucc, hB⟩ := mem_internalEdges.mp he
    simp only [] at hmem hsucc hB
    rw [List.mem_drop_iff_getElem] at hmem
    obtain ⟨j', hj', hje⟩ := hmem
    have hlt : lo + j' < live.size := by simp only [Array.length_toList] at hj'; omega
    rw [Array.getElem_toList] at hje
    subst hje
    have hjs : lo + j' < lsuccs.size := h1 ▸ hlt
    have hs : lsuccs[lo + j'] = succs live[lo + j'] := by
      rw [← getElem!_pos lsuccs _ hjs]; exact hret _ (Nat.le_add_right _ _) hlt
    rw [← hs] at hsucc
    obtain ⟨k, hk, hke⟩ := Array.mem_iff_getElem.mp hsucc
    subst hke
    exact ⟨lo + j', Nat.le_add_right _ _, hjs, k, hk, (inSccF_iff hlwf lo _).mpr hB, hP⟩
  · rintro ⟨j, hlo, hj, k, hk, hin, hP⟩
    have hjl : j < live.size := h1 ▸ hj
    have hs : lsuccs[j] = succs live[j] := by rw [← getElem!_pos lsuccs j hj]; exact hret j hlo hjl
    refine ⟨_, mem_internalEdges.mpr ⟨?_, ?_, (inSccF_iff hlwf lo _).mp hin⟩, hP⟩
    · show live[j] ∈ live.toList.drop lo
      rw [List.mem_drop_iff_getElem]
      refine ⟨j - lo, by simp only [Array.length_toList]; omega, ?_⟩
      have hidx : lo + (j - lo) = j := by omega
      simp only [hidx, Array.getElem_toList]
    · show lsuccs[j][k] ∈ succs live[j]
      rw [← hs]; exact Array.getElem_mem hk

/-- **The retained scan is the callback scan.** On a live stack whose retained arrays hold, from `lo`
up, each state's successors and their `edgeBits`, the two frames agree. When the spec has no options
the payload may be anything — `#[]` on the wired routes — because the scan's early exit fires before
it is read. -/
theorem scanFrameF_eq_scanFrame [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF)
    (succs : State → Array State) (live : Array State) (liveIndex : Std.HashMap State Nat)
    (lsuccs : Array (Array State)) (lopts : Array (Array Nat)) (lo : Nat)
    (hlwf : LiveWF live liveIndex) (h1 : lsuccs.size = live.size)
    (hret : ∀ i, lo ≤ i → (hi : i < live.size) → lsuccs[i]! = succs live[i])
    (hbits : cs.numOptions ≠ 0 → ∀ i, lo ≤ i → (hi : i < live.size) →
      lopts[i]! = (succs live[i]).map fun t => cs.edgeBits (live[i], t)) :
    scanFrameF cs liveIndex lsuccs lopts lo = scanFrame cs succs live lo := by
  by_cases hn : cs.numOptions = 0
  · -- no options: both scans return `(0, 0)` without reading an edge
    have hm : cs.numOptMarks = 0 := by rw [hwf.numOptMarks_eq, hn]; exact hwf.base_zero
    have hlhs : scanFrameF cs liveIndex lsuccs lopts lo = (0, 0) := by
      rw [scanFrameF, hn, hm, scanLiveF]
      by_cases hi : lo < lsuccs.size
      · simp [hi]
      · simp [hi]
    rw [hlhs, scanFrame, scanLetters, hn]
    simp only [Nat.shiftLeft_zero, Nat.sub_self]
    have hfst := fun b => scanLabels_fst_testBit cs b
      (internalEdges succs (sccSetOf live lo) (live.toList.drop lo)) 0 0
    have hsnd := fun b => scanLabels_snd_testBit cs hwf b
      (internalEdges succs (sccSetOf live lo) (live.toList.drop lo)) 0 0
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_and, iff_false, Bool.not_eq_true] at hfst
    rw [hn] at hsnd
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_or] at hsnd
    refine Prod.ext ?_ ?_
    · symm; apply Nat.eq_of_testBit_eq; intro b; simp [hfst b]
    · symm; apply Nat.eq_of_testBit_eq; intro b; rw [Nat.zero_testBit]
      by_contra hc
      obtain ⟨_, _, p, hp, _⟩ := (hsnd b).mp (by simpa using hc)
      omega
  · -- options: bit by bit, through the two characterisations
    have hbits' := hbits hn
    have hentry : ∀ j, lo ≤ j → (hj : j < lsuccs.size) → ∀ k, (hk : k < lsuccs[j].size) →
        lopts[j]![k]! = cs.edgeBits (live[j]'(h1 ▸ hj), lsuccs[j][k]) := by
      intro j hlo hj k hk
      have hjl : j < live.size := h1 ▸ hj
      have hs : lsuccs[j] = succs live[j] := by rw [← getElem!_pos lsuccs j hj]; exact hret j hlo hjl
      have hk' : k < ((succs live[j]).map fun t => cs.edgeBits (live[j], t)).size := by
        rw [Array.size_map, ← hs]; exact hk
      rw [hbits' j hlo hjl, getElem!_pos _ k hk', Array.getElem_map]
      simp only [hs]
    have hbound : ∀ j, lo ≤ j → (hj : j < lsuccs.size) → ∀ k, (hk : k < lsuccs[j].size) →
        ∀ b', cs.numOptMarks ≤ b' → (lopts[j]![k]!).testBit (cs.numOptions + b') = false := by
      intro j hlo hj k hk b' hb'
      rw [hentry j hlo hj k hk]; exact cs.edgeBits_testBit_ge_false hwf _ hb'
    refine Prod.ext ?_ ?_
    · apply Nat.eq_of_testBit_eq; intro b
      rw [scanFrameF, scanFrame, scanLetters]
      apply Bool.eq_iff_iff.mpr
      rw [scanLiveF_fst_testBit cs liveIndex lsuccs lopts lo _ b _ lo _ _ rfl,
        scanLabels_fst_testBit]
      by_cases hb : b < cs.numOptions
      · simp only [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, hb, decide_true, true_and,
          true_implies]
        rw [internalEdges_forall_iff hlwf h1 hret (fun e => cs.regions[b]! e = true)]
        constructor <;> intro h j hlo hj k hk hin
        · have := h j hlo hj k hk hin
          rw [hentry j hlo hj k hk] at this
          exact (cs.edgeBits_testBit_lt _ hb).mp this
        · rw [hentry j hlo hj k hk]
          exact (cs.edgeBits_testBit_lt _ hb).mpr (h j hlo hj k hk hin)
      · simp [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, hb]
    · apply Nat.eq_of_testBit_eq; intro b
      rw [scanFrameF, scanFrame, scanLetters]
      apply Bool.eq_iff_iff.mpr
      rw [scanLiveF_snd_testBit cs liveIndex lsuccs lopts lo cs.numOptMarks b hbound _ lo _ _
          (Nat.le_refl _) rfl, scanLabels_snd_testBit cs hwf]
      simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
      rw [internalEdges_exists_iff hlwf h1 hret (fun l => ∃ p, p < cs.numOptions ∧
        ∃ k, k < (cs.optMarks[p]!).size ∧ cs.optMarkBase[p]! + k = b ∧
          (cs.optMarks[p]!)[k]! l = true)]
      constructor
      · rintro ⟨j, hlo, hj, k, hk, hin, hbit⟩
        refine ⟨j, hlo, hj, k, hk, hin, ?_⟩
        rw [hentry j hlo hj k hk] at hbit
        exact (cs.edgeBits_testBit_ge hwf _ b).mp hbit
      · rintro ⟨j, hlo, hj, k, hk, hin, hP⟩
        refine ⟨j, hlo, hj, k, hk, hin, ?_⟩
        rw [hentry j hlo hj k hk]
        exact (cs.edgeBits_testBit_ge hwf _ b).mpr hP

end ScanProof

/-! ## Proof, part 2: what a letter's bits are -/

section LetterBits

omit [BEq State] [Hashable State] in
private theorem markBitsAt_testBit (gs : Array (L → Bool)) (l : L) (base b : Nat) :
    ∀ n j acc, gs.size - j = n →
      ((markBitsAt gs l base j acc).testBit b = true ↔
        acc.testBit b = true ∨ ∃ k, j ≤ k ∧ k < gs.size ∧ base + k = b ∧ gs[k]! l = true) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j acc hn
  rw [markBitsAt]
  by_cases hj : j < gs.size
  · simp only [hj, dite_true]
    rw [ih (gs.size - (j + 1)) (by omega) (j + 1) _ rfl]
    have hget : gs[j]! = gs[j] := getElem!_pos gs j hj
    by_cases hc : gs[j] l = true
    · simp only [hc, if_true, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
        decide_eq_true_eq]
      constructor
      · rintro ((h | h) | ⟨k, hjk, hk, hbk, hgk⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, Nat.le_refl _, hj, h, by rw [hget]; exact hc⟩
        · exact Or.inr ⟨k, Nat.le_of_succ_le hjk, hk, hbk, hgk⟩
      · rintro (h | ⟨k, hjk, hk, hbk, hgk⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
          · exact Or.inl (Or.inr hbk)
          · exact Or.inr ⟨k, hlt, hk, hbk, hgk⟩
    · simp only [hc]
      constructor
      · rintro (h | ⟨k, hjk, hk, hbk, hgk⟩)
        · exact Or.inl h
        · exact Or.inr ⟨k, Nat.le_of_succ_le hjk, hk, hbk, hgk⟩
      · rintro (h | ⟨k, hjk, hk, hbk, hgk⟩)
        · exact Or.inl h
        · rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
          · exact absurd (hget ▸ hgk) hc
          · exact Or.inr ⟨k, hlt, hk, hbk, hgk⟩
  · simp only [hj, dite_false]
    constructor
    · exact Or.inl
    · rintro (h | ⟨k, hjk, hk, _, _⟩)
      · exact h
      · omega

omit [BEq State] [Hashable State] in
private theorem letterBitsFrom_testBit (cs : CompiledSpec State L) (l : L) (b : Nat) :
    ∀ n o acc, cs.letterOptions.size - o = n →
      ((letterBitsFrom cs l o acc).testBit b = true ↔
        acc.testBit b = true ∨
        (o ≤ b ∧ b < cs.letterOptions.size ∧ (cs.letterOptions[b]!).region l = true) ∨
        (∃ p, o ≤ p ∧ p < cs.letterOptions.size ∧ (cs.letterOptions[p]!).region l = true ∧
          ∃ k, k < (cs.letterOptions[p]!).marks.size ∧ cs.numOptions + cs.optMarkBase[p]! + k = b ∧
            ((cs.letterOptions[p]!).marks)[k]! l = true)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro o acc hn
  rw [letterBitsFrom]
  by_cases ho : o < cs.letterOptions.size
  · simp only [ho, dite_true]
    rw [ih (cs.letterOptions.size - (o + 1)) (by omega) (o + 1) _ rfl]
    have hget : cs.letterOptions[o]! = cs.letterOptions[o] := getElem!_pos _ o ho
    by_cases hr : cs.letterOptions[o].region l = true
    · simp only [hr, if_true]
      rw [markBitsAt_testBit _ _ _ _ _ 0 _ rfl]
      simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
        decide_eq_true_eq, Nat.zero_le, true_and]
      constructor
      · rintro (((h | h) | ⟨k, hk, hbk, hgk⟩) | ⟨hob, hb, hrb⟩ | ⟨p, hop, hp, hrp, k, hk, hbk, hgk⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨h ▸ Nat.le_refl _, h ▸ ho, by rw [← h, hget]; exact hr⟩)
        · exact Or.inr (Or.inr ⟨o, Nat.le_refl _, ho, by rw [hget]; exact hr, k, by rw [hget]; exact hk,
            by omega, by rw [hget]; exact hgk⟩)
        · exact Or.inr (Or.inl ⟨Nat.le_of_succ_le hob, hb, hrb⟩)
        · exact Or.inr (Or.inr ⟨p, Nat.le_of_succ_le hop, hp, hrp, k, hk, hbk, hgk⟩)
      · rintro (h | ⟨hob, hb, hrb⟩ | ⟨p, hop, hp, hrp, k, hk, hbk, hgk⟩)
        · exact Or.inl (Or.inl (Or.inl h))
        · rcases Nat.eq_or_lt_of_le hob with rfl | hlt
          · exact Or.inl (Or.inl (Or.inr rfl))
          · exact Or.inr (Or.inl ⟨hlt, hb, hrb⟩)
        · rcases Nat.eq_or_lt_of_le hop with rfl | hlt
          · exact Or.inl (Or.inr ⟨k, by rw [← hget]; exact hk, by omega, by rw [← hget]; exact hgk⟩)
          · exact Or.inr (Or.inr ⟨p, hlt, hp, hrp, k, hk, hbk, hgk⟩)
    · simp only [hr]
      constructor
      · rintro (h | ⟨hob, hb, hrb⟩ | ⟨p, hop, hp, hrp, k, hk, hbk, hgk⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨Nat.le_of_succ_le hob, hb, hrb⟩)
        · exact Or.inr (Or.inr ⟨p, Nat.le_of_succ_le hop, hp, hrp, k, hk, hbk, hgk⟩)
      · rintro (h | ⟨hob, hb, hrb⟩ | ⟨p, hop, hp, hrp, k, hk, hbk, hgk⟩)
        · exact Or.inl h
        · rcases Nat.eq_or_lt_of_le hob with rfl | hlt
          · exact absurd (hget ▸ hrb) hr
          · exact Or.inr (Or.inl ⟨hlt, hb, hrb⟩)
        · rcases Nat.eq_or_lt_of_le hop with rfl | hlt
          · exact absurd (hget ▸ hrp) hr
          · exact Or.inr (Or.inr ⟨p, hlt, hp, hrp, k, hk, hbk, hgk⟩)
  · simp only [ho, dite_false]
    constructor
    · exact Or.inl
    · rintro (h | ⟨hob, hb, _⟩ | ⟨p, hop, hp, _⟩)
      · exact h
      · omega
      · omega

omit [Hashable State] in
/-- What `letterBits` says, bit by bit. Region bit `o` is option `o`'s region on the letter; mark bit
`numOptions + optMarkBase[p] + k` is option `p`'s region *and* its mark `k` on the letter — the
conjunction `StreettOption.onEdges` builds into each mark predicate. -/
theorem CompiledSpec.letterBits_testBit (cs : CompiledSpec State L) (hwf : cs.WF) (l : L) (b : Nat) :
    (cs.letterBits l).testBit b = true ↔
      (b < cs.numOptions ∧ (cs.letterOptions[b]!).region l = true) ∨
      (∃ p, p < cs.numOptions ∧ (cs.letterOptions[p]!).region l = true ∧
        ∃ k, k < (cs.letterOptions[p]!).marks.size ∧ cs.numOptions + cs.optMarkBase[p]! + k = b ∧
          ((cs.letterOptions[p]!).marks)[k]! l = true) := by
  rw [CompiledSpec.letterBits, letterBitsFrom_testBit cs l b _ 0 0 rfl, hwf.letterOptions_size]
  simp [Nat.zero_testBit]

end LetterBits

/-! ## Proof, part 3: the fast operations run in lockstep with the proved ones

The fast search state projects onto the proved one by forgetting the two retained arrays. The DFS stacks
of the two runs agree on every field but `succOpts`, which the proved route never reads. `InvF` is what
the fast side maintains on top: the retained arrays are parallel to `live`, every frame on the stack sits
at its own live position with the expansion it was built from, positions strictly decrease up the stack
(so a frame that closes an SCC has every position above it already popped), and every live position is
either still on the stack or has been stashed. -/

section Lockstep

/-- Forget the retained arrays. -/
def StreettAuxF.proj (a : StreettAuxF State) : StreettAux State :=
  ⟨a.live, a.liveIndex, a.dead, a.dstack, a.witness, a.witnessOpts, a.pending⟩

omit [BEq State] [Hashable State] in
/-- Forget a frame's payload. Two stacks related by `strip` agree on what the proved route reads. -/
def DFSStep.strip (st : DFSStep State Nat) : DFSStep State Nat := { st with succOpts := #[] }

omit [BEq State] [Hashable State] in
theorem DFSStep.strip_state (st : DFSStep State Nat) : st.strip.state = st.state := rfl
omit [BEq State] [Hashable State] in
theorem DFSStep.strip_pos (st : DFSStep State Nat) : st.strip.pos = st.pos := rfl
omit [BEq State] [Hashable State] in
theorem DFSStep.strip_idx (st : DFSStep State Nat) : st.strip.idx = st.idx := rfl
omit [BEq State] [Hashable State] in
theorem DFSStep.strip_succ (st : DFSStep State Nat) : st.strip.succ = st.succ := rfl
omit [BEq State] [Hashable State] in
theorem DFSStep.strip_succMarks (st : DFSStep State Nat) : st.strip.succMarks = st.succMarks := rfl
omit [BEq State] [Hashable State] in
theorem DFSStep.strip_acc (st : DFSStep State Nat) : st.strip.acc = st.acc := rfl

omit [BEq State] [Hashable State] in
/-- A `strip`-related frame is the same frame with some payload. -/
theorem DFSStep.eq_of_strip_eq {st st' : DFSStep State Nat} (h : st.strip = st'.strip) :
    st' = { st with succOpts := st'.succOpts } := by
  cases st; cases st'
  simp only [DFSStep.strip, DFSStep.mk.injEq, true_and] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  subst h1 h2 h3 h4 h5 h6
  rfl

/-- The retained witness successors are the witness's successors in the graph the search ran on. §13.26 -/
def WitOK [Inhabited State] (succs : State → Array State) (a : StreettAuxF State) : Prop :=
  a.witnessSuccs.size = a.witness.size ∧
    ∀ k, k < a.witness.size → a.witnessSuccs[k]! = succs a.witness[k]!

/-- The fast side's invariant, relative to its DFS stack. -/
structure InvF [Inhabited State] (succs : State → Array State)
    (expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (stk : List (DFSStep State Nat)) (a : StreettAuxF State) : Prop where
  wf : LiveWF a.live a.liveIndex
  size1 : a.liveSuccs.size = a.live.size
  size2 : a.liveOpts.size = a.live.size
  frames : ∀ st ∈ stk, st.pos < a.live.size ∧ a.live[st.pos]! = st.state ∧
    st.succ = succs st.state ∧ st.succOpts = (expandOpts st.state).2.2
  sorted : List.Pairwise (fun (x y : DFSStep State Nat) => y.pos < x.pos) stk
  -- Every live position is on the stack, or stashed, or an *orphan* below every stack frame — the
  -- root of a run that the fixpoint left undefined, which `dfsFromRoot`'s `getD` fallback leaves live
  -- and unpopped. An orphan is never scanned: a scan starts at a stack frame's position and every
  -- later frame is pushed above it.
  retained : ∀ i, i < a.live.size → (∃ st ∈ stk, st.pos = i) ∨
    (a.liveSuccs[i]! = succs a.live[i]! ∧ a.liveOpts[i]! = (expandOpts a.live[i]!).2.2) ∨
    (∀ st ∈ stk, i < st.pos)
  -- §13.26: the report reads the witness's successors off the aux
  witOK : WitOK succs a

/-! ### The flush, as the retained arrays see it -/

theorem liveFlush_fst_size (pos : Nat) : ∀ (live : Array State) (liveIndex : Std.HashMap State Nat)
    (dead : Std.HashSet State), (liveFlush live liveIndex dead pos).1.size = min live.size pos := by
  intro live liveIndex dead
  induction live, liveIndex, dead using liveFlush.induct (pos := pos) with
  | case1 live liveIndex dead hgt hnone =>
    have hempty : live = #[] := Array.back?_eq_none_iff.mp hnone
    simp only [hempty, Array.size_empty] at hgt
    omega
  | case2 live liveIndex dead hgt q hb ih =>
    unfold liveFlush
    simp only [hgt, if_true, hb]
    rw [ih, Array.size_pop]
    omega
  | case3 live liveIndex dead hle =>
    unfold liveFlush
    simp only [hle, if_false]
    omega

theorem liveFlush_fst_getElem! [Inhabited State] (pos : Nat) :
    ∀ (live : Array State) (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State) (i : Nat),
      i < (liveFlush live liveIndex dead pos).1.size → (liveFlush live liveIndex dead pos).1[i]! = live[i]! := by
  intro live liveIndex dead
  induction live, liveIndex, dead using liveFlush.induct (pos := pos) with
  | case1 live liveIndex dead hgt hnone =>
    have hempty : live = #[] := Array.back?_eq_none_iff.mp hnone
    simp only [hempty, Array.size_empty] at hgt
    omega
  | case2 live liveIndex dead hgt q hb ih =>
    intro i hi
    unfold liveFlush at hi ⊢
    simp only [hgt, if_true, hb] at hi ⊢
    rw [ih i hi]
    have hlt : i < live.pop.size := by
      have := liveFlush_fst_size pos live.pop (liveIndex.erase q) (dead.insert q)
      omega
    rw [getElem!_pos _ i hlt, Array.getElem_pop, getElem!_pos live i (by rw [Array.size_pop] at hlt; omega)]
  | case3 live liveIndex dead hle =>
    intro i hi
    unfold liveFlush at hi ⊢
    simp only [hle, if_false] at hi ⊢

/-! ### PUSH and UPDATE -/

theorem streettPushF_proj (a : StreettAuxF State) (q : State) (m : Std.HashSet Nat) :
    (streettPushF a q m).1.proj = (streettPush a.proj q m).1 ∧
      (streettPushF a q m).2 = (streettPush a.proj q m).2 := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending, ls, lo, ws⟩ := a
  exact ⟨rfl, rfl⟩

theorem streettUpdateF_proj (numMarks : Nat) (a : StreettAuxF State) (m : Std.HashSet Nat) (d : State) :
    (streettUpdateF numMarks a m d).1.proj = (streettUpdate numMarks a.proj m d).1 ∧
      (streettUpdateF numMarks a m d).2 = (streettUpdate numMarks a.proj m d).2 := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending, ls, lo, ws⟩ := a
  simp only [streettUpdateF, streettUpdate, StreettAuxF.proj]
  cases dstack.back? with
  | none => exact ⟨rfl, rfl⟩
  | some p => exact ⟨rfl, rfl⟩

theorem InvF.bump [Inhabited State] {succs : State → Array State}
    {expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat}
    {step : DFSStep State Nat} {rest : List (DFSStep State Nat)} {a : StreettAuxF State}
    (h : InvF succs expandOpts (step :: rest) a) (i : Nat) :
    InvF succs expandOpts ({ step with idx := i } :: rest) a := by
  refine ⟨h.wf, h.size1, h.size2, ?_, ?_, ?_, h.witOK⟩
  · intro st hst
    rcases List.mem_cons.mp hst with rfl | hst
    · exact h.frames step (List.mem_cons_self ..)
    · exact h.frames st (List.mem_cons_of_mem _ hst)
  · have hs := h.sorted
    rw [List.pairwise_cons] at hs ⊢
    exact ⟨fun st hst => hs.1 st hst, hs.2⟩
  · intro i hi
    rcases h.retained i hi with ⟨st, hst, hpos⟩ | hr | horph
    · rcases List.mem_cons.mp hst with rfl | hst
      · exact Or.inl ⟨_, List.mem_cons_self .., hpos⟩
      · exact Or.inl ⟨st, List.mem_cons_of_mem _ hst, hpos⟩
    · exact Or.inr (Or.inl hr)
    · refine Or.inr (Or.inr fun st hst => ?_)
      rcases List.mem_cons.mp hst with rfl | hst
      · exact horph step (List.mem_cons_self ..)
      · exact horph st (List.mem_cons_of_mem _ hst)

theorem streettPushF_eq (a : StreettAuxF State) (q : State) (m : Std.HashSet Nat) :
    streettPushF a q m =
      (⟨a.live.push q, a.liveIndex.insert q a.live.size, a.dead, a.dstack.push (a.live.size, 0),
        a.witness, a.witnessOpts, a.pending, a.liveSuccs.push #[], a.liveOpts.push #[], a.witnessSuccs⟩, a.live.size) := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending, ls, lo, ws⟩ := a
  rfl

theorem InvF.push [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {succs : State → Array State}
    {expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat}
    {stk : List (DFSStep State Nat)} {a : StreettAuxF State}
    (h : InvF succs expandOpts stk a) (q : State) (m : Std.HashSet Nat)
    (hq : liveStatusOf a.liveIndex a.dead q = .unknown)
    (hsucc : (expandOpts q).1 = succs q) (acc : Nat) :
    InvF succs expandOpts
      ({ state := q, pos := (streettPushF a q m).2, acc := acc, succ := (expandOpts q).1,
         succMarks := (expandOpts q).2.1, succOpts := (expandOpts q).2.2, idx := 0 } :: stk)
      (streettPushF a q m).1 := by
  rw [streettPushF_eq]
  have hnc : a.liveIndex.contains q = false := by
    unfold liveStatusOf at hq
    by_cases hc : a.liveIndex.contains q
    · simp [hc] at hq
    · simpa using hc
  refine ⟨h.wf.push hnc, ?_, ?_, ?_, ?_, ?_, h.witOK⟩
  · simp only [Array.size_push, h.size1]
  · simp only [Array.size_push, h.size2]
  · intro st hst
    rcases List.mem_cons.mp hst with rfl | hst
    · exact ⟨by simp, by simp only [Array.getElem!_push_eq], hsucc, rfl⟩
    · obtain ⟨h1, h2, h3, h4⟩ := h.frames st hst
      exact ⟨by simp only [Array.size_push]; omega, by rw [Array.getElem!_push_lt h1]; exact h2, h3, h4⟩
  · rw [List.pairwise_cons]
    exact ⟨fun st hst => (h.frames st hst).1, h.sorted⟩
  · intro i hi
    simp only [Array.size_push] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · rcases h.retained i hlt with ⟨st, hst, hpos⟩ | ⟨hr1, hr2⟩ | horph
      · exact Or.inl ⟨st, List.mem_cons_of_mem _ hst, hpos⟩
      · refine Or.inr (Or.inl ⟨?_, ?_⟩)
        · show (a.liveSuccs.push #[])[i]! = succs (a.live.push q)[i]!
          rw [Array.getElem!_push_lt (h.size1 ▸ hlt), Array.getElem!_push_lt hlt]; exact hr1
        · show (a.liveOpts.push #[])[i]! = (expandOpts (a.live.push q)[i]!).2.2
          rw [Array.getElem!_push_lt (h.size2 ▸ hlt), Array.getElem!_push_lt hlt]; exact hr2
      · refine Or.inr (Or.inr fun st hst => ?_)
        rcases List.mem_cons.mp hst with rfl | hst
        · exact hlt
        · exact horph st hst
    · exact Or.inl ⟨_, List.mem_cons_self .., heq.symm⟩

/-! ### POP -/

/-- The invariant after a flush at `pos`, given it held for `rest` below `pos`. -/
theorem InvF.flush [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {succs : State → Array State}
    {expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat}
    {rest : List (DFSStep State Nat)}
    (live : Array State) (liveIndex : Std.HashMap State Nat) (dead : Std.HashSet State)
    (dstack : Array (Nat × Nat)) (wit : Array State) (wopts : Array Nat) (pending : Array (Candidate State))
    (ws : Array (Array State)) (ls : Array (Array State)) (lo : Array (Array Nat)) (pos : Nat)
    (hwfl : LiveWF live liveIndex) (hs1 : ls.size = live.size) (hs2 : lo.size = live.size)
    (hframes : ∀ st ∈ rest, st.pos < live.size ∧ live[st.pos]! = st.state ∧
      st.succ = succs st.state ∧ st.succOpts = (expandOpts st.state).2.2)
    (hrestlt : ∀ st ∈ rest, st.pos < pos)
    (hsorted : List.Pairwise (fun (x y : DFSStep State Nat) => y.pos < x.pos) rest)
    (hret : ∀ i, i < live.size → (∃ st ∈ rest, st.pos = i) ∨
      (ls[i]! = succs live[i]! ∧ lo[i]! = (expandOpts live[i]!).2.2) ∨ (∀ st ∈ rest, i < st.pos))
    (hws : ws.size = wit.size ∧ ∀ k, k < wit.size → ws[k]! = succs wit[k]!) :
    InvF succs expandOpts rest
      ⟨(liveFlush live liveIndex dead pos).1, (liveFlush live liveIndex dead pos).2.1,
        (liveFlush live liveIndex dead pos).2.2, dstack, wit, wopts, pending,
        ls.shrink pos, lo.shrink pos, ws⟩ := by
  have hsz := liveFlush_fst_size pos live liveIndex dead
  refine ⟨hwfl.flush pos, ?_, ?_, ?_, hsorted, ?_, hws⟩
  · show (ls.shrink pos).size = (liveFlush live liveIndex dead pos).1.size
    rw [Array.size_shrink, hsz, hs1, Nat.min_comm]
  · show (lo.shrink pos).size = (liveFlush live liveIndex dead pos).1.size
    rw [Array.size_shrink, hsz, hs2, Nat.min_comm]
  · intro st hst
    obtain ⟨h1, h2, h3, h4⟩ := hframes st hst
    have hlt := hrestlt st hst
    refine ⟨?_, ?_, h3, h4⟩
    · show st.pos < (liveFlush live liveIndex dead pos).1.size
      rw [hsz]; omega
    · show (liveFlush live liveIndex dead pos).1[st.pos]! = st.state
      rw [liveFlush_fst_getElem! pos live liveIndex dead st.pos (by rw [hsz]; omega)]
      exact h2
  · intro i hi
    change i < (liveFlush live liveIndex dead pos).1.size at hi
    rw [hsz] at hi
    rcases hret i (by omega) with hstk | ⟨hr1, hr2⟩ | horph
    · exact Or.inl hstk
    · refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · show (ls.shrink pos)[i]! = succs (liveFlush live liveIndex dead pos).1[i]!
        rw [getElem!_pos (ls.shrink pos) i (by rw [Array.size_shrink]; omega), Array.getElem_shrink,
          liveFlush_fst_getElem! pos live liveIndex dead i (by rw [hsz]; omega),
          ← getElem!_pos ls i (by omega)]
        exact hr1
      · show (lo.shrink pos)[i]! = (expandOpts (liveFlush live liveIndex dead pos).1[i]!).2.2
        rw [getElem!_pos (lo.shrink pos) i (by rw [Array.size_shrink]; omega), Array.getElem_shrink,
          liveFlush_fst_getElem! pos live liveIndex dead i (by rw [hsz]; omega),
          ← getElem!_pos lo i (by omega)]
        exact hr2
    · exact Or.inr (Or.inr horph)

/-- POP in lockstep: same verdict, same projection, and the invariant for the rest of the stack. -/
theorem streettPopF_spec [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (cr : Nat)
    {succs : State → Array State}
    {expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat}
    (hbits : cs.numOptions ≠ 0 → ∀ s, (expandOpts s).2.2 = (succs s).map fun t => cs.edgeBits (s, t))
    {step : DFSStep State Nat} {rest : List (DFSStep State Nat)} {a : StreettAuxF State}
    (h : InvF succs expandOpts (step :: rest) a) :
    (streettPopF cs cr a step).2 = (streettPop cs cr succs a.proj step).2 ∧
    (streettPopF cs cr a step).1.proj = (streettPop cs cr succs a.proj step).1 ∧
    InvF succs expandOpts rest (streettPopF cs cr a step).1 := by
  obtain ⟨hpos, hstate, hsucc, hopts⟩ := h.frames step (List.mem_cons_self ..)
  have hrestlt : ∀ st ∈ rest, st.pos < step.pos := (List.pairwise_cons.mp h.sorted).1
  have hsorted : List.Pairwise (fun (x y : DFSStep State Nat) => y.pos < x.pos) rest :=
    (List.pairwise_cons.mp h.sorted).2
  have hwfl := h.wf
  have hs1 := h.size1
  have hs2 := h.size2
  have hret := h.retained
  have hwit := h.witOK
  have hframes : ∀ st ∈ rest, st.pos < a.live.size ∧ a.live[st.pos]! = st.state ∧
      st.succ = succs st.state ∧ st.succOpts = (expandOpts st.state).2.2 :=
    fun st hst => h.frames st (List.mem_cons_of_mem _ hst)
  obtain ⟨live, liveIndex, dead, dstack0, wit, wopts, pending, ls0, lo0, ws⟩ := a
  simp only [] at hpos hstate hwfl hs1 hs2 hret hframes
  simp only [WitOK] at hwit
  simp only [streettPopF, streettPop, StreettAuxF.proj]
  set ls := ls0.setIfInBounds step.pos step.succ with hls
  set lo := lo0.setIfInBounds step.pos step.succOpts with hlo
  -- the retained arrays after the stash
  have hls1 : ls.size = live.size := by rw [hls, Array.size_setIfInBounds, hs1]
  have hlo1 : lo.size = live.size := by rw [hlo, Array.size_setIfInBounds, hs2]
  have hstash : ∀ i, step.pos ≤ i → i < live.size →
      ls[i]! = succs live[i]! ∧ lo[i]! = (expandOpts live[i]!).2.2 := by
    intro i hlo' hi
    rcases Nat.eq_or_lt_of_le hlo' with rfl | hlt
    · refine ⟨?_, ?_⟩
      · rw [hls, getElem!_pos _ _ (by rw [Array.size_setIfInBounds]; omega),
          Array.getElem_setIfInBounds_self, hsucc, hstate]
      · rw [hlo, getElem!_pos _ _ (by rw [Array.size_setIfInBounds]; omega),
          Array.getElem_setIfInBounds_self, hopts, hstate]
    · have hne : step.pos ≠ i := by omega
      rcases hret i hi with ⟨st, hst, hpst⟩ | ⟨hr1, hr2⟩ | horph
      · rcases List.mem_cons.mp hst with rfl | hst
        · omega
        · have := hrestlt st hst; omega
      · refine ⟨?_, ?_⟩
        · rw [hls, getElem!_pos _ _ (by rw [Array.size_setIfInBounds]; omega),
            Array.getElem_setIfInBounds_ne (by omega) hne, ← getElem!_pos ls0 i (by omega)]
          exact hr1
        · rw [hlo, getElem!_pos _ _ (by rw [Array.size_setIfInBounds]; omega),
            Array.getElem_setIfInBounds_ne (by omega) hne, ← getElem!_pos lo0 i (by omega)]
          exact hr2
      · have := horph step (List.mem_cons_self ..); omega
  have hret' : ∀ i, i < live.size → (∃ st ∈ rest, st.pos = i) ∨
      (ls[i]! = succs live[i]! ∧ lo[i]! = (expandOpts live[i]!).2.2) ∨ (∀ st ∈ rest, i < st.pos) := by
    intro i hi
    by_cases hge : step.pos ≤ i
    · exact Or.inr (Or.inl (hstash i hge hi))
    · have hne : step.pos ≠ i := by omega
      rcases hret i hi with ⟨st, hst, hpst⟩ | ⟨hr1, hr2⟩ | horph
      · rcases List.mem_cons.mp hst with rfl | hst
        · omega
        · exact Or.inl ⟨st, hst, hpst⟩
      · refine Or.inr (Or.inl ⟨?_, ?_⟩)
        · rw [hls, getElem!_pos _ _ (by rw [Array.size_setIfInBounds]; omega),
            Array.getElem_setIfInBounds_ne (by omega) hne, ← getElem!_pos ls0 i (by omega)]
          exact hr1
        · rw [hlo, getElem!_pos _ _ (by rw [Array.size_setIfInBounds]; omega),
            Array.getElem_setIfInBounds_ne (by omega) hne, ← getElem!_pos lo0 i (by omega)]
          exact hr2
      · exact Or.inr (Or.inr fun st hst => horph st (List.mem_cons_of_mem _ hst))
  -- the scan agrees
  have hscan : scanFrameF cs liveIndex ls lo step.pos = scanFrame cs succs live step.pos := by
    refine scanFrameF_eq_scanFrame cs hwf succs live liveIndex ls lo step.pos hwfl hls1 ?_ ?_
    · intro i hlo' hi
      rw [(hstash i hlo' hi).1, getElem!_pos live i hi]
    · intro hn i hlo' hi
      rw [(hstash i hlo' hi).2, hbits hn, getElem!_pos live i hi]
  have hinvNoFlush : ∀ dstack, InvF succs expandOpts rest
      ⟨live, liveIndex, dead, dstack, wit, wopts, pending, ls, lo, ws⟩ :=
    fun dstack => ⟨hwfl, hls1, hlo1, hframes, hsorted, hret', hwit⟩
  have hinvFlush : ∀ dstack wit' wopts' pending' ws',
      (ws'.size = wit'.size ∧ ∀ k, k < wit'.size → ws'[k]! = succs wit'[k]!) →
      InvF succs expandOpts rest
      ⟨(liveFlush live liveIndex dead step.pos).1, (liveFlush live liveIndex dead step.pos).2.1,
        (liveFlush live liveIndex dead step.pos).2.2, dstack, wit', wopts', pending',
        ls.shrink step.pos, lo.shrink step.pos, ws'⟩ :=
    fun dstack wit' wopts' pending' ws' hws' =>
      InvF.flush live liveIndex dead dstack wit' wopts' pending' ws' ls lo step.pos hwfl hls1 hlo1 hframes
        hrestlt hsorted hret' hws'
  -- the accepting POP's witness carries the same slice of the retained arrays (§13.26)
  have hnew : (ls.extract step.pos live.size).size = (live.extract step.pos live.size).size ∧
      ∀ k, k < (live.extract step.pos live.size).size →
        (ls.extract step.pos live.size)[k]! = succs (live.extract step.pos live.size)[k]! := by
    have hsz : (ls.extract step.pos live.size).size = live.size - step.pos := by
      rw [Array.size_extract, hls1]; omega
    have hsz' : (live.extract step.pos live.size).size = live.size - step.pos := by
      rw [Array.size_extract]; omega
    refine ⟨by rw [hsz, hsz'], fun k hk => ?_⟩
    rw [hsz'] at hk
    rw [getElem!_pos _ k (by omega), getElem!_pos _ k (by omega), Array.getElem_extract,
      Array.getElem_extract]
    have := (hstash (step.pos + k) (by omega) (by omega)).1
    rw [getElem!_pos ls _ (by omega), getElem!_pos live _ (by omega)] at this
    exact this
  cases hb : dstack0.back? with
  | none => exact ⟨rfl, rfl, hinvNoFlush _⟩
  | some p =>
    obtain ⟨ll, acc⟩ := p
    by_cases hll : ll = step.pos
    · subst hll
      simp only [if_true]
      by_cases hacc : (acc != fullAccMask cs.numMarks) = true
      · rw [if_pos hacc, if_pos hacc]
        exact ⟨rfl, rfl, hinvFlush _ _ _ _ _ hwit⟩
      · rw [if_neg hacc, if_neg hacc, hscan]
        cases hfu : firstUnsatisfied cs (scanFrame cs succs live step.pos).1
            (scanFrame cs succs live step.pos).2 with
        | none => exact ⟨rfl, rfl, hinvFlush _ _ _ _ _ hnew⟩
        | some liveOpts => exact ⟨rfl, rfl, hinvFlush _ _ _ _ _ hwit⟩
    · simp only [hll, if_false]
      cases hb2 : dstack0.pop.back? with
      | none => exact ⟨rfl, rfl, hinvNoFlush _⟩
      | some p2 =>
        obtain ⟨pll, pacc⟩ := p2
        exact ⟨rfl, rfl, hinvNoFlush _⟩

/-! ### UPDATE keeps the invariant; the proved POP ignores the payload -/

theorem InvF.update [Inhabited State] {succs : State → Array State}
    {expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat}
    {stk : List (DFSStep State Nat)} {a : StreettAuxF State}
    (h : InvF succs expandOpts stk a) (numMarks : Nat) (m : Std.HashSet Nat) (d : State) :
    InvF succs expandOpts stk (streettUpdateF numMarks a m d).1 := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending, ls, lo, ws⟩ := a
  simp only [streettUpdateF]
  cases dstack.back? with
  | none => exact h
  | some p => exact ⟨h.wf, h.size1, h.size2, h.frames, h.sorted, h.retained, h.witOK⟩

omit [BEq State] [Hashable State] in
theorem map_state_of_strip {l l' : List (DFSStep State Nat)}
    (h : l.map DFSStep.strip = l'.map DFSStep.strip) :
    l.map (·.state) = l'.map (·.state) := by
  have := congrArg (List.map (·.state)) h
  simpa only [List.map_map, Function.comp_def, DFSStep.strip_state] using this

theorem streettPop_succOpts [Inhabited State] (cs : CompiledSpec State L) (cr : Nat)
    (succs : State → Array State) (a : StreettAux State) (st : DFSStep State Nat) (sO : Array Nat) :
    streettPop cs cr succs a { st with succOpts := sO } = streettPop cs cr succs a st := by
  cases st; rfl

/-! ### The generic driver, in lockstep -/

/-- The fast run's `dfsGo` returns what the proved run's `dfsGo` returns, projected. -/
theorem dfsGo_lockstep [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (cr : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (hexpO : ExpandCoherent succs edgeMarks expandOpts)
    (hbits : cs.numOptions ≠ 0 → ∀ s, (expandOpts s).2.2 = (succs s).map fun t => cs.edgeBits (s, t)) :
    ∀ (auxF : StreettAuxF State) (stkF : List (DFSStep State Nat))
      (rF : Option (State × List State) × StreettAuxF State),
      dfsGo (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0) expandOpts
        auxF stkF = some rF →
      InvF succs expandOpts stkF auxF →
      ∀ stk : List (DFSStep State Nat), stk.map DFSStep.strip = stkF.map DFSStep.strip →
      ∃ r, dfsGo (streettOps cs cr) succs edgeMarks expand auxF.proj stk = some r ∧
        rF.1 = r.1 ∧ rF.2.proj = r.2 ∧ (rF.1 = none → InvF succs expandOpts [] rF.2) := by
  refine dfsGo.partial_correctness (streettOpsF cs cr) (fun _ => #[])
    (fun _ _ => Std.HashSet.emptyWithCapacity 0) expandOpts
    (fun auxF stkF rF => InvF succs expandOpts stkF auxF →
      ∀ stk : List (DFSStep State Nat), stk.map DFSStep.strip = stkF.map DFSStep.strip →
      ∃ r, dfsGo (streettOps cs cr) succs edgeMarks expand auxF.proj stk = some r ∧
        rF.1 = r.1 ∧ rF.2.proj = r.2 ∧ (rF.1 = none → InvF succs expandOpts [] rF.2)) ?_
  intro dfsGoF ih auxF stkF rF hr hinv stk hstk
  cases stkF with
  | nil =>
    cases stk with
    | nil =>
      simp only [Option.some.injEq] at hr
      refine ⟨(none, auxF.proj), by rw [dfsGo.eq_def], ?_, ?_, ?_⟩
      · rw [← hr]
      · rw [← hr]
      · intro _; rw [← hr]; exact hinv
    | cons _ _ => simp at hstk
  | cons stepF restF =>
    cases stk with
    | nil => simp at hstk
    | cons step rest =>
      simp only [List.map_cons, List.cons.injEq] at hstk
      obtain ⟨hstep, hrest⟩ := hstk
      obtain ⟨sO, rfl⟩ : ∃ sO, step = { stepF with succOpts := sO } :=
        ⟨_, DFSStep.eq_of_strip_eq hstep.symm⟩
      obtain ⟨hposF, hstateF, hsuccF, hoptsF⟩ := hinv.frames stepF (List.mem_cons_self ..)
      have hbumpstk : ∀ i, ({ { stepF with succOpts := sO } with idx := i } :: rest).map DFSStep.strip =
          ({ stepF with idx := i } :: restF).map DFSStep.strip := by
        intro i
        simp only [List.map_cons, hrest, DFSStep.strip]
      rw [dfsGo.eq_def]
      simp only []
      by_cases h : stepF.idx < stepF.succ.size
      · simp only [h, dite_true] at hr
        rw [dif_pos h]
        cases hgs : (streettOpsF cs cr).getStatus auxF stepF.succ[stepF.idx] with
        | dead =>
          simp only [hgs] at hr
          have hgs' : (streettOps cs cr).getStatus auxF.proj stepF.succ[stepF.idx] = .dead := hgs
          simp only [hgs']
          exact ih auxF _ rF hr (hinv.bump _) _ (hbumpstk _)
        | live =>
          simp only [hgs] at hr
          have hgs' : (streettOps cs cr).getStatus auxF.proj stepF.succ[stepF.idx] = .live := hgs
          simp only [hgs']
          rcases hupdF : streettUpdateF cs.numMarks auxF (stepF.succMarks[stepF.idx]!) stepF.succ[stepF.idx]
            with ⟨auxF', foundF⟩
          have hupdF' : (streettOpsF cs cr).update auxF (stepF.succMarks[stepF.idx]!) stepF.succ[stepF.idx]
              = (auxF', foundF) := hupdF
          simp only [hupdF'] at hr
          have hupd : (streettOps cs cr).update auxF.proj (stepF.succMarks[stepF.idx]!) stepF.succ[stepF.idx]
              = (auxF'.proj, foundF) := by
            obtain ⟨h1, h2⟩ := streettUpdateF_proj cs.numMarks auxF (stepF.succMarks[stepF.idx]!)
              stepF.succ[stepF.idx]
            rw [hupdF] at h1 h2
            exact Prod.ext h1.symm h2.symm
          simp only [hupd]
          have hinv' : InvF succs expandOpts (stepF :: restF) auxF' := by
            have := hinv.update cs.numMarks (stepF.succMarks[stepF.idx]!) stepF.succ[stepF.idx]
            rw [hupdF] at this
            exact this
          by_cases hf : foundF = true
          · simp only [hf, if_true, Option.some.injEq] at hr
            simp only [hf, if_true]
            refine ⟨_, rfl, ?_, ?_, ?_⟩
            · rw [← hr]
              simp only [List.map_cons, List.reverse_cons]
              exact congrArg (fun l => some (stepF.state, l.reverse ++ [stepF.state]))
                (map_state_of_strip hrest).symm
            · rw [← hr]
            · intro hn; rw [← hr] at hn; simp at hn
          · simp only [hf] at hr
            simp only [hf]
            exact ih auxF' _ rF hr (hinv'.bump _) _ (hbumpstk _)
        | unknown =>
          simp only [hgs] at hr
          have hgs' : (streettOps cs cr).getStatus auxF.proj stepF.succ[stepF.idx] = .unknown := hgs
          simp only [hgs']
          rcases hpshF : streettPushF auxF stepF.succ[stepF.idx] (stepF.succMarks[stepF.idx]!)
            with ⟨auxF', posF⟩
          have hpshF' : (streettOpsF cs cr).push auxF stepF.succ[stepF.idx] (stepF.succMarks[stepF.idx]!)
              = (auxF', posF) := hpshF
          simp only [hpshF'] at hr
          have hpsh : (streettOps cs cr).push auxF.proj stepF.succ[stepF.idx] (stepF.succMarks[stepF.idx]!)
              = (auxF'.proj, posF) := by
            obtain ⟨h1, h2⟩ := streettPushF_proj auxF stepF.succ[stepF.idx] (stepF.succMarks[stepF.idx]!)
            rw [hpshF] at h1 h2
            exact Prod.ext h1.symm h2.symm
          simp only [hpsh]
          have hinv' := (hinv.bump (stepF.idx + 1)).push stepF.succ[stepF.idx] (stepF.succMarks[stepF.idx]!)
            hgs (hexpO.fst _) (marksToBitmask (stepF.succMarks[stepF.idx]!))
          rw [hpshF] at hinv'
          refine ih auxF' _ rF hr hinv' _ ?_
          simp only [List.map_cons, hrest, DFSStep.strip, hexp.fst, hexpO.fst, hexp.snd, hexpO.snd]
      · simp only [h, dite_false] at hr
        rw [dif_neg h]
        obtain ⟨hpop1, hpop2, hinv'⟩ := streettPopF_spec cs hwf cr hbits hinv
        rcases hpopF : streettPopF cs cr auxF stepF with ⟨auxF', foundF⟩
        have hpopF' : (streettOpsF cs cr).pop (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
            auxF stepF = (auxF', foundF) := hpopF
        simp only [hpopF'] at hr
        rw [hpopF] at hpop1 hpop2 hinv'
        have hpop : (streettOps cs cr).pop succs edgeMarks auxF.proj { stepF with succOpts := sO }
            = (auxF'.proj, foundF) := by
          show streettPop cs cr succs auxF.proj { stepF with succOpts := sO } = _
          rw [streettPop_succOpts]
          exact Prod.ext hpop2.symm hpop1.symm
        simp only [hpop]
        cases foundF with
        | true =>
          simp only [Option.some.injEq] at hr
          refine ⟨_, rfl, ?_, ?_, ?_⟩
          · rw [← hr]
            simp only [List.map_cons, List.reverse_cons]
            exact congrArg (fun l => some (stepF.state, l.reverse ++ [stepF.state]))
              (map_state_of_strip hrest).symm
          · rw [← hr]
          · intro hn; rw [← hr] at hn; simp at hn
        | false =>
          exact ih auxF' restF rF hr hinv' rest hrest

/-- The converse: the proved run's `dfsGo` converging forces the fast run's to, with the related result.
Needed because `dfsFromRoot` and `genericDFS` fall back on `getD` when a run returns `none`, so the two
runs have to agree on divergence as well. -/
theorem dfsGo_lockstep_rev [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (cr : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (hexpO : ExpandCoherent succs edgeMarks expandOpts)
    (hbits : cs.numOptions ≠ 0 → ∀ s, (expandOpts s).2.2 = (succs s).map fun t => cs.edgeBits (s, t)) :
    ∀ (aux : StreettAux State) (stk : List (DFSStep State Nat))
      (r : Option (State × List State) × StreettAux State),
      dfsGo (streettOps cs cr) succs edgeMarks expand aux stk = some r →
      ∀ (auxF : StreettAuxF State) (stkF : List (DFSStep State Nat)), aux = auxF.proj →
      InvF succs expandOpts stkF auxF → stk.map DFSStep.strip = stkF.map DFSStep.strip →
      ∃ rF, dfsGo (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
        expandOpts auxF stkF = some rF ∧ rF.1 = r.1 ∧ rF.2.proj = r.2 := by
  refine dfsGo.partial_correctness (streettOps cs cr) succs edgeMarks expand
    (fun aux stk r => ∀ (auxF : StreettAuxF State) (stkF : List (DFSStep State Nat)), aux = auxF.proj →
      InvF succs expandOpts stkF auxF → stk.map DFSStep.strip = stkF.map DFSStep.strip →
      ∃ rF, dfsGo (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
        expandOpts auxF stkF = some rF ∧ rF.1 = r.1 ∧ rF.2.proj = r.2) ?_
  intro dfsGoP ih aux stk r hr auxF stkF haux hinv hstk
  subst haux
  cases stkF with
  | nil =>
    cases stk with
    | nil =>
      simp only [Option.some.injEq] at hr
      refine ⟨(none, auxF), by rw [dfsGo.eq_def], ?_, ?_⟩
      · rw [← hr]
      · rw [← hr]
    | cons _ _ => simp at hstk
  | cons stepF restF =>
    cases stk with
    | nil => simp at hstk
    | cons step rest =>
      simp only [List.map_cons, List.cons.injEq] at hstk
      obtain ⟨hstep, hrest⟩ := hstk
      obtain ⟨sO, rfl⟩ : ∃ sO, step = { stepF with succOpts := sO } :=
        ⟨_, DFSStep.eq_of_strip_eq hstep.symm⟩
      have hbumpstk : ∀ i, ({ { stepF with succOpts := sO } with idx := i } :: rest).map DFSStep.strip =
          ({ stepF with idx := i } :: restF).map DFSStep.strip := by
        intro i
        simp only [List.map_cons, hrest, DFSStep.strip]
      rw [dfsGo.eq_def]
      simp only []
      by_cases h : stepF.idx < stepF.succ.size
      · simp only [h, dite_true] at hr
        rw [dif_pos h]
        cases hgs : (streettOps cs cr).getStatus auxF.proj stepF.succ[stepF.idx] with
        | dead =>
          simp only [hgs] at hr
          have hgsF : (streettOpsF cs cr).getStatus auxF stepF.succ[stepF.idx] = .dead := hgs
          simp only [hgsF]
          exact ih auxF.proj _ r hr auxF _ rfl (hinv.bump _) (hbumpstk _)
        | live =>
          simp only [hgs] at hr
          have hgsF : (streettOpsF cs cr).getStatus auxF stepF.succ[stepF.idx] = .live := hgs
          simp only [hgsF]
          rcases hupdF : streettUpdateF cs.numMarks auxF (stepF.succMarks[stepF.idx]!) stepF.succ[stepF.idx]
            with ⟨auxF', foundF⟩
          have hupdF' : (streettOpsF cs cr).update auxF (stepF.succMarks[stepF.idx]!) stepF.succ[stepF.idx]
              = (auxF', foundF) := hupdF
          simp only [hupdF']
          have hupd : (streettOps cs cr).update auxF.proj (stepF.succMarks[stepF.idx]!) stepF.succ[stepF.idx]
              = (auxF'.proj, foundF) := by
            obtain ⟨h1, h2⟩ := streettUpdateF_proj cs.numMarks auxF (stepF.succMarks[stepF.idx]!)
              stepF.succ[stepF.idx]
            rw [hupdF] at h1 h2
            exact Prod.ext h1.symm h2.symm
          simp only [hupd] at hr
          have hinv' : InvF succs expandOpts (stepF :: restF) auxF' := by
            have := hinv.update cs.numMarks (stepF.succMarks[stepF.idx]!) stepF.succ[stepF.idx]
            rw [hupdF] at this
            exact this
          by_cases hf : foundF = true
          · simp only [hf, if_true, Option.some.injEq] at hr
            simp only [hf, if_true]
            refine ⟨_, rfl, ?_, ?_⟩
            · rw [← hr]
              simp only [List.map_cons, List.reverse_cons]
              exact congrArg (fun l => some (stepF.state, l.reverse ++ [stepF.state]))
                (map_state_of_strip hrest).symm
            · rw [← hr]
          · simp only [hf] at hr
            simp only [hf]
            exact ih auxF'.proj _ r hr auxF' _ rfl (hinv'.bump _) (hbumpstk _)
        | unknown =>
          simp only [hgs] at hr
          have hgsF : (streettOpsF cs cr).getStatus auxF stepF.succ[stepF.idx] = .unknown := hgs
          simp only [hgsF]
          rcases hpshF : streettPushF auxF stepF.succ[stepF.idx] (stepF.succMarks[stepF.idx]!)
            with ⟨auxF', posF⟩
          have hpshF' : (streettOpsF cs cr).push auxF stepF.succ[stepF.idx] (stepF.succMarks[stepF.idx]!)
              = (auxF', posF) := hpshF
          simp only [hpshF']
          have hpsh : (streettOps cs cr).push auxF.proj stepF.succ[stepF.idx] (stepF.succMarks[stepF.idx]!)
              = (auxF'.proj, posF) := by
            obtain ⟨h1, h2⟩ := streettPushF_proj auxF stepF.succ[stepF.idx] (stepF.succMarks[stepF.idx]!)
            rw [hpshF] at h1 h2
            exact Prod.ext h1.symm h2.symm
          simp only [hpsh] at hr
          have hinv' := (hinv.bump (stepF.idx + 1)).push stepF.succ[stepF.idx] (stepF.succMarks[stepF.idx]!)
            hgs (hexpO.fst _) (marksToBitmask (stepF.succMarks[stepF.idx]!))
          rw [hpshF] at hinv'
          refine ih auxF'.proj _ r hr auxF' _ rfl hinv' ?_
          simp only [List.map_cons, hrest, DFSStep.strip, hexp.fst, hexpO.fst, hexp.snd, hexpO.snd]
      · simp only [h, dite_false] at hr
        rw [dif_neg h]
        obtain ⟨hpop1, hpop2, hinv'⟩ := streettPopF_spec cs hwf cr hbits hinv
        rcases hpopF : streettPopF cs cr auxF stepF with ⟨auxF', foundF⟩
        have hpopF' : (streettOpsF cs cr).pop (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
            auxF stepF = (auxF', foundF) := hpopF
        simp only [hpopF']
        rw [hpopF] at hpop1 hpop2 hinv'
        have hpop : (streettOps cs cr).pop succs edgeMarks auxF.proj { stepF with succOpts := sO }
            = (auxF'.proj, foundF) := by
          show streettPop cs cr succs auxF.proj { stepF with succOpts := sO } = _
          rw [streettPop_succOpts]
          exact Prod.ext hpop2.symm hpop1.symm
        simp only [hpop] at hr
        cases foundF with
        | true =>
          simp only [Option.some.injEq] at hr
          refine ⟨_, rfl, ?_, ?_⟩
          · rw [← hr]
            simp only [List.map_cons, List.reverse_cons]
            exact congrArg (fun l => some (stepF.state, l.reverse ++ [stepF.state]))
              (map_state_of_strip hrest).symm
          · rw [← hr]
        | false =>
          exact ih auxF'.proj rest r hr auxF' restF rfl hinv' hrest

/-- Lift a fast result to a proved one. -/
def liftF (rF : Option (State × List State) × StreettAuxF State) :
    Option (State × List State) × StreettAux State := (rF.1, rF.2.proj)

/-- Both directions at once: the proved `dfsGo` is the fast one, lifted — on divergence too. -/
theorem dfsGo_eq [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (cr : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (hexpO : ExpandCoherent succs edgeMarks expandOpts)
    (hbits : cs.numOptions ≠ 0 → ∀ s, (expandOpts s).2.2 = (succs s).map fun t => cs.edgeBits (s, t))
    (auxF : StreettAuxF State) (stkF stk : List (DFSStep State Nat))
    (hinv : InvF succs expandOpts stkF auxF) (hstk : stk.map DFSStep.strip = stkF.map DFSStep.strip) :
    (dfsGo (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0) expandOpts
        auxF stkF).map liftF = dfsGo (streettOps cs cr) succs edgeMarks expand auxF.proj stk ∧
    (∀ rF, dfsGo (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0) expandOpts
        auxF stkF = some rF → rF.1 = none → InvF succs expandOpts [] rF.2) := by
  cases hF : dfsGo (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
      expandOpts auxF stkF with
  | none =>
    refine ⟨?_, fun rF h => by cases h⟩
    cases hP : dfsGo (streettOps cs cr) succs edgeMarks expand auxF.proj stk with
    | none => rfl
    | some r =>
      obtain ⟨rF, hrF, _⟩ := dfsGo_lockstep_rev cs hwf cr succs edgeMarks expand expandOpts hexp hexpO
        hbits _ _ r hP auxF stkF rfl hinv hstk
      rw [hF] at hrF; cases hrF
  | some rF =>
    obtain ⟨r, hr, h1, h2, h3⟩ := dfsGo_lockstep cs hwf cr succs edgeMarks expand expandOpts hexp hexpO
      hbits auxF stkF rF hF hinv stk hstk
    refine ⟨?_, fun rF' h hn => by cases h; exact h3 hn⟩
    rw [hr]
    exact congrArg some (Prod.ext h1 h2)

/-- A single frame popped off by the fallback leaves an orphan, which the invariant admits. -/
theorem InvF.nil_of_singleton [Inhabited State] {succs : State → Array State}
    {expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat}
    {st : DFSStep State Nat} {a : StreettAuxF State} (h : InvF succs expandOpts [st] a) :
    InvF succs expandOpts [] a := by
  refine ⟨h.wf, h.size1, h.size2, fun _ h' => by simp at h', List.Pairwise.nil, ?_, h.witOK⟩
  intro i hi
  rcases h.retained i hi with _ | hr | _
  · exact Or.inr (Or.inr fun _ h' => by simp at h')
  · exact Or.inr (Or.inl hr)
  · exact Or.inr (Or.inr fun _ h' => by simp at h')

/-! ### The retained witness successors survive every step (§13.26) -/

theorem dfsGo_witOK [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (cr : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexpO : ExpandCoherent succs edgeMarks expandOpts)
    (hbits : cs.numOptions ≠ 0 → ∀ s, (expandOpts s).2.2 = (succs s).map fun t => cs.edgeBits (s, t)) :
    ∀ (auxF : StreettAuxF State) (stkF : List (DFSStep State Nat))
      (rF : Option (State × List State) × StreettAuxF State),
      dfsGo (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0) expandOpts
        auxF stkF = some rF →
      InvF succs expandOpts stkF auxF → WitOK succs rF.2 := by
  refine dfsGo.partial_correctness (streettOpsF cs cr) (fun _ => #[])
    (fun _ _ => Std.HashSet.emptyWithCapacity 0) expandOpts
    (fun auxF stkF rF => InvF succs expandOpts stkF auxF → WitOK succs rF.2) ?_
  intro dfsGoF ih auxF stkF rF hr hinv
  cases stkF with
  | nil =>
    simp only [Option.some.injEq] at hr
    rw [← hr]; exact hinv.witOK
  | cons stepF restF =>
    by_cases h : stepF.idx < stepF.succ.size
    · simp only [h, dite_true] at hr
      cases hgs : (streettOpsF cs cr).getStatus auxF stepF.succ[stepF.idx] with
      | dead =>
        simp only [hgs] at hr
        exact ih auxF _ rF hr (hinv.bump _)
      | live =>
        simp only [hgs] at hr
        rcases hupd : (streettOpsF cs cr).update auxF (stepF.succMarks[stepF.idx]!) stepF.succ[stepF.idx]
          with ⟨auxF', found⟩
        simp only [hupd] at hr
        have hinv' : InvF succs expandOpts (stepF :: restF) auxF' := by
          have := hinv.update cs.numMarks (stepF.succMarks[stepF.idx]!) stepF.succ[stepF.idx]
          rw [show streettUpdateF cs.numMarks auxF (stepF.succMarks[stepF.idx]!) stepF.succ[stepF.idx]
            = (auxF', found) from hupd] at this
          exact this
        by_cases hf : found = true
        · simp only [hf, if_true, Option.some.injEq] at hr
          rw [← hr]; exact hinv'.witOK
        · simp only [hf] at hr
          exact ih auxF' _ rF hr (hinv'.bump _)
      | unknown =>
        simp only [hgs] at hr
        rcases hpshF : (streettOpsF cs cr).push auxF stepF.succ[stepF.idx] (stepF.succMarks[stepF.idx]!)
          with ⟨auxF', posF⟩
        simp only [hpshF] at hr
        have hinv' := (hinv.bump (stepF.idx + 1)).push stepF.succ[stepF.idx] (stepF.succMarks[stepF.idx]!)
          hgs (hexpO.fst _) (marksToBitmask (stepF.succMarks[stepF.idx]!))
        rw [show streettPushF auxF stepF.succ[stepF.idx] (stepF.succMarks[stepF.idx]!) = (auxF', posF)
          from hpshF] at hinv'
        exact ih auxF' _ rF hr hinv'
    · simp only [h, dite_false] at hr
      obtain ⟨-, -, hinv'⟩ := streettPopF_spec cs hwf cr hbits hinv
      rcases hpopF : (streettOpsF cs cr).pop (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
        auxF stepF with ⟨auxF', foundF⟩
      simp only [hpopF] at hr
      rw [show streettPopF cs cr auxF stepF = (auxF', foundF) from hpopF] at hinv'
      cases foundF with
      | true =>
        simp only [Option.some.injEq] at hr
        rw [← hr]; exact hinv'.witOK
      | false => exact ih auxF' _ rF hr hinv'

/-! ### The root, the outer loop, and the run -/

theorem dfsFromRoot_eq [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (cr : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (hexpO : ExpandCoherent succs edgeMarks expandOpts)
    (hbits : cs.numOptions ≠ 0 → ∀ s, (expandOpts s).2.2 = (succs s).map fun t => cs.edgeBits (s, t))
    (auxF : StreettAuxF State) (q0 : State) (hinv : InvF succs expandOpts [] auxF)
    (hq0 : liveStatusOf auxF.liveIndex auxF.dead q0 = .unknown) :
    liftF (dfsFromRoot (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
        expandOpts auxF q0) = dfsFromRoot (streettOps cs cr) succs edgeMarks expand auxF.proj q0 ∧
    ((dfsFromRoot (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
        expandOpts auxF q0).1 = none →
      InvF succs expandOpts []
        (dfsFromRoot (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
          expandOpts auxF q0).2) := by
  unfold dfsFromRoot
  rcases hpshF : streettPushF auxF q0 (Std.HashSet.emptyWithCapacity 0) with ⟨auxF', posF⟩
  have hpshF' : (streettOpsF cs cr).push auxF q0 (Std.HashSet.emptyWithCapacity 0) = (auxF', posF) := hpshF
  have hpsh : (streettOps cs cr).push auxF.proj q0 (Std.HashSet.emptyWithCapacity 0) = (auxF'.proj, posF) := by
    obtain ⟨h1, h2⟩ := streettPushF_proj auxF q0 (Std.HashSet.emptyWithCapacity 0)
    rw [hpshF] at h1 h2
    exact Prod.ext h1.symm h2.symm
  simp only [hpshF', hpsh]
  have hinv' := hinv.push q0 (Std.HashSet.emptyWithCapacity 0) hq0 (hexpO.fst _) 0
  rw [hpshF] at hinv'
  set stepP : DFSStep State Nat := { state := q0, pos := posF, acc := 0, succ := (expand q0).1, succMarks := (expand q0).2.1, succOpts := (expand q0).2.2, idx := 0 } with hstepP
  set stepF : DFSStep State Nat := { state := q0, pos := posF, acc := 0, succ := (expandOpts q0).1, succMarks := (expandOpts q0).2.1, succOpts := (expandOpts q0).2.2, idx := 0 } with hstepF
  have hstk : List.map DFSStep.strip (stepP :: []) = List.map DFSStep.strip (stepF :: []) := by
    simp only [List.map_cons, List.map_nil, hstepP, hstepF, DFSStep.strip, hexp.fst, hexpO.fst,
      hexp.snd, hexpO.snd]
  obtain ⟨heq, hinvr⟩ := dfsGo_eq cs hwf cr succs edgeMarks expand expandOpts hexp hexpO hbits auxF' _ _
    hinv' hstk
  rw [← heq]
  cases hF : dfsGo (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
      expandOpts auxF' (stepF :: []) with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    exact ⟨rfl, fun _ => hinv'.nil_of_singleton⟩
  | some rF =>
    simp only [Option.map_some, Option.getD_some]
    exact ⟨by first | rfl | trivial, fun hn => hinvr rF hF hn⟩

theorem dfsFromRoot_witOK [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (cr : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexpO : ExpandCoherent succs edgeMarks expandOpts)
    (hbits : cs.numOptions ≠ 0 → ∀ s, (expandOpts s).2.2 = (succs s).map fun t => cs.edgeBits (s, t))
    (auxF : StreettAuxF State) (q0 : State) (hinv : InvF succs expandOpts [] auxF)
    (hq0 : liveStatusOf auxF.liveIndex auxF.dead q0 = .unknown) :
    WitOK succs (dfsFromRoot (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
      expandOpts auxF q0).2 := by
  unfold dfsFromRoot
  rcases hpshF : streettPushF auxF q0 (Std.HashSet.emptyWithCapacity 0) with ⟨auxF', posF⟩
  have hpshF' : (streettOpsF cs cr).push auxF q0 (Std.HashSet.emptyWithCapacity 0) = (auxF', posF) := hpshF
  simp only [hpshF']
  have hinv' := hinv.push q0 (Std.HashSet.emptyWithCapacity 0) hq0 (hexpO.fst _) 0
  rw [hpshF] at hinv'
  set stepF : DFSStep State Nat := { state := q0, pos := posF, acc := 0, succ := (expandOpts q0).1, succMarks := (expandOpts q0).2.1, succOpts := (expandOpts q0).2.2, idx := 0 } with hstepF
  cases hF : dfsGo (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
      expandOpts auxF' (stepF :: []) with
  | none => simp only [Option.getD_none]; exact hinv'.witOK
  | some rF =>
    simp only [Option.getD_some]
    exact dfsGo_witOK cs hwf cr succs edgeMarks expandOpts hexpO hbits auxF' _ rF hF hinv'

theorem genericDFSGo_eq [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (cr : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (hexpO : ExpandCoherent succs edgeMarks expandOpts)
    (hbits : cs.numOptions ≠ 0 → ∀ s, (expandOpts s).2.2 = (succs s).map fun t => cs.edgeBits (s, t))
    (roots : List State) :
    ∀ auxF : StreettAuxF State, InvF succs expandOpts [] auxF →
      (genericDFSGo (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
          expandOpts roots auxF).map liftF =
        genericDFSGo (streettOps cs cr) succs edgeMarks expand roots auxF.proj := by
  induction roots with
  | nil =>
    intro auxF _
    rw [genericDFSGo.eq_def (streettOpsF cs cr), genericDFSGo.eq_def (streettOps cs cr)]
    rfl
  | cons q rest ih =>
    intro auxF hinv
    rw [genericDFSGo.eq_def (streettOpsF cs cr), genericDFSGo.eq_def (streettOps cs cr)]
    simp only []
    cases hgs : (streettOpsF cs cr).getStatus auxF q with
    | dead =>
      have hgs' : (streettOps cs cr).getStatus auxF.proj q = .dead := hgs
      simp only [hgs']
      exact ih auxF hinv
    | live =>
      have hgs' : (streettOps cs cr).getStatus auxF.proj q = .live := hgs
      simp only [hgs']
      exact ih auxF hinv
    | unknown =>
      have hgs' : (streettOps cs cr).getStatus auxF.proj q = .unknown := hgs
      simp only [hgs']
      obtain ⟨heq, hinvr⟩ := dfsFromRoot_eq cs hwf cr succs edgeMarks expand expandOpts hexp hexpO hbits
        auxF q hinv hgs
      rcases hdF : dfsFromRoot (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
        expandOpts auxF q with ⟨foundF, auxF'⟩
      rw [hdF] at heq hinvr
      rw [← heq]
      simp only [liftF]
      cases foundF with
      | some v => rfl
      | none =>
        simp only []
        exact ih auxF' (hinvr rfl)

theorem genericDFS_eq [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (cr : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (hexpO : ExpandCoherent succs edgeMarks expandOpts)
    (hbits : cs.numOptions ≠ 0 → ∀ s, (expandOpts s).2.2 = (succs s).map fun t => cs.edgeBits (s, t))
    (roots : List State) (auxF : StreettAuxF State) (hinv : InvF succs expandOpts [] auxF) :
    liftF (genericDFS (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
        expandOpts roots auxF) = genericDFS (streettOps cs cr) succs edgeMarks expand roots auxF.proj := by
  unfold genericDFS
  rw [← genericDFSGo_eq cs hwf cr succs edgeMarks expand expandOpts hexp hexpO hbits roots auxF hinv]
  cases genericDFSGo (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
      expandOpts roots auxF with
  | none => rfl
  | some rF => rfl

theorem genericDFSGo_witOK [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (cr : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (hexpO : ExpandCoherent succs edgeMarks expandOpts)
    (hbits : cs.numOptions ≠ 0 → ∀ s, (expandOpts s).2.2 = (succs s).map fun t => cs.edgeBits (s, t))
    (roots : List State) :
    ∀ auxF : StreettAuxF State, InvF succs expandOpts [] auxF →
      ∀ rF, genericDFSGo (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
        expandOpts roots auxF = some rF → WitOK succs rF.2 := by
  induction roots with
  | nil =>
    intro auxF hinv rF hr
    rw [genericDFSGo.eq_def] at hr
    simp only [Option.some.injEq] at hr
    rw [← hr]; exact hinv.witOK
  | cons q rest ih =>
    intro auxF hinv rF hr
    rw [genericDFSGo.eq_def] at hr
    simp only [] at hr
    cases hgs : (streettOpsF cs cr).getStatus auxF q with
    | dead => simp only [hgs] at hr; exact ih auxF hinv rF hr
    | live => simp only [hgs] at hr; exact ih auxF hinv rF hr
    | unknown =>
      simp only [hgs] at hr
      obtain ⟨-, hinvr⟩ := dfsFromRoot_eq cs hwf cr succs edgeMarks expand expandOpts hexp hexpO hbits
        auxF q hinv hgs
      have hw := dfsFromRoot_witOK cs hwf cr succs edgeMarks expandOpts hexpO hbits auxF q hinv hgs
      rcases hdF : dfsFromRoot (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
        expandOpts auxF q with ⟨foundF, auxF'⟩
      rw [hdF] at hinvr hw
      simp only [hdF] at hr
      cases foundF with
      | some v =>
        simp only [Option.some.injEq] at hr
        rw [← hr]; exact hw
      | none =>
        simp only [] at hr
        exact ih auxF' (hinvr rfl) rF hr

theorem genericDFS_witOK [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (cr : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (hexpO : ExpandCoherent succs edgeMarks expandOpts)
    (hbits : cs.numOptions ≠ 0 → ∀ s, (expandOpts s).2.2 = (succs s).map fun t => cs.edgeBits (s, t))
    (roots : List State) (auxF : StreettAuxF State) (hinv : InvF succs expandOpts [] auxF) :
    WitOK succs (genericDFS (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
      expandOpts roots auxF).2 := by
  unfold genericDFS
  cases hG : genericDFSGo (streettOpsF cs cr) (fun _ => #[]) (fun _ _ => Std.HashSet.emptyWithCapacity 0)
      expandOpts roots auxF with
  | none => simp only [Option.getD_none]; exact hinv.witOK
  | some rF =>
    simp only [Option.getD_some]
    exact genericDFSGo_witOK cs hwf cr succs edgeMarks expand expandOpts hexp hexpO hbits roots auxF hinv
      rF hG

theorem streettInitAuxF_inv [Inhabited State] (succs : State → Array State)
    (expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat) :
    InvF succs expandOpts [] (streettInitAuxF : StreettAuxF State) :=
  ⟨liveWF_init 0, rfl, rfl, fun _ h => by simp at h, List.Pairwise.nil,
    fun i hi => by simp [streettInitAuxF] at hi, rfl, fun k hk => by simp [streettInitAuxF] at hk⟩

/-- **The fast run is the proved run**, projected. -/
theorem streettRunF_eq [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (cr : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (hexpO : ExpandCoherent succs edgeMarks expandOpts)
    (hbits : cs.numOptions ≠ 0 → ∀ s, (expandOpts s).2.2 = (succs s).map fun t => cs.edgeBits (s, t))
    (initialStates : List State) :
    liftF (streettRunF cs cr expandOpts initialStates) =
      streettRun cs cr succs edgeMarks expand initialStates :=
  genericDFS_eq cs hwf cr succs edgeMarks expand expandOpts hexp hexpO hbits initialStates _
    (streettInitAuxF_inv succs expandOpts)

theorem streettRunF_witOK [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (cr : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (hexpO : ExpandCoherent succs edgeMarks expandOpts)
    (hbits : cs.numOptions ≠ 0 → ∀ s, (expandOpts s).2.2 = (succs s).map fun t => cs.edgeBits (s, t))
    (initialStates : List State) :
    WitOK succs (streettRunF cs cr expandOpts initialStates).2 :=
  genericDFS_witOK cs hwf cr succs edgeMarks expand expandOpts hexp hexpO hbits initialStates _
    (streettInitAuxF_inv succs expandOpts)

/-! ### Candidates, the prune loop, and the check -/

omit [BEq State] [Hashable State] in
/-- Filtering a payload that is the successors' image leaves the filtered successors' image. -/
theorem filterExpand_thd {e : Array State × Array (Std.HashSet Nat) × Array Nat}
    {ss : Array State} {g : State → Nat} (p : State → Bool) (h1 : e.1 = ss) (h3 : e.2.2 = ss.map g) :
    (filterExpand e p).2.2 = (ss.filter p).map g := by
  simp only [filterExpand, h1, h3]
  by_cases hs : ss.size = 0
  · have hnil : ss = #[] := Array.eq_empty_of_size_eq_zero hs
    subst hnil
    simp
  · have hne : (ss.map g).isEmpty = false := by
      simp only [Array.isEmpty, Array.size_map]
      simpa using hs
    rw [if_neg (by simp [hne]), zip_filter_map, Array.map_map]
    rfl

theorem candidateRunF_eq [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (rspec : RStreettSpec State L)
    (regionExpandOpts : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hregO : ∀ r, ExpandCoherent (rspec.regionSuccs r) (rspec.regionMarks r) (regionExpandOpts r))
    (hbitsR : cs.numOptions ≠ 0 → ∀ r s,
      (regionExpandOpts r s).2.2 = (rspec.regionSuccs r s).map fun t => cs.edgeBits (s, t))
    (c : Candidate State) :
    liftF (candidateRunF cs regionExpandOpts c) = candidateRun cs rspec c := by
  unfold candidateRunF candidateRun
  refine streettRunF_eq cs hwf c.regions (c.graph cs rspec) (rspec.regionMarks (c.region cs))
    (c.expand cs rspec) _ (c.expand_coherent cs rspec) ?_ ?_ c.states.toList
  · intro s
    exact filterExpand_fst_snd _ (hregO (c.region cs) s)
  · intro hn s
    exact filterExpand_thd _ ((hregO (c.region cs)).fst s) (hbitsR hn _ s)

theorem candidateRunF_witOK [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (rspec : RStreettSpec State L)
    (regionExpandOpts : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hregO : ∀ r, ExpandCoherent (rspec.regionSuccs r) (rspec.regionMarks r) (regionExpandOpts r))
    (hbitsR : cs.numOptions ≠ 0 → ∀ r s,
      (regionExpandOpts r s).2.2 = (rspec.regionSuccs r s).map fun t => cs.edgeBits (s, t))
    (c : Candidate State) :
    WitOK (c.graph cs rspec) (candidateRunF cs regionExpandOpts c).2 := by
  unfold candidateRunF
  refine streettRunF_witOK cs hwf c.regions (c.graph cs rspec) (rspec.regionMarks (c.region cs))
    (c.expand cs rspec) _ (c.expand_coherent cs rspec) ?_ ?_ c.states.toList
  · intro s
    exact filterExpand_fst_snd _ (hregO (c.region cs) s)
  · intro hn s
    exact filterExpand_thd _ ((hregO (c.region cs)).fst s) (hbitsR hn _ s)

/-- A fast prune result without its retained successors: what the proved loop returns. -/
def dropWS (r : Option (State × Array State × Array (Array State) × Array Nat × Candidate State) × Nat) :
    Option (State × Array State × Array Nat × Candidate State) × Nat :=
  (r.1.map fun x => (x.1, x.2.1, x.2.2.2.1, x.2.2.2.2), r.2)

/-- The retained successors a fast prune result carries are its witness's successors in its candidate's
graph, which is what the report's equality needs. -/
def WSOK [Inhabited State] (cs : CompiledSpec State L) (rspec : RStreettSpec State L)
    (r : Option (State × Array State × Array (Array State) × Array Nat × Candidate State) × Nat) : Prop :=
  ∀ a w ws wo C, r.1 = some (a, w, ws, wo, C) →
    ws.size = w.size ∧ ∀ k, k < w.size → ws[k]! = (C.graph cs rspec) w[k]!

theorem pruneLoopF_le [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (rspec : RStreettSpec State L)
    (regionExpandOpts : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hregO : ∀ r, ExpandCoherent (rspec.regionSuccs r) (rspec.regionMarks r) (regionExpandOpts r))
    (hbitsR : cs.numOptions ≠ 0 → ∀ r s,
      (regionExpandOpts r s).2.2 = (rspec.regionSuccs r s).map fun t => cs.edgeBits (s, t)) :
    ∀ n cands r, pruneLoopF cs regionExpandOpts n cands = some r →
      pruneLoop cs rspec n cands = some (dropWS r) ∧ WSOK cs rspec r := by
  refine pruneLoopF.partial_correctness cs regionExpandOpts
    (fun n cands r => pruneLoop cs rspec n cands = some (dropWS r) ∧ WSOK cs rspec r) ?_
  intro pruneLoopF' ih n cands r hr
  cases cands with
  | nil =>
    rw [pruneLoop]
    simp only [Option.some.injEq] at hr
    rw [← hr]
    exact ⟨rfl, fun a w ws wo C h => by simp [dropWS] at h⟩
  | cons c rest =>
    rw [pruneLoop]
    have hc := candidateRunF_eq cs hwf rspec regionExpandOpts hregO hbitsR c
    have hw := candidateRunF_witOK cs hwf rspec regionExpandOpts hregO hbitsR c
    rcases hcF : candidateRunF cs regionExpandOpts c with ⟨found?, aux⟩
    rw [hcF] at hc hw
    simp only [liftF] at hc
    rw [← hc]
    simp only [hcF] at hr
    cases found? with
    | some v =>
      obtain ⟨anchor, stem⟩ := v
      simp only [Option.some.injEq] at hr
      rw [← hr]
      refine ⟨rfl, ?_⟩
      intro a w ws wo C h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      exact hw
    | none => exact ih _ _ r hr

theorem pruneLoop_le [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (rspec : RStreettSpec State L)
    (regionExpandOpts : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hregO : ∀ r, ExpandCoherent (rspec.regionSuccs r) (rspec.regionMarks r) (regionExpandOpts r))
    (hbitsR : cs.numOptions ≠ 0 → ∀ r s,
      (regionExpandOpts r s).2.2 = (rspec.regionSuccs r s).map fun t => cs.edgeBits (s, t)) :
    ∀ n cands r, pruneLoop cs rspec n cands = some r →
      ∃ rF, pruneLoopF cs regionExpandOpts n cands = some rF ∧ dropWS rF = r ∧ WSOK cs rspec rF := by
  refine pruneLoop.partial_correctness cs rspec
    (fun n cands r => ∃ rF, pruneLoopF cs regionExpandOpts n cands = some rF ∧ dropWS rF = r ∧
      WSOK cs rspec rF) ?_
  intro pruneLoop' ih n cands r hr
  cases cands with
  | nil =>
    simp only [Option.some.injEq] at hr
    exact ⟨(none, n), by rw [pruneLoopF], by rw [← hr]; rfl, fun a w ws wo C h => by simp at h⟩
  | cons c rest =>
    have hc := candidateRunF_eq cs hwf rspec regionExpandOpts hregO hbitsR c
    have hw := candidateRunF_witOK cs hwf rspec regionExpandOpts hregO hbitsR c
    rcases hcF : candidateRunF cs regionExpandOpts c with ⟨found?, aux⟩
    rw [hcF] at hc hw
    simp only [liftF] at hc
    simp only [← hc] at hr
    rw [pruneLoopF]
    simp only [hcF]
    cases found? with
    | some v =>
      obtain ⟨anchor, stem⟩ := v
      simp only [Option.some.injEq] at hr
      refine ⟨_, rfl, by rw [← hr]; rfl, ?_⟩
      intro a w ws wo C h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      exact hw
    | none => exact ih _ _ r hr

theorem pruneLoopF_eq [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF) (rspec : RStreettSpec State L)
    (regionExpandOpts : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hregO : ∀ r, ExpandCoherent (rspec.regionSuccs r) (rspec.regionMarks r) (regionExpandOpts r))
    (hbitsR : cs.numOptions ≠ 0 → ∀ r s,
      (regionExpandOpts r s).2.2 = (rspec.regionSuccs r s).map fun t => cs.edgeBits (s, t))
    (n : Nat) (cands : List (Candidate State)) :
    (pruneLoopF cs regionExpandOpts n cands).map dropWS = pruneLoop cs rspec n cands ∧
      ∀ rF, pruneLoopF cs regionExpandOpts n cands = some rF → WSOK cs rspec rF := by
  cases hF : pruneLoopF cs regionExpandOpts n cands with
  | some r =>
    obtain ⟨h1, h2⟩ := pruneLoopF_le cs hwf rspec regionExpandOpts hregO hbitsR n cands r hF
    exact ⟨by rw [Option.map_some, h1], fun rF h => by cases h; exact h2⟩
  | none =>
    refine ⟨?_, fun rF h => by cases h⟩
    cases hP : pruneLoop cs rspec n cands with
    | none => rfl
    | some r =>
      obtain ⟨rF, hrF, -, -⟩ := pruneLoop_le cs hwf rspec regionExpandOpts hregO hbitsR n cands r hP
      rw [hF] at hrF; cases hrF

/-- Every entry of the memo is the witness's successors in `g`. -/
theorem witnessMemo_get [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (wit : Array State) (ws : Array (Array State)) (g : State → Array State)
    (hws : ∀ k, k < wit.size → ws[k]! = g wit[k]!) :
    ∀ s ss, (witnessMemo wit ws)[s]? = some ss → ss = g s := by
  unfold witnessMemo
  have key : ∀ (l : List Nat) (m : Std.HashMap State (Array State)),
      (∀ s ss, m[s]? = some ss → ss = g s) → (∀ k ∈ l, k < wit.size) →
      ∀ s ss, (l.foldl (fun m k => m.insert wit[k]! ws[k]!) m)[s]? = some ss → ss = g s := by
    intro l
    induction l with
    | nil => intro m hm _ s ss h; exact hm s ss h
    | cons k l ih =>
      intro m hm hl s ss h
      refine ih _ ?_ (fun k' hk' => hl k' (List.mem_cons_of_mem _ hk')) s ss h
      intro s' ss' h'
      rw [Std.HashMap.getElem?_insert] at h'
      split at h'
      · next heq =>
        rw [Option.some.injEq] at h'
        rw [← h', ← beq_iff_eq.mp heq]
        exact hws k (hl k (List.mem_cons_self ..))
      · exact hm s' ss' h'
  exact key _ _ (fun s ss h => by rw [Std.HashMap.getElem?_emptyWithCapacity] at h; cases h)
    (fun k hk => List.mem_range.mp hk)

/-- The report's graph is the graph, whenever the memo is correct. -/
theorem memoGraph_eq [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (wit : Array State) (ws : Array (Array State)) (g : State → Array State)
    (hws : ws.size = wit.size ∧ ∀ k, k < wit.size → ws[k]! = g wit[k]!) :
    memoGraph (witnessMemo wit ws) g = g := by
  funext s
  unfold memoGraph
  split
  · next ss h => exact witnessMemo_get wit ws g hws.2 s ss h
  · rfl

/-- **The fast check is the proved check.** -/
theorem streettCheckF_eq [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hwf : cs.WF)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand expandOpts : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (hexpO : ExpandCoherent succs edgeMarks expandOpts)
    (hbits : cs.numOptions ≠ 0 → ∀ s, (expandOpts s).2.2 = (succs s).map fun t => cs.edgeBits (s, t))
    (regionExpandOpts : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hregO : ∀ r, ExpandCoherent (cs.spec.regionSuccs r) (cs.spec.regionMarks r) (regionExpandOpts r))
    (hbitsR : cs.numOptions ≠ 0 → ∀ r s,
      (regionExpandOpts r s).2.2 = (cs.spec.regionSuccs r s).map fun t => cs.edgeBits (s, t))
    (initialStates : List State) :
    streettCheckF cs succs edgeMarks expandOpts regionExpandOpts initialStates =
      streettCheck cs succs edgeMarks expand initialStates := by
  unfold streettCheckF streettCheck
  have hrun := streettRunF_eq cs hwf 0 succs edgeMarks expand expandOpts hexp hexpO hbits initialStates
  have hwtop := streettRunF_witOK cs hwf 0 succs edgeMarks expand expandOpts hexp hexpO hbits initialStates
  rcases hF : streettRunF cs 0 expandOpts initialStates with ⟨found?, auxF⟩
  rw [hF] at hrun hwtop
  rw [← hrun]
  simp only [liftF, StreettAuxF.proj]
  cases found? with
  | some v =>
    obtain ⟨anchor, stem⟩ := v
    dsimp only
    rw [memoGraph_eq _ _ _ hwtop]
  | none =>
    dsimp only
    obtain ⟨hmap, hws⟩ := pruneLoopF_eq cs hwf cs.spec regionExpandOpts hregO hbitsR
      (auxF.live.size + auxF.dead.size) auxF.pending.toList
    rw [← hmap]
    cases hPF : pruneLoopF cs regionExpandOpts (auxF.live.size + auxF.dead.size) auxF.pending.toList with
    | none => rfl
    | some r =>
      obtain ⟨r1, n⟩ := r
      cases r1 with
      | none => rfl
      | some x =>
        obtain ⟨a, w, ws, wo, C⟩ := x
        have hok := hws _ hPF a w ws wo C rfl
        simp only [Option.map_some, dropWS]
        rw [memoGraph_eq _ _ _ hok]

end Lockstep

end LTLLib
