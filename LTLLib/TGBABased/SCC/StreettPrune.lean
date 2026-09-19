/-
  The recursive fairness check of [SLDP09], run on the SCCs a Tarjan search closes, one search plus a prune instead of the
  `2ⁿ` crossing of `FairRouter.lean`.

  A hoisted conjunct is a list of options, an option being a region `FG l` and marks `GF g`, and an SCC satisfies the
  assumption when every conjunct has an option available in it ([LSFZ16, Definition 3] per conjunct). A maximal SCC that
  fails can still contain a passing sub-SCC, so a failing conjunct with options that fail only on their regions sends
  `B ∩ l` back through the same search, which is [EL87]'s prune. Only the first failing conjunct branches, since any fair
  subgraph satisfies it through one of its options.

  ```
  check(B):                                     -- B a maximal SCC of the current subgraph
    if B covers the property marks and every conjunct has an available option:  report B
    if B misses a property mark:  discard B     -- marks are monotone downward
    let i be the first conjunct with no available option
    live := its options whose marks are all present in B
    if live = ∅ then discard B                  -- no subgraph can satisfy conjunct i either
    for each option (l, _) in live:  queue B ∩ l
  ```

  Defines:
  - `CompiledSpec`: `StreettSpec` flattened once, so the scan indexes options and marks by position
  - `CompiledSpec.WF`: what the flattening guarantees
  - `StreettAux`, `streettPush`/`streettUpdate`/`streettPop`, `streettOps`: the refinement of `GenericDFS`
  - `scanOptions`, `firstUnsatisfied`: the per-SCC test
  - `pruneLoop`, `streettCheck`: the outer loop and the entry point

  Proves:
  - `optionAvailable_iff`: the scan decides `StreettOption.availableIn` on the range it was run over
  - `firstUnsatisfied_none_accepting`, `firstUnsatisfied_some_blames`: the per-conjunct test decides
    `StreettSpec.accepting` on the flushed SCC, and names a conjunct with every option of it whose marks are present
  - `streettCheck_nonEmpty_valid`: a reported stem and cycle is an accepting cycle whose states satisfy every conjunct
  - `streettRun_found`: a reported counterexample lies in an internally connected SCC covering every property mark,
    reached by the reported stem, and the options recorded beside it cover every conjunct
  - `streettRun_none_pass`, `pruneLoop_none_refuted`: a search that reports nothing blames a conjunct for every maximal
    SCC covering the property marks and queues its pruned candidates, and a queue drained without a report is refuted
  - `streettCheck_empty_refutes`: an `.empty` answer refutes the whole graph in the sense of `RefutedFrom`
  - `streettCheck_empty_no_fairSCC`: an `.empty` answer rules out every `FairSCC`, on [SLDP09]'s recursion proved in
    `AbstractSpec/StreettPruneSpec.lean`

  References:
  - [SLDP09] Sun, Liu, Dong, Pang. PAT: Towards Flexible Verification under Fairness. CAV 2009.
  - [LSFZ16] Li, Song, Feng, Zhang. Verify LTL with Fairness Assumptions Efficiently. arXiv:1606.08116, 2016.
  - [EL87] Emerson, Lei. Efficient model checking in fragments of the propositional mu-calculus. LICS 1986.
  - [RDKP13] Renault, Duret-Lutz, Kordon, Poitrenaud. Three SCC-based Emptiness Checks for GBA. LPAR-19, 2013.
  - [CCLMT18] Chen, Cohen, Lévy, Merz, Théry. Formal Proofs of Tarjan's Algorithm in Why3, Coq, and Isabelle.
    arXiv:1810.11979, 2018.

  Sections:
  - The compiled spec
  - The search state
  - The per-SCC test
  - What the scan decides
  - What the per-conjunct scan decides
  - What the test decides on the flushed SCC
  - PUSH, UPDATE and POP
  - The `DFSOps` instance
  - The outer loop
  - The contract
-/
import LTLLib.AbstractSpec.EmptinessCheck
import LTLLib.TGBABased.AbstractSpec.EmptinessCheck
import LTLLib.TGBABased.AbstractSpec.LassoCheck
import LTLLib.TGBABased.AbstractSpec.SCCTheory
import LTLLib.TGBABased.AbstractSpec.StreettPruneSpec
import LTLLib.TGBABased.AbstractSpec.StreettSCC
import LTLLib.TGBABased.SCC.GenericDFS
import LTLLib.TGBABased.SCC.LiveStack
import LTLLib.TGBABased.SCC.SCCEnumeration
import LTLLib.TGBABased.SCC.WitnessExtraction

namespace LTLLib

variable {State : Type u} {L : Type w} [BEq State] [Hashable State]

/-! ## The compiled spec

Flattening `StreettSpec` once per check gives every option a position, a mark-bit range and a mask of the bits it needs,
so the scan and the availability test are `Nat` bit operations. -/

/-- `StreettSpec` with option positions, mark-bit ranges and per-option mark masks precomputed. -/
structure CompiledSpec (State : Type u) (L : Type w) where
  numMarks : Nat  -- the property automaton's own marks
  label : State → L
  regions : Array (L → Bool)  -- one per option, in the order the conjuncts are walked
  optMarks : Array (Array (L → Bool))  -- the same options' marks
  optMarkBase : Array Nat  -- the first `marksSeen` bit belonging to each option
  optMarkMask : Array Nat  -- all of that option's `marksSeen` bits at once
  conjunctStart : Array Nat  -- conjunct `i` owns options `conjunctStart[i] ..< conjunctStart[i+1]`
  numOptions : Nat
  numOptMarks : Nat
  spec : StreettSpec State L  -- the specification itself, for the report-time validator

/-- Entry `i` of `prefixSums ns 0 #[0]` totals the first `i` entries of `ns`, the last entry being the total. -/
def prefixSums (ns : Array Nat) (i : Nat) (out : Array Nat) : Array Nat :=
  if h : i < ns.size then prefixSums ns (i + 1) (out.push (out[i]! + ns[i])) else out
termination_by ns.size - i

private theorem prefixSums_spec (ns : Array Nat) :
    ∀ i out, out.size = i + 1 → i ≤ ns.size →
      (prefixSums ns i out).size = ns.size + 1 ∧
      (∀ j < i + 1, (prefixSums ns i out)[j]! = out[j]!) ∧
      (∀ j, i ≤ j → j < ns.size →
        (prefixSums ns i out)[j + 1]! = (prefixSums ns i out)[j]! + ns[j]!) := by
  intro i out
  induction i, out using prefixSums.induct (ns := ns) with
  | case1 i out hi ih =>
    intro hsize hle
    have hsize' : (out.push (out[i]! + ns[i])).size = i + 1 + 1 := by simp [hsize]
    obtain ⟨p1, p2, p3⟩ := ih hsize' (by omega)
    rw [prefixSums]
    simp only [hi, dif_pos]
    refine ⟨p1, fun j hj => ?_, fun j hij hj => ?_⟩
    · rw [p2 j (by omega), getElem!_pos _ _ (by simp [hsize]; omega),
        Array.getElem_push_lt (by omega), ← getElem!_pos _ _ (by omega)]
    · rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · have hlt : i < out.size := by omega
        have h3 : (out.push (out[i]! + ns[i]))[i + 1]! = out[i]! + ns[i] := by
          rw [getElem!_pos _ _ (by simp [hsize])]
          simp [Array.getElem_push, hsize]
        have h4 : (out.push (out[i]! + ns[i]))[i]! = out[i]! := by
          rw [getElem!_pos _ _ (by simp [hsize])]
          simp [Array.getElem_push, hsize]
        rw [p2 (i + 1) (by omega), p2 i (by omega), h3, h4, getElem!_pos ns i hi]
      · exact p3 j hlt hj
  | case2 i out hi =>
    intro hsize hle
    have hieq : i = ns.size := by omega
    subst hieq
    rw [prefixSums]
    simp only [hi, dif_neg, not_false_iff]
    exact ⟨hsize, fun _ _ => trivial, fun j hij hj => absurd hj (by omega)⟩

/-- Flatten a spec, numbering options and their marks in walk order. -/
def CompiledSpec.of (spec : StreettSpec State L) : CompiledSpec State L :=
  let fs := spec.flatten
  let flat : Array (StreettOption L) := fs.1
  let sizes : Array Nat := flat.map (·.marks.size)
  let bases : Array Nat := prefixSums sizes 0 #[0]
  { numMarks := spec.numMarks
    label := spec.label
    regions := flat.map (·.region)
    optMarks := flat.map (·.marks)
    optMarkBase := bases
    optMarkMask := (Array.range flat.size).map fun i => ((1 <<< sizes[i]!) - 1) <<< bases[i]!
    conjunctStart := fs.2
    numOptions := flat.size
    numOptMarks := bases[flat.size]!
    spec := spec }

section Wellformed
omit [BEq State] [Hashable State]

/-- What `CompiledSpec.of` guarantees: each option owns the mark bits `optMarkBase[o] ..< optMarkBase[o] + (optMarks[o]).size`
and its mask selects exactly those, and conjunct `i` owns the options `conjunctStart[i] ..< conjunctStart[i+1]`, in order. -/
structure CompiledSpec.WF (cs : CompiledSpec State L) : Prop where
  label_eq : cs.label = cs.spec.label
  numMarks_eq : cs.numMarks = cs.spec.numMarks
  regions_size : cs.regions.size = cs.numOptions
  optMarks_size : cs.optMarks.size = cs.numOptions
  base_zero : cs.optMarkBase[0]! = 0
  base_succ : ∀ o < cs.numOptions,
    cs.optMarkBase[o + 1]! = cs.optMarkBase[o]! + (cs.optMarks[o]!).size
  numOptMarks_eq : cs.numOptMarks = cs.optMarkBase[cs.numOptions]!
  mask_eq : ∀ o < cs.numOptions,
    cs.optMarkMask[o]! = ((1 <<< (cs.optMarks[o]!).size) - 1) <<< cs.optMarkBase[o]!
  conjunctStart_size : cs.conjunctStart.size = cs.spec.conjuncts.size + 1
  start_zero : cs.conjunctStart[0]! = 0
  start_succ : ∀ i < cs.spec.conjuncts.size,
    cs.conjunctStart[i + 1]! = cs.conjunctStart[i]! + (cs.spec.conjuncts[i]!).size
  numOptions_eq : cs.numOptions = cs.conjunctStart[cs.spec.conjuncts.size]!
  option_region : ∀ i < cs.spec.conjuncts.size, ∀ k < (cs.spec.conjuncts[i]!).size,
    cs.regions[cs.conjunctStart[i]! + k]! = (cs.spec.conjuncts[i]![k]!).region
  option_marks : ∀ i < cs.spec.conjuncts.size, ∀ k < (cs.spec.conjuncts[i]!).size,
    cs.optMarks[cs.conjunctStart[i]! + k]! = (cs.spec.conjuncts[i]![k]!).marks

-- a start array that begins somewhere and steps by the block sizes only ever grows
private theorem starts_mono {st : Array Nat} {sz : Nat → Nat} {n : Nat}
    (hsucc : ∀ i, i < n → st[i + 1]! = st[i]! + sz i) :
    ∀ q, q ≤ n → ∀ p, p ≤ q → st[p]! ≤ st[q]! := by
  intro q
  induction q with
  | zero =>
    intro _ p hp
    have hp0 : p = 0 := by omega
    subst hp0; exact Nat.le_refl _
  | succ q ih =>
    intro hq p hp
    rcases Nat.lt_or_ge p (q + 1) with h | h
    · have h1 := hsucc q (by omega)
      have h2 := ih (by omega) p (by omega)
      omega
    · have hpq : p = q + 1 := by omega
      subst hpq; exact Nat.le_refl _

/-- A flattened spec is well formed. -/
theorem CompiledSpec.of_wf (spec : StreettSpec State L) : (CompiledSpec.of spec).WF := by
  obtain ⟨f1, f2, f3, f4⟩ := spec.flatten_spec
  have hgetF : ∀ (a : Array (StreettOption L)) (j : Nat) (h : j < a.size), a[j]! = a[j]'h :=
    fun a j h => getElem!_pos a j h
  set F : Array (StreettOption L) := spec.flatten.1 with hF
  set S : Array Nat := spec.flatten.2 with hS
  set sizes : Array Nat := F.map (fun opt : StreettOption L => opt.marks.size) with hsizes
  set B : Array Nat := prefixSums sizes 0 #[0] with hB
  have hb := prefixSums_spec sizes 0 #[0] (by simp) (Nat.zero_le _)
  -- an option's recorded mark count is the length of its mark array
  have hsz : ∀ o, o < F.size →
      sizes[o]! = ((F.map (fun opt : StreettOption L => opt.marks))[o]!).size := by
    intro o ho
    rw [hsizes, getElem!_pos _ _ (by simpa using ho), getElem!_pos _ _ (by simpa using ho),
      Array.getElem_map, Array.getElem_map]
  -- conjunct `i` starts at `S[i]` and stays inside the flattened array
  have hSlt : ∀ i, i < spec.conjuncts.size → ∀ k, k < (spec.conjuncts[i]!).size →
      S[i]! + k < F.size := by
    intro i hi k hk
    have h1 := (f4 i hi).1
    have h2 := starts_mono (fun j hj => (f4 j hj).1) spec.conjuncts.size (Nat.le_refl _) (i + 1) hi
    omega
  have hregions : (F.map (fun opt : StreettOption L => opt.region)).size = F.size := by simp
  have hmarks : (F.map (fun opt : StreettOption L => opt.marks)).size = F.size := by simp
  have hzero : B[0]! = 0 := by rw [hB, hb.2.1 0 (by omega)]; simp
  have hsucc : ∀ o, o < F.size →
      B[o + 1]! = B[o]! + ((F.map (fun opt : StreettOption L => opt.marks))[o]!).size :=
    fun o ho => by rw [hB, hb.2.2 o (Nat.zero_le _) (by simp [hsizes]; omega), hsz o ho]
  have hmask : ∀ o, o < F.size →
      ((Array.range F.size).map fun i => ((1 <<< sizes[i]!) - 1) <<< B[i]!)[o]! =
        ((1 <<< ((F.map (fun opt : StreettOption L => opt.marks))[o]!).size) - 1) <<< B[o]! :=
    fun o ho => by
      rw [getElem!_pos _ _ (by simpa using ho), Array.getElem_map, Array.getElem_range, hsz o ho]
  have hregion_at : ∀ i, i < spec.conjuncts.size → ∀ k, k < (spec.conjuncts[i]!).size →
      (F.map (fun opt : StreettOption L => opt.region))[S[i]! + k]! =
        (spec.conjuncts[i]![k]!).region := fun i hi k hk => by
    have hidx := hSlt i hi k hk
    rw [getElem!_pos _ _ (by simpa using hidx), Array.getElem_map, ← hgetF F _ hidx,
      (f4 i hi).2 k hk]
  have hmarks_at : ∀ i, i < spec.conjuncts.size → ∀ k, k < (spec.conjuncts[i]!).size →
      (F.map (fun opt : StreettOption L => opt.marks))[S[i]! + k]! =
        (spec.conjuncts[i]![k]!).marks := fun i hi k hk => by
    have hidx := hSlt i hi k hk
    rw [getElem!_pos _ _ (by simpa using hidx), Array.getElem_map, ← hgetF F _ hidx,
      (f4 i hi).2 k hk]
  exact ⟨rfl, rfl, hregions, hmarks, hzero, hsucc, rfl, hmask, f1, f2, fun i hi => (f4 i hi).1, f3,
    hregion_at, hmarks_at⟩

theorem CompiledSpec.WF.base_mono {cs : CompiledSpec State L} (hwf : cs.WF) :
    ∀ q, q ≤ cs.numOptions → ∀ p, p ≤ q → cs.optMarkBase[p]! ≤ cs.optMarkBase[q]! :=
  starts_mono hwf.base_succ

theorem CompiledSpec.WF.start_mono {cs : CompiledSpec State L} (hwf : cs.WF) :
    ∀ q, q ≤ cs.spec.conjuncts.size → ∀ p, p ≤ q →
      cs.conjunctStart[p]! ≤ cs.conjunctStart[q]! :=
  starts_mono hwf.start_succ

/-- Every option of a conjunct is one of the compiled options. -/
theorem CompiledSpec.WF.option_lt {cs : CompiledSpec State L} (hwf : cs.WF) {i k : Nat}
    (hi : i < cs.spec.conjuncts.size) (hk : k < (cs.spec.conjuncts[i]!).size) :
    cs.conjunctStart[i]! + k < cs.numOptions := by
  have h1 := hwf.start_succ i hi
  have h2 := hwf.start_mono cs.spec.conjuncts.size (Nat.le_refl _) (i + 1) hi
  have h3 := hwf.numOptions_eq
  omega

private theorem base_block_lt {cs : CompiledSpec State L} (hwf : cs.WF) {p o : Nat}
    (hpo : p < o) (ho : o ≤ cs.numOptions) :
    cs.optMarkBase[p]! + (cs.optMarks[p]!).size ≤ cs.optMarkBase[o]! := by
  have h1 := hwf.base_succ p (by omega)
  have h2 := hwf.base_mono o ho (p + 1) hpo
  omega

/-- Every mark bit an option owns is below `numOptMarks`. -/
theorem CompiledSpec.WF.bit_lt {cs : CompiledSpec State L} (hwf : cs.WF) {p k : Nat}
    (hp : p < cs.numOptions) (hk : k < (cs.optMarks[p]!).size) :
    cs.optMarkBase[p]! + k < cs.numOptMarks := by
  have h1 := hwf.base_succ p hp
  have h2 := hwf.base_mono cs.numOptions (Nat.le_refl _) (p + 1) hp
  have h3 := hwf.numOptMarks_eq
  omega

/-- Distinct options own disjoint mark-bit ranges, so a set bit names the option it came from. -/
theorem CompiledSpec.WF.base_inj {cs : CompiledSpec State L} (hwf : cs.WF) {p o k j : Nat}
    (hp : p < cs.numOptions) (ho : o < cs.numOptions) (hk : k < (cs.optMarks[p]!).size)
    (hj : j < (cs.optMarks[o]!).size)
    (h : cs.optMarkBase[p]! + k = cs.optMarkBase[o]! + j) : p = o := by
  rcases Nat.lt_trichotomy p o with hlt | heq | hgt
  · have := base_block_lt hwf hlt (Nat.le_of_lt ho); omega
  · exact heq
  · have := base_block_lt hwf hgt (Nat.le_of_lt hp); omega

end Wellformed

/-- Every property mark plus the internal-edge bit. -/
def fullAccMask (numMarks : Nat) : Nat := (1 <<< (numMarks + 1)) - 1

/-! ## The search state

Tarjan's two stacks, plus the SCC that passed and the queue of pruned candidates. `acc` carries the property
marks in bits `0 ..< numMarks` and "this frame's component has an internal edge" in bit `numMarks`, so the
generalized Büchi half of the test never scans an edge. -/

/-- The prune's private search state. -/
structure StreettAux (State : Type u) [BEq State] [Hashable State] where
  live : Array State
  liveIndex : Std.HashMap State Nat -- position of each live state, for O(1) membership
  dead : Std.HashSet State
  dstack : Array (Nat × Nat)  -- (lowlink, acc), one entry per open frame
  witness : Array State  -- the SCC that passed, empty until one does
  witnessOpts : Array Nat  -- one available option per conjunct, whose marks the reported cycle also covers
  pending : Array (Std.HashSet State)  -- pruned candidates, each strictly smaller than the SCC that queued it

def streettInitAux : StreettAux State where
  live := #[]
  liveIndex := Std.HashMap.emptyWithCapacity 0
  dead := Std.HashSet.emptyWithCapacity 0
  dstack := #[]
  witness := #[]
  witnessOpts := #[]
  pending := #[]

def streettGetStatus (aux : StreettAux State) (q : State) : DFSStatus :=
  liveStatusOf aux.liveIndex aux.dead q

/-! ## The per-SCC test -/

/-- One option's marks at one state, which own bits `base ..< base + gs.size` of `marksSeen`. -/
private def scanMarksAt (gs : Array (L → Bool)) (lab : L) (base : Nat) (j : Nat) (marksSeen : Nat) : Nat :=
  if h : j < gs.size then
    scanMarksAt gs lab base (j + 1)
      (if !marksSeen.testBit (base + j) && gs[j] lab then marksSeen ||| (1 <<< (base + j)) else marksSeen)
  else marksSeen
termination_by gs.size - j

/-- Every option at one state, clearing the regions that fail here and setting the marks that hold here. -/
private def scanOptionsAt (cs : CompiledSpec State L) (lab : L) (o : Nat) (regionAlive marksSeen : Nat) :
    Nat × Nat :=
  if h : o < cs.numOptions then
    let regionAlive' :=
      if regionAlive.testBit o && !(cs.regions[o]! lab) then regionAlive ^^^ (1 <<< o) else regionAlive
    let need := cs.optMarkMask[o]!
    let marksSeen' :=
      if marksSeen &&& need != need then scanMarksAt cs.optMarks[o]! lab cs.optMarkBase[o]! 0 marksSeen
      else marksSeen
    scanOptionsAt cs lab (o + 1) regionAlive' marksSeen'
  else (regionAlive, marksSeen)
termination_by cs.numOptions - o

/-- One pass over `live[i …]`, stopping as soon as neither mask can move again. -/
private def scanStates (cs : CompiledSpec State L) (live : Array State) (i : Nat)
    (regionAlive marksSeen : Nat) : Nat × Nat :=
  if h : i < live.size then
    if regionAlive == 0 && marksSeen == (1 <<< cs.numOptMarks) - 1 then (regionAlive, marksSeen)
    else
      let (ra, ms) := scanOptionsAt cs (cs.label live[i]) 0 regionAlive marksSeen
      scanStates cs live (i + 1) ra ms
  else (regionAlive, marksSeen)
termination_by live.size - i

/-- One pass over the SCC, which is `live[lo …]`. `regionAlive` starts all ones and only loses bits, `marksSeen`
starts empty and only gains them. -/
def scanOptions (cs : CompiledSpec State L) (live : Array State) (lo : Nat) : Nat × Nat :=
  scanStates cs live lo ((1 <<< cs.numOptions) - 1) 0

/-- The option's marks are all present, so it is still worth pruning to even when its region fails. -/
def optionLive (cs : CompiledSpec State L) (marksSeen : Nat) (o : Nat) : Bool :=
  marksSeen &&& cs.optMarkMask[o]! == cs.optMarkMask[o]!

/-- The option's region holds everywhere and its marks are all present. -/
def optionAvailable (cs : CompiledSpec State L) (regionAlive marksSeen : Nat) (o : Nat) : Bool :=
  regionAlive.testBit o && optionLive cs marksSeen o

-- the first available option in `[o, hi)`
private def selectOne (cs : CompiledSpec State L) (regionAlive marksSeen : Nat) (o hi : Nat) :
    Option Nat :=
  if o < hi then
    if optionAvailable cs regionAlive marksSeen o then some o
    else selectOne cs regionAlive marksSeen (o + 1) hi
  else none
termination_by hi - o

-- the options of `[o, hi)` whose marks are all present
private def liveOptionsIn (cs : CompiledSpec State L) (marksSeen : Nat) (o hi : Nat)
    (acc : Array Nat) : Array Nat :=
  if o < hi then
    liveOptionsIn cs marksSeen (o + 1) hi (if optionLive cs marksSeen o then acc.push o else acc)
  else acc
termination_by hi - o

-- one available option per conjunct, from conjunct `i` on
private def selectFrom (cs : CompiledSpec State L) (regionAlive marksSeen : Nat) (i : Nat)
    (sel : Array Nat) : Array Nat :=
  if i < cs.conjunctStart.size - 1 then
    selectFrom cs regionAlive marksSeen (i + 1)
      (match selectOne cs regionAlive marksSeen cs.conjunctStart[i]! cs.conjunctStart[i + 1]! with
        | some o => sel.push o
        | none => sel)
  else sel
termination_by cs.conjunctStart.size - 1 - i

/-- The first available option of each conjunct, whose marks join the acceptance condition the reported cycle has to
cover. -/
def selectedOptions (cs : CompiledSpec State L) (regionAlive marksSeen : Nat) : Array Nat :=
  selectFrom cs regionAlive marksSeen 0 #[]

-- the live options of the first conjunct from `i` on with no available option
private def firstUnsatFrom (cs : CompiledSpec State L) (regionAlive marksSeen : Nat) (i : Nat) :
    Option (Array Nat) :=
  if i < cs.conjunctStart.size - 1 then
    if (selectOne cs regionAlive marksSeen cs.conjunctStart[i]! cs.conjunctStart[i + 1]!).isSome then
      firstUnsatFrom cs regionAlive marksSeen (i + 1)
    else some (liveOptionsIn cs marksSeen cs.conjunctStart[i]! cs.conjunctStart[i + 1]! #[])
  else none
termination_by cs.conjunctStart.size - 1 - i

/-- The live options of the first conjunct with no available option, `none` when every conjunct is satisfied.
Only the first such conjunct branches, since a fair subgraph has to satisfy it through one of its options. -/
def firstUnsatisfied (cs : CompiledSpec State L) (regionAlive marksSeen : Nat) : Option (Array Nat) :=
  firstUnsatFrom cs regionAlive marksSeen 0

/-- The part of the closing SCC that the option's region admits, which is the pruned candidate. -/
private def regionSubset (cs : CompiledSpec State L) (live : Array State) (lo : Nat)
    (r : L → Bool) : Std.HashSet State :=
  (live.extract lo live.size).foldl (init := Std.HashSet.emptyWithCapacity (live.size - lo))
    fun C s => if r (cs.label s) then C.insert s else C

/-! ## What the scan decides -/

section ScanCorrect
omit [BEq State] [Hashable State]

private theorem mask_testBit {size base k : Nat} (hk : k < size) :
    ((((1 <<< size) - 1) <<< base) : Nat).testBit (base + k) = true := by
  simp [Nat.testBit_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, hk]

private theorem mask_testBit_iff {size base x : Nat} :
    ((((1 <<< size) - 1) <<< base) : Nat).testBit x = true ↔ base ≤ x ∧ x - base < size := by
  simp [Nat.testBit_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

private theorem testBit_of_and_eq {ms need x : Nat} (h : ms &&& need = need)
    (hx : need.testBit x = true) : ms.testBit x = true := by
  have hb := congrArg (Nat.testBit · x) h
  simp only [Nat.testBit_and, hx, Bool.and_true] at hb
  exact hb

private theorem and_eq_iff {ms mask : Nat} :
    ms &&& mask = mask ↔ ∀ x, mask.testBit x = true → ms.testBit x = true := by
  constructor
  · intro h x hx; exact testBit_of_and_eq h hx
  · intro h
    refine Nat.eq_of_testBit_eq fun x => ?_
    rw [Nat.testBit_and]
    cases hx : mask.testBit x with
    | false => simp
    | true => simp [h x hx]

private theorem scanMarksAt_testBit (gs : Array (L → Bool)) (lab : L) (base b : Nat)
    (j marksSeen : Nat) :
    (scanMarksAt gs lab base j marksSeen).testBit b = true ↔
      marksSeen.testBit b = true ∨
        ∃ k, k < gs.size ∧ j ≤ k ∧ base + k = b ∧ gs[k]! lab = true := by
  induction j, marksSeen using scanMarksAt.induct (gs := gs) (lab := lab) (base := base) with
  | case1 j ms hj ih =>
    rw [scanMarksAt]
    simp only [hj, dif_pos]
    simp only [dite_eq_ite] at ih
    rw [ih]; clear ih
    have hget : gs[j]! = gs[j] := getElem!_pos gs j hj
    by_cases hc : (!ms.testBit (base + j) && gs[j] lab) = true
    · rw [if_pos hc]
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
        decide_eq_true_eq]
      constructor
      · rintro ((h | h) | ⟨k, hk, hjk, hbk, hgk⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, hj, Nat.le_refl _, h, by rw [hget]; exact hc.2⟩
        · exact Or.inr ⟨k, hk, Nat.le_of_succ_le hjk, hbk, hgk⟩
      · rintro (h | ⟨k, hk, hjk, hbk, hgk⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
          · exact Or.inl (Or.inr hbk)
          · exact Or.inr ⟨k, hk, hlt, hbk, hgk⟩
    · rw [if_neg hc]
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_and] at hc
      constructor
      · rintro (h | ⟨k, hk, hjk, hbk, hgk⟩)
        · exact Or.inl h
        · exact Or.inr ⟨k, hk, Nat.le_of_succ_le hjk, hbk, hgk⟩
      · rintro (h | ⟨k, hk, hjk, hbk, hgk⟩)
        · exact Or.inl h
        · rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
          · have hset : ms.testBit (base + j) = true := by
              by_contra hcon
              exact hc (by simpa using hcon) (by rw [← hget]; exact hgk)
            exact Or.inl (hbk ▸ hset)
          · exact Or.inr ⟨k, hk, hlt, hbk, hgk⟩
  | case2 j ms hj =>
    rw [scanMarksAt]
    simp only [hj, dif_neg, not_false_iff]
    constructor
    · exact Or.inl
    · rintro (h | ⟨k, hk, hjk, _, _⟩)
      · exact h
      · omega

private theorem scanOptionsAt_fst_testBit (cs : CompiledSpec State L) (lab : L) (b : Nat)
    (o ra ms : Nat) :
    (scanOptionsAt cs lab o ra ms).1.testBit b = true ↔
      ra.testBit b = true ∧ (o ≤ b → b < cs.numOptions → cs.regions[b]! lab = true) := by
  induction o, ra, ms using scanOptionsAt.induct (cs := cs) (lab := lab) with
  | case1 o ra ms ho ra' need ms' ih =>
    rw [scanOptionsAt]
    simp only [ho, dif_pos]
    simp only [ra', need, ms', dite_eq_ite] at ih
    rw [ih]; clear ih
    by_cases hcond : (ra.testBit o && !(cs.regions[o]! lab)) = true
    · rw [if_pos hcond]
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hcond
      simp only [Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow]
      grind
    · rw [if_neg hcond]
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_and,
        Bool.not_eq_false] at hcond
      grind
  | case2 o ra ms ho =>
    rw [scanOptionsAt]
    simp only [ho, dif_neg, not_false_iff]
    grind

private theorem scanOptionsAt_snd_testBit (cs : CompiledSpec State L) (hwf : cs.WF) (lab : L)
    (b : Nat) (o ra ms : Nat) :
    (scanOptionsAt cs lab o ra ms).2.testBit b = true ↔
      ms.testBit b = true ∨ ∃ p, o ≤ p ∧ p < cs.numOptions ∧ ∃ k, k < (cs.optMarks[p]!).size ∧
        cs.optMarkBase[p]! + k = b ∧ (cs.optMarks[p]!)[k]! lab = true := by
  induction o, ra, ms using scanOptionsAt.induct (cs := cs) (lab := lab) with
  | case1 o ra ms ho ra' need ms' ih =>
    rw [scanOptionsAt]
    simp only [ho, dif_pos]
    simp only [ra', need, ms', dite_eq_ite] at ih
    rw [ih]; clear ih
    by_cases hskip : (ms &&& cs.optMarkMask[o]! != cs.optMarkMask[o]!) = true
    · rw [if_pos hskip, scanMarksAt_testBit]
      constructor
      · rintro ((h | ⟨k, hk, _, hbk, hmk⟩) | ⟨p, hop, hp, hrest⟩)
        · exact Or.inl h
        · exact Or.inr ⟨o, Nat.le_refl _, ho, k, hk, hbk, hmk⟩
        · exact Or.inr ⟨p, Nat.le_of_succ_le hop, hp, hrest⟩
      · rintro (h | ⟨p, hop, hp, k, hk, hbk, hmk⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.eq_or_lt_of_le hop with rfl | hlt
          · exact Or.inl (Or.inr ⟨k, hk, Nat.zero_le _, hbk, hmk⟩)
          · exact Or.inr ⟨p, hlt, hp, k, hk, hbk, hmk⟩
    · rw [if_neg hskip]
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hskip
      constructor
      · rintro (h | ⟨p, hop, hp, hrest⟩)
        · exact Or.inl h
        · exact Or.inr ⟨p, Nat.le_of_succ_le hop, hp, hrest⟩
      · rintro (h | ⟨p, hop, hp, k, hk, hbk, hmk⟩)
        · exact Or.inl h
        · rcases Nat.eq_or_lt_of_le hop with rfl | hlt
          · exact Or.inl (hbk ▸ testBit_of_and_eq hskip ((hwf.mask_eq o hp) ▸ mask_testBit hk))
          · exact Or.inr ⟨p, hlt, hp, k, hk, hbk, hmk⟩
  | case2 o ra ms ho =>
    rw [scanOptionsAt]
    simp only [ho, dif_neg, not_false_iff]
    grind

private theorem scanStates_fst_testBit (cs : CompiledSpec State L) (live : Array State)
    (b i ra ms : Nat) :
    (scanStates cs live i ra ms).1.testBit b = true ↔
      ra.testBit b = true ∧
        (b < cs.numOptions → ∀ s ∈ live.toList.drop i, cs.regions[b]! (cs.label s) = true) := by
  induction i, ra, ms using scanStates.induct (cs := cs) (live := live) with
  | case1 i ra ms hi hbreak =>
    rw [scanStates]
    simp only [hi, dif_pos, hbreak, if_pos]
    simp only [Bool.and_eq_true, beq_iff_eq] at hbreak
    simp [hbreak.1]
  | case2 i ra ms hi hbreak ra' ms' heq ih =>
    rw [scanStates]
    simp only [hi, dif_pos]
    rw [if_neg hbreak, heq, ih]
    have hra' : ra' = (scanOptionsAt cs (cs.label live[i]) 0 ra ms).1 := by rw [heq]
    have hbit := scanOptionsAt_fst_testBit cs (cs.label live[i]) b 0 ra ms
    rw [← hra'] at hbit
    have hdrop : live.toList.drop i = live[i] :: live.toList.drop (i + 1) :=
      List.drop_eq_getElem_cons (by simpa using hi)
    rw [hbit, hdrop]
    grind
  | case3 i ra ms hi =>
    rw [scanStates]
    simp only [hi, dif_neg, not_false_iff]
    have hnil : live.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    simp [hnil]

private theorem scanStates_snd_testBit (cs : CompiledSpec State L) (hwf : cs.WF)
    (live : Array State) (b i ra ms : Nat) :
    (scanStates cs live i ra ms).2.testBit b = true ↔
      ms.testBit b = true ∨ ∃ s ∈ live.toList.drop i, ∃ p, p < cs.numOptions ∧
        ∃ k, k < (cs.optMarks[p]!).size ∧ cs.optMarkBase[p]! + k = b ∧
          (cs.optMarks[p]!)[k]! (cs.label s) = true := by
  induction i, ra, ms using scanStates.induct (cs := cs) (live := live) with
  | case1 i ra ms hi hbreak =>
    rw [scanStates]
    simp only [hi, dif_pos, hbreak, if_pos]
    simp only [Bool.and_eq_true, beq_iff_eq] at hbreak
    constructor
    · exact Or.inl
    · rintro (h | ⟨s, _, p, hp, k, hk, hbk, _⟩)
      · exact h
      · have := hwf.bit_lt hp hk
        rw [hbreak.2]
        simp only [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
        omega
  | case2 i ra ms hi hbreak ra' ms' heq ih =>
    rw [scanStates]
    simp only [hi, dif_pos]
    rw [if_neg hbreak, heq, ih]
    have hms' : ms' = (scanOptionsAt cs (cs.label live[i]) 0 ra ms).2 := by rw [heq]
    have hbit := scanOptionsAt_snd_testBit cs hwf (cs.label live[i]) b 0 ra ms
    rw [← hms'] at hbit
    have hdrop : live.toList.drop i = live[i] :: live.toList.drop (i + 1) :=
      List.drop_eq_getElem_cons (by simpa using hi)
    rw [hbit, hdrop]
    grind
  | case3 i ra ms hi =>
    rw [scanStates]
    simp only [hi, dif_neg, not_false_iff]
    have hnil : live.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    simp [hnil]

/-- An option's region bit survives the scan exactly when its region holds at every scanned state. -/
theorem scanOptions_fst_testBit (cs : CompiledSpec State L) (live : Array State) (lo b : Nat)
    (hb : b < cs.numOptions) :
    (scanOptions cs live lo).1.testBit b = true ↔
      ∀ s ∈ live.toList.drop lo, cs.regions[b]! (cs.label s) = true := by
  rw [scanOptions, scanStates_fst_testBit]
  simp [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, hb]

private theorem scanOptions_fst_lt (cs : CompiledSpec State L) (live : Array State) (lo b : Nat)
    (h : (scanOptions cs live lo).1.testBit b = true) : b < cs.numOptions := by
  rw [scanOptions, scanStates_fst_testBit] at h
  simp only [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, decide_eq_true_eq] at h
  exact h.1

/-- A mark bit is set after the scan exactly when the mark owning it holds at some scanned state. -/
theorem scanOptions_snd_testBit (cs : CompiledSpec State L) (hwf : cs.WF) (live : Array State)
    (lo b : Nat) :
    (scanOptions cs live lo).2.testBit b = true ↔
      ∃ s ∈ live.toList.drop lo, ∃ p, p < cs.numOptions ∧ ∃ k, k < (cs.optMarks[p]!).size ∧
        cs.optMarkBase[p]! + k = b ∧ (cs.optMarks[p]!)[k]! (cs.label s) = true := by
  rw [scanOptions, scanStates_snd_testBit _ hwf]
  simp

/-- The mask test reads back exactly the option's own mark bits. -/
theorem optionLive_iff_bits {cs : CompiledSpec State L} (hwf : cs.WF) {ms o : Nat}
    (ho : o < cs.numOptions) :
    optionLive cs ms o = true ↔
      ∀ j < (cs.optMarks[o]!).size, ms.testBit (cs.optMarkBase[o]! + j) = true := by
  rw [optionLive, beq_iff_eq, and_eq_iff]
  constructor
  · intro h j hj
    exact h _ ((hwf.mask_eq o ho) ▸ mask_testBit hj)
  · intro h x hx
    rw [hwf.mask_eq o ho, mask_testBit_iff] at hx
    have hb := h (x - cs.optMarkBase[o]!) hx.2
    rwa [Nat.add_sub_cancel' hx.1] at hb

/-- `optionLive` decides `StreettOption.marksPresent` on the scanned range. -/
theorem optionLive_iff (cs : CompiledSpec State L) (hwf : cs.WF) (live : Array State) (lo o : Nat)
    (ho : o < cs.numOptions) :
    optionLive cs (scanOptions cs live lo).2 o = true ↔
      ∀ g ∈ cs.optMarks[o]!, ∃ s ∈ live.toList.drop lo, g (cs.label s) = true := by
  rw [optionLive_iff_bits hwf ho]
  constructor
  · intro h g hg
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hg
    have hbit := h j hj
    rw [scanOptions_snd_testBit cs hwf] at hbit
    obtain ⟨s, hs, p, hp, k, hk, hbk, hmk⟩ := hbit
    have hpo : p = o := hwf.base_inj hp ho hk hj hbk
    subst hpo
    have hkj : k = j := by omega
    subst hkj
    exact ⟨s, hs, by rwa [getElem!_pos (cs.optMarks[p]!) k hk] at hmk⟩
  · intro h j hj
    rw [scanOptions_snd_testBit cs hwf]
    obtain ⟨s, hs, hgs⟩ := h _ (Array.getElem_mem hj)
    exact ⟨s, hs, o, ho, j, hj, rfl, by rwa [getElem!_pos (cs.optMarks[o]!) j hj]⟩

/-- The scan decides `StreettOption.availableIn` on the scanned range: the option's region holds at every
scanned state, and each of its marks holds at some scanned state. -/
theorem optionAvailable_iff (cs : CompiledSpec State L) (hwf : cs.WF) (live : Array State)
    (lo o : Nat) (ho : o < cs.numOptions) :
    optionAvailable cs (scanOptions cs live lo).1 (scanOptions cs live lo).2 o = true ↔
      (∀ s ∈ live.toList.drop lo, cs.regions[o]! (cs.label s) = true) ∧
        ∀ g ∈ cs.optMarks[o]!, ∃ s ∈ live.toList.drop lo, g (cs.label s) = true := by
  rw [optionAvailable, Bool.and_eq_true, scanOptions_fst_testBit cs live lo o ho,
    optionLive_iff cs hwf live lo o ho]

/-! ## What the per-conjunct scan decides -/

private theorem selectOne_eq_none {cs : CompiledSpec State L} {ra ms hi : Nat} :
    ∀ o, selectOne cs ra ms o hi = none ↔
      ∀ p, o ≤ p → p < hi → optionAvailable cs ra ms p = false := by
  intro o
  induction o using selectOne.induct (cs := cs) (regionAlive := ra) (marksSeen := ms) (hi := hi) with
  | case1 x hx havail =>
    rw [selectOne, if_pos hx, if_pos havail]
    constructor
    · intro h; exact absurd h (by simp)
    · intro h
      have hc := h x (Nat.le_refl _) hx
      rw [havail] at hc
      exact absurd hc (by simp)
  | case2 x hx hnavail ih =>
    rw [selectOne, if_pos hx, if_neg hnavail, ih]
    constructor
    · intro h p hp hph
      rcases Nat.eq_or_lt_of_le hp with rfl | hlt
      · simpa using hnavail
      · exact h p hlt hph
    · intro h p hp hph
      exact h p (Nat.le_of_succ_le hp) hph
  | case3 x hx =>
    rw [selectOne, if_neg hx]
    simp only [true_iff]
    intro p hp hph
    omega

private theorem selectOne_eq_some {cs : CompiledSpec State L} {ra ms hi : Nat} :
    ∀ o r, selectOne cs ra ms o hi = some r →
      o ≤ r ∧ r < hi ∧ optionAvailable cs ra ms r = true := by
  intro o
  induction o using selectOne.induct (cs := cs) (regionAlive := ra) (marksSeen := ms) (hi := hi) with
  | case1 x hx havail =>
    intro r h
    rw [selectOne, if_pos hx, if_pos havail] at h
    obtain rfl : x = r := by simpa using h
    exact ⟨Nat.le_refl _, hx, havail⟩
  | case2 x hx hnavail ih =>
    intro r h
    rw [selectOne, if_pos hx, if_neg hnavail] at h
    obtain ⟨h1, h2, h3⟩ := ih r h
    exact ⟨Nat.le_of_succ_le h1, h2, h3⟩
  | case3 x hx =>
    intro r h
    rw [selectOne, if_neg hx] at h
    exact absurd h (by simp)

private theorem mem_liveOptionsIn {cs : CompiledSpec State L} {ms hi : Nat} :
    ∀ o acc p, p ∈ liveOptionsIn cs ms o hi acc ↔
      p ∈ acc ∨ (o ≤ p ∧ p < hi ∧ optionLive cs ms p = true) := by
  intro o acc
  induction o, acc using liveOptionsIn.induct (cs := cs) (marksSeen := ms) (hi := hi) with
  | case1 x acc hx ih =>
    intro p
    rw [liveOptionsIn, if_pos hx]
    simp only [dite_eq_ite] at ih
    rw [ih p]
    by_cases hl : optionLive cs ms x = true
    · rw [if_pos hl]
      simp only [Array.mem_push]
      constructor
      · rintro ((hp | rfl) | ⟨h1, h2, h3⟩)
        · exact Or.inl hp
        · exact Or.inr ⟨Nat.le_refl _, hx, hl⟩
        · exact Or.inr ⟨Nat.le_of_succ_le h1, h2, h3⟩
      · rintro (hp | ⟨h1, h2, h3⟩)
        · exact Or.inl (Or.inl hp)
        · rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr ⟨hlt, h2, h3⟩
    · rw [if_neg hl]
      constructor
      · rintro (hp | ⟨h1, h2, h3⟩)
        · exact Or.inl hp
        · exact Or.inr ⟨Nat.le_of_succ_le h1, h2, h3⟩
      · rintro (hp | ⟨h1, h2, h3⟩)
        · exact Or.inl hp
        · rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
          · exact absurd h3 hl
          · exact Or.inr ⟨hlt, h2, h3⟩
  | case2 x acc hx =>
    intro p
    rw [liveOptionsIn, if_neg hx]
    constructor
    · exact Or.inl
    · rintro (hp | ⟨h1, h2, _⟩)
      · exact hp
      · omega

private theorem firstUnsatFrom_eq_none {cs : CompiledSpec State L} {ra ms : Nat} :
    ∀ i, firstUnsatFrom cs ra ms i = none →
      ∀ j, i ≤ j → j < cs.conjunctStart.size - 1 →
        ∃ o, cs.conjunctStart[j]! ≤ o ∧ o < cs.conjunctStart[j + 1]! ∧
          optionAvailable cs ra ms o = true := by
  intro i
  induction i using firstUnsatFrom.induct (cs := cs) (regionAlive := ra) (marksSeen := ms) with
  | case1 x hx hsome ih =>
    intro h j hj hjn
    rw [firstUnsatFrom, if_pos hx, if_pos hsome] at h
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨o, selectOne_eq_some _ _ ho⟩
    · exact ih h j hlt hjn
  | case2 x hx hnone =>
    intro h _ _ _
    rw [firstUnsatFrom, if_pos hx, if_neg hnone] at h
    exact absurd h (by simp)
  | case3 x hx =>
    intro _ j hj hjn
    omega

private theorem firstUnsatFrom_eq_some {cs : CompiledSpec State L} {ra ms : Nat} :
    ∀ i opts, firstUnsatFrom cs ra ms i = some opts →
      ∃ j, i ≤ j ∧ j < cs.conjunctStart.size - 1 ∧
        (∀ o, cs.conjunctStart[j]! ≤ o → o < cs.conjunctStart[j + 1]! →
          optionAvailable cs ra ms o = false) ∧
        ∀ p, p ∈ opts ↔ cs.conjunctStart[j]! ≤ p ∧ p < cs.conjunctStart[j + 1]! ∧
          optionLive cs ms p = true := by
  intro i
  induction i using firstUnsatFrom.induct (cs := cs) (regionAlive := ra) (marksSeen := ms) with
  | case1 x hx hsome ih =>
    intro opts h
    rw [firstUnsatFrom, if_pos hx, if_pos hsome] at h
    obtain ⟨j, h1, h2, h3, h4⟩ := ih opts h
    exact ⟨j, Nat.le_of_succ_le h1, h2, h3, h4⟩
  | case2 x hx hnone =>
    intro opts h
    rw [firstUnsatFrom, if_pos hx, if_neg hnone] at h
    obtain rfl : liveOptionsIn cs ms cs.conjunctStart[x]! cs.conjunctStart[x + 1]! #[] = opts := by
      simpa using h
    refine ⟨x, Nat.le_refl _, hx, ?_, fun p => ?_⟩
    · have := selectOne_eq_none (cs := cs) (ra := ra) (ms := ms)
        (hi := cs.conjunctStart[x + 1]!) cs.conjunctStart[x]!
      exact this.mp (Option.not_isSome_iff_eq_none.mp (by simpa using hnone))
    · rw [mem_liveOptionsIn]
      simp
  | case3 x hx =>
    intro opts h
    rw [firstUnsatFrom, if_neg hx] at h
    exact absurd h (by simp)

private theorem mem_selectFrom_of_mem {cs : CompiledSpec State L} {ra ms : Nat} :
    ∀ i sel p, p ∈ sel → p ∈ selectFrom cs ra ms i sel := by
  intro i sel
  induction i, sel using selectFrom.induct (cs := cs) (regionAlive := ra) (marksSeen := ms) with
  | case1 i sel hi ih =>
    intro p hp
    rw [selectFrom, if_pos hi]
    refine ih p ?_
    split <;> simp [hp]
  | case2 i sel hi =>
    intro p hp
    rw [selectFrom, if_neg hi]
    exact hp

private theorem mem_selectFrom {cs : CompiledSpec State L} {ra ms : Nat} :
    ∀ i sel p, p ∈ selectFrom cs ra ms i sel →
      p ∈ sel ∨ optionAvailable cs ra ms p = true := by
  intro i sel
  induction i, sel using selectFrom.induct (cs := cs) (regionAlive := ra) (marksSeen := ms) with
  | case1 i sel hi ih =>
    intro p hp
    rw [selectFrom, if_pos hi] at hp
    rcases ih p hp with h | h
    · revert h
      split
      · next o ho =>
        rw [Array.mem_push]
        rintro (h | rfl)
        · exact Or.inl h
        · exact Or.inr (selectOne_eq_some _ _ ho).2.2
      · exact Or.inl
    · exact Or.inr h
  | case2 i sel hi =>
    intro p hp
    rw [selectFrom, if_neg hi] at hp
    exact Or.inl hp

private theorem selectFrom_covers {cs : CompiledSpec State L} {ra ms : Nat} :
    ∀ i sel j, i ≤ j → j < cs.conjunctStart.size - 1 →
      (selectOne cs ra ms cs.conjunctStart[j]! cs.conjunctStart[j + 1]!).isSome = true →
      ∃ o ∈ selectFrom cs ra ms i sel, cs.conjunctStart[j]! ≤ o ∧
        o < cs.conjunctStart[j + 1]! ∧ optionAvailable cs ra ms o = true := by
  intro i sel
  induction i, sel using selectFrom.induct (cs := cs) (regionAlive := ra) (marksSeen := ms) with
  | case1 i sel hi ih =>
    intro j hij hj hsome
    rw [selectFrom, if_pos hi]
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hsome
      refine ⟨o, mem_selectFrom_of_mem _ _ o ?_, selectOne_eq_some _ _ ho⟩
      rw [ho]
      simp
    · exact ih j hlt hj hsome
  | case2 i sel hi =>
    intro j hij hj _
    omega

/-- Every option `selectedOptions` reports is available. -/
theorem selectedOptions_available (cs : CompiledSpec State L) (ra ms : Nat) :
    ∀ o ∈ selectedOptions cs ra ms, optionAvailable cs ra ms o = true := by
  intro o ho
  rcases mem_selectFrom 0 #[] o ho with h | h
  · simp at h
  · exact h

/-- When no conjunct is unsatisfied, `selectedOptions` holds an available option of every conjunct. -/
theorem selectedOptions_covers {cs : CompiledSpec State L} (hwf : cs.WF) (ra ms : Nat)
    (h : firstUnsatisfied cs ra ms = none) :
    ∀ i < cs.spec.conjuncts.size, ∃ o ∈ selectedOptions cs ra ms,
      cs.conjunctStart[i]! ≤ o ∧ o < cs.conjunctStart[i + 1]! ∧
        optionAvailable cs ra ms o = true := by
  intro i hi
  have hn : i < cs.conjunctStart.size - 1 := by rw [hwf.conjunctStart_size]; omega
  obtain ⟨o, h1, h2, h3⟩ := firstUnsatFrom_eq_none 0 h i (Nat.zero_le _) hn
  have hsome : (selectOne cs ra ms cs.conjunctStart[i]! cs.conjunctStart[i + 1]!).isSome = true := by
    rcases hsel : selectOne cs ra ms cs.conjunctStart[i]! cs.conjunctStart[i + 1]! with _ | r
    · have := (selectOne_eq_none cs.conjunctStart[i]!).mp hsel o h1 h2
      rw [h3] at this
      exact absurd this (by simp)
    · simp
  exact selectFrom_covers 0 #[] i (Nat.zero_le _) hn hsome

end ScanCorrect


/-! ## What the test decides on the flushed SCC

The scan and the per-conjunct test on `live.toList.drop lo`, the range POP flushes, read as the set the specification is
written against. -/

section FlushedSCC

private theorem getElem!_option (a : Array (StreettOption L)) (j : Nat) (h : j < a.size) :
    a[j]! = a[j]'h := getElem!_pos a j h

section SetOfRange
variable [LawfulBEq State] [LawfulHashable State]

private theorem mem_foldl_insert (l : List State) (init : Std.HashSet State) (x : State) :
    x ∈ l.foldl (fun acc s => acc.insert s) init ↔ x ∈ init ∨ x ∈ l := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Std.HashSet.mem_insert, List.mem_cons, beq_iff_eq]
    tauto

/-- The flushed range read as a set. -/
theorem mem_sccSet {live : Array State} {lo n : Nat} {s : State} :
    s ∈ (live.extract lo live.size).foldl
        (init := Std.HashSet.emptyWithCapacity n) (fun h x => h.insert x) ↔
      s ∈ live.toList.drop lo := by
  rw [← Array.foldl_toList, mem_foldl_insert]
  simp only [Std.HashSet.not_mem_emptyWithCapacity, false_or, Array.toList_extract,
    List.take_of_length_le (by simp : (List.drop lo live.toList).length ≤ live.size - lo)]

private theorem mem_foldl_cond_insert (l : List State) (p : State → Bool)
    (init : Std.HashSet State) (x : State) :
    x ∈ l.foldl (fun acc s => if p s then acc.insert s else acc) init ↔
      x ∈ init ∨ (x ∈ l ∧ p x = true) := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    by_cases hp : p a = true
    · simp only [if_pos hp, Std.HashSet.mem_insert, beq_iff_eq]
      constructor
      · rintro ((rfl | hx) | ⟨hx, hpx⟩)
        · exact Or.inr ⟨Or.inl rfl, hp⟩
        · exact Or.inl hx
        · exact Or.inr ⟨Or.inr hx, hpx⟩
      · rintro (hx | ⟨rfl | hx, hpx⟩)
        · exact Or.inl (Or.inr hx)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr ⟨hx, hpx⟩
    · simp only [if_neg hp]
      constructor
      · rintro (hx | ⟨hx, hpx⟩)
        · exact Or.inl hx
        · exact Or.inr ⟨Or.inr hx, hpx⟩
      · rintro (hx | ⟨rfl | hx, hpx⟩)
        · exact Or.inl hx
        · exact absurd hpx hp
        · exact Or.inr ⟨hx, hpx⟩

/-- The pruned candidate holds exactly the flushed states the region admits. -/
private theorem mem_regionSubset {cs : CompiledSpec State L} {live : Array State} {lo : Nat}
    {r : L → Bool} {s : State} :
    s ∈ regionSubset cs live lo r ↔ s ∈ live.toList.drop lo ∧ r (cs.label s) = true := by
  rw [regionSubset, ← Array.foldl_toList, mem_foldl_cond_insert]
  simp only [Std.HashSet.not_mem_emptyWithCapacity, false_or, Array.toList_extract,
    List.take_of_length_le (by simp : (List.drop lo live.toList).length ≤ live.size - lo)]

end SetOfRange

/-- The compiled test on option `k` of conjunct `i` decides that option's availability on the flushed set. -/
theorem optionAvailable_iff_availableIn {cs : CompiledSpec State L} (hwf : cs.WF)
    (live : Array State) (lo : Nat) {B : Std.HashSet State}
    (hB : ∀ s, s ∈ B ↔ s ∈ live.toList.drop lo) {i k : Nat}
    (hi : i < cs.spec.conjuncts.size) (hk : k < (cs.spec.conjuncts[i]!).size) :
    optionAvailable cs (scanOptions cs live lo).1 (scanOptions cs live lo).2
        (cs.conjunctStart[i]! + k) = true ↔
      (cs.spec.conjuncts[i]![k]!).availableIn cs.spec.label B := by
  rw [optionAvailable_iff cs hwf live lo _ (hwf.option_lt hi hk), hwf.option_region i hi k hk,
    hwf.option_marks i hi k hk, hwf.label_eq]
  simp only [StreettOption.availableIn, StreettOption.regionHolds, StreettOption.marksPresent]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun s hs => h1 s ((hB s).mp hs), fun g hg => ?_⟩
    obtain ⟨s, hs, hgs⟩ := h2 g hg
    exact ⟨s, (hB s).mpr hs, hgs⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun s hs => h1 s ((hB s).mpr hs), fun g hg => ?_⟩
    obtain ⟨s, hs, hgs⟩ := h2 g hg
    exact ⟨s, (hB s).mp hs, hgs⟩

/-- No unsatisfied conjunct means the flushed set satisfies the whole assumption. -/
theorem firstUnsatisfied_none_accepting {cs : CompiledSpec State L} (hwf : cs.WF)
    (live : Array State) (lo : Nat) {B : Std.HashSet State}
    (hB : ∀ s, s ∈ B ↔ s ∈ live.toList.drop lo)
    (h : firstUnsatisfied cs (scanOptions cs live lo).1 (scanOptions cs live lo).2 = none) :
    cs.spec.accepting B := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hc
  have hce : cs.spec.conjuncts[i]! = cs.spec.conjuncts[i] := getElem!_pos _ i hi
  have hn : i < cs.conjunctStart.size - 1 := by rw [hwf.conjunctStart_size]; omega
  obtain ⟨o, h1, h2, h3⟩ := firstUnsatFrom_eq_none 0 h i (Nat.zero_le _) hn
  -- `o` sits at position `o - conjunctStart[i]` of conjunct `i`
  have hstep := hwf.start_succ i hi
  have hk : o - cs.conjunctStart[i]! < (cs.spec.conjuncts[i]!).size := by omega
  have hidx : cs.conjunctStart[i]! + (o - cs.conjunctStart[i]!) = o := by omega
  have hk2 : o - cs.conjunctStart[i]! < (cs.spec.conjuncts[i]).size := by rwa [hce] at hk
  refine ⟨(cs.spec.conjuncts[i]!)[o - cs.conjunctStart[i]!]!, ?_, ?_⟩
  · rw [hce, getElem!_option _ _ hk2]
    exact Array.getElem_mem _
  · rw [← optionAvailable_iff_availableIn hwf live lo hB hi hk, hidx]
    exact h3

/-- The blamed conjunct, together with every option of it whose marks are present in the flushed set, each one among
the reported positions. -/
theorem firstUnsatisfied_some_blames {cs : CompiledSpec State L} (hwf : cs.WF)
    (live : Array State) (lo : Nat) {B : Std.HashSet State}
    (hB : ∀ s, s ∈ B ↔ s ∈ live.toList.drop lo) {opts : Array Nat}
    (h : firstUnsatisfied cs (scanOptions cs live lo).1 (scanOptions cs live lo).2 = some opts) :
    ∃ c ∈ cs.spec.conjuncts, (∀ o ∈ opts, o < cs.numOptions) ∧
      ∀ opt ∈ c, opt.marksPresent cs.spec.label B →
        ∃ o ∈ opts, cs.regions[o]! = opt.region ∧ cs.optMarks[o]! = opt.marks := by
  obtain ⟨j, _, hjn, _, hmem⟩ := firstUnsatFrom_eq_some 0 opts h
  have hj : j < cs.spec.conjuncts.size := by rw [hwf.conjunctStart_size] at hjn; omega
  have hce : cs.spec.conjuncts[j]! = cs.spec.conjuncts[j] := getElem!_pos _ j hj
  have hstep := hwf.start_succ j hj
  have htop := hwf.start_mono cs.spec.conjuncts.size (Nat.le_refl _) (j + 1) hj
  have hnum := hwf.numOptions_eq
  refine ⟨cs.spec.conjuncts[j]!, by rw [hce]; exact Array.getElem_mem _, ?_, fun opt hopt hpres => ?_⟩
  · intro o ho
    have := (hmem o).mp ho
    omega
  · rw [hce] at hopt
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hopt
    have hk' : k < (cs.spec.conjuncts[j]!).size := by rw [hce]; exact hk
    have hget : (cs.spec.conjuncts[j]!)[k]! = cs.spec.conjuncts[j][k] := by
      rw [hce, getElem!_option _ _ hk]
    have hlive : optionLive cs (scanOptions cs live lo).2 (cs.conjunctStart[j]! + k) = true := by
      rw [optionLive_iff cs hwf live lo _ (hwf.option_lt hj hk'), hwf.option_marks j hj k hk', hget]
      intro g hg
      obtain ⟨s, hs, hgs⟩ := hpres g hg
      exact ⟨s, (hB s).mp hs, by rwa [hwf.label_eq]⟩
    refine ⟨cs.conjunctStart[j]! + k, (hmem _).mpr ⟨Nat.le_add_right _ _, by omega, hlive⟩, ?_, ?_⟩
    · rw [hwf.option_region j hj k hk', hget]
    · rw [hwf.option_marks j hj k hk', hget]

section Decrease
variable [LawfulBEq State] [LawfulHashable State]

/-- Every candidate one POP queues is a proper subset of the SCC it closed. -/
private theorem regionSubset_ssubset {cs : CompiledSpec State L} (hwf : cs.WF) (live : Array State)
    (lo : Nat) {opts : Array Nat} {o : Nat}
    (hfu : firstUnsatisfied cs (scanOptions cs live lo).1 (scanOptions cs live lo).2 = some opts)
    (ho : o ∈ opts) :
    (∀ s ∈ regionSubset cs live lo cs.regions[o]!, s ∈ live.toList.drop lo) ∧
      ∃ s ∈ live.toList.drop lo, s ∉ regionSubset cs live lo cs.regions[o]! := by
  obtain ⟨j, _, hjn, hnotavail, hmem⟩ := firstUnsatFrom_eq_some 0 opts hfu
  obtain ⟨hlo, hhi, hlive⟩ := (hmem o).mp ho
  -- the option's marks are present, so `optionAvailable` can only have failed on the region bit
  have hbit : (scanOptions cs live lo).1.testBit o = false := by
    have := hnotavail o hlo hhi
    rw [optionAvailable, hlive, Bool.and_true] at this
    exact this
  have hj : j < cs.spec.conjuncts.size := by rw [hwf.conjunctStart_size] at hjn; omega
  have ho' : o < cs.numOptions := by
    have h1 := hwf.start_mono cs.spec.conjuncts.size (Nat.le_refl _) (j + 1) hj
    have h2 := hwf.numOptions_eq
    omega
  refine ⟨fun s hs => (mem_regionSubset.mp hs).1, ?_⟩
  have hfail : ¬ ∀ s ∈ live.toList.drop lo, cs.regions[o]! (cs.label s) = true := by
    rw [← scanOptions_fst_testBit cs live lo o ho', hbit]
    simp
  obtain ⟨s, hs, hns⟩ := by simpa using hfail
  exact ⟨s, hs, fun hc => by simp [(mem_regionSubset.mp hc).2] at hns⟩

end Decrease

end FlushedSCC

/-! ## PUSH, UPDATE and POP -/

/-- A fresh frame is its own lowlink with no marks and no internal edge yet. All three operations destructure the
search state rather than using `{ aux with … }`, so the arrays are updated in place instead of copied. -/
def streettPush (aux : StreettAux State) (q : State) (_marks : Std.HashSet Nat) :
    StreettAux State × Nat :=
  let ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  let pos := live.size
  (⟨live.push q, liveIndex.insert q pos, dead, dstack.push (pos, 0), wit, wopts, pending⟩, pos)

/-- A back-edge lowers the top frame's lowlink and folds in the edge's marks and the internal-edge bit. It never
reports, an SCC only being decided once complete. -/
def streettUpdate (numMarks : Nat) (aux : StreettAux State) (marks : Std.HashSet Nat) (d : State) :
    StreettAux State × Bool :=
  let ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  match dstack.back? with
  | none => (⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩, false)
  | some (ll, acc) =>
    let top := (min ll (liveIndex.getD d 0), acc ||| marksToBitmask marks ||| (1 <<< numMarks))
    (⟨live, liveIndex, dead, dstack.pop.push top, wit, wopts, pending⟩, false)

/-- POP, where a closing frame either merges into its parent or completes an SCC and runs the test. A completed SCC
is always flushed, whether it passes, is discarded, or is queued for pruning. -/
def streettPop [Inhabited State] (cs : CompiledSpec State L) (aux : StreettAux State)
    (step : DFSStep State Nat) : StreettAux State × Bool :=
  let ⟨live, liveIndex, dead, dstack0, wit, wopts, pending⟩ := aux
  match dstack0.back? with
  | none => (⟨live, liveIndex, dead, dstack0, wit, wopts, pending⟩, false)
  | some (ll, acc) =>
    let dstack := dstack0.pop
    if ll = step.pos then
      -- the property's own marks are monotone downward, so a gap here kills every subgraph too
      if acc != fullAccMask cs.numMarks then
        let (live', liveIndex', dead') := liveFlush live liveIndex dead step.pos
        (⟨live', liveIndex', dead', dstack, wit, wopts, pending⟩, false)
      else
        let (regionAlive, marksSeen) := scanOptions cs live step.pos
        match firstUnsatisfied cs regionAlive marksSeen with
        | none =>
          let wit' := live.extract step.pos live.size
          let wopts' := selectedOptions cs regionAlive marksSeen
          let (live', liveIndex', dead') := liveFlush live liveIndex dead step.pos
          (⟨live', liveIndex', dead', dstack, wit', wopts', pending⟩, true)
        | some liveOpts =>
          let pending' := liveOpts.foldl (init := pending) fun ps o =>
            let C := regionSubset cs live step.pos cs.regions[o]!
            if C.isEmpty then ps else ps.push C
          let (live', liveIndex', dead') := liveFlush live liveIndex dead step.pos
          (⟨live', liveIndex', dead', dstack, wit, wopts, pending'⟩, false)
    else
      match dstack.back? with
      | none => (⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩, false)
      | some (pll, pacc) =>
        -- the tree edge into the closing frame is internal to the parent's component
        let merged := (min pll ll, pacc ||| step.acc ||| acc ||| (1 <<< cs.numMarks))
        (⟨live, liveIndex, dead, dstack.pop.push merged, wit, wopts, pending⟩, false)

/-! ## The `DFSOps` instance -/

/-- The SCC the test accepted. Empty until POP reports, and POP reports only after setting it. -/
def streettSccHint [LawfulBEq State] [LawfulHashable State] (aux : StreettAux State) :
    Std.HashSet State :=
  aux.witness.foldl (init := Std.HashSet.emptyWithCapacity aux.witness.size) fun h s => h.insert s

/-- Tarjan refined with the prune's own POP, the property marks arriving in `acc`. -/
def streettOps [Inhabited State] [LawfulBEq State] [LawfulHashable State] (cs : CompiledSpec State L) :
    DFSOps State where
  Aux := StreettAux State
  Position := Nat
  initAux := streettInitAux
  sccHint := streettSccHint
  numExplored := fun aux => aux.live.size + aux.dead.size
  getStatus := streettGetStatus
  push := streettPush
  update := streettUpdate cs.numMarks
  pop := fun _succs _edgeMarks aux step => streettPop cs aux step

/-- UPDATE only touches `dstack`. -/
private theorem streettUpdate_fields (numMarks : Nat) (aux : StreettAux State)
    (marks : Std.HashSet Nat) (d : State) :
    (streettUpdate numMarks aux marks d).1.live = aux.live ∧
    (streettUpdate numMarks aux marks d).1.liveIndex = aux.liveIndex ∧
    (streettUpdate numMarks aux marks d).1.dead = aux.dead ∧
    (streettUpdate numMarks aux marks d).1.pending = aux.pending := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  cases hb : dstack.back? with
  | none => simp [streettUpdate, hb]
  | some x => obtain ⟨ll, acc⟩ := x; simp [streettUpdate, hb]

private theorem streettUpdate_snd (numMarks : Nat) (aux : StreettAux State) (marks : Std.HashSet Nat)
    (d : State) : (streettUpdate numMarks aux marks d).2 = false := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  cases hb : dstack.back? with
  | none => simp [streettUpdate, hb]
  | some x => obtain ⟨ll, acc⟩ := x; simp [streettUpdate, hb]

private theorem streettPush_fields (aux : StreettAux State) (q : State) (marks : Std.HashSet Nat) :
    (streettPush aux q marks).1.live = aux.live.push q ∧
    (streettPush aux q marks).1.liveIndex = aux.liveIndex.insert q aux.live.size ∧
    (streettPush aux q marks).1.dead = aux.dead ∧
    (streettPush aux q marks).1.pending = aux.pending := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- POP either leaves the live and dead bookkeeping alone, or flushes it at the closing frame's position. -/
private theorem streettPop_triple [Inhabited State] (cs : CompiledSpec State L)
    (aux : StreettAux State) (step : DFSStep State Nat) :
    ((streettPop cs aux step).1.live, (streettPop cs aux step).1.liveIndex,
        (streettPop cs aux step).1.dead) = (aux.live, aux.liveIndex, aux.dead) ∨
      ((streettPop cs aux step).1.live, (streettPop cs aux step).1.liveIndex,
        (streettPop cs aux step).1.dead) = liveFlush aux.live aux.liveIndex aux.dead step.pos := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  rcases hb : dstack.back? with _ | ⟨ll, acc⟩
  · exact Or.inl (by simp only [streettPop, hb])
  · by_cases h : ll = step.pos
    · by_cases hacc : acc != fullAccMask cs.numMarks
      · exact Or.inr (by simp only [streettPop, hb, if_pos h, if_pos hacc])
      · rcases hfu : firstUnsatisfied cs (scanOptions cs live step.pos).1
            (scanOptions cs live step.pos).2 with _ | opts
        · exact Or.inr (by simp only [streettPop, hb, if_pos h, if_neg hacc, hfu])
        · exact Or.inr (by simp only [streettPop, hb, if_pos h, if_neg hacc, hfu])
    · rcases hb2 : dstack.pop.back? with _ | ⟨pll, pacc⟩
      · exact Or.inl (by simp only [streettPop, hb, if_neg h, hb2])
      · exact Or.inl (by simp only [streettPop, hb, if_neg h, hb2])

/-- POP reports only at a closing frame whose accumulator is full and whose scan blames no conjunct, recording the
flushed range as the witness and the selected options beside it. -/
private theorem streettPop_eq_true [Inhabited State] {cs : CompiledSpec State L}
    {aux aux' : StreettAux State} {step : DFSStep State Nat} (h : streettPop cs aux step = (aux', true)) :
    aux.dstack.back? = some (step.pos, fullAccMask cs.numMarks) ∧
      aux'.witness = aux.live.extract step.pos aux.live.size ∧
      firstUnsatisfied cs (scanOptions cs aux.live step.pos).1 (scanOptions cs aux.live step.pos).2 = none ∧
      aux'.witnessOpts =
        selectedOptions cs (scanOptions cs aux.live step.pos).1 (scanOptions cs aux.live step.pos).2 := by
  have h2 : (streettPop cs aux step).2 = true := by rw [h]
  have hw : aux'.witness = (streettPop cs aux step).1.witness := by rw [h]
  have ho : aux'.witnessOpts = (streettPop cs aux step).1.witnessOpts := by rw [h]
  rw [hw, ho]
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  rcases hb : dstack.back? with _ | ⟨ll, acc⟩
  · simp only [streettPop, hb, Bool.false_eq_true] at h2
  · by_cases hll : ll = step.pos
    · by_cases hacc : acc != fullAccMask cs.numMarks
      · simp only [streettPop, hb, if_pos hll, if_pos hacc, Bool.false_eq_true] at h2
      · have hacc' : acc = fullAccMask cs.numMarks := by simpa using hacc
        rcases hfu : firstUnsatisfied cs (scanOptions cs live step.pos).1
            (scanOptions cs live step.pos).2 with _ | opts
        · exact ⟨by simp only [hll, hacc'],
            by simp only [streettPop, hb, if_pos hll, if_neg hacc, hfu], rfl,
            by simp only [streettPop, hb, if_pos hll, if_neg hacc, hfu]⟩
        · simp only [streettPop, hb, if_pos hll, if_neg hacc, hfu, Bool.false_eq_true] at h2
    · rcases hb2 : dstack.pop.back? with _ | ⟨pll, pacc⟩
      · simp only [streettPop, hb, if_neg hll, hb2, Bool.false_eq_true] at h2
      · simp only [streettPop, hb, if_neg hll, hb2, Bool.false_eq_true] at h2

private theorem mem_foldl_push_cond {α : Type v} {β : Type v'} (g : α → β) (p : α → Bool) :
    ∀ (l : List α) (ps : Array β) (P : β),
    P ∈ l.foldl (fun ps x => if p x then ps else ps.push (g x)) ps ↔
      P ∈ ps ∨ ∃ x ∈ l, p x = false ∧ P = g x := by
  intro l
  induction l with
  | nil => intro ps P; simp
  | cons a l ih =>
    intro ps P
    rw [List.foldl_cons, ih]
    by_cases hp : p a = true
    · rw [if_pos hp]
      constructor
      · rintro (h | ⟨x, hx, hpx, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hpx, rfl⟩
      · rintro (h | ⟨x, hx, hpx, rfl⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp hx with rfl | hx'
          · exact absurd hpx (by simp [hp])
          · exact Or.inr ⟨x, hx', hpx, rfl⟩
    · rw [if_neg hp, Array.mem_push]
      constructor
      · rintro ((h | rfl) | ⟨x, hx, hpx, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨a, List.mem_cons_self .., by simpa using hp, rfl⟩
        · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hpx, rfl⟩
      · rintro (h | ⟨x, hx, hpx, rfl⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hx with rfl | hx'
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr ⟨x, hx', hpx, rfl⟩

/-- POP either leaves the queue alone or appends candidates the blamed conjunct of the closing SCC named. -/
private theorem streettPop_pending [Inhabited State] (cs : CompiledSpec State L)
    (aux : StreettAux State) (step : DFSStep State Nat) (P : Std.HashSet State)
    (hP : P ∈ (streettPop cs aux step).1.pending) :
    P ∈ aux.pending ∨ ∃ opts o, firstUnsatisfied cs (scanOptions cs aux.live step.pos).1
        (scanOptions cs aux.live step.pos).2 = some opts ∧ o ∈ opts ∧
      P = regionSubset cs aux.live step.pos cs.regions[o]! := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  rcases hb : dstack.back? with _ | ⟨ll, acc⟩
  · exact Or.inl (by simpa only [streettPop, hb] using hP)
  · by_cases h : ll = step.pos
    · by_cases hacc : acc != fullAccMask cs.numMarks
      · exact Or.inl (by simpa only [streettPop, hb, if_pos h, if_pos hacc] using hP)
      · rcases hfu : firstUnsatisfied cs (scanOptions cs live step.pos).1
            (scanOptions cs live step.pos).2 with _ | opts
        · exact Or.inl (by simpa only [streettPop, hb, if_pos h, if_neg hacc, hfu] using hP)
        · simp only [streettPop, hb, if_pos h, if_neg hacc, hfu] at hP
          rw [← Array.foldl_toList] at hP
          rcases (mem_foldl_push_cond _ _ opts.toList pending P).mp hP with hP' | ⟨o, ho, -, hPo⟩
          · exact Or.inl hP'
          · exact Or.inr ⟨opts, o, rfl, by simpa using ho, hPo⟩
    · rcases hb2 : dstack.pop.back? with _ | ⟨pll, pacc⟩
      · exact Or.inl (by simpa only [streettPop, hb, if_neg h, hb2] using hP)
      · exact Or.inl (by simpa only [streettPop, hb, if_neg h, hb2] using hP)

/-- A touched state is still live or has joined the dead after POP. -/
private theorem streettPop_touched_mono [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (aux : StreettAux State) (step : DFSStep State Nat) (s : State)
    (h : s ∈ aux.live ∨ s ∈ aux.dead) :
    s ∈ (streettPop cs aux step).1.live ∨ s ∈ (streettPop cs aux step).1.dead := by
  rcases streettPop_triple cs aux step with ht | ht
  · have h1 : (streettPop cs aux step).1.live = aux.live := congrArg (fun t => t.1) ht
    have h3 : (streettPop cs aux step).1.dead = aux.dead := congrArg (fun t => t.2.2) ht
    rw [h1, h3]; exact h
  · have h1 : (streettPop cs aux step).1.live =
        (liveFlush aux.live aux.liveIndex aux.dead step.pos).1 := congrArg (fun t => t.1) ht
    have h3 : (streettPop cs aux step).1.dead =
        (liveFlush aux.live aux.liveIndex aux.dead step.pos).2.2 := congrArg (fun t => t.2.2) ht
    rw [h1, h3]
    exact liveFlush_touched_mono step.pos aux.live aux.liveIndex aux.dead s h

/-- The prune's search invariant: `LiveWF` on the live bookkeeping, and every queued candidate a proper subset of the
states touched so far. -/
structure StreettWF [Inhabited State] (aux : StreettAux State) : Prop where
  live : LiveWF aux.live aux.liveIndex
  pending : ∀ P ∈ aux.pending, (∀ s ∈ P, s ∈ aux.live ∨ s ∈ aux.dead) ∧
    ∃ x, (x ∈ aux.live ∨ x ∈ aux.dead) ∧ x ∉ P

/-- `streettOps` is a lawful refinement: PUSH, UPDATE and POP preserve `StreettWF`, and the three status laws hold. -/
def streettLawful [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (hcs : cs.WF) : LawfulDFSOps (streettOps cs) (State := State) where
  WellFormed := StreettWF
  wf_push := fun aux q marks hq hwf => by
    show StreettWF (streettPush aux q marks).1
    obtain ⟨hl, hli, hd, hp⟩ := streettPush_fields aux q marks
    refine ⟨?_, ?_⟩
    · rw [hl, hli]
      refine hwf.live.push ?_
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      rw [show (streettOps cs).getStatus aux q = liveStatusOf aux.liveIndex aux.dead q from rfl,
        liveStatusOf, if_pos hc] at hq
      exact absurd hq (by simp)
    · rw [hl, hd, hp]
      intro P hP
      obtain ⟨hsub, x, hx, hxP⟩ := hwf.pending P hP
      exact ⟨fun s hs => (hsub s hs).imp (fun h => Array.mem_push.mpr (Or.inl h)) id,
        x, hx.imp (fun h => Array.mem_push.mpr (Or.inl h)) id, hxP⟩
  wf_update := fun aux marks d hwf => by
    show StreettWF (streettUpdate cs.numMarks aux marks d).1
    obtain ⟨hl, hli, hd, hp⟩ := streettUpdate_fields cs.numMarks aux marks d
    exact ⟨by rw [hl, hli]; exact hwf.live, by rw [hl, hd, hp]; exact hwf.pending⟩
  wf_pop := fun _succs _edgeMarks aux step hwf => by
    show StreettWF (streettPop cs aux step).1
    refine ⟨?_, fun P hP => ?_⟩
    · rcases streettPop_triple cs aux step with h | h
      · have h1 : (streettPop cs aux step).1.live = aux.live := congrArg (fun t => t.1) h
        have h2 : (streettPop cs aux step).1.liveIndex = aux.liveIndex := congrArg (fun t => t.2.1) h
        rw [h1, h2]
        exact hwf.live
      · have h1 : (streettPop cs aux step).1.live =
            (liveFlush aux.live aux.liveIndex aux.dead step.pos).1 := congrArg (fun t => t.1) h
        have h2 : (streettPop cs aux step).1.liveIndex =
            (liveFlush aux.live aux.liveIndex aux.dead step.pos).2.1 := congrArg (fun t => t.2.1) h
        rw [h1, h2]
        exact hwf.live.flush step.pos
    · rcases streettPop_pending cs aux step P hP with hold | ⟨opts, o, hfu, ho, rfl⟩
      · obtain ⟨hsub, x, hx, hxP⟩ := hwf.pending P hold
        exact ⟨fun s hs => streettPop_touched_mono cs aux step s (hsub s hs),
          x, streettPop_touched_mono cs aux step x hx, hxP⟩
      · obtain ⟨hsub, x, hx, hxP⟩ := regionSubset_ssubset hcs aux.live step.pos hfu ho
        -- a flushed state is still touched, which is all the queued candidate needs
        have hmem : ∀ y ∈ aux.live.toList.drop step.pos, y ∈ aux.live ∨ y ∈ aux.dead :=
          fun y hy => Or.inl (Array.mem_toList_iff.mp (List.mem_of_mem_drop hy))
        exact ⟨fun s hs => streettPop_touched_mono cs aux step s (hmem s (hsub s hs)),
          x, streettPop_touched_mono cs aux step x (hmem x hx), hxP⟩
  push_status := fun aux q marks q' => liveStatusOf_insert aux.liveIndex aux.dead q aux.live.size q'
  update_status := fun aux marks d q => by
    show liveStatusOf (streettUpdate cs.numMarks aux marks d).1.liveIndex
      (streettUpdate cs.numMarks aux marks d).1.dead q = liveStatusOf aux.liveIndex aux.dead q
    obtain ⟨_, hli, hd, _⟩ := streettUpdate_fields cs.numMarks aux marks d
    rw [hli, hd]
  pop_status := fun _succs _edgeMarks aux step q hwf => by
    show liveStatusOf (streettPop cs aux step).1.liveIndex (streettPop cs aux step).1.dead q =
        liveStatusOf aux.liveIndex aux.dead q ∨
      (liveStatusOf aux.liveIndex aux.dead q = .live ∧
        liveStatusOf (streettPop cs aux step).1.liveIndex (streettPop cs aux step).1.dead q = .dead)
    rcases streettPop_triple cs aux step with h | h
    · have h2 : (streettPop cs aux step).1.liveIndex = aux.liveIndex := congrArg (fun t => t.2.1) h
      have h3 : (streettPop cs aux step).1.dead = aux.dead := congrArg (fun t => t.2.2) h
      rw [h2, h3]
      exact Or.inl rfl
    · have h2 : (streettPop cs aux step).1.liveIndex =
          (liveFlush aux.live aux.liveIndex aux.dead step.pos).2.1 := congrArg (fun t => t.2.1) h
      have h3 : (streettPop cs aux step).1.dead =
          (liveFlush aux.live aux.liveIndex aux.dead step.pos).2.2 := congrArg (fun t => t.2.2) h
      rw [h2, h3]
      exact (liveFlush_spec step.pos aux.live aux.liveIndex aux.dead hwf.live.fwd hwf.live.bwd).2.2 q

/-- The prune's view of its search state for the flush-enumeration contract. -/
def streettView [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) : LowlinkView (streettOps cs) where
  live := fun aux => aux.live
  liveIndex := fun aux => aux.liveIndex
  dead := fun aux => aux.dead
  lowlinks := fun aux => aux.dstack.map (·.1)
  accs := fun aux => aux.dstack.map (·.2)
  extraAcc := 1 <<< cs.numMarks
  posNat := id

/-- The prune's search obeys the shared lowlink discipline. -/
def streettLowlinkLawful [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) : LowlinkLawful (streettOps cs) (streettView cs) where
  status := fun _ _ => rfl
  push_live := fun aux q m => (streettPush_fields aux q m).1
  push_liveIndex := fun aux q m => (streettPush_fields aux q m).2.1
  push_dead := fun aux q m => (streettPush_fields aux q m).2.2.1
  push_lowlinks := fun aux q m => by
    obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
    simp [streettView, streettOps, streettPush]
  push_accs := fun aux q m => by
    obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
    simp [streettView, streettOps, streettPush]
  push_pos := fun _ _ _ => rfl
  update_live := fun aux m d => (streettUpdate_fields cs.numMarks aux m d).1
  update_liveIndex := fun aux m d => (streettUpdate_fields cs.numMarks aux m d).2.1
  update_dead := fun aux m d => (streettUpdate_fields cs.numMarks aux m d).2.2.1
  update_lowlinks := fun aux m d ll hll => by
    obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
    simp only [streettView, Array.back?_map, Option.map_eq_some_iff] at hll
    obtain ⟨⟨ll', acc⟩, hb, rfl⟩ := hll
    simp [streettView, streettOps, streettUpdate, hb, Array.map_pop]
  update_accs := fun aux m d acc hacc => by
    obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
    simp only [streettView, Array.back?_map, Option.map_eq_some_iff] at hacc
    obtain ⟨⟨ll', acc'⟩, hb, rfl⟩ := hacc
    simp [streettView, streettOps, streettUpdate, hb, Array.map_pop]
  pop_close := fun succs edgeMarks aux step hcl => by
    obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
    simp only [LowlinkView.closes, streettView, Array.back?_map, beq_iff_eq,
      Option.map_eq_some_iff] at hcl
    obtain ⟨⟨ll, acc⟩, hb, hll⟩ := hcl
    have hll' : ll = step.pos := by simpa using hll
    refine ⟨?_, ?_, ?_⟩
    · by_cases hacc : acc != fullAccMask cs.numMarks
      · simp only [streettView, streettOps, streettPop, hb, if_pos hll', if_pos hacc]; rfl
      · rcases hfu : firstUnsatisfied cs (scanOptions cs live step.pos).1
            (scanOptions cs live step.pos).2 with _ | opts
        · simp only [streettView, streettOps, streettPop, hb, if_pos hll', if_neg hacc, hfu]; rfl
        · simp only [streettView, streettOps, streettPop, hb, if_pos hll', if_neg hacc, hfu]; rfl
    · subst hll'
      grind [streettPop, Array.map_pop, streettView, streettOps]
    · subst hll'
      grind [streettPop, Array.map_pop, streettView, streettOps]
  pop_merge := fun succs edgeMarks aux step hcl => by
    obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
    rcases hb : dstack.back? with _ | ⟨ll, acc⟩
    · exact ⟨by simp only [streettView, streettOps, streettPop, hb],
        by simp only [streettView, streettOps, streettPop, hb],
        by simp only [streettView, streettOps, streettPop, hb]⟩
    · have hne : ll ≠ step.pos := by
        intro hEq
        simp only [LowlinkView.closes, streettView, Array.back?_map, hb, hEq] at hcl
        simp at hcl
      rcases hb2 : dstack.pop.back? with _ | ⟨pll, pacc⟩
      · exact ⟨by simp only [streettView, streettOps, streettPop, hb, if_neg hne, hb2],
          by simp only [streettView, streettOps, streettPop, hb, if_neg hne, hb2],
          by simp only [streettView, streettOps, streettPop, hb, if_neg hne, hb2]⟩
      · exact ⟨by simp only [streettView, streettOps, streettPop, hb, if_neg hne, hb2],
          by simp only [streettView, streettOps, streettPop, hb, if_neg hne, hb2],
          by simp only [streettView, streettOps, streettPop, hb, if_neg hne, hb2]⟩
  pop_merge_lowlinks := fun succs edgeMarks aux step ll hcl hb => by
    obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
    simp only [streettView, Array.back?_map, Option.map_eq_some_iff] at hb
    obtain ⟨⟨ll', acc⟩, hbk, hll⟩ := hb
    simp only at hll
    subst hll
    have hne : ll' ≠ step.pos := by
      intro hEq
      simp only [LowlinkView.closes, streettView, Array.back?_map, hbk, hEq] at hcl
      simp at hcl
    have hmb : ((dstack.map (·.1)).pop).back? = Option.map (·.1) (dstack.pop.back?) := by
      rw [← Array.map_pop, Array.back?_map]
    rcases hb2 : dstack.pop.back? with _ | ⟨pll, pacc⟩
    · simp only [streettView, streettOps, streettPop, hbk, if_neg hne, hb2, hmb,
        Option.map_none, Array.map_pop]
    · simp only [streettView, streettOps, streettPop, hbk, if_neg hne, hb2, hmb,
        Option.map_some, Array.map_pop, Array.map_push]
  pop_merge_accs := fun succs edgeMarks aux step acc hcl hb => by
    obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
    simp only [streettView, Array.back?_map, Option.map_eq_some_iff] at hb
    obtain ⟨⟨ll', acc'⟩, hbk, hac⟩ := hb
    simp only at hac
    subst hac
    have hne : ll' ≠ step.pos := by
      intro hEq
      simp only [LowlinkView.closes, streettView, Array.back?_map, hbk, hEq] at hcl
      simp at hcl
    have hmb : ((dstack.map (·.2)).pop).back? = Option.map (·.2) (dstack.pop.back?) := by
      rw [← Array.map_pop, Array.back?_map]
    rcases hb2 : dstack.pop.back? with _ | ⟨pll, pacc⟩
    · simp only [streettView, streettOps, streettPop, hbk, if_neg hne, hb2, hmb,
        Option.map_none, Array.map_pop]
    · simp only [streettView, streettOps, streettPop, hbk, if_neg hne, hb2, hmb,
        Option.map_some, Array.map_pop, Array.map_push]
  init_live := rfl
  init_dead := by simp [streettView, streettOps, streettInitAux]
  init_lowlinks := by simp [streettView, streettOps, streettInitAux]
  init_accs := by simp [streettView, streettOps, streettInitAux]
  init_status := by simp [streettOps, streettGetStatus, liveStatusOf, streettInitAux]

private theorem streettPop_pending_mono [Inhabited State] (cs : CompiledSpec State L)
    (aux : StreettAux State) (step : DFSStep State Nat) (P : Std.HashSet State) (hP : P ∈ aux.pending) :
    P ∈ (streettPop cs aux step).1.pending := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  rcases hb : dstack.back? with _ | ⟨ll, acc⟩
  · simpa only [streettPop, hb] using hP
  · by_cases h : ll = step.pos
    · by_cases hacc : acc != fullAccMask cs.numMarks
      · simpa only [streettPop, hb, if_pos h, if_pos hacc] using hP
      · rcases hfu : firstUnsatisfied cs (scanOptions cs live step.pos).1
            (scanOptions cs live step.pos).2 with _ | opts
        · simpa only [streettPop, hb, if_pos h, if_neg hacc, hfu] using hP
        · simp only [streettPop, hb, if_pos h, if_neg hacc, hfu]
          rw [← Array.foldl_toList]
          exact (mem_foldl_push_cond _ _ opts.toList pending P).mpr (Or.inl hP)
    · rcases hb2 : dstack.pop.back? with _ | ⟨pll, pacc⟩
      · simpa only [streettPop, hb, if_neg h, hb2] using hP
      · simpa only [streettPop, hb, if_neg h, hb2] using hP

private theorem streettMonotone [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) :
    MonotoneAlong (streettOps cs) (fun a b : StreettAux State => ∀ P ∈ a.pending, P ∈ b.pending) where
  refl := fun _ _ h => h
  trans := fun _ _ _ h1 h2 P hP => h2 P (h1 P hP)
  push := fun a q m P hP => by
    show P ∈ (streettPush a q m).1.pending
    rw [(streettPush_fields a q m).2.2.2]
    exact hP
  update := fun a m d P hP => by
    show P ∈ (streettUpdate cs.numMarks a m d).1.pending
    rw [(streettUpdate_fields cs.numMarks a m d).2.2.2]
    exact hP
  pop := fun _ _ a step P hP => streettPop_pending_mono cs a step P hP

/-- A closing POP with a full accumulator that does not report has blamed a conjunct, and queued the pruned
candidate of each option it named unless that candidate is empty. -/
private theorem streettPop_queues [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {cs : CompiledSpec State L} {aux aux' : StreettAux State} {step : DFSStep State Nat}
    (hcl : (streettView cs).closes aux step = true)
    (hfull : (streettView cs).accAt aux 0 = fullAccMask cs.numMarks)
    (h : streettPop cs aux step = (aux', false)) :
    ∃ opts, firstUnsatisfied cs (scanOptions cs aux.live step.pos).1 (scanOptions cs aux.live step.pos).2 =
        some opts ∧
      ∀ o ∈ opts, (regionSubset cs aux.live step.pos cs.regions[o]!).isEmpty = true ∨
        regionSubset cs aux.live step.pos cs.regions[o]! ∈ aux'.pending := by
  obtain ⟨x, hb, hx1⟩ : ∃ x, aux.dstack.back? = some x ∧ x.1 = step.pos := by
    simp only [LowlinkView.closes, streettView, Array.back?_map, beq_iff_eq, Option.map_eq_some_iff] at hcl
    exact hcl
  have hx2 : x.2 = fullAccMask cs.numMarks := by
    rw [← hfull]
    exact (revGetD_zero (by simp [streettView, Array.back?_map, hb])).symm
  have h2 : (streettPop cs aux step).2 = false := by rw [h]
  have hp : aux'.pending = (streettPop cs aux step).1.pending := by rw [h]
  rw [hp]
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  obtain ⟨ll, acc⟩ := x
  have hb' : dstack.back? = some (ll, acc) := hb
  have hll : ll = step.pos := hx1
  have hacc0 : acc = fullAccMask cs.numMarks := hx2
  subst hll hacc0
  have hacc : ¬ ((fullAccMask cs.numMarks != fullAccMask cs.numMarks) = true) := by simp
  rcases hfu : firstUnsatisfied cs (scanOptions cs live step.pos).1 (scanOptions cs live step.pos).2
    with _ | opts
  · simp only [streettPop, hb', if_neg hacc, hfu] at h2
    exact absurd h2 (by simp)
  · refine ⟨opts, rfl, fun o ho => ?_⟩
    simp only [streettPop, hb', if_neg hacc, hfu]
    rw [← Array.foldl_toList]
    by_cases he : (regionSubset cs live step.pos cs.regions[o]!).isEmpty = true
    · exact Or.inl he
    · exact Or.inr ((mem_foldl_push_cond _ _ opts.toList pending _).mpr
        (Or.inr ⟨o, by simpa using ho, by simpa using he, rfl⟩))

/-! ## The outer loop -/

variable [Inhabited State] [LawfulBEq State] [LawfulHashable State]

/-- One search, over the whole product or over one pruned candidate. -/
def streettRun (cs : CompiledSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) :
    Option (State × List State) × StreettAux State :=
  genericDFS (streettOps cs) succs edgeMarks initialStates (streettOps cs).initAux

/-- Drain the queue of pruned candidates, each searched on the subgraph it induces. New candidates go to the
front, so the deepest prune is finished first and a witness is reached without draining the siblings. -/
def pruneLoop (cs : CompiledSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) :
    Nat → List (Std.HashSet State) → Option (Option (State × Array State × Array Nat) × Nat)
  | explored, [] => some (none, explored)
  | explored, C :: rest =>
    let (found?, aux) := streettRun cs (sccSuccs succs C) edgeMarks C.toList
    let explored' := explored + aux.live.size + aux.dead.size
    match found? with
    | some (anchor, _) => some (some (anchor, aux.witness, aux.witnessOpts), explored')
    | none => pruneLoop cs succs edgeMarks explored' (aux.pending.toList ++ rest)
partial_fixpoint -- terminating because every queued candidate is strictly smaller than the SCC that queued it

private theorem pruneLoop_cons_found (cs : CompiledSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (e : Nat) (C : Std.HashSet State)
    (rest : List (Std.HashSet State))
    (h : (streettRun cs (sccSuccs succs C) edgeMarks C.toList).1 ≠ none) :
    pruneLoop cs succs edgeMarks e (C :: rest) ≠ none := by
  rw [pruneLoop]
  cases hf : (streettRun cs (sccSuccs succs C) edgeMarks C.toList).1 with
  | none => exact absurd hf h
  | some r => simp [hf]

private theorem pruneLoop_cons_step (cs : CompiledSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (e : Nat) (C : Std.HashSet State)
    (rest : List (Std.HashSet State))
    (h : (streettRun cs (sccSuccs succs C) edgeMarks C.toList).1 = none) :
    pruneLoop cs succs edgeMarks e (C :: rest) =
      pruneLoop cs succs edgeMarks
        (e + (streettRun cs (sccSuccs succs C) edgeMarks C.toList).2.live.size
           + (streettRun cs (sccSuccs succs C) edgeMarks C.toList).2.dead.size)
        ((streettRun cs (sccSuccs succs C) edgeMarks C.toList).2.pending.toList ++ rest) := by
  rw [pruneLoop]
  simp [h]

/-- The worklist drains, on the hypothesis that a search queues only candidates strictly smaller than the one it ran
on. -/
theorem pruneLoop_drains (cs : CompiledSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (hdec : ∀ C : Std.HashSet State,
      ∀ P ∈ (streettRun cs (sccSuccs succs C) edgeMarks C.toList).2.pending, P.size < C.size) :
    ∀ n q, (∀ C ∈ q, C.size ≤ n) → ∀ b, (∀ e, pruneLoop cs succs edgeMarks e b ≠ none) →
      ∀ e, pruneLoop cs succs edgeMarks e (q ++ b) ≠ none := by
  intro n
  induction n with
  | zero =>
    intro q
    induction q with
    | nil => intro _ b hb e; simpa using hb e
    | cons C q' ih =>
      intro hq b hb e
      have hC : C.size = 0 := Nat.le_zero.mp (hq C (by simp))
      rw [List.cons_append]
      by_cases hf : (streettRun cs (sccSuccs succs C) edgeMarks C.toList).1 = none
      · rw [pruneLoop_cons_step _ _ _ _ _ _ hf]
        -- nothing can be strictly smaller than the empty candidate, so nothing was queued
        have hnil : (streettRun cs (sccSuccs succs C) edgeMarks C.toList).2.pending.toList = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro P hP
          have := hdec C P (by simpa using hP)
          omega
        rw [hnil, List.nil_append]
        exact ih (fun D hD => hq D (by simp [hD])) b hb _
      · exact pruneLoop_cons_found _ _ _ _ _ _ hf
  | succ n ihn =>
    intro q
    induction q with
    | nil => intro _ b hb e; simpa using hb e
    | cons C q' ih =>
      intro hq b hb e
      have hC : C.size ≤ n + 1 := hq C (by simp)
      rw [List.cons_append]
      by_cases hf : (streettRun cs (sccSuccs succs C) edgeMarks C.toList).1 = none
      · rw [pruneLoop_cons_step _ _ _ _ _ _ hf]
        refine ihn _ (fun P hP => ?_) (q' ++ b)
          (fun e' => ih (fun D hD => hq D (by simp [hD])) b hb e') _
        have := hdec C P (by simpa using hP)
        omega
      · exact pruneLoop_cons_found _ _ _ _ _ _ hf

/-- `pruneLoop` is defined on every queue, given that a search queues only candidates strictly smaller than the one it
ran on. -/
theorem pruneLoop_ne_none (cs : CompiledSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (hdec : ∀ C : Std.HashSet State,
      ∀ P ∈ (streettRun cs (sccSuccs succs C) edgeMarks C.toList).2.pending, P.size < C.size)
    (e : Nat) (q : List (Std.HashSet State)) : pruneLoop cs succs edgeMarks e q ≠ none := by
  obtain ⟨n, hn⟩ : ∃ n, ∀ C ∈ q, C.size ≤ n := by
    induction q with
    | nil => exact ⟨0, by simp⟩
    | cons C q' ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨max n C.size, fun D hD => ?_⟩
      rcases List.mem_cons.mp hD with rfl | hD'
      · exact Nat.le_max_right _ _
      · exact Nat.le_trans (hn D hD') (Nat.le_max_left _ _)
  have hb : ∀ e', pruneLoop cs succs edgeMarks e' ([] : List (Std.HashSet State)) ≠ none := by
    intro e'; rw [pruneLoop]; simp
  simpa using pruneLoop_drains cs succs edgeMarks hdec n q hn [] hb e

omit [Inhabited State] in
private theorem hashSet_size_lt {A B : Std.HashSet State} (hsub : ∀ s ∈ A, s ∈ B)
    {x : State} (hxB : x ∈ B) (hxA : x ∉ A) : A.size < B.size := by
  have hnd : (x :: A.toList).Nodup := by
    refine List.nodup_cons.mpr ⟨fun hc => hxA (Std.HashSet.mem_toList.mp hc), ?_⟩
    exact (Std.HashSet.distinct_toList (m := A)).imp (fun h => by simpa using h)
  have hsubl : (x :: A.toList) ⊆ B.toList := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact Std.HashSet.mem_toList.mpr hxB
    · exact Std.HashSet.mem_toList.mpr (hsub y (Std.HashSet.mem_toList.mp hy'))
  have hlen := (List.Nodup.subperm hnd hsubl).length_le
  simp only [List.length_cons, Std.HashSet.length_toList] at hlen
  omega

private theorem streettGetStatus_ne_unknown {aux : StreettAux State}
    (hwf : LiveWF aux.live aux.liveIndex) {s : State} (h : s ∈ aux.live ∨ s ∈ aux.dead) :
    streettGetStatus aux s ≠ .unknown := by
  rw [streettGetStatus, liveStatusOf]
  rcases h with h | h
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp h
    have hc : aux.liveIndex.contains aux.live[i] := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, hwf.fwd i hi]; rfl
    simp [hc]
  · by_cases hc : aux.liveIndex.contains s
    · simp [hc]
    · simp [hc, Std.HashSet.mem_iff_contains.mp h]

omit [LawfulBEq State] [LawfulHashable State] in
private theorem streettInitAux_wf : StreettWF (streettInitAux : StreettAux State) :=
  ⟨liveWF_init 0, by intro P hP; simp [streettInitAux] at hP⟩

/-- The sets the prune's own POP flushes are the maximal SCCs of the reachable subgraph. -/
theorem streettSCCs_sound (cs : CompiledSpec State L) (hcs : cs.WF) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (fr : FiniteReach initialStates succs) :
    SCCEnumerationSound initialStates succs
      (enumSCCs (streettOps cs) (streettView cs) succs edgeMarks initialStates) :=
  enumSCCs_sound (streettOps cs) (streettView cs) (streettLowlinkLawful cs) (streettLawful cs hcs)
    streettInitAux_wf succs edgeMarks initialStates fr

private theorem streettInitAux_unknown (cs : CompiledSpec State L) (q : State) :
    (streettOps cs).getStatus (streettOps cs).initAux q = .unknown := by
  show streettGetStatus streettInitAux q = .unknown
  simp [streettGetStatus, liveStatusOf, streettInitAux]

/-- Every candidate a search on `C` queues is strictly smaller than `C`. -/
theorem streettRun_pending_size_lt (cs : CompiledSpec State L) (hcs : cs.WF)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (C P : Std.HashSet State)
    (hP : P ∈ (streettRun cs (sccSuccs succs C) edgeMarks C.toList).2.pending) :
    P.size < C.size := by
  have hwf : StreettWF (streettRun cs (sccSuccs succs C) edgeMarks C.toList).2 :=
    genericDFS_wellFormed (streettOps cs) (sccSuccs succs C) edgeMarks (streettLawful cs hcs)
      C.toList (streettOps cs).initAux streettInitAux_wf
  obtain ⟨hsub, x, hx, hxP⟩ := hwf.pending P hP
  have htouched : ∀ s, (s ∈ (streettRun cs (sccSuccs succs C) edgeMarks C.toList).2.live ∨
      s ∈ (streettRun cs (sccSuccs succs C) edgeMarks C.toList).2.dead) → s ∈ C := by
    intro s hs
    rcases genericDFS_touched_reachable (streettOps cs) (sccSuccs succs C) edgeMarks
      (streettLawful cs hcs) C.toList (streettOps cs).initAux streettInitAux_wf s
      (streettGetStatus_ne_unknown hwf.live hs) with h | h
    · exact absurd (streettInitAux_unknown cs s) h
    · exact mem_of_reachable_sccSuccs h
  exact hashSet_size_lt (fun s hs => htouched s (hsub s hs)) (htouched x hx) hxP

/-- Every candidate a search queues holds only states the search reached. -/
theorem streettRun_pending_reachable (cs : CompiledSpec State L) (hcs : cs.WF) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) :
    ∀ P ∈ (streettRun cs succs edgeMarks initialStates).2.pending, ∀ s ∈ P, Reachable initialStates succs s := by
  intro P hP s hs
  have hwf : StreettWF (streettRun cs succs edgeMarks initialStates).2 :=
    genericDFS_wellFormed (streettOps cs) succs edgeMarks (streettLawful cs hcs) initialStates
      (streettOps cs).initAux streettInitAux_wf
  rcases genericDFS_touched_reachable (streettOps cs) succs edgeMarks (streettLawful cs hcs) initialStates
    (streettOps cs).initAux streettInitAux_wf s (streettGetStatus_ne_unknown hwf.live ((hwf.pending P hP).1 s hs))
    with h | h
  · exact absurd (streettInitAux_unknown cs s) h
  · exact h

/-- The prune terminates: `pruneLoop` is defined on every queue. -/
theorem pruneLoop_defined (cs : CompiledSpec State L) (hcs : cs.WF) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (e : Nat) (q : List (Std.HashSet State)) :
    pruneLoop cs succs edgeMarks e q ≠ none :=
  pruneLoop_ne_none cs succs edgeMarks
    (fun C P hP => streettRun_pending_size_lt cs hcs succs edgeMarks C P hP) e q

/-- The accepted SCC as a set. -/
private def witnessSet (wit : Array State) : Std.HashSet State :=
  wit.foldl (init := Std.HashSet.emptyWithCapacity wit.size) fun h s => h.insert s

/-- The selected options' marks in order. -/
private def witnessExtra (cs : CompiledSpec State L) (wopts : Array Nat) : Array (L → Bool) :=
  wopts.foldl (init := #[]) fun a o => a ++ cs.optMarks[o]!

/-- The graph's own marks on an edge, plus mark `numMarks + j` whenever `extra[j]` holds at the edge's source. -/
private def witnessMarks (cs : CompiledSpec State L) (edgeMarks : State → State → Std.HashSet Nat)
    (extra : Array (L → Bool)) (s t : State) : Std.HashSet Nat :=
  let lab := cs.label s
  (Array.range extra.size).foldl (init := edgeMarks s t) fun h j =>
    if extra[j]! lab then h.insert (cs.numMarks + j) else h

/-- Rebuild the cycle through `anchor` inside the accepted SCC, as `checkWithWitness` does, but against the selected
options' marks as well as the property's, since a stitched cycle need not meet every state of the SCC. -/
private def witnessCycle (cs : CompiledSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (wit : Array State) (wopts : Array Nat)
    (anchor : State) : List State :=
  let scc := witnessSet wit
  let sccSuccsMap : Std.HashMap State (Array State) :=
    wit.foldl (init := ∅) fun m s => m.insert s ((succs s).filter scc.contains)
  let sccSuccs' : State → Array State := fun s =>
    match sccSuccsMap[s]? with
    | some a => a
    -- never taken, and agrees with `sccSuccs`
    | none => (succs s).filter scc.contains
  let extra := witnessExtra cs wopts
  stitchCycleAt scc sccSuccs' (witnessMarks cs edgeMarks extra) (cs.numMarks + extra.size) anchor

/-- The reported answer, with the witness checked rather than trusted. A failed check degrades to `.empty`. -/
private def buildResult (cs : CompiledSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (wit : Array State) (wopts : Array Nat)
    (anchor : State) (stem : List State) (explored : Nat) : EmptinessResult State :=
  match witnessCycle cs succs edgeMarks wit wopts anchor with
  | [] => .empty explored
  | cycle =>
    if validLasso succs edgeMarks cs.numMarks initialStates stem cycle && cs.spec.fairCycle cycle then
      .nonEmpty stem (anchor :: cycle)
    else .empty explored

/-- Does the product hold a fair accepting cycle? One search over the whole graph, then the prune's own queue. A
witness a pruned search finds gets its stem by BFS over the first search's `dead`, the reachable set. -/
def streettCheck (cs : CompiledSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) :
    EmptinessResult State :=
  match streettRun cs succs edgeMarks initialStates with
  | (some (anchor, stem), aux) =>
    buildResult cs succs edgeMarks initialStates aux.witness aux.witnessOpts anchor stem
      (aux.live.size + aux.dead.size)
  | (none, aux) =>
    match pruneLoop cs succs edgeMarks (aux.live.size + aux.dead.size) aux.pending.toList with
    | some (some (anchor, wit, wopts), n) =>
      buildResult cs succs edgeMarks initialStates wit wopts anchor
        ((bfsFindPath aux.dead succs initialStates (· == anchor)).getD [anchor]) n
    | some (none, n) => .empty n
    | none => .empty (aux.live.size + aux.dead.size)

/-! ## The contract

The two obligations, stated against `FairSCC` since the prune decides the fair condition as well as the generalized
Büchi one. -/

/-- Anything `buildResult` reports has passed both checks on the stem it was handed. -/
private theorem buildResult_valid (cs : CompiledSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (wit : Array State) (wopts : Array Nat) (anchor : State) (stem : List State) (explored : Nat)
    {s l : List State}
    (h : buildResult cs succs edgeMarks initialStates wit wopts anchor stem explored = .nonEmpty s l) :
    s = stem ∧ validLasso succs edgeMarks cs.numMarks initialStates stem l.tail = true ∧
      cs.spec.fairCycle l.tail = true := by
  rw [buildResult] at h
  split at h
  · exact absurd h (by simp)
  · next cyc hcyc =>
    split at h
    · next hvalid =>
      simp only [EmptinessResult.nonEmpty.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [Bool.and_eq_true] at hvalid
      exact ⟨rfl, by simpa using hvalid.1, by simpa using hvalid.2⟩
    · exact absurd h (by simp)

/-- Soundness: a reported stem and cycle form a `TAcceptingCycle` whose states carry every conjunct. -/
theorem streettCheck_nonEmpty_valid (cs : CompiledSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    {stem loop : List State}
    (h : streettCheck cs succs edgeMarks initialStates = .nonEmpty stem loop) :
    ∃ ac : TAcceptingCycle initialStates succs edgeMarks cs.numMarks, ac.stem = stem ∧
      ac.cycle = loop.tail ∧ cs.spec.fairCycle loop.tail = true := by
  have hvalid : validLasso succs edgeMarks cs.numMarks initialStates stem loop.tail = true ∧
      cs.spec.fairCycle loop.tail = true := by
    rw [streettCheck] at h
    split at h
    · obtain ⟨rfl, hv⟩ := buildResult_valid _ _ _ _ _ _ _ _ _ h
      exact hv
    · split at h
      · obtain ⟨rfl, hv⟩ := buildResult_valid _ _ _ _ _ _ _ _ _ h
        exact hv
      · exact absurd h (by simp)
      · exact absurd h (by simp)
  exact ⟨TAcceptingCycle.ofValid hvalid.1, by simp, by simp, hvalid.2⟩

/-- At a closing POP a full accumulator means the flushed set covers every property mark. -/
theorem streett_acceptingMarks_of_full (cs : CompiledSpec State L) {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State} {aux : (streettOps cs).Aux}
    {step : DFSStep State (streettOps cs).Position} {gray : List (GrayFrame State)}
    (hclose : (streettView cs).closes aux step = true)
    (hwf : SearchWF (streettOps cs) (streettView cs) succs edgeMarks initialStates aux
      (⟨step.state, (streettView cs).posNat step.pos, step.idx, step.acc⟩ :: gray))
    (hfull : (streettView cs).accAt aux 0 = fullAccMask cs.numMarks) :
    AcceptingMarks succs edgeMarks cs.numMarks
      (flushedSet ((streettView cs).live aux) ((streettView cs).posNat step.pos)) := by
  have hll0 : (streettView cs).lowlinkAt aux 0 = (streettView cs).posNat step.pos :=
    revGetD_zero (by rw [LowlinkView.closes] at hclose; exact beq_iff_eq.mp hclose)
  -- every bit of the full accumulator sits on an internal edge of the flushed set
  have hbit : ∀ b, b ≤ cs.numMarks →
      ∃ u ∈ flushedSet ((streettView cs).live aux) ((streettView cs).posNat step.pos),
      ∃ v ∈ flushedSet ((streettView cs).live aux) ((streettView cs).posNat step.pos), v ∈ succs u ∧
        ((1 <<< cs.numMarks).testBit b = true ∨ b ∈ edgeMarks u v) := by
    intro b hb
    have htb : ((streettView cs).accAt aux 0).testBit b = true := by
      rw [hfull, fullAccMask, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_sub_one]
      simpa using Nat.lt_succ_of_le hb
    obtain ⟨u, v, pu, pv, he, hu, hv, hlo, ⟨l, hl, hlb⟩, -, hmk⟩ := hwf.acc_sound 0 (by simp) b htb
    obtain rfl : l = 0 := by omega
    rw [hll0] at hlb
    obtain ⟨hpu, hpu'⟩ := hwf.liveWF.bwd u pu hu
    obtain ⟨hpv, hpv'⟩ := hwf.liveWF.bwd v pv hv
    rw [getElem!_pos ((streettView cs).live aux) pu hpu] at hpu'
    rw [getElem!_pos ((streettView cs).live aux) pv hpv] at hpv'
    exact ⟨u, (mem_flushedSet _ _ u).mpr ⟨pu, hpu, hlo, hpu'⟩,
      v, (mem_flushedSet _ _ v).mpr ⟨pv, hpv, hlb, hpv'⟩, he.mem, hmk⟩
  refine ⟨?_, fun m hm => ?_⟩
  · obtain ⟨u, hu, v, hv, he, -⟩ := hbit cs.numMarks le_rfl
    exact ⟨u, hu, v, hv, he⟩
  · obtain ⟨u, hu, v, hv, he, hmk⟩ := hbit m hm.le
    refine ⟨u, hu, v, hv, he, hmk.resolve_left ?_⟩
    simp only [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, decide_eq_true_eq]
    omega

/-- At a closing POP a flushed set covering every property mark leaves the accumulator full, the graph's own marks
being below `numMarks`. -/
theorem streett_full_of_acceptingMarks (cs : CompiledSpec State L) {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State} {aux : (streettOps cs).Aux}
    {step : DFSStep State (streettOps cs).Position} {gray : List (GrayFrame State)}
    (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < cs.numMarks)
    (hsucc : step.succ = succs step.state) (hidx : ¬ step.idx < step.succ.size)
    (hwf : SearchWF (streettOps cs) (streettView cs) succs edgeMarks initialStates aux
      (⟨step.state, (streettView cs).posNat step.pos, step.idx, step.acc⟩ :: gray))
    (hA : AcceptingMarks succs edgeMarks cs.numMarks
      (flushedSet ((streettView cs).live aux) ((streettView cs).posNat step.pos))) :
    (streettView cs).accAt aux 0 = fullAccMask cs.numMarks := by
  have hcomp := hwf.close_acc_complete hsucc hidx
  apply Nat.eq_of_testBit_eq
  intro b
  rw [fullAccMask, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_sub_one]
  rcases Nat.lt_trichotomy b cs.numMarks with hb | rfl | hb
  -- a property mark, carried by an internal edge
  · obtain ⟨u, hu, v, hv, he, hm⟩ := hA.2 b hb
    rw [hcomp u hu v hv he b (Or.inr hm)]
    exact (decide_eq_true (by omega)).symm
  -- the internal-edge bit
  · obtain ⟨u, hu, v, hv, he⟩ := hA.1
    rw [hcomp u hu v hv he _ (Or.inl (by simp [streettView, Nat.shiftLeft_eq]))]
    exact (decide_eq_true (by omega)).symm
  -- nothing above it, since every bit comes from an edge mark or the internal-edge bit
  · have hfalse : ((streettView cs).accAt aux 0).testBit b = false := by
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      obtain ⟨u, v, -, -, -, -, -, -, -, -, hmk⟩ := hwf.acc_sound 0 (by simp) b hc
      rcases hmk with hx | hx
      · simp [streettView, Nat.shiftLeft_eq, Nat.testBit_two_pow] at hx
        omega
      · have := hmarksBound u v b hx
        omega
    rw [hfalse]
    exact (decide_eq_false (by omega)).symm

/-- Every recorded option is available on `B`, and every conjunct has one of them among its own options. -/
def OptionsCover (cs : CompiledSpec State L) (B : Std.HashSet State) (wopts : Array Nat) : Prop :=
  (∀ o ∈ wopts, (∀ s ∈ B, cs.regions[o]! (cs.label s) = true) ∧ ∀ g ∈ cs.optMarks[o]!, ∃ s ∈ B, g (cs.label s) = true) ∧
  ∀ i < cs.spec.conjuncts.size, ∃ o ∈ wopts, cs.conjunctStart[i]! ≤ o ∧ o < cs.conjunctStart[i + 1]!

/-- A counterexample the search reports lies in an internally connected SCC covering every property mark, reached
by the reported stem, and the options recorded beside it cover every conjunct on that SCC. Connectivity and marks are
read off the search invariant at the reporting POP [CCLMT18]. -/
theorem streettRun_found (cs : CompiledSpec State L) (hcs : cs.WF) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (fr : FiniteReach initialStates succs) {anchor : State} {stem : List State}
    (hfound : (streettRun cs succs edgeMarks initialStates).1 = some (anchor, stem)) :
    InternallyConnected succs (streettSccHint (streettRun cs succs edgeMarks initialStates).2) ∧
    AcceptingMarks succs edgeMarks cs.numMarks (streettSccHint (streettRun cs succs edgeMarks initialStates).2) ∧
    anchor ∈ streettSccHint (streettRun cs succs edgeMarks initialStates).2 ∧
    (∃ hs : stem ≠ [], stem.head hs ∈ initialStates ∧
      (∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs (stem[i])) ∧ stem.getLast hs = anchor) ∧
    OptionsCover cs (streettSccHint (streettRun cs succs edgeMarks initialStates).2)
      (streettRun cs succs edgeMarks initialStates).2.witnessOpts := by
  unfold streettRun at hfound ⊢
  obtain ⟨-, hout⟩ := genericDFS_searchOutcome (streettOps cs) (streettView cs) (streettLowlinkLawful cs)
    (streettLawful cs hcs) streettInitAux_wf succs edgeMarks initialStates fr
  obtain ⟨aux, step, gray, hwf, hsucc, hanchor, hrep⟩ := hout anchor stem hfound
  rcases hrep with ⟨hidx, hpop⟩ | ⟨d, -, -, hupd⟩
  swap
  -- UPDATE never reports
  · have h1 := congrArg Prod.snd hupd
    have h2 : ((streettOps cs).update aux (edgeMarks step.state d) d).2 = false :=
      streettUpdate_snd cs.numMarks aux _ d
    rw [h2] at h1
    exact absurd h1 (by simp)
  obtain ⟨hback, hwit, hfu, hwo⟩ := streettPop_eq_true hpop
  have hclose : (streettView cs).closes aux step = true := by
    simp [LowlinkView.closes, streettView, Array.back?_map, hback]
  obtain ⟨-, hconn⟩ := hwf.close_flushed hsucc hidx hclose
  set F := flushedSet ((streettView cs).live aux) ((streettView cs).posNat step.pos) with hF
  have hacc0 : (streettView cs).accAt aux 0 = fullAccMask cs.numMarks :=
    revGetD_zero (by simp [streettView, Array.back?_map, hback])
  -- the hint holds exactly the flushed range
  have hmemF : ∀ s, s ∈ F ↔
      s ∈ (streettOps cs).sccHint (genericDFS (streettOps cs) succs edgeMarks initialStates
        (streettOps cs).initAux).2 := by
    intro s
    show s ∈ flushedSet _ _ ↔ s ∈ streettSccHint _
    rw [streettSccHint, hwit, flushedSet]
    exact mem_sccSet.trans mem_sccSet.symm
  have hanchorF : anchor ∈ F := by
    obtain ⟨h1, h2⟩ := hwf.frame_pos ⟨step.state, (streettView cs).posNat step.pos, step.idx, step.acc⟩
      (List.mem_cons_self ..)
    rw [getElem!_pos ((streettView cs).live aux) _ h1] at h2
    exact (mem_flushedSet _ _ anchor).mpr ⟨_, h1, le_refl _, h2.trans hanchor⟩
  have hAF := streett_acceptingMarks_of_full cs hclose hwf hacc0
  -- the recorded options are the ones the scan selected on the flushed range
  have hB : ∀ s, s ∈ (streettOps cs).sccHint (genericDFS (streettOps cs) succs edgeMarks initialStates
      (streettOps cs).initAux).2 ↔ s ∈ aux.live.toList.drop step.pos := by
    intro s
    show s ∈ streettSccHint _ ↔ _
    rw [streettSccHint, hwit]
    exact mem_sccSet
  have hopts : OptionsCover cs (streettSccHint (genericDFS (streettOps cs) succs edgeMarks initialStates
      (streettOps cs).initAux).2) (genericDFS (streettOps cs) succs edgeMarks initialStates
      (streettOps cs).initAux).2.witnessOpts := by
    refine ⟨fun o ho => ?_, fun i hi => ?_⟩
    · rw [hwo] at ho
      have hav := selectedOptions_available cs _ _ o ho
      have hlt : o < cs.numOptions := by
        simp only [optionAvailable, Bool.and_eq_true] at hav
        exact scanOptions_fst_lt cs aux.live step.pos o hav.1
      obtain ⟨hreg, hmk⟩ := (optionAvailable_iff cs hcs aux.live step.pos o hlt).mp hav
      refine ⟨fun s hs => hreg s ((hB s).mp hs), fun g hg => ?_⟩
      obtain ⟨s, hs, hgs⟩ := hmk g hg
      exact ⟨s, (hB s).mpr hs, hgs⟩
    · obtain ⟨o, ho, h1, h2, -⟩ := selectedOptions_covers hcs _ _ hfu i hi
      exact ⟨o, by rw [hwo]; exact ho, h1, h2⟩
  exact ⟨hconn.congr hmemF, hAF.mono (fun s hs => (hmemF s).mp hs), (hmemF anchor).mp hanchorF,
    genericDFS_stem_path (streettOps cs) succs edgeMarks initialStates _ anchor stem hfound, hopts⟩

/-- A counterexample the search reports lies in an internally connected SCC covering every property mark, reached
by the reported stem. -/
theorem streett_sccHintSound (cs : CompiledSpec State L) (hcs : cs.WF) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (fr : FiniteReach initialStates succs) :
    SccHintSound (streettOps cs) succs edgeMarks cs.numMarks initialStates := by
  intro anchor stem hfound
  obtain ⟨h1, h2, h3, h4, -⟩ := streettRun_found cs hcs succs edgeMarks initialStates fr hfound
  exact ⟨h1, h2, h3, h4⟩

omit [LawfulBEq State] [LawfulHashable State] in
private theorem mem_foldl_append {α : Type v} {β : Type v'} (f : α → Array β) (x : β) :
    ∀ (l : List α) (init : Array β), x ∈ l.foldl (fun a o => a ++ f o) init ↔ x ∈ init ∨ ∃ o ∈ l, x ∈ f o := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons a l ih =>
    intro init
    simp only [List.foldl_cons, ih, Array.mem_append, List.mem_cons]
    grind

private theorem mem_foldl_insertIf (p : Nat → Bool) (c m : Nat) :
    ∀ (l : List Nat) (init : Std.HashSet Nat),
      m ∈ l.foldl (fun h j => if p j then h.insert (c + j) else h) init ↔
        m ∈ init ∨ ∃ j ∈ l, p j = true ∧ m = c + j := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons a l ih =>
    intro init
    rw [List.foldl_cons, ih]
    by_cases hp : p a = true
    · simp only [if_pos hp, Std.HashSet.mem_insert, beq_iff_eq, List.mem_cons]
      grind
    · simp only [if_neg hp, List.mem_cons]
      grind

omit [Inhabited State] in
private theorem witnessCycle_eq (cs : CompiledSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (wit : Array State) (wopts : Array Nat) (anchor : State) :
    witnessCycle cs succs edgeMarks wit wopts anchor =
      stitchCycleAt (witnessSet wit) (sccSuccs succs (witnessSet wit))
        (witnessMarks cs edgeMarks (witnessExtra cs wopts)) (cs.numMarks + (witnessExtra cs wopts).size) anchor := by
  have hs : (fun s => match (wit.foldl (init := (∅ : Std.HashMap State (Array State)))
        fun m x => m.insert x ((succs x).filter (witnessSet wit).contains))[s]? with
      | some a => a
      | none => (succs s).filter (witnessSet wit).contains) = sccSuccs succs (witnessSet wit) := by
    funext s
    rcases hm : (wit.foldl (init := (∅ : Std.HashMap State (Array State)))
        fun m x => m.insert x ((succs x).filter (witnessSet wit).contains))[s]? with _ | v
    · rw [hm]; rfl
    · rw [hm]
      rw [← Array.foldl_toList] at hm
      exact foldl_insert_getElem?_eq (fun x => (succs x).filter (witnessSet wit).contains) wit.toList ∅
        (by intro s' v' h'; simp at h') s v hm
  exact congrArg (fun g => stitchCycleAt (witnessSet wit) g (witnessMarks cs edgeMarks (witnessExtra cs wopts))
    (cs.numMarks + (witnessExtra cs wopts).size) anchor) hs

/-- A genuine find never degrades to `.empty`. -/
private theorem buildResult_ne_empty (cs : CompiledSpec State L) (hcs : cs.WF) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < cs.numMarks) {wit : Array State} {wopts : Array Nat}
    {anchor : State} {stem : List State} (explored : Nat)
    (hconn : InternallyConnected succs (witnessSet wit))
    (hA : AcceptingMarks succs edgeMarks cs.numMarks (witnessSet wit)) (hanchor : anchor ∈ witnessSet wit)
    (hstem : ∃ hs : stem ≠ [], stem.head hs ∈ initialStates ∧
      (∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs (stem[i])) ∧ stem.getLast hs = anchor)
    (hopts : OptionsCover cs (witnessSet wit) wopts) {n : Nat} :
    buildResult cs succs edgeMarks initialStates wit wopts anchor stem explored ≠ .empty n := by
  have hmem' : ∀ s t m, m ∈ witnessMarks cs edgeMarks (witnessExtra cs wopts) s t ↔
      m ∈ edgeMarks s t ∨ ∃ j < (witnessExtra cs wopts).size,
        (witnessExtra cs wopts)[j]! (cs.label s) = true ∧ m = cs.numMarks + j := by
    intro s t m
    simp only [witnessMarks]
    rw [← Array.foldl_toList, mem_foldl_insertIf, Array.toList_range]
    simp only [List.mem_range]
  have hextra : ∀ g, g ∈ witnessExtra cs wopts ↔ ∃ o ∈ wopts, g ∈ cs.optMarks[o]! := by
    intro g
    simp only [witnessExtra]
    rw [← Array.foldl_toList, mem_foldl_append]
    simp
  -- the SCC's internal edges cover the extended marks, an option's mark sitting on any edge out of a state it holds at
  have hsucc := hconn.exists_succ hA.1
  have hA' : AcceptingMarks succs (witnessMarks cs edgeMarks (witnessExtra cs wopts))
      (cs.numMarks + (witnessExtra cs wopts).size) (witnessSet wit) := by
    refine ⟨hA.1, fun m hm => ?_⟩
    by_cases hlt : m < cs.numMarks
    · obtain ⟨s, hs, t, ht, hst, hmk⟩ := hA.2 m hlt
      exact ⟨s, hs, t, ht, hst, (hmem' s t m).mpr (Or.inl hmk)⟩
    · have hj : m - cs.numMarks < (witnessExtra cs wopts).size := by omega
      obtain ⟨o, ho, hgo⟩ := (hextra _).mp (Array.getElem_mem hj)
      obtain ⟨s, hs, hgs⟩ := (hopts.1 o ho).2 _ hgo
      obtain ⟨t, ht, hst⟩ := hsucc s hs
      refine ⟨s, hs, t, ht, hst, (hmem' s t m).mpr (Or.inr ⟨m - cs.numMarks, hj, ?_, by omega⟩)⟩
      rwa [getElem!_pos (witnessExtra cs wopts) _ hj]
  obtain ⟨hs, hhead, hchain, hlast⟩ := hstem
  obtain ⟨ac, hacstem, haccycle⟩ := stitchCycleAt_toTAcceptingCycle hconn hA' hanchor hs hhead hchain hlast
  obtain ⟨-, -, hconf, -⟩ := stitchCycleAt_valid (witnessSet wit) (sccSuccs succs (witnessSet wit))
    (witnessMarks cs edgeMarks (witnessExtra cs wopts)) (cs.numMarks + (witnessExtra cs wopts).size) anchor
    hA'.sccSuccs hconn.domainBlocked (Std.HashSet.mem_iff_contains.mp hanchor) ac.cycle haccycle.symm
  have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)
  -- the property's own marks are exactly the extended marks below `numMarks`
  have hvalid : validLasso succs edgeMarks cs.numMarks initialStates stem ac.cycle = true := by
    rw [← hacstem]
    exact validLasso_of_TAcceptingCycle (ac.restrictMarks (Nat.le_add_right _ _) fun s t m hm hin => by
      rcases (hmem' s t m).mp hin with h | ⟨j, -, -, rfl⟩
      · exact h
      · omega)
  have hfair : cs.spec.fairCycle ac.cycle = true := by
    refine fairCycle_of_options fun c hc => ?_
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hc
    obtain ⟨o, ho, hlo, hhi⟩ := hopts.2 i hi
    have hce : cs.spec.conjuncts[i]! = cs.spec.conjuncts[i] := getElem!_pos _ i hi
    have hstep := hcs.start_succ i hi
    have hk : o - cs.conjunctStart[i]! < (cs.spec.conjuncts[i]!).size := by omega
    have hidx : cs.conjunctStart[i]! + (o - cs.conjunctStart[i]!) = o := by omega
    have hk2 : o - cs.conjunctStart[i]! < (cs.spec.conjuncts[i]).size := by rwa [hce] at hk
    have hreg := hcs.option_region i hi _ hk
    have hmk := hcs.option_marks i hi _ hk
    rw [hidx] at hreg hmk
    refine ⟨(cs.spec.conjuncts[i]!)[o - cs.conjunctStart[i]!]!, ?_, fun s hs => ?_, fun g hg => ?_⟩
    · rw [hce, getElem!_pos (cs.spec.conjuncts[i]) _ hk2]
      exact Array.getElem_mem _
    -- the region holds on the whole SCC, which contains the cycle
    · rw [← hreg, ← hcs.label_eq]
      exact (hopts.1 o ho).1 s (Std.HashSet.mem_iff_contains.mpr (hconf s hs))
    -- each mark is an extended mark, carried by a cycle edge whose source it holds at
    · rw [← hmk] at hg
      obtain ⟨p, hp, hpg⟩ := Array.mem_iff_getElem.mp ((hextra g).mpr ⟨o, ho, hg⟩)
      obtain ⟨q, hq, hqm⟩ := ac.cycle_covers_marks (cs.numMarks + p) (by omega)
      rcases (hmem' _ _ _).mp hqm with hin | ⟨j, -, hjt, hjeq⟩
      · exact absurd (hmarksBound _ _ _ hin) (by omega)
      · have hjp : j = p := by omega
        rw [hjp, getElem!_pos (witnessExtra cs wopts) p hp, hpg] at hjt
        exact ⟨_, List.getElem_mem hq, by rw [← hcs.label_eq]; exact hjt⟩
  intro hres
  rw [buildResult, (witnessCycle_eq cs succs edgeMarks wit wopts anchor).trans haccycle.symm] at hres
  revert hne hvalid hfair hres
  generalize ac.cycle = c
  intro hne hvalid hfair hres
  cases c with
  | nil => exact hne rfl
  | cons x xs => simp [hvalid, hfair] at hres

/-- A search that reports nothing blames a conjunct for every maximal SCC covering the property marks, and has queued
the pruned candidate of every option of that conjunct whose marks are present, unless that candidate is empty. -/
theorem streettRun_none_pass (cs : CompiledSpec State L) (hcs : cs.WF) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (fr : FiniteReach initialStates succs) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < cs.numMarks)
    (hnone : (streettRun cs succs edgeMarks initialStates).1 = none) :
    ∃ (sccs : List (Std.HashSet State)) (pick : Std.HashSet State → Array (StreettOption L)),
      SCCEnumerationSound initialStates succs sccs ∧
      (∀ M ∈ sccs, AcceptingMarks succs edgeMarks cs.numMarks M → pick M ∈ cs.spec.conjuncts) ∧
      ∀ M ∈ sccs, AcceptingMarks succs edgeMarks cs.numMarks M → ∀ opt ∈ pick M,
        opt.marksPresent cs.spec.label M → (∀ s, s ∉ opt.prune cs.spec.label M) ∨
          ∃ P ∈ (streettRun cs succs edgeMarks initialStates).2.pending,
            ∀ s, s ∈ P ↔ s ∈ opt.prune cs.spec.label M := by
  have hrec := enumRun_recordedAt (streettOps cs) (streettView cs) (streettLowlinkLawful cs)
    (streettLawful cs hcs) streettInitAux_wf (streettMonotone cs) succs edgeMarks initialStates fr hnone
  have hblame : ∀ M, ∃ c : Array (StreettOption L),
      M ∈ enumSCCs (streettOps cs) (streettView cs) succs edgeMarks initialStates →
      AcceptingMarks succs edgeMarks cs.numMarks M → c ∈ cs.spec.conjuncts ∧ ∀ opt ∈ c,
        opt.marksPresent cs.spec.label M → (∀ s, s ∉ opt.prune cs.spec.label M) ∨
          ∃ P ∈ (streettRun cs succs edgeMarks initialStates).2.pending,
            ∀ s, s ∈ P ↔ s ∈ opt.prune cs.spec.label M := by
    intro M
    by_cases hM : M ∈ enumSCCs (streettOps cs) (streettView cs) succs edgeMarks initialStates ∧
      AcceptingMarks succs edgeMarks cs.numMarks M
    swap
    · exact ⟨#[], fun h1 h2 => absurd ⟨h1, h2⟩ hM⟩
    obtain ⟨hMmem, hA⟩ := hM
    simp only [enumSCCs, List.mem_map] at hMmem
    obtain ⟨p, hp, rfl⟩ := hMmem
    obtain ⟨step, gray, hwf, hsucc, hidx, hcl, hflush, hpop, hR⟩ := hrec p (by simpa using hp)
    rw [hflush] at hA
    -- the SCC covers the property marks, so its POP took the scan branch, and not reporting means it blamed
    have hfull := streett_full_of_acceptingMarks cs hmarksBound hsucc hidx hwf hA
    have hpop' : streettPop cs p.2 step = ((streettPop cs p.2 step).1, false) := Prod.ext rfl hpop
    obtain ⟨opts, hfu, hq⟩ := streettPop_queues hcl hfull hpop'
    have hB : ∀ s, s ∈ p.1 ↔ s ∈ ((streettView cs).live p.2).toList.drop step.pos := by
      intro s
      rw [hflush, flushedSet]
      exact mem_sccSet
    obtain ⟨c, hc, -, hcover⟩ := firstUnsatisfied_some_blames hcs _ _ hB hfu
    refine ⟨c, fun _ _ => ⟨hc, fun opt hopt hpres => ?_⟩⟩
    obtain ⟨o, ho, hreg, -⟩ := hcover opt hopt hpres
    -- the queued candidate is the option's prune of the SCC
    have hto : ∀ s, s ∈ opt.prune cs.spec.label p.1 →
        s ∈ regionSubset cs (streettView cs |>.live p.2) step.pos cs.regions[o]! := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := StreettOption.mem_prune.mp hs
      exact mem_regionSubset.mpr ⟨(hB s).mp hs1, by rw [hreg, hcs.label_eq]; exact hs2⟩
    rcases hq o ho with hempty | hin
    · refine Or.inl fun s hs => ?_
      rw [Std.HashSet.isEmpty_iff_forall_not_mem] at hempty
      exact hempty s (hto s hs)
    · refine Or.inr ⟨_, hR _ hin, fun s => ⟨fun hs => ?_, hto s⟩⟩
      obtain ⟨hs1, hs2⟩ := mem_regionSubset.mp hs
      exact StreettOption.mem_prune.mpr ⟨(hB s).mpr hs1, by rw [← hcs.label_eq, ← hreg]; exact hs2⟩
  choose pick hpick using hblame
  exact ⟨enumSCCs (streettOps cs) (streettView cs) succs edgeMarks initialStates, pick,
    streettSCCs_sound cs hcs succs edgeMarks initialStates fr,
    fun M hM hA => (hpick M hM hA).1, fun M hM hA => (hpick M hM hA).2⟩

omit [Inhabited State] [LawfulHashable State] in
private theorem finiteReach_sccSuccs (succs : State → Array State) (C : Std.HashSet State) :
    FiniteReach C.toList (sccSuccs succs C) :=
  (List.finite_toSet C.toList).subset fun _ hs => Std.HashSet.mem_toList.mpr (mem_of_reachable_sccSuccs hs)

/-- A queue the prune drains without a report holds only refuted candidates. -/
theorem pruneLoop_none_refuted (cs : CompiledSpec State L) (hcs : cs.WF) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < cs.numMarks) :
    ∀ e q r, pruneLoop cs succs edgeMarks e q = some r → r.1 = none →
      ∀ C ∈ q, Refuted cs.spec succs edgeMarks C := by
  refine pruneLoop.partial_correctness cs succs edgeMarks
    (fun _ q r => r.1 = none → ∀ C ∈ q, Refuted cs.spec succs edgeMarks C) ?_
  intro f ih e q r hr hnone
  cases q with
  | nil => intro C hC; simp at hC
  | cons C rest =>
    cases hrun : (streettRun cs (sccSuccs succs C) edgeMarks C.toList).1 with
    | some x =>
      simp [hrun] at hr
      rw [← hr] at hnone
      simp at hnone
    | none =>
      simp [hrun] at hr
      have hall := ih _ _ r hr hnone
      have hpend : ∀ P ∈ (streettRun cs (sccSuccs succs C) edgeMarks C.toList).2.pending,
          Refuted cs.spec succs edgeMarks P :=
        fun P hP => hall P (List.mem_append_left _ (by simpa using hP))
      intro D hD
      rcases List.mem_cons.mp hD with rfl | hD'
      -- the candidate itself is one pass of the prune, its queued candidates refuted by the rest of the loop
      · obtain ⟨sccs, pick, henum, hpick, hrec⟩ := streettRun_none_pass cs hcs (sccSuccs succs D) edgeMarks
          D.toList (finiteReach_sccSuccs succs D) hmarksBound hrun
        refine .pass sccs pick henum (fun M hM hA => hpick M hM (by rwa [hcs.numMarks_eq]))
          (fun M hM hA opt hopt hpres => ?_)
        rcases hrec M hM (by rwa [hcs.numMarks_eq]) opt hopt hpres with hempty | ⟨P, hP, hPm⟩
        · exact Refuted.of_empty hempty
        · exact (hpend P hP).congr hPm
      · exact hall D (List.mem_append_right _ hD')

/-- When the whole-graph search reports nothing and the prune drains its queue without a report, the whole graph
is refuted. -/
theorem refutedFrom_of_none (cs : CompiledSpec State L) (hcs : cs.WF) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (fr : FiniteReach initialStates succs) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < cs.numMarks)
    (hnone : (streettRun cs succs edgeMarks initialStates).1 = none) {e : Nat}
    {r : Option (State × Array State × Array Nat) × Nat}
    (hq : pruneLoop cs succs edgeMarks e (streettRun cs succs edgeMarks initialStates).2.pending.toList = some r)
    (hr : r.1 = none) :
    RefutedFrom cs.spec succs edgeMarks initialStates := by
  obtain ⟨sccs, pick, henum, hpick, hrec⟩ :=
    streettRun_none_pass cs hcs succs edgeMarks initialStates fr hmarksBound hnone
  have hpend := pruneLoop_none_refuted cs hcs succs edgeMarks hmarksBound e _ r hq hr
  refine ⟨sccs, pick, henum, fun M hM hA => hpick M hM (by rwa [hcs.numMarks_eq]),
    fun M hM hA opt hopt hpres => ?_⟩
  rcases hrec M hM (by rwa [hcs.numMarks_eq]) opt hopt hpres with hempty | ⟨P, hP, hPm⟩
  · exact Refuted.of_empty hempty
  · exact (hpend P (by simpa using hP)).congr hPm

/-- A search that reports nothing leaves every reachable state dead. -/
theorem streettRun_none_dead (cs : CompiledSpec State L) (hcs : cs.WF) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (fr : FiniteReach initialStates succs) (hnone : (streettRun cs succs edgeMarks initialStates).1 = none) :
    ∀ s, Reachable initialStates succs s → s ∈ (streettRun cs succs edgeMarks initialStates).2.dead := by
  unfold streettRun at hnone ⊢
  intro s hs
  have hwf := (genericDFS_searchOutcome (streettOps cs) (streettView cs) (streettLowlinkLawful cs)
    (streettLawful cs hcs) streettInitAux_wf succs edgeMarks initialStates fr).1 hnone
  have hexpl := genericDFS_returns_none_fully_explored (streettOps cs) succs edgeMarks (streettLawful cs hcs)
    (Reachable initialStates succs)
    (fun aux q hq hw hu => dfsGo_ne_none (streettOps cs) succs edgeMarks initialStates fr
      (streettLawful cs hcs) _ _ ((streettLawful cs hcs).wf_push aux q _ hu hw)
      (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; rfl)
      (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; exact hq))
    initialStates (fun q hq => Reachable.base hq)
    (genericDFSGo_ne_none (streettOps cs) succs edgeMarks initialStates _)
    streettInitAux_wf (streettInitAux_unknown cs) hnone s hs
  set fin := (genericDFS (streettOps cs) succs edgeMarks initialStates (streettOps cs).initAux).2 with hfin
  -- no frame is open, so nothing is live
  have hlive : ((streettView cs).live fin).size = 0 := by
    by_contra hne
    obtain ⟨st, hst, -⟩ := hwf.live_reaches_gray 0 (by omega)
    exact absurd hst (by simp)
  have hst : liveStatusOf fin.liveIndex fin.dead s ≠ .unknown := hexpl
  rw [liveStatusOf] at hst
  have hnl : fin.liveIndex.contains s = false := by
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    obtain ⟨p, hp⟩ : ∃ p, fin.liveIndex[s]? = some p := by
      rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
      exact Option.isSome_iff_exists.mp hc
    have := (hwf.liveWF.bwd s p hp).1
    omega
  simp only [hnl, Bool.false_eq_true, if_false] at hst
  by_cases hd : fin.dead.contains s = true
  · exact Std.HashSet.mem_iff_contains.mpr hd
  · simp [hd] at hst

/-- A witness the prune reports comes from the run on one candidate, and that candidate lies in `Q` whenever every
queued candidate does. -/
theorem pruneLoop_found (cs : CompiledSpec State L) (hcs : cs.WF) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (Q : State → Prop) :
    ∀ e q r, pruneLoop cs succs edgeMarks e q = some r → (∀ C ∈ q, ∀ s ∈ C, Q s) →
      ∀ anchor wit wopts, r.1 = some (anchor, wit, wopts) →
        ∃ C : Std.HashSet State, (∀ s ∈ C, Q s) ∧ ∃ stem,
          (streettRun cs (sccSuccs succs C) edgeMarks C.toList).1 = some (anchor, stem) ∧
          (streettRun cs (sccSuccs succs C) edgeMarks C.toList).2.witness = wit ∧
          (streettRun cs (sccSuccs succs C) edgeMarks C.toList).2.witnessOpts = wopts := by
  refine pruneLoop.partial_correctness cs succs edgeMarks
    (fun _ q r => (∀ C ∈ q, ∀ s ∈ C, Q s) → ∀ anchor wit wopts, r.1 = some (anchor, wit, wopts) →
      ∃ C : Std.HashSet State, (∀ s ∈ C, Q s) ∧ ∃ stem,
        (streettRun cs (sccSuccs succs C) edgeMarks C.toList).1 = some (anchor, stem) ∧
        (streettRun cs (sccSuccs succs C) edgeMarks C.toList).2.witness = wit ∧
        (streettRun cs (sccSuccs succs C) edgeMarks C.toList).2.witnessOpts = wopts) ?_
  intro f ih e q r hr hQ anchor wit wopts hfound
  cases q with
  | nil =>
    simp at hr
    subst hr
    simp at hfound
  | cons C rest =>
    cases hrun : (streettRun cs (sccSuccs succs C) edgeMarks C.toList).1 with
    | some x =>
      obtain ⟨a, st⟩ := x
      simp [hrun] at hr
      subst hr
      simp at hfound
      obtain ⟨rfl, rfl, rfl⟩ := hfound
      exact ⟨C, hQ C (by simp), st, hrun, rfl, rfl⟩
    | none =>
      simp [hrun] at hr
      refine ih _ _ r hr (fun D hD s hs => ?_) anchor wit wopts hfound
      rcases List.mem_append.mp hD with hD | hD
      -- a candidate queued by this run lies inside the candidate it ran on
      · exact hQ C (by simp) s (mem_of_reachable_sccSuccs
          (streettRun_pending_reachable cs hcs (sccSuccs succs C) edgeMarks C.toList D (by simpa using hD) s hs))
      · exact hQ D (by simp [hD]) s hs

/-- An `.empty` answer means the search refuted the whole graph in the sense of `RefutedFrom`. -/
theorem streettCheck_empty_refutes (spec : StreettSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < spec.numMarks)
    (fr : FiniteReach initialStates succs) {n : Nat}
    (h : streettCheck (CompiledSpec.of spec) succs edgeMarks initialStates = .empty n) :
    RefutedFrom spec succs edgeMarks initialStates := by
  have hcs := CompiledSpec.of_wf spec
  have hbound : ∀ s t, ∀ m ∈ edgeMarks s t, m < (CompiledSpec.of spec).numMarks := hmarksBound
  rcases hrun : streettRun (CompiledSpec.of spec) succs edgeMarks initialStates with
    ⟨_ | ⟨anchor, stem⟩, aux⟩
  · rcases hq : pruneLoop (CompiledSpec.of spec) succs edgeMarks (aux.live.size + aux.dead.size)
        aux.pending.toList with _ | ⟨_ | ⟨anchor, wit, wopts⟩, n'⟩
    · exact absurd hq (pruneLoop_defined _ hcs succs edgeMarks _ _)
    · exact refutedFrom_of_none (CompiledSpec.of spec) hcs succs edgeMarks initialStates fr hbound
        (by rw [hrun]) (e := aux.live.size + aux.dead.size) (r := (none, n')) (by rw [hrun]; exact hq) rfl
    -- a genuine find in a pruned candidate never degrades to `.empty`
    · exfalso
      have hdead : ∀ s, Reachable initialStates succs s → s ∈ aux.dead := by
        have := streettRun_none_dead _ hcs succs edgeMarks initialStates fr (by rw [hrun])
        rwa [hrun] at this
      have hpend : ∀ P ∈ aux.pending, ∀ s ∈ P, Reachable initialStates succs s := by
        have := streettRun_pending_reachable _ hcs succs edgeMarks initialStates
        rwa [hrun] at this
      -- the find comes from the run on one candidate, and every candidate is reachable
      obtain ⟨C, hCreach, stem', hfound, hwit, hwopts⟩ := pruneLoop_found _ hcs succs edgeMarks
        (Reachable initialStates succs) _ _ _ hq (fun P hP s hs => hpend P (by simpa using hP) s hs)
        anchor wit wopts rfl
      obtain ⟨hconn, hA, hanchor, hstem', hopts⟩ :=
        streettRun_found _ hcs (sccSuccs succs C) edgeMarks C.toList (finiteReach_sccSuccs succs C) hfound
      rw [streettSccHint, hwit] at hconn hA hanchor
      rw [streettSccHint, hwit, hwopts] at hopts
      -- the anchor ends the candidate run's own stem, so it lies in the candidate
      have hanchorC : anchor ∈ C := by
        obtain ⟨hs, hhead, hchain, hlast⟩ := hstem'
        have hheadC : stem'.head hs ∈ C := by simpa using hhead
        rcases chain_reaches stem' hchain hs with heq | hp
        · rw [← hlast, ← heq]
          exact hheadC
        · rw [← hlast]
          exact hp.closed (P := (· ∈ C)) hheadC
            fun _ _ y hy => Std.HashSet.mem_iff_contains.mpr (Array.mem_filter.mp hy).2
      have hg : ∀ a b, b ∈ sccSuccs succs C a → b ∈ succs a := fun _ _ hb => (Array.mem_filter.mp hb).1
      -- the BFS over the first run's dead states finds a stem to it
      obtain ⟨path, hpath, hstem⟩ := bfsFindPath_stem hdead (hCreach anchor hanchorC)
      rw [streettCheck, hrun] at h
      simp only [hq, hpath, Option.getD_some] at h
      exact buildResult_ne_empty _ hcs succs edgeMarks initialStates hbound _ (hconn.mono_graph hg)
        (hA.mono_graph hg) hanchor hstem hopts h
  -- a genuine find on the whole graph never degrades to `.empty`
  · exfalso
    have hfound : (streettRun (CompiledSpec.of spec) succs edgeMarks initialStates).1 = some (anchor, stem) := by
      rw [hrun]
    obtain ⟨hconn, hA, hanchor, hstem, hopts⟩ := streettRun_found _ hcs succs edgeMarks initialStates fr hfound
    rw [hrun] at hconn hA hanchor hopts
    rw [streettCheck, hrun] at h
    exact buildResult_ne_empty _ hcs succs edgeMarks initialStates hbound _ hconn hA hanchor hstem hopts h

/-- Completeness: an `.empty` answer rules out every fair accepting SCC. -/
theorem streettCheck_empty_no_fairSCC (spec : StreettSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < spec.numMarks)
    (fr : FiniteReach initialStates succs) {n : Nat}
    (h : streettCheck (CompiledSpec.of spec) succs edgeMarks initialStates = .empty n)
    (A : FairSCC initialStates succs edgeMarks spec) : False :=
  (streettCheck_empty_refutes spec succs edgeMarks initialStates hmarksBound fr h).no_fairSCC A

end LTLLib
