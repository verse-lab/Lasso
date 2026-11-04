module

/-
  The recursive fairness check of [SLDP09], run on the SCCs a Tarjan search closes, one search plus a prune instead of the
  `2ⁿ` crossing of `Fairness/FairRouter.lean`.

  A hoisted conjunct is a list of options, an option being a region `FG l` and marks `GF g`, and an SCC satisfies the
  assumption when every conjunct has an option available in it ([LSFZ16, Definition 3] per conjunct). A maximal SCC that
  fails can still contain a passing sub-SCC, so a failing conjunct with options that fail only on their regions sends the
  SCC back through the same search with that option's region conjoined, which is [EL87]'s prune. Only the first failing
  conjunct branches, since any fair subgraph satisfies it through one of its options, and it branches only once on any
path: once an option of it is conjoined, a fair subgraph satisfying it through another option lies in that option's
sibling branch.

  ```
  check(r, B):                                  -- B a maximal SCC of the r-restricted subgraph
    if B covers the property marks and every conjunct has an available option:  report B
    if B misses a property mark:  discard B     -- marks are monotone downward
    let i be the first conjunct with no available option
    if an option of i is already conjoined into r then discard B   -- its marks are missing in B
    live := its options whose marks are all witnessed in B
    if live = ∅ then discard B                  -- no subgraph can satisfy conjunct i either
    for each option opt in live:  check(r ∧ opt.region, B)
  ```

  **The regions restrict steps, not states** (`EdgeLabels.md` §6.5). A product pair can have several parallel
  realizations reading different letters, so "is this edge in-region?" and "does this edge carry the mark?" have to be
  answered on *one* realization; a single label per state, or per endpoint pair, cannot do that. The spec therefore
  exposes a region-indexed graph and marks (`RStreettSpec`), the scan walks the closing SCC's internal *edges*, and a
  prune step narrows the region rather than deleting states — an edge prune need not remove any state, which is why a
  candidate carries the conjoined options as a bitmask and the loop decreases on that.

  Defines:
  - `CompiledSpec`: `RStreettSpec` flattened once, so the scan indexes options and marks by position; it keeps both the
    options' *letter* regions and their *edge* readings, the latter derived from the former by `map`
  - `CompiledSpec.WF`: what the flattening guarantees
  - `Candidate`, `Candidate.region`/`graph`/`expand`/`measure`: a pruned candidate and what it induces
  - `internalEdges`, `scanLetters`, `scanFrame`, `firstUnsatisfied`: the per-SCC test, run on edges
  - `StreettAux`, `streettPush`/`streettUpdate`/`streettPop`, `streettOps`: the refinement of `GenericDFS`
  - `cycleEdges`, `CompiledSpec.fairCycleOpts`: the report-time validator, read on the reported cycle's
    edges inside the reporting candidate's own region
  - `pruneLoop`, `streettCheck`: the outer loop and the entry point

  Proves:
  - `optionAvailable_iff_availableIn`: the edge scan decides `RStreettSpec.AvailableWith`'s per-option condition
  - `firstUnsatisfied_none_accepting`, `firstUnsatisfied_some_blames`: the per-conjunct test decides availability on the
    flushed SCC, and names a conjunct with every option of it whose marks are witnessed, or with a committed option
    whose marks are not
  - `blamed_bit_new`: a blamed option's bit was not already conjoined, so skipping such options loses nothing
  - `Candidate.measure_lt`, `pruneLoop_defined`: the prune terminates, on the bitmask deficit alone
  - `streettCheck_nonEmpty_valid`: a reported stem and cycle is an accepting cycle whose *edges* satisfy every conjunct
  - `streettRun_found`: a reported counterexample lies in an internally connected SCC covering every property mark,
    reached by the reported stem, and the options recorded beside it cover every conjunct
  - `streettRun_none_pass`, `pruneLoop_none_refuted`: a search that reports nothing blames a conjunct for every maximal
    SCC covering the property marks and, unless it is committed to an option of that conjunct, queues its pruned candidates,
    and a queue drained without a report is refuted
  - `streettCheck_empty_refutes`: an `.empty` answer refutes the whole graph in the sense of `RRefutedFrom`
  - `streettCheck_empty_no_fairSCC`: an `.empty` answer rules out every `RFairSCC`, on [SLDP09]'s recursion proved in
    `AbstractSpec/StreettPruneSpec.lean`

  References:
  - [SLDP09] Sun, Liu, Dong, Pang. PAT: Towards Flexible Verification under Fairness. CAV 2009.
  - [LSFZ16] Li, Song, Feng, Zhang. Verify LTL with Fairness Assumptions Efficiently. arXiv:1606.08116, 2016.
  - [EL87] Emerson, Lei. Modalities for model checking: branching time logic strikes back. Sci. Comput. Program.
    8(3), 1987.
  - [RDKP13] Renault, Duret-Lutz, Kordon, Poitrenaud. Three SCC-based Emptiness Checks for GBA. LPAR-19, 2013.
  - [CCLMT18] Chen, Cohen, Lévy, Merz, Théry. Formal Proofs of Tarjan's Algorithm in Why3, Coq, and Isabelle.
    arXiv:1810.11979, 2018.

  Sections:
  - The compiled spec
  - Candidates
  - The search state
  - The per-SCC test
  - What the scan decides
  - The SCC's internal edges
  - What the per-conjunct scan decides
  - What the test decides on the flushed SCC
  - PUSH, UPDATE and POP
  - The `DFSOps` instance
  - The outer loop
  - The contract
-/
public import LTLLib.AbstractSpec.Reachability
public import LTLLib.AbstractSpec.EmptinessCheck
public import LTLLib.AbstractSpec.LassoCheck
public import LTLLib.AbstractSpec.SCCTheory
public import LTLLib.AbstractSpec.StreettPruneSpec
public import LTLLib.AbstractSpec.StreettSCC
public import LTLLib.AbstractSpec.StreettSCCRegion
public import LTLLib.SCC.GenericDFS
public import LTLLib.SCC.LiveStack
public import LTLLib.SCC.SCCEnumeration
public import LTLLib.SCC.WitnessExtraction
meta import Lentil
meta import LTLLib.Tactic.Set

import Batteries.Data.List.Perm

public section

namespace LTLLib

variable {State : Type u} {L : Type w} [BEq State] [Hashable State]

/-! ## The compiled spec

Flattening `StreettSpec` once per check gives every option a position, a mark-bit range and a mask of the bits it needs,
so the scan and the availability test are `Nat` bit operations. -/

/-- `StreettSpec` with option positions, mark-bit ranges and per-option mark masks precomputed. -/
structure CompiledSpec (State : Type u) (L : Type w) where
  numMarks : Nat  -- the property automaton's own marks
  letterOptions : Array (StreettOption L)  -- the options in walk order, at the letter level
  regions : Array ((State × State) → Bool)  -- their edge readings, which is what the scan folds over
  optMarks : Array (Array ((State × State) → Bool))  -- the same options' marks, read on edges
  optMarkBase : Array Nat  -- the first `marksSeen` bit belonging to each option
  optMarkMask : Array Nat  -- all of that option's `marksSeen` bits at once
  conjunctStart : Array Nat  -- conjunct `i` owns options `conjunctStart[i] ..< conjunctStart[i+1]`
  numOptions : Nat
  numOptMarks : Nat
  spec : RStreettSpec State L  -- the specification itself, for the report-time validator
  /-- The candidate's own region: the conjunction of the options already committed to the search this
  spec was compiled for. Every option's edge reading above is taken *inside* it, so the scan's verdict
  is joint with those commitments rather than per-option (`EdgeLabels.md` §6.3, §12). The top-level
  search compiles at `⊤`, where this is a no-op and `onEdgesIn` is `onEdges`. -/
  restrict : L → Bool
  restrictBits : Nat  -- the same region as a bitmask over `letterOptions`, so every report is stated at `atBits` of one

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
          rw [getElem!_pos _ _ (by simp only [Array.size_push, hsize]; omega)]
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

/-- Flatten a spec, numbering options and their marks in walk order. The scan works on the *edge* readings
of the options, but the candidate machinery needs their *letter* regions, so both are kept and the edge
readings are derived from the letter ones by `map` — which is what makes `cs.regions[o]` and
`cs.letterOptions[o]` correspond by `Array.getElem_map` rather than by a flatten/map commutation. -/
@[expose] def CompiledSpec.ofAt (spec : RStreettSpec State L) (restrict : L → Bool) (restrictBits : Nat) :
    CompiledSpec State L :=
  let fs := flattenOpts spec.conjuncts
  let flat : Array (StreettOption L) := fs.1
  let sizes : Array Nat := flat.map (fun opt => ((opt.onEdgesIn spec restrict).marks).size)
  let bases : Array Nat := prefixSums sizes 0 #[0]
  { numMarks := spec.numMarks
    letterOptions := flat
    regions := flat.map (fun opt => (opt.onEdgesIn spec restrict).region)
    optMarks := flat.map (fun opt => (opt.onEdgesIn spec restrict).marks)
    optMarkBase := bases
    optMarkMask := (Array.range flat.size).map fun i => ((1 <<< sizes[i]!) - 1) <<< bases[i]!
    conjunctStart := fs.2
    numOptions := flat.size
    numOptMarks := bases[flat.size]!
    spec := spec
    restrict := restrict
    restrictBits := restrictBits }

/-- The spec the top-level search is compiled at: no option committed, so no restriction. -/
@[expose] def CompiledSpec.of (spec : RStreettSpec State L) : CompiledSpec State L :=
  CompiledSpec.ofAt spec (fun _ => true) 0


omit [Hashable State] in
/-- Projections of a flattened spec that callers need without forcing the flattening itself. `CompiledSpec.of`
is a `let`-heavy definition over `flattenOpts` and `prefixSums`, so leaving these to `whnf` makes any goal
mentioning `(CompiledSpec.of spec).spec` blow up; rewriting with them first keeps it syntactic. -/
@[simp] theorem CompiledSpec.ofAt_spec (spec : RStreettSpec State L) (r : L → Bool) (b : Nat) :
    (CompiledSpec.ofAt spec r b).spec = spec := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.ofAt_numMarks (spec : RStreettSpec State L) (r : L → Bool) (b : Nat) :
    (CompiledSpec.ofAt spec r b).numMarks = spec.numMarks := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.ofAt_restrict (spec : RStreettSpec State L) (r : L → Bool) (b : Nat) :
    (CompiledSpec.ofAt spec r b).restrict = r := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.ofAt_restrictBits (spec : RStreettSpec State L) (r : L → Bool) (b : Nat) :
    (CompiledSpec.ofAt spec r b).restrictBits = b := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.of_spec (spec : RStreettSpec State L) :
    (CompiledSpec.of spec).spec = spec := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.of_numMarks (spec : RStreettSpec State L) :
    (CompiledSpec.of spec).numMarks = spec.numMarks := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.of_restrictBits (spec : RStreettSpec State L) :
    (CompiledSpec.of spec).restrictBits = 0 := rfl

/-! The flattening itself does not see the restriction: `flattenOpts` reads only `spec.conjuncts`, and
the mark-bit layout reads only the *number* of marks an option has, which `onEdgesIn` preserves. So every
index, block base and mask a candidate's compiled spec carries is the one the top-level spec carries, and
a candidate's bitmask means there what it means here. Each is `rfl`. -/

omit [Hashable State] in
@[simp] theorem CompiledSpec.ofAt_letterOptions (spec : RStreettSpec State L) (r : L → Bool) (b : Nat) :
    (CompiledSpec.ofAt spec r b).letterOptions = (flattenOpts spec.conjuncts).1 := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.ofAt_numOptions (spec : RStreettSpec State L) (r : L → Bool) (b : Nat) :
    (CompiledSpec.ofAt spec r b).numOptions = (flattenOpts spec.conjuncts).1.size := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.ofAt_conjunctStart (spec : RStreettSpec State L) (r : L → Bool) (b : Nat) :
    (CompiledSpec.ofAt spec r b).conjunctStart = (flattenOpts spec.conjuncts).2 := rfl

section Wellformed
omit [Hashable State]

/-! ## The region a bitmask denotes

A candidate carries the options conjoined into it as a bitmask; `regionOf` is the letter predicate
those bits denote. It lives here, above `CompiledSpec.WF`, because the well-formedness of a compiled
spec ties its `restrict` predicate to its `restrictBits` (`WF.restrict_eq`), and `Candidate.region`
below is just this at a candidate's own bitmask. -/

/-- The conjunction of the selected options' regions from option `o` on, as a loop. `regionOf` used to be
`(List.range cs.numOptions).all …` under the `fun l`, and Lean eta-expands `regionOf` to its full arity,
so the list was allocated on every call — once per step of every candidate expansion and once per witness
state of every report (`EdgeLabels.md` §13.26). -/
private def regionFrom (cs : CompiledSpec State L) (bits : Nat) (l : L) (o : Nat) : Bool :=
  if h : o < cs.numOptions then
    (!bits.testBit o || (cs.letterOptions[o]!).region l) && regionFrom cs bits l (o + 1)
  else true
termination_by cs.numOptions - o

/-- The letter restriction a candidate carries: the conjunction of its selected options' regions. -/
def regionOf (cs : CompiledSpec State L) (bits : Nat) : L → Bool :=
  fun l => regionFrom cs bits l 0

omit [BEq State] [Hashable State] in
private theorem regionFrom_eq_true {cs : CompiledSpec State L} {bits : Nat} {l : L} :
    ∀ n o, cs.numOptions - o = n → (regionFrom cs bits l o = true ↔
      ∀ o', o ≤ o' → o' < cs.numOptions → bits.testBit o' = true →
        (cs.letterOptions[o']!).region l = true) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro o hn
  rw [regionFrom]
  by_cases ho : o < cs.numOptions
  · simp only [ho, dite_true, Bool.and_eq_true, Bool.or_eq_true]
    rw [ih (cs.numOptions - (o + 1)) (by omega) (o + 1) rfl]
    constructor
    · rintro ⟨h0, hrest⟩ o' hoo' ho' hbit
      rcases Nat.eq_or_lt_of_le hoo' with rfl | hlt
      · rcases h0 with h0 | h0
        · simp [hbit] at h0
        · exact h0
      · exact hrest o' hlt ho' hbit
    · intro h
      refine ⟨?_, fun o' hoo' ho' hbit => h o' (Nat.le_of_succ_le hoo') ho' hbit⟩
      rcases hbit : bits.testBit o with _ | _
      · exact Or.inl (by simp)
      · exact Or.inr (h o (Nat.le_refl _) ho hbit)
  · simp only [ho, dite_false, true_iff]
    intro o' hoo' ho'; omega

omit [BEq State] [Hashable State] in
theorem regionOf_eq_true {cs : CompiledSpec State L} {bits : Nat} {l : L} :
    regionOf cs bits l = true ↔
      ∀ o < cs.numOptions, bits.testBit o = true → (cs.letterOptions[o]!).region l = true := by
  rw [regionOf, regionFrom_eq_true _ 0 rfl]
  exact ⟨fun h o ho hb => h o (Nat.zero_le _) ho hb, fun h o _ ho hb => h o ho hb⟩

omit [BEq State] in
theorem regionOf_mono {cs : CompiledSpec State L} {b b' : Nat}
    (hbits : ∀ o, b.testBit o = true → b'.testBit o = true) :
    LePred (regionOf cs b') (regionOf cs b) :=
  fun _ hl => regionOf_eq_true.mpr fun o ho hbit => regionOf_eq_true.mp hl o ho (hbits o hbit)

omit [BEq State] in
/-- A region bit that is set is entailed by the conjunction. -/
theorem regionOf_le {cs : CompiledSpec State L} {bits o : Nat} (ho : o < cs.numOptions)
    (hbit : bits.testBit o = true) : LePred (regionOf cs bits) (cs.letterOptions[o]!).region :=
  fun _ hl => regionOf_eq_true.mp hl o ho hbit

/-- The options a bitmask commits to. -/
def committedOpts (cs : CompiledSpec State L) (bits : Nat) : List (StreettOption L) :=
  (List.range cs.numOptions).filterMap fun k => if bits.testBit k then some cs.letterOptions[k]! else none

omit [BEq State] [Hashable State] in
theorem mem_committedOpts {cs : CompiledSpec State L} {bits : Nat} {x : StreettOption L} :
    x ∈ committedOpts cs bits ↔ ∃ k < cs.numOptions, bits.testBit k = true ∧ cs.letterOptions[k]! = x := by
  simp only [committedOpts, List.mem_filterMap, List.mem_range, Option.ite_none_right_eq_some, Option.some.injEq]

omit [BEq State] in
/-- The empty bitmask is the top region. -/
theorem regionOf_zero (cs : CompiledSpec State L) : regionOf cs 0 = fun _ => true := by
  funext l
  exact regionOf_eq_true.mpr fun o _ h => by simp at h

/-- What `CompiledSpec.of` guarantees: each option owns the mark bits `optMarkBase[o] ..< optMarkBase[o] + (optMarks[o]).size`
and its mask selects exactly those, and conjunct `i` owns the options `conjunctStart[i] ..< conjunctStart[i+1]`, in order. -/
structure CompiledSpec.WF (cs : CompiledSpec State L) : Prop where
  numMarks_eq : cs.numMarks = cs.spec.numMarks
  letterOptions_size : cs.letterOptions.size = cs.numOptions
  regions_eq : cs.regions = cs.letterOptions.map fun opt => (opt.onEdgesIn cs.spec cs.restrict).region
  optMarks_eq : cs.optMarks = cs.letterOptions.map fun opt => (opt.onEdgesIn cs.spec cs.restrict).marks
  letter_option : ∀ i < cs.spec.conjuncts.size, ∀ k < (cs.spec.conjuncts[i]!).size,
    cs.letterOptions[cs.conjunctStart[i]! + k]! = (cs.spec.conjuncts[i]!)[k]!
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
    cs.regions[cs.conjunctStart[i]! + k]! =
      ((cs.spec.conjuncts[i]![k]!).onEdgesIn cs.spec cs.restrict).region
  option_marks : ∀ i < cs.spec.conjuncts.size, ∀ k < (cs.spec.conjuncts[i]!).size,
    cs.optMarks[cs.conjunctStart[i]! + k]! =
      ((cs.spec.conjuncts[i]![k]!).onEdgesIn cs.spec cs.restrict).marks
  /-- The predicate and the bitmask denote the same region. Carrying both is what lets the report-time
  validator establish `restrict ⊑ opt.region` for a committed option syntactically, by `regionOf_le`. -/
  restrict_eq : cs.restrict = regionOf cs cs.restrictBits

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
theorem CompiledSpec.ofAt_wf (spec : RStreettSpec State L) (r : L → Bool) (b : Nat)
    (hr : r = regionOf (CompiledSpec.ofAt spec r b) b) : (CompiledSpec.ofAt spec r b).WF := by
  obtain ⟨f1, f2, f3, f4⟩ := flattenOpts_spec spec.conjuncts
  have hgetF : ∀ (a : Array (StreettOption L)) (j : Nat) (h : j < a.size), a[j]! = a[j]'h :=
    fun a j h => getElem!_pos a j h
  set F : Array (StreettOption L) := (flattenOpts spec.conjuncts).1 with hF
  set S : Array Nat := (flattenOpts spec.conjuncts).2 with hS
  set sizes : Array Nat :=
    F.map (fun opt : StreettOption L => ((opt.onEdgesIn spec r).marks).size) with hsizes
  set B : Array Nat := prefixSums sizes 0 #[0] with hB
  have hb := prefixSums_spec sizes 0 #[0] (by simp) (Nat.zero_le _)
  -- an option's recorded mark count is the length of its mark array
  have hsz : ∀ o, o < F.size →
      sizes[o]! = ((F.map (fun opt : StreettOption L => (opt.onEdgesIn spec r).marks))[o]!).size := by
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
  have hregions : (F.map (fun opt : StreettOption L => (opt.onEdgesIn spec r).region)).size = F.size := by simp
  have hmarks : (F.map (fun opt : StreettOption L => (opt.onEdgesIn spec r).marks)).size = F.size := by simp
  have hzero : B[0]! = 0 := by rw [hB, hb.2.1 0 (by omega)]; simp
  have hsucc : ∀ o, o < F.size →
      B[o + 1]! = B[o]! + ((F.map (fun opt : StreettOption L => (opt.onEdgesIn spec r).marks))[o]!).size :=
    fun o ho => by rw [hB, hb.2.2 o (Nat.zero_le _) (by simp [hsizes]; omega), hsz o ho]
  have hmask : ∀ o, o < F.size →
      ((Array.range F.size).map fun i => ((1 <<< sizes[i]!) - 1) <<< B[i]!)[o]! =
        ((1 <<< ((F.map (fun opt : StreettOption L => (opt.onEdgesIn spec r).marks))[o]!).size) - 1) <<< B[o]! :=
    fun o ho => by
      rw [getElem!_pos _ _ (by simpa using ho), Array.getElem_map, Array.getElem_range, hsz o ho]
  have hregion_at : ∀ i, i < spec.conjuncts.size → ∀ k, k < (spec.conjuncts[i]!).size →
      (F.map (fun opt : StreettOption L => (opt.onEdgesIn spec r).region))[S[i]! + k]! =
        ((spec.conjuncts[i]![k]!).onEdgesIn spec r).region := fun i hi k hk => by
    have hidx := hSlt i hi k hk
    rw [getElem!_pos _ _ (by simpa using hidx), Array.getElem_map, ← hgetF F _ hidx,
      (f4 i hi).2 k hk]
  have hmarks_at : ∀ i, i < spec.conjuncts.size → ∀ k, k < (spec.conjuncts[i]!).size →
      (F.map (fun opt : StreettOption L => (opt.onEdgesIn spec r).marks))[S[i]! + k]! =
        ((spec.conjuncts[i]![k]!).onEdgesIn spec r).marks := fun i hi k hk => by
    have hidx := hSlt i hi k hk
    rw [getElem!_pos _ _ (by simpa using hidx), Array.getElem_map, ← hgetF F _ hidx,
      (f4 i hi).2 k hk]
  have hletter : ∀ i, i < spec.conjuncts.size → ∀ k, k < (spec.conjuncts[i]!).size →
      F[S[i]! + k]! = (spec.conjuncts[i]!)[k]! := fun i hi k hk => (f4 i hi).2 k hk
  exact ⟨rfl, rfl, rfl, rfl, hletter, hregions, hmarks, hzero, hsucc, rfl, hmask, f1, f2,
    fun i hi => (f4 i hi).1, f3, hregion_at, hmarks_at, hr⟩

/-- Option `o`'s edge region is the edge reading of its letter option. -/
theorem CompiledSpec.WF.regions_getElem {cs : CompiledSpec State L} (hwf : cs.WF) {o : Nat}
    (ho : o < cs.numOptions) :
    cs.regions[o]! = ((cs.letterOptions[o]!).onEdgesIn cs.spec cs.restrict).region := by
  have ho' : o < cs.letterOptions.size := by rw [hwf.letterOptions_size]; exact ho
  rw [hwf.regions_eq, getElem!_pos _ o (by simpa using ho'), getElem!_pos _ o ho',
    Array.getElem_map]

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
@[expose] def fullAccMask (numMarks : Nat) : Nat := (1 <<< (numMarks + 1)) - 1

/-! ## Candidates

A pruned candidate carries the options whose regions have been conjoined into it as a bitmask, not the
region itself. The regions a candidate can ever carry are conjunctions of a subset of the spec's own
options' regions — a finite set fixed by the spec — which is what gives the prune loop a bounded measure to
decrease (`EdgeLabels.md` §6.5, Change 4). A state set alone no longer suffices: an edge prune need not
remove any state. -/

/-- A state set together with the options whose regions have been conjoined into it. -/
structure Candidate (State : Type u) [BEq State] [Hashable State] where
  states : Std.HashSet State
  regions : Nat

/-- The letter restriction a candidate carries. -/
@[expose] def Candidate.region (cs : CompiledSpec State L) (c : Candidate State) : L → Bool :=
  regionOf cs c.regions

/-- The candidate form of `regionOf_eq_true`. -/
theorem Candidate.region_eq_true {cs : CompiledSpec State L} {c : Candidate State} {l : L} :
    c.region cs l = true ↔
      ∀ o < cs.numOptions, c.regions.testBit o = true → (cs.letterOptions[o]!).region l = true :=
  regionOf_eq_true

theorem Candidate.region_mono {cs : CompiledSpec State L} {c c' : Candidate State}
    (hbits : ∀ o, c.regions.testBit o = true → c'.regions.testBit o = true) :
    LePred (c'.region cs) (c.region cs) := regionOf_mono hbits



/-- The same spec recompiled for a candidate carrying `bits`: every option is now read *inside* the
region those bits denote. Only the readings change — the flattening, the block bases and the masks are
functions of `spec.conjuncts` and of how many marks each option has, none of which the restriction
touches — so a bitmask means in the recompiled spec exactly what it means here. -/
@[expose] def CompiledSpec.atRegion (cs : CompiledSpec State L) (r : L → Bool) : CompiledSpec State L :=
  { cs with
    restrict := r
    regions := cs.letterOptions.map fun opt => (opt.onEdgesIn cs.spec r).region
    optMarks := cs.letterOptions.map fun opt => (opt.onEdgesIn cs.spec r).marks }

/-- The same at the region a bitmask denotes, recording the bitmask too. -/
@[expose] def CompiledSpec.atBits (cs : CompiledSpec State L) (bits : Nat) : CompiledSpec State L :=
  { cs.atRegion (regionOf cs bits) with restrictBits := bits }

omit [Hashable State] in
@[simp] theorem CompiledSpec.atRegion_letterOptions (cs : CompiledSpec State L) (r : L → Bool) :
    (cs.atRegion r).letterOptions = cs.letterOptions := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.atRegion_numOptions (cs : CompiledSpec State L) (r : L → Bool) :
    (cs.atRegion r).numOptions = cs.numOptions := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.atRegion_regions (cs : CompiledSpec State L) (r : L → Bool) :
    (cs.atRegion r).regions = cs.letterOptions.map fun opt => (opt.onEdgesIn cs.spec r).region := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.atBits_atRegion (cs : CompiledSpec State L) (bits : Nat) :
    (cs.atBits bits).regions = (cs.atRegion (regionOf cs bits)).regions := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.atBits_optMarks (cs : CompiledSpec State L) (bits : Nat) :
    (cs.atBits bits).optMarks = (cs.atRegion (regionOf cs bits)).optMarks := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.atBits_spec (cs : CompiledSpec State L) (bits : Nat) :
    (cs.atBits bits).spec = cs.spec := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.atBits_letterOptions (cs : CompiledSpec State L) (bits : Nat) :
    (cs.atBits bits).letterOptions = cs.letterOptions := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.atBits_restrict (cs : CompiledSpec State L) (bits : Nat) :
    (cs.atBits bits).restrict = regionOf cs bits := rfl

omit [Hashable State] in
/-- A bitmask denotes the same region in a recompiled spec: `regionOf` reads only `letterOptions` and
`numOptions`, neither of which the restriction touches. -/
@[simp] theorem regionOf_atBits (cs : CompiledSpec State L) (bits b : Nat) :
    regionOf (cs.atBits bits) b = regionOf cs b := by
  funext l
  rw [Bool.eq_iff_iff, regionOf_eq_true, regionOf_eq_true]
  rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.atBits_numOptions (cs : CompiledSpec State L) (bits : Nat) :
    (cs.atBits bits).numOptions = cs.numOptions := rfl

@[simp] theorem Candidate.region_atBits (cs : CompiledSpec State L) (bits : Nat)
    (c : Candidate State) : Candidate.region (cs.atBits bits) c = Candidate.region cs c :=
  regionOf_atBits cs bits c.regions

omit [Hashable State] in
@[simp] theorem CompiledSpec.atBits_conjunctStart (cs : CompiledSpec State L) (bits : Nat) :
    (cs.atBits bits).conjunctStart = cs.conjunctStart := rfl

omit [Hashable State] in
/-- The two readings of an option differ only in which realizations they accept, never in how many marks
they have. -/
private theorem map_marks_size (cs : CompiledSpec State L) (r r' : L → Bool) (o : Nat) :
    Array.size ((cs.letterOptions.map fun opt => (opt.onEdgesIn cs.spec r).marks)[o]!) =
      Array.size ((cs.letterOptions.map fun opt => (opt.onEdgesIn cs.spec r').marks)[o]!) := by
  by_cases ho : o < cs.letterOptions.size
  · rw [getElem!_pos _ o (by simpa using ho), getElem!_pos _ o (by simpa using ho),
      Array.getElem_map, Array.getElem_map]
    simp [StreettOption.onEdgesIn]
  · rw [getElem!_neg _ o (by simpa using ho), getElem!_neg _ o (by simpa using ho)]

omit [Hashable State] in
private theorem map_getElem!_letter (cs : CompiledSpec State L) (r : L → Bool)
    {f : StreettOption (State × State) → γ} [Inhabited γ] {o : Nat}
    (ho : o < cs.letterOptions.size) :
    (cs.letterOptions.map fun opt => f (opt.onEdgesIn cs.spec r))[o]! =
      f ((cs.letterOptions[o]!).onEdgesIn cs.spec r) := by
  rw [getElem!_pos _ o (by simpa using ho), Array.getElem_map, ← getElem!_pos _ o ho]

omit [Hashable State] in
/-- Recompiling preserves well-formedness. Every structural field is copied, and the two that change are
`map`s over the same `letterOptions` whose mark counts `onEdgesIn` preserves — so the block bases and
masks that `cs.WF` pins still describe the new readings. -/
theorem CompiledSpec.WF.atBits {cs : CompiledSpec State L} (hwf : cs.WF) (bits : Nat) :
    (cs.atBits bits).WF := by
  have hom : (cs.atBits bits).optMarks =
      cs.letterOptions.map fun opt => (opt.onEdgesIn cs.spec (regionOf cs bits)).marks := rfl
  have hsize : ∀ o : Nat,
      Array.size ((cs.atBits bits).optMarks[o]!) = Array.size (cs.optMarks[o]!) := by
    intro o
    rw [hom, hwf.optMarks_eq]
    exact map_marks_size cs _ _ o
  refine { hwf with
    regions_eq := rfl
    optMarks_eq := rfl
    regions_size := by
      show Array.size (cs.letterOptions.map _) = _
      simpa using hwf.letterOptions_size
    optMarks_size := by
      show Array.size (cs.letterOptions.map _) = _
      simpa using hwf.letterOptions_size
    base_succ := fun o ho => by rw [hsize o]; exact hwf.base_succ o ho
    mask_eq := fun o ho => by rw [hsize o]; exact hwf.mask_eq o ho
    option_region := fun i hi k hk => ?_
    option_marks := fun i hi k hk => ?_
    restrict_eq := by
      show regionOf cs bits = regionOf (cs.atBits bits) bits
      rw [regionOf_atBits] }
  · have hlt : cs.conjunctStart[i]! + k < cs.letterOptions.size := by
      rw [hwf.letterOptions_size]; exact hwf.option_lt hi hk
    show (cs.letterOptions.map fun opt =>
      (opt.onEdgesIn cs.spec (regionOf cs bits)).region)[cs.conjunctStart[i]! + k]! = _
    rw [map_getElem!_letter cs _ hlt, hwf.letter_option i hi k hk]
    rfl
  · have hlt : cs.conjunctStart[i]! + k < cs.letterOptions.size := by
      rw [hwf.letterOptions_size]; exact hwf.option_lt hi hk
    show (cs.letterOptions.map fun opt =>
      (opt.onEdgesIn cs.spec (regionOf cs bits)).marks)[cs.conjunctStart[i]! + k]! = _
    rw [map_getElem!_letter cs _ hlt, hwf.letter_option i hi k hk]
    rfl

omit [Hashable State] in
/-- Recompiling at the bitmask a spec already carries is the identity. -/
theorem CompiledSpec.atBits_self {cs : CompiledSpec State L} (hwf : cs.WF) :
    cs.atBits cs.restrictBits = cs := by
  have hr : regionOf cs cs.restrictBits = cs.restrict := hwf.restrict_eq.symm
  rw [CompiledSpec.atBits, hr, CompiledSpec.atRegion, ← hwf.regions_eq, ← hwf.optMarks_eq]

omit [Hashable State] in
theorem CompiledSpec.of_wf (spec : RStreettSpec State L) : (CompiledSpec.of spec).WF :=
  CompiledSpec.ofAt_wf spec _ _ (regionOf_zero _).symm

omit [Hashable State] in
@[simp] theorem CompiledSpec.atBits_restrictBits (cs : CompiledSpec State L) (bits : Nat) :
    (cs.atBits bits).restrictBits = bits := rfl

omit [Hashable State] in
@[simp] theorem CompiledSpec.atBits_numMarks (cs : CompiledSpec State L) (bits : Nat) :
    (cs.atBits bits).numMarks = cs.numMarks := rfl


theorem testBit_or_shift {bits o x : Nat} :
    (bits ||| (1 <<< o)).testBit x = true ↔ bits.testBit x = true ∨ x = o := by
  simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro (h | h); · exact Or.inl h
    · exact Or.inr h.symm
  · rintro (h | rfl); · exact Or.inl h
    · exact Or.inr rfl

omit [BEq State] [Hashable State] in
/-- Setting one more bit conjoins exactly that option's region. This is the bridge between the bitmask the
prune loop carries and the region `RRefuted` recurses on: `RRefuted.pass` asks for `r ∧ opt.region`, and the
queued candidate's region is `regionOf` of the extended mask. Since both sides are `L → Bool`, pointwise
equality *is* equality, so the derivation needs no congruence lemma in the region. -/
theorem regionOf_or_shift {cs : CompiledSpec State L} {bits o : Nat} (ho : o < cs.numOptions) :
    regionOf cs (bits ||| (1 <<< o))
      = fun l => regionOf cs bits l && (cs.letterOptions[o]!).region l := by
  funext l
  rw [Bool.eq_iff_iff, Bool.and_eq_true, regionOf_eq_true, regionOf_eq_true]
  constructor
  · intro h
    exact ⟨fun x hx hb => h x hx (testBit_or_shift.mpr (Or.inl hb)),
      h o ho (testBit_or_shift.mpr (Or.inr rfl))⟩
  · rintro ⟨h1, h2⟩ x hx hb
    rcases testBit_or_shift.mp hb with hb' | rfl
    · exact h1 x hx hb'
    · exact h2

section CandidateGraph
variable [LawfulBEq State] [LawfulHashable State]

/-- The subgraph a candidate induces: the spec's graph restricted to the candidate's region, then to its
states. -/
@[expose] def Candidate.graph (cs : CompiledSpec State L) (spec : RStreettSpec State L)
    (c : Candidate State) : State → Array State :=
  sccSuccs (spec.regionSuccs (c.region cs)) c.states

/-- The fused expansion for a candidate's graph: the spec's own `regionExpand`, filtered to the
candidate's states in lockstep.

The region is decided on steps, so this cannot reuse the *caller's* fused expansion — but the spec can
carry its own, and `regionExpand` is it. This used to be `ss.map (spec.regionMarks … s)`: successors
first, then the two-argument spec form of the marks once per successor, each call re-deriving the
source's label and steps. `EdgeLabels.md` §13.8 measured that shape at `1 + d` `sysSucc` and `1 + 2d`
`sysLabel` calls per state against the top-level scan's 1.0x, and 4.58x the wall clock for an identical
answer. Body inlined from `sccExpand` rather than calling it, since that one lives under a later
`variable` block. -/
@[expose] def Candidate.expand (cs : CompiledSpec State L) (spec : RStreettSpec State L)
    (c : Candidate State) : State → Array State × Array (Std.HashSet Nat) × Array Nat :=
  fun s => filterExpand (spec.regionExpand (c.region cs) s) c.states.contains

omit [LawfulBEq State] [LawfulHashable State] in
theorem Candidate.expand_coherent (cs : CompiledSpec State L) (spec : RStreettSpec State L)
    (c : Candidate State) :
    ExpandCoherent (c.graph cs spec) (spec.regionMarks (c.region cs)) (c.expand cs spec) :=
  -- `c.graph` is `sccSuccs (regionSuccs …) c.states`, which unfolds to the same `filter` the expansion
  -- is filtered by, so this is `filterExpand_fst_snd` at the spec's own coherence law.
  fun s => filterExpand_fst_snd _ (spec.regionExpand_coherent (c.region cs) s)

omit [LawfulHashable State] [LawfulBEq State] in
/-- A candidate's graph admits only ambient edges, which is all `RRefuted.no_fairSCC` asks of the graph a
search runs on. -/
theorem Candidate.graph_sub {cs : CompiledSpec State L} {spec : RStreettSpec State L}
    {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat}
    (hcompat : spec.Compat succs edgeMarks) (c : Candidate State) :
    ∀ a b, b ∈ c.graph cs spec a → b ∈ succs a := by
  intro a b hb
  exact hcompat.succs_sub _ a b (Array.mem_filter.mp hb).1

omit [LawfulBEq State] [LawfulHashable State] in
/-- A candidate's graph shrinks when its bitmask grows. -/
theorem Candidate.graph_mono {cs : CompiledSpec State L} {spec : RStreettSpec State L}
    {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat}
    (hcompat : spec.Compat succs edgeMarks) {c c' : Candidate State}
    (hbits : ∀ o, c.regions.testBit o = true → c'.regions.testBit o = true)
    (hst : ∀ s, s ∈ c'.states → s ∈ c.states) :
    ∀ a b, b ∈ c'.graph cs spec a → b ∈ c.graph cs spec a := by
  intro a b hb
  obtain ⟨h1, h2⟩ := Array.mem_filter.mp hb
  exact Array.mem_filter.mpr
    ⟨hcompat.succs_mono (Candidate.region_mono hbits) a b h1,
     Std.HashSet.mem_iff_contains.mp (hst b (Std.HashSet.mem_iff_contains.mpr h2))⟩

/-- The measure the prune loop decreases: how many of the spec's options are still unconjoined. An edge prune need not drop a
state, but every queued candidate gains an option bit its search lacked (`StreettWF.pending_fresh`), so this alone decreases. -/
@[expose] def Candidate.measure (cs : CompiledSpec State L) (c : Candidate State) : Nat :=
  cs.numOptions - (List.range cs.numOptions).countP fun o => c.regions.testBit o

omit [LawfulBEq State] [LawfulHashable State] in
/-- Conjoining an option that was not already conjoined strictly drops the measure, so a prune step that
restricts edges without removing a state still decreases it. -/
theorem Candidate.measure_lt {cs : CompiledSpec State L} {c : Candidate State} {o : Nat}
    (ho : o < cs.numOptions) (hnew : c.regions.testBit o = false) :
    Candidate.measure cs ⟨c.states, c.regions ||| (1 <<< o)⟩ < Candidate.measure cs c := by
  have hlt : (List.range cs.numOptions).countP (fun x => c.regions.testBit x) <
      (List.range cs.numOptions).countP fun x => (c.regions ||| (1 <<< o)).testBit x :=
    LTLLib.List.countP_lt_countP (fun _ _ hx => testBit_or_shift.mpr (Or.inl hx)) (List.mem_range.mpr ho)
      hnew (testBit_or_shift.mpr (Or.inr rfl))
  have hle := List.countP_le_length (p := fun x => (c.regions ||| (1 <<< o)).testBit x)
    (l := List.range cs.numOptions)
  rw [List.length_range] at hle
  simp only [Candidate.measure]
  omega

end CandidateGraph

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
  pending : Array (Candidate State)
    -- pruned candidates: the same states with one more region conjoined, or fewer states, or both

@[expose] def streettInitAux : StreettAux State where
  live := #[]
  liveIndex := Std.HashMap.emptyWithCapacity 0
  dead := Std.HashSet.emptyWithCapacity 0
  dstack := #[]
  witness := #[]
  witnessOpts := #[]
  pending := #[]

@[expose] def streettGetStatus (aux : StreettAux State) (q : State) : DFSStatus :=
  liveStatusOf aux.liveIndex aux.dead q

/-! ## The per-SCC test -/

/-- One option's marks at one state, which own bits `base ..< base + gs.size` of `marksSeen`. -/
def scanMarksAt (gs : Array ((State × State) → Bool)) (lab : State × State)
    (base : Nat) (j : Nat) (marksSeen : Nat) : Nat :=
  if h : j < gs.size then
    scanMarksAt gs lab base (j + 1)
      (if !marksSeen.testBit (base + j) && gs[j] lab then marksSeen ||| (1 <<< (base + j)) else marksSeen)
  else marksSeen
termination_by gs.size - j

/-- Every option at one state, clearing the regions that fail here and setting the marks that hold here.

**Each option is decided independently of the others**, and with *step* regions that is an
over-approximation: two options can both survive an edge through different realizations of it, while no
single step satisfies both. For a state-labelled system the two coincide, and every caller is state-labelled
(`modelCheckPruneSplit`'s signature enforces it). Making the scan joint is `EdgeLabels.md` §11 item 4;
`Tests/PruneJointRegions.lean` is the counterexample that fixes what "joint" has to mean. -/
@[expose] def scanOptionsAt (cs : CompiledSpec State L) (lab : State × State) (o : Nat)
    (regionAlive marksSeen : Nat) :
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


@[expose] def scanLabels (cs : CompiledSpec State L) : List (State × State) → Nat → Nat → Nat × Nat
  | [], regionAlive, marksSeen => (regionAlive, marksSeen)
  | lab :: rest, regionAlive, marksSeen =>
    if regionAlive == 0 && marksSeen == (1 <<< cs.numOptMarks) - 1 then (regionAlive, marksSeen)
    else
      let (ra, ms) := scanOptionsAt cs lab 0 regionAlive marksSeen
      scanLabels cs rest ra ms

/-- One pass over an explicit letter list, from the full `regionAlive` and the empty `marksSeen`. -/
@[expose] def scanLetters (cs : CompiledSpec State L) (labs : List (State × State)) : Nat × Nat :=
  scanLabels cs labs ((1 <<< cs.numOptions) - 1) 0


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

-- whether `bits` commits to an option of `[o, hi)`
private def anyBitIn (bits : Nat) (o hi : Nat) : Bool :=
  if o < hi then bits.testBit o || anyBitIn bits (o + 1) hi else false
termination_by hi - o

-- the first available option in `[o, hi)` the candidate has already committed to
private def selectCommitted (cs : CompiledSpec State L) (bits regionAlive marksSeen : Nat)
    (o hi : Nat) : Option Nat :=
  if o < hi then
    if bits.testBit o && optionAvailable cs regionAlive marksSeen o then some o
    else selectCommitted cs bits regionAlive marksSeen (o + 1) hi
  else none
termination_by hi - o

/-- The option a conjunct is reported with: one the candidate has already committed to when it has one, otherwise the first
available one. A committed available option is exact, the candidate's region already entailing that option's, so the scan's
per-option verdict for it is a verdict at the conjunction. The preference only chooses the options recorded beside a report. -/
private def selectPref (cs : CompiledSpec State L) (bits regionAlive marksSeen : Nat) (o hi : Nat) :
    Option Nat :=
  (selectCommitted cs bits regionAlive marksSeen o hi).or (selectOne cs regionAlive marksSeen o hi)

-- one available option per conjunct, from conjunct `i` on
private def selectFrom (cs : CompiledSpec State L) (bits regionAlive marksSeen : Nat) (i : Nat)
    (sel : Array Nat) : Array Nat :=
  if i < cs.conjunctStart.size - 1 then
    selectFrom cs bits regionAlive marksSeen (i + 1)
      (match selectPref cs bits regionAlive marksSeen
          cs.conjunctStart[i]! cs.conjunctStart[i + 1]! with
        | some o => sel.push o
        | none => sel)
  else sel
termination_by cs.conjunctStart.size - 1 - i

/-- The preferred available option of each conjunct, whose marks join the acceptance condition the reported cycle has to
cover. -/
def selectedOptions (cs : CompiledSpec State L) (bits regionAlive marksSeen : Nat) : Array Nat :=
  selectFrom cs bits regionAlive marksSeen 0 #[]

-- the live options of the first conjunct from `i` on with no available option, `some #[]` if `bits` commits to one of its options
private def firstUnsatFrom (cs : CompiledSpec State L) (bits regionAlive marksSeen : Nat) (i : Nat) :
    Option (Array Nat) :=
  if i < cs.conjunctStart.size - 1 then
    if (selectOne cs regionAlive marksSeen cs.conjunctStart[i]! cs.conjunctStart[i + 1]!).isSome then
      firstUnsatFrom cs bits regionAlive marksSeen (i + 1)
    else if anyBitIn bits cs.conjunctStart[i]! cs.conjunctStart[i + 1]! then some #[]
    else some (liveOptionsIn cs marksSeen cs.conjunctStart[i]! cs.conjunctStart[i + 1]! #[])
  else none
termination_by cs.conjunctStart.size - 1 - i

/-- The live options of the first conjunct with no available option, `none` when every conjunct is satisfied.
Only the first such conjunct branches, since a fair subgraph has to satisfy it through one of its options. A
conjunct the candidate has already committed to (`bits`) branches no further and gives `some #[]`, since its committed
option's region holds by restriction, so its marks are missing, and each of its other options that was live where it
branched was searched by a sibling. -/
def firstUnsatisfied (cs : CompiledSpec State L) (bits regionAlive marksSeen : Nat) : Option (Array Nat) :=
  firstUnsatFrom cs bits regionAlive marksSeen 0

/-! ## What the scan decides -/

section ScanCorrect
omit [Hashable State]

theorem mask_testBit {size base k : Nat} (hk : k < size) :
    ((((1 <<< size) - 1) <<< base) : Nat).testBit (base + k) = true := by
  simp [Nat.testBit_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, hk]

theorem mask_testBit_iff {size base x : Nat} :
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

omit [BEq State] in
theorem scanMarksAt_testBit (gs : Array ((State × State) → Bool)) (lab : State × State)
    (base b : Nat)
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

omit [BEq State] in
theorem scanOptionsAt_fst_testBit (cs : CompiledSpec State L) (lab : State × State)
    (b : Nat)
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

theorem scanOptionsAt_snd_testBit (cs : CompiledSpec State L) (hwf : cs.WF)
    (lab : State × State)
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

omit [BEq State] in
theorem scanLabels_fst_testBit (cs : CompiledSpec State L) (b : Nat) :
    ∀ (labs : List (State × State)) (ra ms : Nat),
      (scanLabels cs labs ra ms).1.testBit b = true ↔
        ra.testBit b = true ∧ (b < cs.numOptions → ∀ l ∈ labs, cs.regions[b]! l = true)
  | [], ra, ms => by rw [scanLabels]; simp
  | lab :: rest, ra, ms => by
    rw [scanLabels]
    by_cases hbreak : (ra == 0 && ms == (1 <<< cs.numOptMarks) - 1) = true
    · rw [if_pos hbreak]
      simp only [Bool.and_eq_true, beq_iff_eq] at hbreak
      simp [hbreak.1]
    · rw [if_neg hbreak]
      have hbit := scanOptionsAt_fst_testBit cs lab b 0 ra ms
      show (scanLabels cs rest (scanOptionsAt cs lab 0 ra ms).1
        (scanOptionsAt cs lab 0 ra ms).2).1.testBit b = true ↔ _
      rw [scanLabels_fst_testBit cs b rest, hbit]
      grind

theorem scanLabels_snd_testBit (cs : CompiledSpec State L) (hwf : cs.WF) (b : Nat) :
    ∀ (labs : List (State × State)) (ra ms : Nat),
      (scanLabels cs labs ra ms).2.testBit b = true ↔
        ms.testBit b = true ∨ ∃ l ∈ labs, ∃ p, p < cs.numOptions ∧
          ∃ k, k < (cs.optMarks[p]!).size ∧ cs.optMarkBase[p]! + k = b ∧
            (cs.optMarks[p]!)[k]! l = true
  | [], ra, ms => by rw [scanLabels]; simp
  | lab :: rest, ra, ms => by
    rw [scanLabels]
    by_cases hbreak : (ra == 0 && ms == (1 <<< cs.numOptMarks) - 1) = true
    · rw [if_pos hbreak]
      simp only [Bool.and_eq_true, beq_iff_eq] at hbreak
      constructor
      · exact Or.inl
      · rintro (h | ⟨l, _, p, hp, k, hk, hbk, _⟩)
        · exact h
        · have := hwf.bit_lt hp hk
          rw [hbreak.2]
          simp only [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
          omega
    · rw [if_neg hbreak]
      have hbit := scanOptionsAt_snd_testBit cs hwf lab b 0 ra ms
      show (scanLabels cs rest (scanOptionsAt cs lab 0 ra ms).1
        (scanOptionsAt cs lab 0 ra ms).2).2.testBit b = true ↔ _
      rw [scanLabels_snd_testBit cs hwf b rest, hbit]
      grind

omit [BEq State] in
/-- An option's region bit survives the letter scan exactly when its region holds at every scanned letter. -/
theorem scanLetters_fst_testBit (cs : CompiledSpec State L) (labs : List (State × State)) (b : Nat)
    (hb : b < cs.numOptions) :
    (scanLetters cs labs).1.testBit b = true ↔ ∀ l ∈ labs, cs.regions[b]! l = true := by
  rw [scanLetters, scanLabels_fst_testBit]
  simp [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, hb]

/-- A mark bit is set after the letter scan exactly when the mark owning it holds at some scanned letter. -/
theorem scanLetters_snd_testBit (cs : CompiledSpec State L) (hwf : cs.WF)
    (labs : List (State × State)) (b : Nat) :
    (scanLetters cs labs).2.testBit b = true ↔
      ∃ l ∈ labs, ∃ p, p < cs.numOptions ∧ ∃ k, k < (cs.optMarks[p]!).size ∧
        cs.optMarkBase[p]! + k = b ∧ (cs.optMarks[p]!)[k]! l = true := by
  rw [scanLetters, scanLabels_snd_testBit _ hwf]
  simp

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

theorem optionLive_letters (cs : CompiledSpec State L) (hwf : cs.WF)
    (labs : List (State × State)) (o : Nat)
    (ho : o < cs.numOptions) :
    optionLive cs (scanLetters cs labs).2 o = true ↔
      ∀ g ∈ cs.optMarks[o]!, ∃ l ∈ labs, g l = true := by
  rw [optionLive_iff_bits hwf ho]
  constructor
  · intro h g hg
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hg
    obtain ⟨l, hl, p, hp, k, hk, hbk, hmk⟩ :=
      (scanLetters_snd_testBit cs hwf labs _).mp (h j hj)
    have hpo : p = o := hwf.base_inj hp ho hk hj hbk
    subst hpo
    have hkj : k = j := by omega
    subst hkj
    exact ⟨l, hl, by rwa [getElem!_pos (cs.optMarks[p]!) k hk] at hmk⟩
  · intro h j hj
    rw [scanLetters_snd_testBit cs hwf]
    obtain ⟨l, hl, hgl⟩ := h _ (Array.getElem_mem hj)
    exact ⟨l, hl, o, ho, j, hj, rfl, by rwa [getElem!_pos (cs.optMarks[o]!) j hj]⟩

/-- The letter scan decides an option's availability on the scanned letters. Pointed at the SCC's internal
edges with the edge-indexed predicates, this is `RStreettSpec.AvailableWith`'s two edge conditions. -/
theorem optionAvailable_letters (cs : CompiledSpec State L) (hwf : cs.WF)
    (labs : List (State × State)) (o : Nat)
    (ho : o < cs.numOptions) :
    optionAvailable cs (scanLetters cs labs).1 (scanLetters cs labs).2 o = true ↔
      (∀ l ∈ labs, cs.regions[o]! l = true) ∧ ∀ g ∈ cs.optMarks[o]!, ∃ l ∈ labs, g l = true := by
  rw [optionAvailable, Bool.and_eq_true, scanLetters_fst_testBit cs labs o ho,
    optionLive_letters cs hwf labs o ho]

/-! ## What the per-conjunct scan decides -/

omit [BEq State] in
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

omit [BEq State] in
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

omit [BEq State] in
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

private theorem anyBitIn_eq_true_iff {bits : Nat} :
    ∀ {o hi : Nat}, anyBitIn bits o hi = true ↔ ∃ k, o ≤ k ∧ k < hi ∧ bits.testBit k = true := by
  intro o hi
  induction o using anyBitIn.induct (hi := hi) with
  | case1 x hx ih =>
    rw [anyBitIn, if_pos hx, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨k, h1, h2, h3⟩)
      · exact ⟨x, Nat.le_refl _, hx, h⟩
      · exact ⟨k, by omega, h2, h3⟩
    · rintro ⟨k, h1, h2, h3⟩
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact Or.inl h3
      · exact Or.inr ⟨k, hlt, h2, h3⟩
  | case2 x hx =>
    rw [anyBitIn, if_neg hx]
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro k h1 h2
    omega

omit [BEq State] in
private theorem firstUnsatFrom_eq_none {cs : CompiledSpec State L} {bits ra ms : Nat} :
    ∀ i, firstUnsatFrom cs bits ra ms i = none →
      ∀ j, i ≤ j → j < cs.conjunctStart.size - 1 →
        ∃ o, cs.conjunctStart[j]! ≤ o ∧ o < cs.conjunctStart[j + 1]! ∧
          optionAvailable cs ra ms o = true := by
  intro i
  induction i using firstUnsatFrom.induct (cs := cs) (bits := bits) (regionAlive := ra)
    (marksSeen := ms) with
  | case1 x hx hsome ih =>
    intro h j hj hjn
    rw [firstUnsatFrom, if_pos hx, if_pos hsome] at h
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨o, selectOne_eq_some _ _ ho⟩
    · exact ih h j hlt hjn
  | case2 x hx hnone hcom =>
    intro h _ _ _
    rw [firstUnsatFrom, if_pos hx, if_neg hnone, if_pos hcom] at h
    exact absurd h (by simp)
  | case3 x hx hnone hcom =>
    intro h _ _ _
    rw [firstUnsatFrom, if_pos hx, if_neg hnone, if_neg hcom] at h
    exact absurd h (by simp)
  | case4 x hx =>
    intro _ j hj hjn
    omega

omit [BEq State] in
private theorem firstUnsatFrom_eq_some {cs : CompiledSpec State L} {bits ra ms : Nat} :
    ∀ i opts, firstUnsatFrom cs bits ra ms i = some opts →
      ∃ j, i ≤ j ∧ j < cs.conjunctStart.size - 1 ∧
        (∀ o, cs.conjunctStart[j]! ≤ o → o < cs.conjunctStart[j + 1]! →
          optionAvailable cs ra ms o = false) ∧
        ∀ p, p ∈ opts ↔ anyBitIn bits cs.conjunctStart[j]! cs.conjunctStart[j + 1]! = false ∧
          cs.conjunctStart[j]! ≤ p ∧ p < cs.conjunctStart[j + 1]! ∧ optionLive cs ms p = true := by
  intro i
  induction i using firstUnsatFrom.induct (cs := cs) (bits := bits) (regionAlive := ra)
    (marksSeen := ms) with
  | case1 x hx hsome ih =>
    intro opts h
    rw [firstUnsatFrom, if_pos hx, if_pos hsome] at h
    obtain ⟨j, h1, h2, h3, h4⟩ := ih opts h
    exact ⟨j, Nat.le_of_succ_le h1, h2, h3, h4⟩
  | case2 x hx hnone hcom =>
    intro opts h
    rw [firstUnsatFrom, if_pos hx, if_neg hnone, if_pos hcom] at h
    obtain rfl : (#[] : Array Nat) = opts := by simpa using h
    refine ⟨x, Nat.le_refl _, hx, ?_, fun p => ?_⟩
    · have := selectOne_eq_none (cs := cs) (ra := ra) (ms := ms)
        (hi := cs.conjunctStart[x + 1]!) cs.conjunctStart[x]!
      exact this.mp (Option.not_isSome_iff_eq_none.mp (by simpa using hnone))
    · simp [hcom]
  | case3 x hx hnone hcom =>
    intro opts h
    rw [firstUnsatFrom, if_pos hx, if_neg hnone, if_neg hcom] at h
    obtain rfl : liveOptionsIn cs ms cs.conjunctStart[x]! cs.conjunctStart[x + 1]! #[] = opts := by
      simpa using h
    refine ⟨x, Nat.le_refl _, hx, ?_, fun p => ?_⟩
    · have := selectOne_eq_none (cs := cs) (ra := ra) (ms := ms)
        (hi := cs.conjunctStart[x + 1]!) cs.conjunctStart[x]!
      exact this.mp (Option.not_isSome_iff_eq_none.mp (by simpa using hnone))
    · rw [mem_liveOptionsIn]
      simp [hcom]
  | case4 x hx =>
    intro opts h
    rw [firstUnsatFrom, if_neg hx] at h
    exact absurd h (by simp)

omit [BEq State] in
/-- A blamed option's bit is not set in the candidate's bitmask. -/
private theorem blamed_bit_new {cs : CompiledSpec State L} {curRegions ra ms : Nat} {opts : Array Nat} {o : Nat}
    (hfu : firstUnsatisfied cs curRegions ra ms = some opts) (ho : o ∈ opts) : curRegions.testBit o = false := by
  obtain ⟨j, _, _, _, hmem⟩ := firstUnsatFrom_eq_some 0 opts hfu
  obtain ⟨hany, hlo, hhi, _⟩ := (hmem o).mp ho
  cases hb : curRegions.testBit o
  · rfl
  · rw [anyBitIn_eq_true_iff.mpr ⟨o, hlo, hhi, hb⟩] at hany
    exact Bool.noConfusion hany

omit [BEq State] in
private theorem selectCommitted_eq_some {cs : CompiledSpec State L} {bits ra ms hi : Nat} :
    ∀ o r, selectCommitted cs bits ra ms o hi = some r →
      o ≤ r ∧ r < hi ∧ bits.testBit r = true ∧ optionAvailable cs ra ms r = true := by
  intro o
  induction o using selectCommitted.induct (cs := cs) (bits := bits) (regionAlive := ra)
    (marksSeen := ms) (hi := hi) with
  | case1 x hx havail =>
    intro r h
    rw [selectCommitted, if_pos hx, if_pos havail] at h
    obtain rfl : x = r := by simpa using h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp havail
    exact ⟨Nat.le_refl _, hx, h1, h2⟩
  | case2 x hx hnavail ih =>
    intro r h
    rw [selectCommitted, if_pos hx, if_neg hnavail] at h
    obtain ⟨h1, h2, h3, h4⟩ := ih r h
    exact ⟨Nat.le_of_succ_le h1, h2, h3, h4⟩
  | case3 x hx =>
    intro r h
    rw [selectCommitted, if_neg hx] at h
    exact absurd h (by simp)

omit [BEq State] in
private theorem selectCommitted_eq_none {cs : CompiledSpec State L} {bits ra ms hi : Nat} :
    ∀ o, selectCommitted cs bits ra ms o hi = none ↔
      ∀ p, o ≤ p → p < hi → (bits.testBit p && optionAvailable cs ra ms p) = false := by
  intro o
  induction o using selectCommitted.induct (cs := cs) (bits := bits) (regionAlive := ra)
    (marksSeen := ms) (hi := hi) with
  | case1 x hx havail =>
    rw [selectCommitted, if_pos hx, if_pos havail]
    constructor
    · intro h; exact absurd h (by simp)
    · intro h
      have hc := h x (Nat.le_refl _) hx
      rw [havail] at hc
      exact absurd hc (by simp)
  | case2 x hx hnavail ih =>
    rw [selectCommitted, if_pos hx, if_neg hnavail, ih]
    constructor
    · intro h p hp hph
      rcases Nat.eq_or_lt_of_le hp with rfl | hlt
      · simpa using hnavail
      · exact h p hlt hph
    · intro h p hp hph
      exact h p (Nat.le_of_succ_le hp) hph
  | case3 x hx =>
    rw [selectCommitted, if_neg hx]
    simp only [true_iff]
    intro p hp hph
    omega

omit [BEq State] in
/-- The preferred option is available, and lies in the conjunct's block. -/
private theorem selectPref_eq_some {cs : CompiledSpec State L} {bits ra ms hi : Nat} :
    ∀ o r, selectPref cs bits ra ms o hi = some r →
      o ≤ r ∧ r < hi ∧ optionAvailable cs ra ms r = true := by
  intro o r h
  rw [selectPref] at h
  rcases hc : selectCommitted cs bits ra ms o hi with _ | c
  · rw [hc, Option.none_or] at h
    exact selectOne_eq_some _ _ h
  · rw [hc, Option.some_or] at h
    obtain rfl : c = r := by simpa using h
    obtain ⟨h1, h2, -, h4⟩ := selectCommitted_eq_some _ _ hc
    exact ⟨h1, h2, h4⟩

omit [BEq State] in
/-- `selectPref` finds something whenever `selectOne` does. -/
private theorem selectPref_isSome {cs : CompiledSpec State L} {bits ra ms o hi : Nat}
    (h : (selectOne cs ra ms o hi).isSome = true) :
    (selectPref cs bits ra ms o hi).isSome = true := by
  rw [selectPref]
  rcases hc : selectCommitted cs bits ra ms o hi with _ | c
  · rw [Option.none_or]; exact h
  · rw [Option.some_or]; simp

omit [BEq State] in
/-- When the conjunct has a committed available option, the preferred one is committed. -/
private theorem selectPref_committed {cs : CompiledSpec State L} {bits ra ms o hi r : Nat}
    (hc : (selectCommitted cs bits ra ms o hi).isSome = true)
    (h : selectPref cs bits ra ms o hi = some r) : bits.testBit r = true := by
  obtain ⟨c, hcv⟩ := Option.isSome_iff_exists.mp hc
  rw [selectPref, hcv, Option.some_or] at h
  obtain rfl : c = r := by simpa using h
  exact (selectCommitted_eq_some _ _ hcv).2.2.1



omit [BEq State] in
private theorem mem_selectFrom_of_mem {cs : CompiledSpec State L} {bits ra ms : Nat} :
    ∀ i sel p, p ∈ sel → p ∈ selectFrom cs bits ra ms i sel := by
  intro i sel
  induction i, sel using selectFrom.induct (cs := cs) (bits := bits) (regionAlive := ra)
    (marksSeen := ms) with
  | case1 i sel hi ih =>
    intro p hp
    rw [selectFrom, if_pos hi]
    refine ih p ?_
    split <;> simp [hp]
  | case2 i sel hi =>
    intro p hp
    rw [selectFrom, if_neg hi]
    exact hp

omit [BEq State] in
private theorem mem_selectFrom {cs : CompiledSpec State L} {bits ra ms : Nat} :
    ∀ i sel p, p ∈ selectFrom cs bits ra ms i sel →
      p ∈ sel ∨ optionAvailable cs ra ms p = true := by
  intro i sel
  induction i, sel using selectFrom.induct (cs := cs) (bits := bits) (regionAlive := ra)
    (marksSeen := ms) with
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
        · exact Or.inr (selectPref_eq_some _ _ ho).2.2
      · exact Or.inl
    · exact Or.inr h
  | case2 i sel hi =>
    intro p hp
    rw [selectFrom, if_neg hi] at hp
    exact Or.inl hp

omit [BEq State] in
private theorem selectFrom_covers {cs : CompiledSpec State L} {bits ra ms : Nat} :
    ∀ i sel j, i ≤ j → j < cs.conjunctStart.size - 1 →
      (selectPref cs bits ra ms cs.conjunctStart[j]! cs.conjunctStart[j + 1]!).isSome = true →
      ∃ o ∈ selectFrom cs bits ra ms i sel, cs.conjunctStart[j]! ≤ o ∧
        o < cs.conjunctStart[j + 1]! ∧ optionAvailable cs ra ms o = true ∧
        ((selectCommitted cs bits ra ms
            cs.conjunctStart[j]! cs.conjunctStart[j + 1]!).isSome = true → bits.testBit o = true) := by
  intro i sel
  induction i, sel using selectFrom.induct (cs := cs) (bits := bits) (regionAlive := ra)
    (marksSeen := ms) with
  | case1 i sel hi ih =>
    intro j hij hj hsome
    rw [selectFrom, if_pos hi]
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hsome
      refine ⟨o, mem_selectFrom_of_mem _ _ o ?_, ?_, ?_, ?_, fun hc => selectPref_committed hc ho⟩
      · rw [ho]; simp
      · exact (selectPref_eq_some _ _ ho).1
      · exact (selectPref_eq_some _ _ ho).2.1
      · exact (selectPref_eq_some _ _ ho).2.2
    · exact ih j hlt hj hsome
  | case2 i sel hi =>
    intro j hij hj _
    omega

omit [BEq State] in
private theorem selectFrom_committed {cs : CompiledSpec State L} {bits ra ms : Nat}
    (hfc : ∀ j, j < cs.conjunctStart.size - 1 →
      (selectCommitted cs bits ra ms cs.conjunctStart[j]! cs.conjunctStart[j + 1]!).isSome = true) :
    ∀ i sel p, p ∈ selectFrom cs bits ra ms i sel → p ∈ sel ∨ bits.testBit p = true := by
  intro i sel
  induction i, sel using selectFrom.induct (cs := cs) (bits := bits) (regionAlive := ra)
    (marksSeen := ms) with
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
        · exact Or.inr (selectPref_committed (hfc i hi) ho)
      · exact Or.inl
    · exact Or.inr h
  | case2 i sel hi =>
    intro p hp
    rw [selectFrom, if_neg hi] at hp
    exact Or.inl hp

omit [BEq State] in
theorem selectedOptions_available (cs : CompiledSpec State L) (bits ra ms : Nat) :
    ∀ o ∈ selectedOptions cs bits ra ms, optionAvailable cs ra ms o = true := by
  intro o ho
  rcases mem_selectFrom 0 #[] o ho with h | h
  · simp at h
  · exact h

/-- When no conjunct is unsatisfied, `selectedOptions` holds an available option of every conjunct. -/
private theorem selectedOptions_covers {cs : CompiledSpec State L} (hwf : cs.WF) (bits ra ms : Nat)
    (h : firstUnsatisfied cs bits ra ms = none) :
    ∀ i < cs.spec.conjuncts.size, ∃ o ∈ selectedOptions cs bits ra ms,
      cs.conjunctStart[i]! ≤ o ∧ o < cs.conjunctStart[i + 1]! ∧
        optionAvailable cs ra ms o = true ∧
        ((selectCommitted cs bits ra ms
            cs.conjunctStart[i]! cs.conjunctStart[i + 1]!).isSome = true → bits.testBit o = true) := by
  intro i hi
  have hn : i < cs.conjunctStart.size - 1 := by rw [hwf.conjunctStart_size]; omega
  obtain ⟨o, h1, h2, h3⟩ := firstUnsatFrom_eq_none 0 h i (Nat.zero_le _) hn
  have hsome : (selectOne cs ra ms cs.conjunctStart[i]! cs.conjunctStart[i + 1]!).isSome = true := by
    rcases hsel : selectOne cs ra ms cs.conjunctStart[i]! cs.conjunctStart[i + 1]! with _ | r
    · have := (selectOne_eq_none cs.conjunctStart[i]!).mp hsel o h1 h2
      rw [h3] at this
      exact absurd this (by simp)
    · simp
  exact selectFrom_covers 0 #[] i (Nat.zero_le _) hn (selectPref_isSome hsome)

end ScanCorrect


section EdgeScan
variable [LawfulBEq State] [LawfulHashable State]

private theorem mem_foldl_insert (l : List State) (init : Std.HashSet State) (x : State) :
    x ∈ l.foldl (fun acc s => acc.insert s) init ↔ x ∈ init ∨ x ∈ l := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Std.HashSet.mem_insert, List.mem_cons, beq_iff_eq]
    grind

/-- The closing SCC as a set: the live stack from `lo` on. -/

@[expose] def sccSetOf (live : Array State) (lo : Nat) : Std.HashSet State :=
  (live.extract lo live.size).foldl
    (init := Std.HashSet.emptyWithCapacity (live.size - lo)) fun h x => h.insert x

/-- The flushed range read as a set. -/

theorem mem_sccSet {live : Array State} {lo n : Nat} {s : State} :
    s ∈ (live.extract lo live.size).foldl
        (init := Std.HashSet.emptyWithCapacity n) (fun h x => h.insert x) ↔
      s ∈ live.toList.drop lo := by
  rw [← Array.foldl_toList, mem_foldl_insert]
  simp only [Std.HashSet.not_mem_emptyWithCapacity, false_or, Array.toList_extract,
    List.take_of_length_le (by simp : (List.drop lo live.toList).length ≤ live.size - lo)]

/-! ## The SCC's internal edges

What the edge-aware scan is pointed at. A candidate's internal edges are enumerated from the states the
search has flushed, keeping the targets that stay inside the candidate. -/

/-- The edges of `states` that stay inside `B`, in walk order. -/
@[expose] def internalEdges (succs : State → Array State) (B : Std.HashSet State)
    (states : List State) : List (State × State) :=
  states.flatMap fun s => ((succs s).filter B.contains).toList.map fun t => (s, t)

omit [LawfulBEq State] [LawfulHashable State] in
theorem mem_internalEdges {succs : State → Array State}
    {B : Std.HashSet State} {states : List State} {e : State × State} :
    e ∈ internalEdges succs B states ↔ e.1 ∈ states ∧ e.2 ∈ succs e.1 ∧ e.2 ∈ B := by
  rw [internalEdges, List.mem_flatMap]
  constructor
  · rintro ⟨s, hs, hmem⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
    obtain ⟨h1, h2⟩ := Array.mem_filter.mp (Array.mem_def.mpr ht)
    exact ⟨hs, h1, Std.HashSet.mem_iff_contains.mpr h2⟩
  · rintro ⟨hs, h1, h2⟩
    refine ⟨e.1, hs, List.mem_map.mpr ⟨e.2, ?_, rfl⟩⟩
    simpa using Array.mem_filter.mpr ⟨h1, Std.HashSet.mem_iff_contains.mp h2⟩

/-! ## The edge scan decides `AvailableWith`

`StreettOption.onEdges` lives in `AbstractSpec/StreettSCCRegion.lean`; this is the bridge saying the scan's
verdict for one option is exactly the per-option half of `RStreettSpec.AvailableWith` on `B`. -/

omit [LawfulHashable State] in
/-- Region half: every internal edge of `B` has a realization satisfying the candidate's region `r` and
the option's together. -/
theorem optionRegion_onEdges {spec : RStreettSpec State L} {r : L → Bool} (opt : StreettOption L)
    (B : Std.HashSet State) (states : List State) (succs : State → Array State)
    (hstates : ∀ s, s ∈ states ↔ s ∈ B) :
    (∀ e ∈ internalEdges succs B states, (opt.onEdgesIn spec r).region e = true) ↔
      ∀ s ∈ B, ∀ t ∈ B, t ∈ succs s →
        t ∈ spec.regionSuccs (fun l => r l && opt.region l) s := by
  constructor
  · intro hreg s hs t ht hst
    exact Array.contains_iff_mem.mp
      (hreg (s, t) (mem_internalEdges.mpr ⟨(hstates s).mpr hs, hst, ht⟩))
  · intro hreg e he
    obtain ⟨h1, h2, h3⟩ := mem_internalEdges.mp he
    exact Array.contains_iff_mem.mpr (hreg e.1 ((hstates e.1).mp h1) e.2 h3 h2)

omit [LawfulHashable State] in
/-- Mark half: each of the option's marks is carried by an internal edge that is itself in-region.

The witnessing pair is required to be an edge of the graph the scan walks, not merely of the spec's
`opt.region ∧ g` restriction. On the whole product the two agree — `Compat.succs_sub` — but a *candidate*
runs on a strictly smaller graph, and there the extra conjunct is what ties the witness to an edge the scan
actually visited. Carrying it in the statement is what lets this bridge drop its `Compat` hypothesis, which
a candidate's graph cannot supply. -/
theorem optionMarks_onEdges {spec : RStreettSpec State L} {succs : State → Array State}
    {r : L → Bool} (opt : StreettOption L) (B : Std.HashSet State) (states : List State)
    (hstates : ∀ s, s ∈ states ↔ s ∈ B) :
    (∀ g ∈ (opt.onEdgesIn spec r).marks, ∃ e ∈ internalEdges succs B states, g e = true) ↔
      ∀ g ∈ opt.marks, ∃ s ∈ B, ∃ t ∈ B, t ∈ succs s ∧
        t ∈ spec.regionSuccs (fun l => r l && opt.region l && g l) s := by
  constructor
  · intro hmk g hg
    obtain ⟨e, he, hge⟩ := hmk _ (Array.mem_map.mpr ⟨g, hg, rfl⟩)
    obtain ⟨h1, hsucc, ht⟩ := mem_internalEdges.mp he
    exact ⟨e.1, (hstates e.1).mp h1, e.2, ht, hsucc, Array.contains_iff_mem.mp hge⟩
  · intro hmk g hg
    obtain ⟨g₀, hg₀, rfl⟩ := Array.mem_map.mp hg
    obtain ⟨s, hs, t, ht, hsucc, hst⟩ := hmk g₀ hg₀
    exact ⟨(s, t), mem_internalEdges.mpr ⟨(hstates s).mpr hs, hsucc, ht⟩,
      Array.contains_iff_mem.mpr hst⟩

/-- The masks the scan produces for the frame closing at `lo`: the two bitmasks folded over the closing
SCC's internal edges. This is the edge-aware replacement for `scanFrame cs succs live lo`. -/
@[expose] def scanFrame (cs : CompiledSpec State L) (succs : State → Array State)
    (live : Array State) (lo : Nat) : Nat × Nat :=
  scanLetters cs (internalEdges succs (sccSetOf live lo) (live.toList.drop lo))

end EdgeScan

/-! ## What the test decides on the flushed SCC

The scan and the per-conjunct test on `live.toList.drop lo`, the range POP flushes, read as the set the specification is
written against. -/

section FlushedSCC

private theorem getElem!_option (a : Array (StreettOption L)) (j : Nat) (h : j < a.size) :
    a[j]! = a[j]'h := getElem!_pos a j h

section SetOfRange
variable [LawfulBEq State] [LawfulHashable State]
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


/-- The mask says option `k` of conjunct `i` is available on `B` in the `AvailableWith` sense: every
internal edge of `B` has an in-region realization, and each of the option's marks is carried by an internal
edge that is itself in-region. -/
theorem optionAvailable_iff_availableIn {cs : CompiledSpec State L}
    {succs : State → Array State}
    (hwf : cs.WF) (live : Array State) (lo : Nat) {B : Std.HashSet State}
    (hB : ∀ s, s ∈ B ↔ s ∈ live.toList.drop lo) {i k : Nat}
    (hi : i < cs.spec.conjuncts.size) (hk : k < (cs.spec.conjuncts[i]!).size) :
    optionAvailable cs (scanFrame cs succs live lo).1 (scanFrame cs succs live lo).2
        (cs.conjunctStart[i]! + k) = true ↔
      ((∀ s ∈ B, ∀ t ∈ B, t ∈ succs s →
          t ∈ cs.spec.regionSuccs
            (fun l => cs.restrict l && ((cs.spec.conjuncts[i]!)[k]!).region l) s) ∧
        ∀ g ∈ ((cs.spec.conjuncts[i]!)[k]!).marks, ∃ s ∈ B, ∃ t ∈ B, t ∈ succs s ∧
          t ∈ cs.spec.regionSuccs
            (fun l => cs.restrict l && ((cs.spec.conjuncts[i]!)[k]!).region l && g l) s) := by
  have hst : ∀ s, s ∈ live.toList.drop lo ↔ s ∈ sccSetOf live lo := fun s => mem_sccSet.symm
  rw [optionAvailable, Bool.and_eq_true, scanFrame,
    scanLetters_fst_testBit cs _ _ (hwf.option_lt hi hk),
    optionLive_letters cs hwf _ _ (hwf.option_lt hi hk),
    hwf.option_region i hi k hk, hwf.option_marks i hi k hk,
    optionRegion_onEdges _ (sccSetOf live lo) (live.toList.drop lo) succs hst,
    optionMarks_onEdges _ (sccSetOf live lo) (live.toList.drop lo) hst]
  have hBS : ∀ s, s ∈ B ↔ s ∈ sccSetOf live lo := fun s => (hB s).trans (hst s)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun s hs t ht hsucc => h1 s ((hBS s).mp hs) t ((hBS t).mp ht) hsucc, fun g hg => ?_⟩
    obtain ⟨s, hs, t, ht, hgt⟩ := h2 g hg
    exact ⟨s, (hBS s).mpr hs, t, (hBS t).mpr ht, hgt⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun s hs t ht hsucc => h1 s ((hBS s).mpr hs) t ((hBS t).mpr ht) hsucc, fun g hg => ?_⟩
    obtain ⟨s, hs, t, ht, hgt⟩ := h2 g hg
    exact ⟨s, (hBS s).mp hs, t, (hBS t).mp ht, hgt⟩

/-- No unsatisfied conjunct means the flushed set is available with the options the scan selected. -/
theorem firstUnsatisfied_none_accepting {cs : CompiledSpec State L}
    {succs : State → Array State} {bits : Nat}
    (hwf : cs.WF) (live : Array State) (lo : Nat) {B : Std.HashSet State}
    (hB : ∀ s, s ∈ B ↔ s ∈ live.toList.drop lo)
    (h : firstUnsatisfied cs bits (scanFrame cs succs live lo).1 (scanFrame cs succs live lo).2 = none) :
    ∀ c ∈ cs.spec.conjuncts, ∃ opt ∈ c,
      (∀ s ∈ B, ∀ t ∈ B, t ∈ succs s →
        t ∈ cs.spec.regionSuccs (fun l => cs.restrict l && opt.region l) s) ∧
      ∀ g ∈ opt.marks, ∃ s ∈ B, ∃ t ∈ B, t ∈ succs s ∧
        t ∈ cs.spec.regionSuccs (fun l => cs.restrict l && opt.region l && g l) s := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hc
  have hce : cs.spec.conjuncts[i]! = cs.spec.conjuncts[i] := getElem!_pos _ i hi
  have hn : i < cs.conjunctStart.size - 1 := by rw [hwf.conjunctStart_size]; omega
  obtain ⟨o, h1, h2, h3⟩ := firstUnsatFrom_eq_none 0 h i (Nat.zero_le _) hn
  have hstep := hwf.start_succ i hi
  have hk : o - cs.conjunctStart[i]! < (cs.spec.conjuncts[i]!).size := by omega
  have hidx : cs.conjunctStart[i]! + (o - cs.conjunctStart[i]!) = o := by omega
  have hk2 : o - cs.conjunctStart[i]! < (cs.spec.conjuncts[i]).size := by rwa [hce] at hk
  refine ⟨(cs.spec.conjuncts[i]!)[o - cs.conjunctStart[i]!]!, ?_, ?_⟩
  · rw [hce, getElem!_option _ _ hk2]
    exact Array.getElem_mem _
  · rw [← optionAvailable_iff_availableIn hwf live lo hB hi hk, hidx]
    exact h3

/-- The blamed conjunct, together with every option of it whose marks are present in the flushed set.

The named index `o` comes back with the option's *letter-level* identity as well as its two edge readings:
the candidate machinery conjoins `cs.letterOptions[o]!.region` into the pruned candidate's bitmask, so the
pass has to know that this is the very option that was blamed. -/
theorem blamedBlock_blames {cs : CompiledSpec State L}
    {succs : State → Array State}
    (hwf : cs.WF) (live : Array State) (lo : Nat) {B : Std.HashSet State}
    (hB : ∀ s, s ∈ B ↔ s ∈ live.toList.drop lo) {opts : Array Nat} {j : Nat}
    (hjn : j < cs.conjunctStart.size - 1)
    (hmem : ∀ p, p ∈ opts ↔ cs.conjunctStart[j]! ≤ p ∧ p < cs.conjunctStart[j + 1]! ∧
      optionLive cs (scanFrame cs succs live lo).2 p = true) :
    ∃ c ∈ cs.spec.conjuncts, (∀ o ∈ opts, o < cs.numOptions) ∧
      ∀ opt ∈ c, (∀ g ∈ opt.marks, ∃ s ∈ B, ∃ t ∈ B, t ∈ succs s ∧
          t ∈ cs.spec.regionSuccs (fun l => cs.restrict l && opt.region l && g l) s) →
        ∃ o ∈ opts, cs.letterOptions[o]! = opt ∧
          cs.regions[o]! = (opt.onEdgesIn cs.spec cs.restrict).region ∧
          cs.optMarks[o]! = (opt.onEdgesIn cs.spec cs.restrict).marks := by
  have hst : ∀ s, s ∈ live.toList.drop lo ↔ s ∈ sccSetOf live lo := fun s => mem_sccSet.symm
  have hBS : ∀ s, s ∈ B ↔ s ∈ sccSetOf live lo := fun s => (hB s).trans (hst s)
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
    have hlive : optionLive cs (scanFrame cs succs live lo).2 (cs.conjunctStart[j]! + k) = true := by
      rw [scanFrame, optionLive_letters cs hwf _ _ (hwf.option_lt hj hk'),
        hwf.option_marks j hj k hk', hget,
        optionMarks_onEdges _ (sccSetOf live lo) (live.toList.drop lo) hst]
      intro g hg
      obtain ⟨s, hs, t, ht, hsucc, hgt⟩ := hpres g hg
      exact ⟨s, (hBS s).mp hs, t, (hBS t).mp ht, hsucc, hgt⟩
    refine ⟨cs.conjunctStart[j]! + k, (hmem _).mpr ⟨Nat.le_add_right _ _, by omega, hlive⟩, ?_, ?_, ?_⟩
    · rw [hwf.letter_option j hj k hk', hget]
    · rw [hwf.option_region j hj k hk', hget]
    · rw [hwf.option_marks j hj k hk', hget]

end SetOfRange

section Decrease
variable [LawfulBEq State] [LawfulHashable State]

omit [Hashable State] [LawfulBEq State] [LawfulHashable State] in
/-- Every option the scan blames is one of the compiled options. -/
private theorem firstUnsatisfied_opt_lt {cs : CompiledSpec State L} (hwf : cs.WF) {bits ra ms : Nat}
    {opts : Array Nat} (hfu : firstUnsatisfied cs bits ra ms = some opts) {o : Nat} (ho : o ∈ opts) :
    o < cs.numOptions := by
  obtain ⟨j, _, hjn, _, hmem⟩ := firstUnsatFrom_eq_some 0 opts hfu
  obtain ⟨_, hlo, hhi, _⟩ := (hmem o).mp ho
  have hj : j < cs.spec.conjuncts.size := by rw [hwf.conjunctStart_size] at hjn; omega
  have h1 := hwf.start_mono cs.spec.conjuncts.size (Nat.le_refl _) (j + 1) hj
  have h2 := hwf.numOptions_eq
  omega


omit [Hashable State] [LawfulBEq State] [LawfulHashable State] in
/-- The blame names only compiled options. -/
private theorem blamed_opt_lt {cs : CompiledSpec State L} (hwf : cs.WF) {bits ra ms : Nat}
    {opts : Array Nat} (hfu : firstUnsatisfied cs bits ra ms = some opts)
    {o : Nat} (ho : o ∈ opts) : o < cs.numOptions :=
  firstUnsatisfied_opt_lt hwf hfu ho

omit [LawfulHashable State] in
/-- A committed option's region bit survives the scan: with the bit set, the candidate's region entails
that option's, so every edge of the graph the search walked already has an in-region realization. -/
private theorem committed_region_bit {cs : CompiledSpec State L} {curRegions : Nat}
    {succs : State → Array State}
    (hwf : cs.WF) (hmono : cs.spec.Mono) (hres : LePred (regionOf cs curRegions) cs.restrict)
    (hgraph : ∀ s t, t ∈ succs s → t ∈ cs.spec.regionSuccs (regionOf cs curRegions) s)
    (live : Array State) (lo : Nat) {o : Nat} (ho : o < cs.numOptions)
    (hset : curRegions.testBit o = true) :
    (scanFrame cs succs live lo).1.testBit o = true := by
  have hall : ∀ e ∈ internalEdges succs (sccSetOf live lo) (live.toList.drop lo),
      cs.regions[o]! e = true := by
    intro e he
    obtain ⟨-, hsucc, -⟩ := mem_internalEdges.mp he
    rw [hwf.regions_getElem ho]
    refine Array.contains_iff_mem.mpr
      (hmono.succs_mono (r := fun l => cs.restrict l && (cs.letterOptions[o]!).region l)
        (fun l hl => ?_) e.1 e.2 (hgraph e.1 e.2 hsucc))
    exact Bool.and_eq_true _ _ |>.mpr ⟨hres l hl, regionOf_le ho hset l hl⟩
  rw [scanFrame, scanLetters_fst_testBit cs _ _ ho]
  exact hall

/-- The blamed conjunct of an unsatisfied scan. Either the candidate has already committed to an option of it,
whose marks are then not all witnessed, or the blame covers every option of it whose marks are witnessed. -/
theorem firstUnsatisfied_some_blames {cs : CompiledSpec State L} {curRegions : Nat}
    {succs : State → Array State}
    (hwf : cs.WF) (hmono : cs.spec.Mono) (hres : LePred (regionOf cs curRegions) cs.restrict)
    (hgraph : ∀ s t, t ∈ succs s → t ∈ cs.spec.regionSuccs (regionOf cs curRegions) s)
    (live : Array State) (lo : Nat) {B : Std.HashSet State}
    (hB : ∀ s, s ∈ B ↔ s ∈ live.toList.drop lo) {opts : Array Nat}
    (h : firstUnsatisfied cs curRegions (scanFrame cs succs live lo).1 (scanFrame cs succs live lo).2
      = some opts) :
    ∃ c ∈ cs.spec.conjuncts, (∀ o ∈ opts, o < cs.numOptions) ∧
      ((∃ k < cs.numOptions, curRegions.testBit k = true ∧ cs.letterOptions[k]! ∈ c ∧
          ¬ ∀ g ∈ (cs.letterOptions[k]!).marks, ∃ s ∈ B, ∃ t ∈ B, t ∈ succs s ∧
            t ∈ cs.spec.regionSuccs
              (fun l => cs.restrict l && (cs.letterOptions[k]!).region l && g l) s) ∨
        ∀ opt ∈ c, (∀ g ∈ opt.marks, ∃ s ∈ B, ∃ t ∈ B, t ∈ succs s ∧
            t ∈ cs.spec.regionSuccs (fun l => cs.restrict l && opt.region l && g l) s) →
          ∃ o ∈ opts, cs.letterOptions[o]! = opt ∧
            cs.regions[o]! = (opt.onEdgesIn cs.spec cs.restrict).region ∧
            cs.optMarks[o]! = (opt.onEdgesIn cs.spec cs.restrict).marks) := by
  obtain ⟨j, _, hjn, hnotavail, hmem⟩ := firstUnsatFrom_eq_some 0 opts h
  rcases hany : anyBitIn curRegions cs.conjunctStart[j]! cs.conjunctStart[j + 1]! with _ | _
  · obtain ⟨c, hc, hlt, hall⟩ := blamedBlock_blames hwf live lo hB hjn
      fun p => (hmem p).trans ⟨fun hp => hp.2, fun hp => ⟨hany, hp⟩⟩
    exact ⟨c, hc, hlt, Or.inr hall⟩
  -- a committed option's region bit survives the scan, so it is unavailable on its marks
  obtain ⟨k, hlo, hhi, hbit⟩ := anyBitIn_eq_true_iff.mp hany
  have hj : j < cs.spec.conjuncts.size := by rw [hwf.conjunctStart_size] at hjn; omega
  have hce : cs.spec.conjuncts[j]! = cs.spec.conjuncts[j] := getElem!_pos _ j hj
  have hstep := hwf.start_succ j hj
  obtain ⟨k, rfl⟩ : ∃ k', k = cs.conjunctStart[j]! + k' := ⟨k - cs.conjunctStart[j]!, by omega⟩
  have hk : k < (cs.spec.conjuncts[j]!).size := by omega
  have hkn := hwf.option_lt hj hk
  have hst : ∀ s, s ∈ live.toList.drop lo ↔ s ∈ sccSetOf live lo := fun s => mem_sccSet.symm
  have hBS : ∀ s, s ∈ B ↔ s ∈ sccSetOf live lo := fun s => (hB s).trans (hst s)
  refine ⟨cs.spec.conjuncts[j]!, by rw [hce]; exact Array.getElem_mem _,
    fun o ho => Bool.noConfusion (hany.symm.trans ((hmem o).mp ho).1),
    Or.inl ⟨_, hkn, hbit, ?_, fun hpres => ?_⟩⟩
  · have hk2 : k < (cs.spec.conjuncts[j]).size := by rwa [hce] at hk
    rw [hwf.letter_option j hj k hk, hce, getElem!_option _ _ hk2]
    exact Array.getElem_mem _
  · rw [hwf.letter_option j hj k hk] at hpres
    have hlive : optionLive cs (scanFrame cs succs live lo).2 (cs.conjunctStart[j]! + k) = true := by
      rw [scanFrame, optionLive_letters cs hwf _ _ hkn, hwf.option_marks j hj k hk,
        optionMarks_onEdges _ (sccSetOf live lo) (live.toList.drop lo) hst]
      intro g hg
      obtain ⟨s, hs, t, ht, hsucc, hgt⟩ := hpres g hg
      exact ⟨s, (hBS s).mp hs, t, (hBS t).mp ht, hsucc, hgt⟩
    have hav := hnotavail _ hlo hhi
    rw [optionAvailable, committed_region_bit hwf hmono hres hgraph live lo hkn hbit, hlive] at hav
    exact Bool.noConfusion hav

/-- The blame names a conjunct. `firstUnsatisfied` is the only blame reason, so this is
`firstUnsatisfied_some_blames`. -/
theorem blamed_some_blames {cs : CompiledSpec State L} {curRegions : Nat}
    {succs : State → Array State}
    (hwf : cs.WF) (hmono : cs.spec.Mono) (hres : LePred (regionOf cs curRegions) cs.restrict)
    (hgraph : ∀ s t, t ∈ succs s → t ∈ cs.spec.regionSuccs (regionOf cs curRegions) s)
    (live : Array State) (lo : Nat) {B : Std.HashSet State}
    (hB : ∀ s, s ∈ B ↔ s ∈ live.toList.drop lo) {opts : Array Nat}
    (h : firstUnsatisfied cs curRegions (scanFrame cs succs live lo).1 (scanFrame cs succs live lo).2
      = some opts) :
    ∃ c ∈ cs.spec.conjuncts, (∀ o ∈ opts, o < cs.numOptions) ∧
      ((∃ k < cs.numOptions, curRegions.testBit k = true ∧ cs.letterOptions[k]! ∈ c ∧
          ¬ ∀ g ∈ (cs.letterOptions[k]!).marks, ∃ s ∈ B, ∃ t ∈ B, t ∈ succs s ∧
            t ∈ cs.spec.regionSuccs
              (fun l => cs.restrict l && (cs.letterOptions[k]!).region l && g l) s) ∨
        ∀ opt ∈ c, (∀ g ∈ opt.marks, ∃ s ∈ B, ∃ t ∈ B, t ∈ succs s ∧
            t ∈ cs.spec.regionSuccs (fun l => cs.restrict l && opt.region l && g l) s) →
          ∃ o ∈ opts, cs.letterOptions[o]! = opt ∧
            cs.regions[o]! = (opt.onEdgesIn cs.spec cs.restrict).region ∧
            cs.optMarks[o]! = (opt.onEdgesIn cs.spec cs.restrict).marks) :=
  firstUnsatisfied_some_blames hwf hmono hres hgraph live lo hB h

end Decrease

end FlushedSCC

/-! ## PUSH, UPDATE and POP -/

/-- A fresh frame is its own lowlink with no marks and no internal edge yet. All three operations destructure the
search state rather than using `{ aux with … }`, so the arrays are updated in place instead of copied. -/
@[expose] def streettPush (aux : StreettAux State) (q : State) (_marks : Std.HashSet Nat) :
    StreettAux State × Nat :=
  let ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  let pos := live.size
  (⟨live.push q, liveIndex.insert q pos, dead, dstack.push (pos, 0), wit, wopts, pending⟩, pos)

/-- A back-edge lowers the top frame's lowlink and folds in the edge's marks and the internal-edge bit. It never
reports, an SCC only being decided once complete. -/
@[expose] def streettUpdate (numMarks : Nat) (aux : StreettAux State) (marks : Std.HashSet Nat) (d : State) :
    StreettAux State × Bool :=
  let ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  match dstack.back? with
  | none => (⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩, false)
  | some (ll, acc) =>
    let top := (min ll (liveIndex.getD d 0), acc ||| marksToBitmask marks ||| (1 <<< numMarks))
    (⟨live, liveIndex, dead, dstack.pop.push top, wit, wopts, pending⟩, false)

/-- POP, where a closing frame either merges into its parent or completes an SCC and runs the test. A completed SCC
is always flushed, whether it passes, is discarded, or is queued for pruning. -/
@[expose] def streettPop [Inhabited State] (cs : CompiledSpec State L) (curRegions : Nat)
    (succs : State → Array State) (aux : StreettAux State)
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
        -- the scan walks the closing SCC's internal *edges*, not its states
        let (regionAlive, marksSeen) := scanFrame cs succs live step.pos
        -- An edge prune need not drop a state, so a blamed candidate keeps the SCC and gains a region bit. Options already
        -- conjoined are skipped, so that bit is fresh by construction, and termination needs no hypothesis about the graph
        -- the search ran on. `blamed_bit_new` says the skip drops no blamed option.
        let blame : Array Nat → Array (Candidate State) := fun liveOpts =>
          liveOpts.foldl (init := pending) fun ps o =>
            let C : Candidate State := ⟨sccSetOf live step.pos, curRegions ||| (1 <<< o)⟩
            if C.states.isEmpty || curRegions.testBit o then ps else ps.push C
        match firstUnsatisfied cs curRegions regionAlive marksSeen with
        | none =>
          -- Every conjunct has an available option, so the SCC is reported. Jointness of the selection
          -- is guaranteed by the *caller*: `LSys.StateOnly` regions hold at the source state and so keep
          -- every step out of them, which makes the per-option verdicts compose. Properties whose
          -- hoisted regions mention an edge atom do not satisfy that and are routed to the crossing
          -- before they reach here — `Veil.LivenessMC.checkFair`, `EdgeLabels.md` §17.
          let wit' := live.extract step.pos live.size
          let wopts' := selectedOptions cs curRegions regionAlive marksSeen
          let (live', liveIndex', dead') := liveFlush live liveIndex dead step.pos
          (⟨live', liveIndex', dead', dstack, wit', wopts', pending⟩, true)
        | some liveOpts =>
          let (live', liveIndex', dead') := liveFlush live liveIndex dead step.pos
          (⟨live', liveIndex', dead', dstack, wit, wopts, blame liveOpts⟩, false)
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
@[expose] def streettOps [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (curRegions : Nat) : DFSOps State where
  Aux := StreettAux State
  Position := Nat
  initAux := streettInitAux
  sccHint := streettSccHint
  numExplored := fun aux => aux.live.size + aux.dead.size
  getStatus := streettGetStatus
  push := streettPush
  update := streettUpdate cs.numMarks
  pop := fun succs _edgeMarks aux step => streettPop cs curRegions succs aux step

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
private theorem streettPop_triple [Inhabited State] (cs : CompiledSpec State L) (curRegions : Nat)
    (succs : State → Array State)
    (aux : StreettAux State) (step : DFSStep State Nat) :
    ((streettPop cs curRegions succs aux step).1.live, (streettPop cs curRegions succs aux step).1.liveIndex,
        (streettPop cs curRegions succs aux step).1.dead) = (aux.live, aux.liveIndex, aux.dead) ∨
      ((streettPop cs curRegions succs aux step).1.live, (streettPop cs curRegions succs aux step).1.liveIndex,
        (streettPop cs curRegions succs aux step).1.dead) = liveFlush aux.live aux.liveIndex aux.dead step.pos := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  rcases hb : dstack.back? with _ | ⟨ll, acc⟩
  · exact Or.inl (by simp only [streettPop, hb])
  · by_cases h : ll = step.pos
    · by_cases hacc : acc != fullAccMask cs.numMarks
      · exact Or.inr (by simp only [streettPop, hb, if_pos h, if_pos hacc])
      · rcases hfu : firstUnsatisfied cs curRegions (scanFrame cs succs live step.pos).1
            (scanFrame cs succs live step.pos).2 with _ | opts
        · exact Or.inr (by simp only [streettPop, hb, if_pos h, if_neg hacc, hfu])
        · exact Or.inr (by simp only [streettPop, hb, if_pos h, if_neg hacc, hfu])
    · rcases hb2 : dstack.pop.back? with _ | ⟨pll, pacc⟩
      · exact Or.inl (by simp only [streettPop, hb, if_neg h, hb2])
      · exact Or.inl (by simp only [streettPop, hb, if_neg h, hb2])

/-- POP reports only at a closing frame whose accumulator is full and whose scan blames no conjunct, recording the
flushed range as the witness and the selected options beside it. -/
private theorem streettPop_eq_true [Inhabited State] {cs : CompiledSpec State L} {curRegions : Nat}
    {succs : State → Array State}
    {aux aux' : StreettAux State} {step : DFSStep State Nat} (h : streettPop cs curRegions succs aux step = (aux', true)) :
    aux.dstack.back? = some (step.pos, fullAccMask cs.numMarks) ∧
      aux'.witness = aux.live.extract step.pos aux.live.size ∧
      firstUnsatisfied cs curRegions (scanFrame cs succs aux.live step.pos).1 (scanFrame cs succs aux.live step.pos).2 = none ∧
      aux'.witnessOpts =
        selectedOptions cs curRegions (scanFrame cs succs aux.live step.pos).1
          (scanFrame cs succs aux.live step.pos).2 := by
  have h2 : (streettPop cs curRegions succs aux step).2 = true := by rw [h]
  have hw : aux'.witness = (streettPop cs curRegions succs aux step).1.witness := by rw [h]
  have ho : aux'.witnessOpts = (streettPop cs curRegions succs aux step).1.witnessOpts := by rw [h]
  rw [hw, ho]
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  rcases hb : dstack.back? with _ | ⟨ll, acc⟩
  · simp only [streettPop, hb, Bool.false_eq_true] at h2
  · by_cases hll : ll = step.pos
    · by_cases hacc : acc != fullAccMask cs.numMarks
      · simp only [streettPop, hb, if_pos hll, if_pos hacc, Bool.false_eq_true] at h2
      · have hacc' : acc = fullAccMask cs.numMarks := by simpa using hacc
        rcases hfu : firstUnsatisfied cs curRegions (scanFrame cs succs live step.pos).1
            (scanFrame cs succs live step.pos).2 with _ | opts
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
private theorem streettPop_pending [Inhabited State] (cs : CompiledSpec State L) (curRegions : Nat)
    (succs : State → Array State)
    (aux : StreettAux State) (step : DFSStep State Nat) (P : Candidate State)
    (hP : P ∈ (streettPop cs curRegions succs aux step).1.pending) :
    P ∈ aux.pending ∨ ∃ opts o,
      firstUnsatisfied cs curRegions (scanFrame cs succs aux.live step.pos).1
          (scanFrame cs succs aux.live step.pos).2 = some opts ∧ o ∈ opts ∧
      curRegions.testBit o = false ∧
      P = ⟨sccSetOf aux.live step.pos, curRegions ||| (1 <<< o)⟩ := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  rcases hb : dstack.back? with _ | ⟨ll, acc⟩
  · exact Or.inl (by simpa only [streettPop, hb] using hP)
  · by_cases h : ll = step.pos
    · by_cases hacc : acc != fullAccMask cs.numMarks
      · exact Or.inl (by simpa only [streettPop, hb, if_pos h, if_pos hacc] using hP)
      · rcases hfu : firstUnsatisfied cs curRegions (scanFrame cs succs live step.pos).1
            (scanFrame cs succs live step.pos).2 with _ | opts
        · exact Or.inl (by simpa only [streettPop, hb, if_pos h, if_neg hacc, hfu] using hP)
        · simp only [streettPop, hb, if_pos h, if_neg hacc, hfu] at hP
          rw [← Array.foldl_toList] at hP
          rcases (mem_foldl_push_cond _ _ opts.toList pending P).mp hP with hP' | ⟨o, ho, hguard, hPo⟩
          · exact Or.inl hP'
          · refine Or.inr ⟨opts, o, rfl, by simpa using ho, ?_, hPo⟩
            simpa using (Bool.or_eq_false_iff.mp hguard).2
    · rcases hb2 : dstack.pop.back? with _ | ⟨pll, pacc⟩
      · exact Or.inl (by simpa only [streettPop, hb, if_neg h, hb2] using hP)
      · exact Or.inl (by simpa only [streettPop, hb, if_neg h, hb2] using hP)

/-- A touched state is still live or has joined the dead after POP. -/
private theorem streettPop_touched_mono [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (curRegions : Nat)
    (succs : State → Array State) (aux : StreettAux State) (step : DFSStep State Nat) (s : State)
    (h : s ∈ aux.live ∨ s ∈ aux.dead) :
    s ∈ (streettPop cs curRegions succs aux step).1.live ∨ s ∈ (streettPop cs curRegions succs aux step).1.dead := by
  rcases streettPop_triple cs curRegions succs aux step with ht | ht
  · have h1 : (streettPop cs curRegions succs aux step).1.live = aux.live := congrArg (fun t => t.1) ht
    have h3 : (streettPop cs curRegions succs aux step).1.dead = aux.dead := congrArg (fun t => t.2.2) ht
    rw [h1, h3]; exact h
  · have h1 : (streettPop cs curRegions succs aux step).1.live =
        (liveFlush aux.live aux.liveIndex aux.dead step.pos).1 := congrArg (fun t => t.1) ht
    have h3 : (streettPop cs curRegions succs aux step).1.dead =
        (liveFlush aux.live aux.liveIndex aux.dead step.pos).2.2 := congrArg (fun t => t.2.2) ht
    rw [h1, h3]
    exact liveFlush_touched_mono step.pos aux.live aux.liveIndex aux.dead s h

/-- The prune's search invariant: `LiveWF` on the live bookkeeping, every queued candidate drawn from the states touched so far,
and every queued candidate carrying the search's bitmask plus one option it lacked, which bounds the prune. -/
structure StreettWF [Inhabited State] (cs : CompiledSpec State L) (curRegions : Nat)
    (aux : StreettAux State) : Prop where
  live : LiveWF aux.live aux.liveIndex
  pending_states : ∀ P ∈ aux.pending, ∀ s ∈ P.states, s ∈ aux.live ∨ s ∈ aux.dead
  pending_fresh : ∀ P ∈ aux.pending, ∃ o, o < cs.numOptions ∧ curRegions.testBit o = false ∧
    P.regions = curRegions ||| (1 <<< o)

/-- `streettOps` is a lawful refinement: PUSH, UPDATE and POP preserve `StreettWF`, and the three status laws hold. -/
def streettLawful [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (curRegions : Nat)
    (hcs : cs.WF) : LawfulDFSOps (streettOps cs curRegions) (State := State) where
  WellFormed := StreettWF cs curRegions
  wf_push := fun aux q marks hq hwf => by
    show StreettWF cs curRegions (streettPush aux q marks).1
    obtain ⟨hl, hli, hd, hp⟩ := streettPush_fields aux q marks
    refine ⟨?_, ?_, ?_⟩
    · rw [hl, hli]
      refine hwf.live.push ?_
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      rw [show (streettOps cs curRegions).getStatus aux q = liveStatusOf aux.liveIndex aux.dead q from rfl,
        liveStatusOf, if_pos hc] at hq
      exact absurd hq (by simp)
    · rw [hl, hd, hp]
      intro P hP
      exact fun s hs => (hwf.pending_states P hP s hs).imp (fun h => Array.mem_push.mpr (Or.inl h)) id
    · rw [hp]; exact hwf.pending_fresh
  wf_update := fun aux marks d hwf => by
    show StreettWF cs curRegions (streettUpdate cs.numMarks aux marks d).1
    obtain ⟨hl, hli, hd, hp⟩ := streettUpdate_fields cs.numMarks aux marks d
    exact ⟨by rw [hl, hli]; exact hwf.live, by rw [hl, hd, hp]; exact hwf.pending_states,
      by rw [hp]; exact hwf.pending_fresh⟩
  wf_pop := fun succs _edgeMarks aux step hwf => by
    show StreettWF cs curRegions (streettPop cs curRegions succs aux step).1
    refine ⟨?_, fun P hP => ?_, fun P hP => ?_⟩
    · rcases streettPop_triple cs curRegions succs aux step with h | h
      · have h1 : (streettPop cs curRegions succs aux step).1.live = aux.live := congrArg (fun t => t.1) h
        have h2 : (streettPop cs curRegions succs aux step).1.liveIndex = aux.liveIndex := congrArg (fun t => t.2.1) h
        rw [h1, h2]
        exact hwf.live
      · have h1 : (streettPop cs curRegions succs aux step).1.live =
            (liveFlush aux.live aux.liveIndex aux.dead step.pos).1 := congrArg (fun t => t.1) h
        have h2 : (streettPop cs curRegions succs aux step).1.liveIndex =
            (liveFlush aux.live aux.liveIndex aux.dead step.pos).2.1 := congrArg (fun t => t.2.1) h
        rw [h1, h2]
        exact hwf.live.flush step.pos
    · rcases streettPop_pending cs curRegions succs aux step P hP with hold | ⟨opts, o, hfu, ho, -, rfl⟩
      · exact fun s hs =>
          streettPop_touched_mono cs curRegions succs aux step s (hwf.pending_states P hold s hs)
      · -- the queued candidate carries the closing SCC, every state of which is live
        intro s hs
        have hlive : s ∈ aux.live :=
          Array.mem_def.mpr (List.mem_of_mem_drop (mem_sccSet.mp hs))
        exact streettPop_touched_mono cs curRegions succs aux step s (Or.inl hlive)
    · rcases streettPop_pending cs curRegions succs aux step P hP with hold | ⟨opts, o, hfu, ho, hfresh, rfl⟩
      · exact hwf.pending_fresh P hold
      · exact ⟨o, blamed_opt_lt hcs hfu ho, hfresh, rfl⟩
  push_status := fun aux q marks q' => liveStatusOf_insert aux.liveIndex aux.dead q aux.live.size q'
  update_status := fun aux marks d q => by
    show liveStatusOf (streettUpdate cs.numMarks aux marks d).1.liveIndex
      (streettUpdate cs.numMarks aux marks d).1.dead q = liveStatusOf aux.liveIndex aux.dead q
    obtain ⟨_, hli, hd, _⟩ := streettUpdate_fields cs.numMarks aux marks d
    rw [hli, hd]
  pop_status := fun succs _edgeMarks aux step q hwf => by
    show liveStatusOf (streettPop cs curRegions succs aux step).1.liveIndex (streettPop cs curRegions succs aux step).1.dead q =
        liveStatusOf aux.liveIndex aux.dead q ∨
      (liveStatusOf aux.liveIndex aux.dead q = .live ∧
        liveStatusOf (streettPop cs curRegions succs aux step).1.liveIndex (streettPop cs curRegions succs aux step).1.dead q = .dead)
    rcases streettPop_triple cs curRegions succs aux step with h | h
    · have h2 : (streettPop cs curRegions succs aux step).1.liveIndex = aux.liveIndex := congrArg (fun t => t.2.1) h
      have h3 : (streettPop cs curRegions succs aux step).1.dead = aux.dead := congrArg (fun t => t.2.2) h
      rw [h2, h3]
      exact Or.inl rfl
    · have h2 : (streettPop cs curRegions succs aux step).1.liveIndex =
          (liveFlush aux.live aux.liveIndex aux.dead step.pos).2.1 := congrArg (fun t => t.2.1) h
      have h3 : (streettPop cs curRegions succs aux step).1.dead =
          (liveFlush aux.live aux.liveIndex aux.dead step.pos).2.2 := congrArg (fun t => t.2.2) h
      rw [h2, h3]
      exact (liveFlush_spec step.pos aux.live aux.liveIndex aux.dead hwf.live.fwd hwf.live.bwd).2.2 q

/-- The prune's view of its search state for the flush-enumeration contract. -/
@[expose] def streettView [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (curRegions : Nat) :
    LowlinkView (streettOps cs curRegions) where
  live := fun aux => aux.live
  liveIndex := fun aux => aux.liveIndex
  dead := fun aux => aux.dead
  lowlinks := fun aux => aux.dstack.map (·.1)
  accs := fun aux => aux.dstack.map (·.2)
  extraAcc := 1 <<< cs.numMarks
  posNat := id

/-- The prune's search obeys the shared lowlink discipline. -/
theorem streettLowlinkLawful [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (curRegions : Nat) : LowlinkLawful (streettOps cs curRegions) (streettView cs curRegions) where
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
      · rcases hfu : firstUnsatisfied cs curRegions (scanFrame cs succs live step.pos).1
            (scanFrame cs succs live step.pos).2 with _ | opts
        · simp only [streettView, streettOps, streettPop, hb, if_pos hll', if_neg hacc, hfu]
          rfl
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

private theorem streettPop_pending_mono [Inhabited State] (cs : CompiledSpec State L) (curRegions : Nat)
    (succs : State → Array State)
    (aux : StreettAux State) (step : DFSStep State Nat) (P : Candidate State)
    (hP : P ∈ aux.pending) :
    P ∈ (streettPop cs curRegions succs aux step).1.pending := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  rcases hb : dstack.back? with _ | ⟨ll, acc⟩
  · simpa only [streettPop, hb] using hP
  · by_cases h : ll = step.pos
    · by_cases hacc : acc != fullAccMask cs.numMarks
      · simpa only [streettPop, hb, if_pos h, if_pos hacc] using hP
      · rcases hfu : firstUnsatisfied cs curRegions (scanFrame cs succs live step.pos).1
            (scanFrame cs succs live step.pos).2 with _ | opts
        · simpa only [streettPop, hb, if_pos h, if_neg hacc, hfu] using hP
        · simp only [streettPop, hb, if_pos h, if_neg hacc, hfu]
          rw [← Array.foldl_toList]
          exact (mem_foldl_push_cond _ _ opts.toList pending P).mpr (Or.inl hP)
    · rcases hb2 : dstack.pop.back? with _ | ⟨pll, pacc⟩
      · simpa only [streettPop, hb, if_neg h, hb2] using hP
      · simpa only [streettPop, hb, if_neg h, hb2] using hP

private theorem streettMonotone [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    (cs : CompiledSpec State L) (curRegions : Nat) :
    MonotoneAlong (streettOps cs curRegions) (fun a b : StreettAux State => ∀ P ∈ a.pending, P ∈ b.pending) where
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
  pop := fun succs _ a step P hP => streettPop_pending_mono cs curRegions succs a step P hP

/-- A closing POP with a full accumulator that does not report has blamed a conjunct, and queued the pruned
candidate of each option it named unless that candidate is empty. -/
private theorem streettPop_queues [Inhabited State] [LawfulBEq State] [LawfulHashable State]
    {cs : CompiledSpec State L} {curRegions : Nat}
    {succs : State → Array State} {aux aux' : StreettAux State} {step : DFSStep State Nat}
    (hcl : (streettView cs curRegions).closes aux step = true)
    (hfull : (streettView cs curRegions).accAt aux 0 = fullAccMask cs.numMarks)
    (h : streettPop cs curRegions succs aux step = (aux', false)) :
    ∃ opts,
      firstUnsatisfied cs curRegions (scanFrame cs succs aux.live step.pos).1
          (scanFrame cs succs aux.live step.pos).2 = some opts ∧
      ∀ o ∈ opts, (sccSetOf aux.live step.pos).isEmpty = true ∨ curRegions.testBit o = true ∨
        (⟨sccSetOf aux.live step.pos, curRegions ||| (1 <<< o)⟩ : Candidate State)
          ∈ aux'.pending := by
  obtain ⟨x, hb, hx1⟩ : ∃ x, aux.dstack.back? = some x ∧ x.1 = step.pos := by
    simp only [LowlinkView.closes, streettView, Array.back?_map, beq_iff_eq, Option.map_eq_some_iff] at hcl
    exact hcl
  have hx2 : x.2 = fullAccMask cs.numMarks := by
    rw [← hfull]
    exact (revGetD_zero (by simp [streettView, Array.back?_map, hb])).symm
  have h2 : (streettPop cs curRegions succs aux step).2 = false := by rw [h]
  have hp : aux'.pending = (streettPop cs curRegions succs aux step).1.pending := by rw [h]
  rw [hp]
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  obtain ⟨ll, acc⟩ := x
  have hb' : dstack.back? = some (ll, acc) := hb
  have hll : ll = step.pos := hx1
  have hacc0 : acc = fullAccMask cs.numMarks := hx2
  subst hll hacc0
  have hacc : ¬ ((fullAccMask cs.numMarks != fullAccMask cs.numMarks) = true) := by simp
  rcases hfu : firstUnsatisfied cs curRegions (scanFrame cs succs live step.pos).1 (scanFrame cs succs live step.pos).2
    with _ | opts
  · simp only [streettPop, hb', if_neg hacc, hfu] at h2
    exact absurd h2 (by simp)
  · refine ⟨opts, rfl, fun o ho => ?_⟩
    simp only [streettPop, hb', if_neg hacc, hfu]
    rw [← Array.foldl_toList]
    by_cases he : (sccSetOf live step.pos).isEmpty = true
    · exact Or.inl he
    · by_cases hbit : curRegions.testBit o = true
      · exact Or.inr (Or.inl hbit)
      · refine Or.inr (Or.inr ((mem_foldl_push_cond _ _ opts.toList pending _).mpr
          (Or.inr ⟨o, by simpa using ho, ?_, rfl⟩)))
        simp [he, hbit]

/-! ## The outer loop -/

variable [Inhabited State] [LawfulBEq State] [LawfulHashable State]

/-- One search, over the whole product or over one pruned candidate. -/
@[expose] def streettRun (cs : CompiledSpec State L) (curRegions : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) (initialStates : List State) :
    Option (State × List State) × StreettAux State :=
  genericDFS (streettOps cs curRegions) succs edgeMarks expand initialStates
    (streettOps cs curRegions).initAux

/-- The fused expansion restricted to a pruned candidate: the caller's `expand` filtered in lockstep, so the
recursive runs inherit the fusion instead of re-deriving each edge's marks. -/
def sccExpand (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) (C : Std.HashSet State) :
    State → Array State × Array (Std.HashSet Nat) × Array Nat :=
  fun s => filterExpand (expand s) C.contains

omit [Inhabited State] [LawfulBEq State] [LawfulHashable State] in
theorem sccExpand_coherent {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat}
    {expand : State → Array State × Array (Std.HashSet Nat) × Array Nat}
    (hexp : ExpandCoherent succs edgeMarks expand) (C : Std.HashSet State) :
    ExpandCoherent (sccSuccs succs C) edgeMarks (sccExpand expand C) :=
  fun s => filterExpand_fst_snd _ (hexp s)

/-- The search one pruned candidate gets: its own restricted graph, marks and fused expansion — and its
own *compiled spec*, recompiled at the region its bitmask denotes.

Recompiling is the whole of `EdgeLabels.md` §12's first half. An option's edge reading has to be taken
inside the candidate's region, not beside it: otherwise the scan can see a mark on a realization the
candidate's region excludes, and two conjuncts end up witnessed by realizations no single run can take. -/
@[expose] def candidateRun (cs : CompiledSpec State L) (rspec : RStreettSpec State L) (c : Candidate State) :
    Option (State × List State) × StreettAux State :=
  streettRun (cs.atBits c.regions) c.regions (c.graph cs rspec)
    (rspec.regionMarks (c.region cs)) (c.expand cs rspec) c.states.toList

/-- Drain the queue of pruned candidates, each searched on the subgraph it induces. New candidates go to
the front, so the deepest prune is finished first and a witness is reached without draining the siblings. -/
@[expose] def pruneLoop (cs : CompiledSpec State L) (rspec : RStreettSpec State L) :
    Nat → List (Candidate State) →
      Option (Option (State × Array State × Array Nat × Candidate State) × Nat)
  | explored, [] => some (none, explored)
  | explored, c :: rest =>
    let (found?, aux) := candidateRun cs rspec c
    let explored' := explored + aux.live.size + aux.dead.size
    match found? with
    -- the candidate travels with the witness: its graph is where the report-time cycle must be rebuilt,
    -- since an edge its region excludes is not one the recorded options admit
    | some (anchor, _) => some (some (anchor, aux.witness, aux.witnessOpts, c), explored')
    | none => pruneLoop cs rspec explored' (aux.pending.toList ++ rest)
partial_fixpoint -- terminating because every queued candidate has a smaller measure than the one that queued it

private theorem pruneLoop_cons_found (cs : CompiledSpec State L) (rspec : RStreettSpec State L)
    (e : Nat) (c : Candidate State) (rest : List (Candidate State))
    (h : (candidateRun cs rspec c).1 ≠ none) :
    pruneLoop cs rspec e (c :: rest) ≠ none := by
  rw [pruneLoop]
  cases hf : (candidateRun cs rspec c).1 with
  | none => exact absurd hf h
  | some r => simp [hf]

private theorem pruneLoop_cons_step (cs : CompiledSpec State L) (rspec : RStreettSpec State L)
    (e : Nat) (c : Candidate State) (rest : List (Candidate State))
    (h : (candidateRun cs rspec c).1 = none) :
    pruneLoop cs rspec e (c :: rest) =
      pruneLoop cs rspec
        (e + (candidateRun cs rspec c).2.live.size + (candidateRun cs rspec c).2.dead.size)
        ((candidateRun cs rspec c).2.pending.toList ++ rest) := by
  rw [pruneLoop]
  simp [h]

/-- The worklist drains, on the hypothesis that a search queues only candidates strictly smaller than the one it ran
on. -/
theorem pruneLoop_drains (cs : CompiledSpec State L) (rspec : RStreettSpec State L)
    (hdec : ∀ c : Candidate State, ∀ P ∈ (candidateRun cs rspec c).2.pending,
      Candidate.measure cs P < Candidate.measure cs c) :
    ∀ n q, (∀ c ∈ q, Candidate.measure cs c ≤ n) → ∀ b, (∀ e, pruneLoop cs rspec e b ≠ none) →
      ∀ e, pruneLoop cs rspec e (q ++ b) ≠ none := by
  intro n
  induction n with
  | zero =>
    intro q
    induction q with
    | nil => intro _ b hb e; simpa using hb e
    | cons C q' ih =>
      intro hq b hb e
      have hC : Candidate.measure cs C = 0 := Nat.le_zero.mp (hq C (by simp))
      rw [List.cons_append]
      by_cases hf : (candidateRun cs rspec C).1 = none
      · rw [pruneLoop_cons_step _ _ _ _ _ hf]
        -- nothing can be below measure zero, so nothing was queued
        have hnil : (candidateRun cs rspec C).2.pending.toList = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro P hP
          have := hdec C P (by simpa using hP)
          omega
        rw [hnil, List.nil_append]
        exact ih (fun D hD => hq D (by simp [hD])) b hb _
      · exact pruneLoop_cons_found _ _ _ _ _ hf
  | succ n ihn =>
    intro q
    induction q with
    | nil => intro _ b hb e; simpa using hb e
    | cons C q' ih =>
      intro hq b hb e
      have hC : Candidate.measure cs C ≤ n + 1 := hq C (by simp)
      rw [List.cons_append]
      by_cases hf : (candidateRun cs rspec C).1 = none
      · rw [pruneLoop_cons_step _ _ _ _ _ hf]
        refine ihn _ (fun P hP => ?_) (q' ++ b)
          (fun e' => ih (fun D hD => hq D (by simp [hD])) b hb e') _
        have := hdec C P (by simpa using hP)
        omega
      · exact pruneLoop_cons_found _ _ _ _ _ hf

/-- `pruneLoop` is defined on every queue, given that a search queues only candidates strictly smaller than the one it
ran on. -/
theorem pruneLoop_ne_none (cs : CompiledSpec State L) (rspec : RStreettSpec State L)
    (hdec : ∀ c : Candidate State, ∀ P ∈ (candidateRun cs rspec c).2.pending,
      Candidate.measure cs P < Candidate.measure cs c)
    (e : Nat) (q : List (Candidate State)) : pruneLoop cs rspec e q ≠ none := by
  obtain ⟨n, hn⟩ : ∃ n, ∀ c ∈ q, Candidate.measure cs c ≤ n := by
    induction q with
    | nil => exact ⟨0, by simp⟩
    | cons C q' ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨max n (Candidate.measure cs C), fun D hD => ?_⟩
      rcases List.mem_cons.mp hD with rfl | hD'
      · exact Nat.le_max_right _ _
      · exact Nat.le_trans (hn D hD') (Nat.le_max_left _ _)
  have hb : ∀ e', pruneLoop cs rspec e' ([] : List (Candidate State)) ≠ none := by
    intro e'; rw [pruneLoop]; simp
  simpa using pruneLoop_drains cs rspec hdec n q hn [] hb e

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
  have hlen := (List.subperm_of_subset hnd hsubl).length_le
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
private theorem streettInitAux_wf : StreettWF cs curRegions (streettInitAux : StreettAux State) :=
  ⟨liveWF_init 0, by intro P hP; simp [streettInitAux] at hP,
    by intro P hP; simp [streettInitAux] at hP⟩

/-- The sets the prune's own POP flushes are the maximal SCCs of the reachable subgraph. -/
theorem streettSCCs_sound (cs : CompiledSpec State L) (hcs : cs.WF) (curRegions : Nat)
    (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (initialStates : List State)
    (fr : FiniteReach initialStates succs) :
    SCCEnumerationSound initialStates succs
      (enumSCCs (streettOps cs curRegions) (streettView cs curRegions) succs edgeMarks expand initialStates) :=
  enumSCCs_sound (streettOps cs curRegions) (streettView cs curRegions) (streettLowlinkLawful cs curRegions) (streettLawful cs curRegions hcs)
    streettInitAux_wf succs edgeMarks expand hexp initialStates fr

private theorem streettInitAux_unknown (cs : CompiledSpec State L) (curRegions : Nat)
    (q : State) :
    (streettOps cs curRegions).getStatus (streettOps cs curRegions).initAux q = .unknown := by
  show streettGetStatus streettInitAux q = .unknown
  simp [streettGetStatus, liveStatusOf, streettInitAux]

/-- Every candidate a search on `c` queues has strictly smaller measure: by construction it carries a
region bit the search did not already have. -/
theorem streettRun_pending_fresh (cs : CompiledSpec State L) (hcs : cs.WF)
    (rspec : RStreettSpec State L) (c P : Candidate State)
    (hP : P ∈ (candidateRun cs rspec c).2.pending) :
    Candidate.measure cs P < Candidate.measure cs c := by
  have hwf : StreettWF (cs.atBits c.regions) c.regions (candidateRun cs rspec c).2 :=
    genericDFS_wellFormed (streettOps (cs.atBits c.regions) c.regions) (c.graph cs rspec)
      (rspec.regionMarks (c.region cs)) (c.expand cs rspec)
      (streettLawful (cs.atBits c.regions) c.regions (hcs.atBits c.regions))
      c.states.toList (streettOps (cs.atBits c.regions) c.regions).initAux streettInitAux_wf
  obtain ⟨o, ho, hfresh, hPr⟩ := hwf.pending_fresh P hP
  have hm : Candidate.measure cs P
      = Candidate.measure cs ⟨c.states, c.regions ||| (1 <<< o)⟩ := by
    simp only [Candidate.measure, hPr]
  rw [hm]
  exact Candidate.measure_lt (by simpa using ho) hfresh

/-- Every candidate a search queues holds only states the search reached. -/
theorem streettRun_pending_reachable (cs : CompiledSpec State L) (hcs : cs.WF) (curRegions : Nat)
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (initialStates : List State) :
    ∀ P ∈ (streettRun cs curRegions succs edgeMarks expand initialStates).2.pending,
      ∀ s ∈ P.states, Reachable initialStates succs s := by
  intro P hP s hs
  have hwf : StreettWF cs curRegions (streettRun cs curRegions succs edgeMarks expand initialStates).2 :=
    genericDFS_wellFormed (streettOps cs curRegions) succs edgeMarks expand
      (streettLawful cs curRegions hcs) initialStates
      (streettOps cs curRegions).initAux streettInitAux_wf
  rcases genericDFS_touched_reachable (streettOps cs curRegions) succs edgeMarks expand hexp
    (streettLawful cs curRegions hcs) initialStates
    (streettOps cs curRegions).initAux streettInitAux_wf s
    (streettGetStatus_ne_unknown hwf.live (hwf.pending_states P hP s hs)) with h | h
  · exact absurd (streettInitAux_unknown cs curRegions s) h
  · exact h

/-- The prune terminates: `pruneLoop` is defined on every queue. -/
theorem pruneLoop_defined (cs : CompiledSpec State L) (hcs : cs.WF) (rspec : RStreettSpec State L)
    (e : Nat) (q : List (Candidate State)) : pruneLoop cs rspec e q ≠ none :=
  pruneLoop_ne_none cs rspec (fun c P hP => streettRun_pending_fresh cs hcs rspec c P hP) e q

/-- The accepted SCC as a set. -/
private def witnessSet (wit : Array State) : Std.HashSet State :=
  wit.foldl (init := Std.HashSet.emptyWithCapacity wit.size) fun h s => h.insert s

/-- The edges of a reported cycle, indexed exactly as `TAcceptingCycle.cycle_covers_marks` indexes them:
edge `i` is `(cycle[i], cycle[(i+1) % length])`, the last one wrapping round to the head. -/
@[expose] def cycleEdges [Inhabited State] (l : List State) : List (State × State) :=
  (List.range l.length).map fun i => (l[i]!, l[(i + 1) % l.length]!)

omit [BEq State] [Hashable State] [Inhabited State] [LawfulBEq State] [LawfulHashable State] in
theorem mem_cycleEdges_iff [Inhabited State] {l : List State} {e : State × State} :
    e ∈ cycleEdges l ↔ ∃ i < l.length, e = (l[i]!, l[(i + 1) % l.length]!) := by
  simp [cycleEdges, List.mem_map, List.mem_range, eq_comm]

/-- The fair test decided on a reported cycle, read on its edges inside the reporting candidate's own region: every cycle edge has
a realization in `cs.restrict`, and every conjunct has an option whose region admits every cycle edge and each of whose marks a
cycle edge carries. `cs.regions` and `cs.optMarks` are already conjoined with `cs.restrict`, so a mark and its region are answered
on one realization. Jointness across conjuncts is the caller's `LSys.StateOnly` obligation (`EdgeLabels.md` §17). `streettPop`
reports only when every conjunct has an available option, so this check passes on every genuine find (`buildResult_ne_empty`),
and a failure degrades to `.empty`. -/
def CompiledSpec.fairCycleOpts (cs : CompiledSpec State L) (edges : List (State × State)) : Bool :=
  -- every cycle edge has a realization inside the candidate's region, stated once rather than per
  -- conjunct: it is what makes the cycle a cycle *of the restricted graph*, and it has to hold even
  -- when there is no conjunct to ask
  edges.all (fun e => (cs.spec.regionSuccs cs.restrict e.1).contains e.2) &&
  (List.range cs.spec.conjuncts.size).all fun i =>
    (List.range cs.numOptions).any fun o =>
      decide (cs.conjunctStart[i]! ≤ o) && decide (o < cs.conjunctStart[i + 1]!) &&
        edges.all (fun e => cs.regions[o]! e) &&
        (cs.optMarks[o]!).all fun g => edges.any fun e => g e

omit [Hashable State] [Inhabited State] [LawfulHashable State] in
/-- The cycle lives in the restricted graph. -/
theorem fairCycleOpts_edges {cs : CompiledSpec State L} {edges : List (State × State)}
    (h : cs.fairCycleOpts edges = true) :
    ∀ e ∈ edges, e.2 ∈ cs.spec.regionSuccs cs.restrict e.1 := by
  rw [CompiledSpec.fairCycleOpts, Bool.and_eq_true] at h
  exact fun e he => Array.contains_iff_mem.mp (List.all_eq_true.mp h.1 e he)

omit [Hashable State] [Inhabited State] [LawfulHashable State] in
/-- What a passing check gives back, per conjunct: an option whose region admits every cycle edge and
each of whose marks is witnessed by a cycle edge, both inside `cs.restrict`. Jointness of the selection
across conjuncts is *not* established here — it is the caller's `LSys.StateOnly` obligation, discharged
by routing (`EdgeLabels.md` §17). -/
theorem exists_option_of_fairCycleOpts {cs : CompiledSpec State L} (hwf : cs.WF)
    (hmono : cs.spec.Mono) {edges : List (State × State)} (h : cs.fairCycleOpts edges = true)
    {i : Nat} (hi : i < cs.spec.conjuncts.size) :
    ∃ opt ∈ cs.spec.conjuncts[i]!,
      (∀ e ∈ edges, e.2 ∈ cs.spec.regionSuccs opt.region e.1) ∧
      ∀ g ∈ opt.marks, ∃ e ∈ edges,
        e.2 ∈ cs.spec.regionSuccs (fun l => opt.region l && g l) e.1 := by
  rw [CompiledSpec.fairCycleOpts, Bool.and_eq_true] at h
  obtain ⟨o, ho, hall⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp h.2 i (List.mem_range.mpr hi))
  have holt : o < cs.numOptions := List.mem_range.mp ho
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  obtain ⟨⟨⟨hlo, hhi⟩, hreg⟩, hmk⟩ := hall
  have hstep := hwf.start_succ i hi
  have hk : o - cs.conjunctStart[i]! < (cs.spec.conjuncts[i]!).size := by omega
  have hidx : cs.conjunctStart[i]! + (o - cs.conjunctStart[i]!) = o := by omega
  have hlet := hwf.letter_option i hi _ hk
  have hmkEq := hwf.option_marks i hi _ hk
  rw [hidx] at hlet hmkEq
  set opt := (cs.spec.conjuncts[i]!)[o - cs.conjunctStart[i]!]! with hoptdef
  have hmem : opt ∈ cs.spec.conjuncts[i]! := by
    have hce : cs.spec.conjuncts[i]! = cs.spec.conjuncts[i] := getElem!_pos _ i hi
    have hk2 : o - cs.conjunctStart[i]! < (cs.spec.conjuncts[i]).size := by rwa [hce] at hk
    rw [hoptdef, hce, getElem!_option _ _ hk2]
    exact Array.getElem_mem _
  refine ⟨opt, hmem, fun e he => ?_, fun g hg => ?_⟩
  -- every cycle edge has a realization satisfying the candidate's region
  · have hc := List.all_eq_true.mp hreg e he
    rw [hwf.regions_getElem holt, hlet] at hc
    simp only [StreettOption.onEdgesIn] at hc
    exact hmono.succs_mono (r := opt.region)
      (fun l hl => (Bool.and_eq_true _ _ |>.mp hl).2) e.1 e.2 (Array.contains_iff_mem.mp hc)
  -- each mark is witnessed by a cycle edge, on a realization that is also in region
  · have hgmem : (fun e => (cs.spec.regionSuccs (fun l => cs.restrict l && opt.region l && g l)
        e.1).contains e.2) ∈ cs.optMarks[o]! := by
      rw [hmkEq]
      exact Array.mem_map.mpr ⟨g, hg, rfl⟩
    obtain ⟨e, he, hge⟩ := List.any_eq_true.mp (Array.all_eq_true'.mp hmk _ hgmem)
    refine ⟨e, he, hmono.succs_mono (fun l hl => ?_) e.1 e.2 (Array.contains_iff_mem.mp hge)⟩
    obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hl
    exact Bool.and_eq_true _ _ |>.mpr ⟨(Bool.and_eq_true _ _ |>.mp h1).2, h2⟩

/-- The selected options' marks in order. -/
private def witnessExtra (cs : CompiledSpec State L) (wopts : Array Nat) :
    Array ((State × State) → Bool) :=
  wopts.foldl (init := #[]) fun a o => a ++ cs.optMarks[o]!

/-- The graph's own marks on an edge, plus mark `numMarks + j` whenever `extra[j]` holds *of that edge*.
Reading the extras on the edge rather than on its source is the whole point: an option's mark and its
region have to be witnessed by one realization. -/
private def witnessMarks (cs : CompiledSpec State L) (edgeMarks : State → State → Std.HashSet Nat)
    (extra : Array ((State × State) → Bool)) (s t : State) : Std.HashSet Nat :=
  (Array.range extra.size).foldl (init := edgeMarks s t) fun h j =>
    if extra[j]! (s, t) then h.insert (cs.numMarks + j) else h

/-- Rebuild the cycle through `anchor` inside the accepted SCC, as `checkWithWitness` does, but against the selected
options' marks as well as the property's, since a stitched cycle need not meet every state of the SCC. -/
private def witnessCycle (cs : CompiledSpec State L) (cycGraph : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (wit : Array State) (wopts : Array Nat)
    (anchor : State) : List State :=
  let scc := witnessSet wit
  let sccSuccsMap : Std.HashMap State (Array State) :=
    wit.foldl (init := ∅) fun m s => m.insert s ((cycGraph s).filter scc.contains)
  let sccSuccs' : State → Array State := fun s =>
    match sccSuccsMap[s]? with
    | some a => a
    -- never taken, and agrees with `sccSuccs`
    | none => (cycGraph s).filter scc.contains
  let extra := witnessExtra cs wopts
  stitchCycleAt scc sccSuccs' (witnessMarks cs edgeMarks extra) (cs.numMarks + extra.size) anchor

/-- The reported answer, with the witness checked rather than trusted. A failed check degrades to `.empty`.

Two graphs, and the distinction is load-bearing. The cycle is rebuilt in `cycGraph`, the graph the search
that found the witness actually walked — for a pruned candidate that is its region-restricted subgraph, and
rebuilding in the ambient graph could pick an edge the recorded options do not admit, making
`fairCycleOpts` fail and the answer degrade to `.empty` without a refutation to back it. The lasso is then
validated against the ambient `succs`, which the stem walks and which `cycGraph` is contained in. -/
def buildResult (cs : CompiledSpec State L) (cycGraph : State → Array State)
    (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (wit : Array State) (wopts : Array Nat)
    (anchor : State) (stem : List State) (explored : Nat) : EmptinessResult State :=
  match witnessCycle cs cycGraph edgeMarks wit wopts anchor with
  | [] => .empty explored
  | cycle =>
    if validLasso succs edgeMarks cs.numMarks initialStates stem cycle &&
        cs.fairCycleOpts (cycleEdges cycle) then
      .nonEmpty stem (anchor :: cycle)
    else .empty explored

/-- Does the product hold a fair accepting cycle? One search over the whole graph, then the prune's own queue. A
witness a pruned search finds gets its stem by BFS over the first search's `dead`, the reachable set. -/
@[expose] def streettCheck (cs : CompiledSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) (initialStates : List State) :
    EmptinessResult State :=
  match streettRun cs 0 succs edgeMarks expand initialStates with
  | (some (anchor, stem), aux) =>
    buildResult cs succs succs (cs.spec.regionMarks cs.restrict) initialStates aux.witness
      aux.witnessOpts anchor stem (aux.live.size + aux.dead.size)
  | (none, aux) =>
    match pruneLoop cs cs.spec (aux.live.size + aux.dead.size) aux.pending.toList with
    | some (some (anchor, wit, wopts, C), n) =>
      -- the report is validated against the candidate's own compiled spec, whose `restrict` is the
      -- region the witness was actually found inside
      buildResult (cs.atBits C.regions) (C.graph cs cs.spec) succs
        (cs.spec.regionMarks (C.region cs)) initialStates wit wopts anchor
        ((bfsFindPath aux.dead succs initialStates (· == anchor)).getD [anchor]) n
    | some (none, n) => .empty n
    | none => .empty (aux.live.size + aux.dead.size)

/-! ## The contract

The two obligations, stated against `RFairSCC` since the prune decides the fair condition as well as the generalized
Büchi one, and its regions restrict steps. -/

/-- Anything `buildResult` reports has passed both checks on the stem it was handed. -/
private theorem buildResult_valid (cs : CompiledSpec State L) (cycGraph : State → Array State)
    (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (wit : Array State) (wopts : Array Nat) (anchor : State) (stem : List State) (explored : Nat)
    {s l : List State}
    (h : buildResult cs cycGraph succs edgeMarks initialStates wit wopts anchor stem explored
      = .nonEmpty s l) :
    s = stem ∧ validLasso succs edgeMarks cs.numMarks initialStates stem l.tail = true ∧
      cs.fairCycleOpts (cycleEdges l.tail) = true := by
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

/-- Soundness: a reported stem and cycle form a `TAcceptingCycle` whose cycle carries every conjunct.

The validator runs at the *reporting* spec, which for a witness found in a pruned candidate is `cs`
recompiled at that candidate's bitmask. It is quantified here rather than fixed to `cs`, because which
bitmask that is depends on where the witness was found; everything the caller needs — `numMarks`, the
conjuncts, the option layout — is the same in both (`CompiledSpec.atBits_*`). -/
theorem streettCheck_nonEmpty_valid (cs : CompiledSpec State L) (hcs : cs.WF)
    (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) (initialStates : List State)
    {stem loop : List State}
    (h : streettCheck cs succs edgeMarks expand initialStates = .nonEmpty stem loop) :
    ∃ bits : Nat,
      ∃ ac : TAcceptingCycle initialStates succs
        (cs.spec.regionMarks (regionOf cs bits)) cs.numMarks, ac.stem = stem ∧
      ac.cycle = loop.tail ∧ (cs.atBits bits).fairCycleOpts (cycleEdges loop.tail) = true := by
  have hvalid : ∃ bits : Nat,
      validLasso succs (cs.spec.regionMarks (regionOf cs bits)) cs.numMarks initialStates stem
          loop.tail = true ∧
      (cs.atBits bits).fairCycleOpts (cycleEdges loop.tail) = true := by
    rw [streettCheck] at h
    split at h
    · obtain ⟨rfl, hv⟩ := buildResult_valid _ _ _ _ _ _ _ _ _ _ h
      refine ⟨cs.restrictBits, ?_, ?_⟩
      · rw [← hcs.restrict_eq]; exact hv.1
      · rw [CompiledSpec.atBits_self hcs]; exact hv.2
    · split at h
      · next _ _ C _ _ =>
        obtain ⟨rfl, hv⟩ := buildResult_valid _ _ _ _ _ _ _ _ _ _ h
        exact ⟨C.regions, hv.1, hv.2⟩
      · exact absurd h (by simp)
      · exact absurd h (by simp)
  obtain ⟨bits, hv1, hv2⟩ := hvalid
  exact ⟨bits, TAcceptingCycle.ofValid hv1, by simp, by simp, hv2⟩

/-- At a closing POP a full accumulator means the flushed set covers every property mark. -/
theorem streett_acceptingMarks_of_full (cs : CompiledSpec State L) {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State} {aux : (streettOps cs curRegions).Aux}
    {step : DFSStep State (streettOps cs curRegions).Position} {gray : List (GrayFrame State)}
    (hclose : (streettView cs curRegions).closes aux step = true)
    (hwf : SearchWF (streettOps cs curRegions) (streettView cs curRegions) succs edgeMarks initialStates aux
      (⟨step.state, (streettView cs curRegions).posNat step.pos, step.idx, step.acc⟩ :: gray))
    (hfull : (streettView cs curRegions).accAt aux 0 = fullAccMask cs.numMarks) :
    AcceptingMarks succs edgeMarks cs.numMarks
      (flushedSet ((streettView cs curRegions).live aux) ((streettView cs curRegions).posNat step.pos)) := by
  have hll0 : (streettView cs curRegions).lowlinkAt aux 0 = (streettView cs curRegions).posNat step.pos :=
    revGetD_zero (by rw [LowlinkView.closes] at hclose; exact beq_iff_eq.mp hclose)
  -- every bit of the full accumulator sits on an internal edge of the flushed set
  have hbit : ∀ b, b ≤ cs.numMarks →
      ∃ u ∈ flushedSet ((streettView cs curRegions).live aux) ((streettView cs curRegions).posNat step.pos),
      ∃ v ∈ flushedSet ((streettView cs curRegions).live aux) ((streettView cs curRegions).posNat step.pos), v ∈ succs u ∧
        ((1 <<< cs.numMarks).testBit b = true ∨ b ∈ edgeMarks u v) := by
    intro b hb
    have htb : ((streettView cs curRegions).accAt aux 0).testBit b = true := by
      rw [hfull, fullAccMask, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
      simpa using Nat.lt_succ_of_le hb
    obtain ⟨u, v, pu, pv, he, hu, hv, hlo, ⟨l, hl, hlb⟩, -, hmk⟩ := hwf.acc_sound 0 (by simp) b htb
    obtain rfl : l = 0 := by omega
    rw [hll0] at hlb
    obtain ⟨hpu, hpu'⟩ := hwf.liveWF.bwd u pu hu
    obtain ⟨hpv, hpv'⟩ := hwf.liveWF.bwd v pv hv
    rw [getElem!_pos ((streettView cs curRegions).live aux) pu hpu] at hpu'
    rw [getElem!_pos ((streettView cs curRegions).live aux) pv hpv] at hpv'
    exact ⟨u, (mem_flushedSet _ _ u).mpr ⟨pu, hpu, hlo, hpu'⟩,
      v, (mem_flushedSet _ _ v).mpr ⟨pv, hpv, hlb, hpv'⟩, he.mem, hmk⟩
  refine ⟨?_, fun m hm => ?_⟩
  · obtain ⟨u, hu, v, hv, he, -⟩ := hbit cs.numMarks (Nat.le_refl _)
    exact ⟨u, hu, v, hv, he⟩
  · obtain ⟨u, hu, v, hv, he, hmk⟩ := hbit m (Nat.le_of_lt hm)
    refine ⟨u, hu, v, hv, he, hmk.resolve_left ?_⟩
    simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, decide_eq_true_eq]
    omega

/-- At a closing POP a flushed set covering every property mark leaves the accumulator full, the graph's own marks
being below `numMarks`. -/
theorem streett_full_of_acceptingMarks (cs : CompiledSpec State L) {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State} {aux : (streettOps cs curRegions).Aux}
    {step : DFSStep State (streettOps cs curRegions).Position} {gray : List (GrayFrame State)}
    (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < cs.numMarks)
    (hsucc : step.succ = succs step.state) (hidx : ¬ step.idx < step.succ.size)
    (hwf : SearchWF (streettOps cs curRegions) (streettView cs curRegions) succs edgeMarks initialStates aux
      (⟨step.state, (streettView cs curRegions).posNat step.pos, step.idx, step.acc⟩ :: gray))
    (hA : AcceptingMarks succs edgeMarks cs.numMarks
      (flushedSet ((streettView cs curRegions).live aux) ((streettView cs curRegions).posNat step.pos))) :
    (streettView cs curRegions).accAt aux 0 = fullAccMask cs.numMarks := by
  have hcomp := hwf.close_acc_complete hsucc hidx
  apply Nat.eq_of_testBit_eq
  intro b
  rw [fullAccMask, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
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
  · have hfalse : ((streettView cs curRegions).accAt aux 0).testBit b = false := by
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
@[expose] def OptionsCover (cs : CompiledSpec State L) (succs : State → Array State) (B : Std.HashSet State)
    (wopts : Array Nat) : Prop :=
  (∀ o ∈ wopts,
      (∀ s ∈ B, ∀ t ∈ B, t ∈ succs s → cs.regions[o]! (s, t) = true) ∧
      ∀ g ∈ cs.optMarks[o]!, ∃ s ∈ B, ∃ t ∈ B, t ∈ succs s ∧ g (s, t) = true) ∧
  ∀ i < cs.spec.conjuncts.size, ∃ o ∈ wopts, cs.conjunctStart[i]! ≤ o ∧ o < cs.conjunctStart[i + 1]!

/-- A counterexample the search reports lies in an internally connected SCC covering every property mark, reached
by the reported stem, and the options recorded beside it cover every conjunct on that SCC. Connectivity and marks are
read off the search invariant at the reporting POP [CCLMT18]. -/
theorem streettRun_found (cs : CompiledSpec State L) (curRegions : Nat) (hcs : cs.WF)
    (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (initialStates : List State)
    (fr : FiniteReach initialStates succs) {anchor : State} {stem : List State}
    (hfound : (streettRun cs curRegions succs edgeMarks expand initialStates).1 = some (anchor, stem)) :
    InternallyConnected succs (streettSccHint (streettRun cs curRegions succs edgeMarks expand initialStates).2) ∧
    AcceptingMarks succs edgeMarks cs.numMarks (streettSccHint (streettRun cs curRegions succs edgeMarks expand initialStates).2) ∧
    anchor ∈ streettSccHint (streettRun cs curRegions succs edgeMarks expand initialStates).2 ∧
    (∃ hs : stem ≠ [], stem.head hs ∈ initialStates ∧
      (∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs (stem[i])) ∧ stem.getLast hs = anchor) ∧
    OptionsCover cs succs (streettSccHint (streettRun cs curRegions succs edgeMarks expand initialStates).2)
      (streettRun cs curRegions succs edgeMarks expand initialStates).2.witnessOpts := by
  unfold streettRun at hfound ⊢
  obtain ⟨-, hout⟩ := genericDFS_searchOutcome (streettOps cs curRegions) (streettView cs curRegions) (streettLowlinkLawful cs curRegions)
    (streettLawful cs curRegions hcs) streettInitAux_wf succs edgeMarks expand hexp initialStates fr
  obtain ⟨aux, step, gray, hwf, hsucc, hanchor, hrep⟩ := hout anchor stem hfound
  rcases hrep with ⟨hidx, hpop⟩ | ⟨d, -, -, hupd⟩
  swap
  -- UPDATE never reports
  · have h1 := congrArg Prod.snd hupd
    have h2 : ((streettOps cs curRegions).update aux (step.succMarks[step.idx]!) d).2 = false :=
      streettUpdate_snd cs.numMarks aux _ d
    rw [h2] at h1
    exact absurd h1 (by simp)
  obtain ⟨hback, hwit, hfu, hwo⟩ := streettPop_eq_true hpop
  have hclose : (streettView cs curRegions).closes aux step = true := by
    simp [LowlinkView.closes, streettView, Array.back?_map, hback]
  obtain ⟨-, hconn⟩ := hwf.close_flushed hsucc hidx hclose
  set F := flushedSet ((streettView cs curRegions).live aux) ((streettView cs curRegions).posNat step.pos) with hF
  have hacc0 : (streettView cs curRegions).accAt aux 0 = fullAccMask cs.numMarks :=
    revGetD_zero (by simp [streettView, Array.back?_map, hback])
  -- the hint holds exactly the flushed range
  have hmemF : ∀ s, s ∈ F ↔
      s ∈ (streettOps cs curRegions).sccHint (genericDFS (streettOps cs curRegions) succs edgeMarks expand initialStates
        (streettOps cs curRegions).initAux).2 := by
    intro s
    show s ∈ flushedSet _ _ ↔ s ∈ streettSccHint _
    rw [streettSccHint, hwit, flushedSet]
    exact mem_sccSet.trans mem_sccSet.symm
  have hanchorF : anchor ∈ F := by
    obtain ⟨h1, h2⟩ := hwf.frame_pos ⟨step.state, (streettView cs curRegions).posNat step.pos, step.idx, step.acc⟩
      (List.mem_cons_self ..)
    rw [getElem!_pos ((streettView cs curRegions).live aux) _ h1] at h2
    exact (mem_flushedSet _ _ anchor).mpr ⟨_, h1, Nat.le_refl _, h2.trans hanchor⟩
  have hAF := streett_acceptingMarks_of_full cs hclose hwf hacc0
  -- the recorded options are the ones the scan selected on the flushed range
  have hB : ∀ s, s ∈ (streettOps cs curRegions).sccHint (genericDFS (streettOps cs curRegions) succs edgeMarks expand initialStates
      (streettOps cs curRegions).initAux).2 ↔ s ∈ aux.live.toList.drop step.pos := by
    intro s
    show s ∈ streettSccHint _ ↔ _
    rw [streettSccHint, hwit]
    exact mem_sccSet
  have hopts : OptionsCover cs succs (streettSccHint (genericDFS (streettOps cs curRegions) succs edgeMarks expand initialStates
      (streettOps cs curRegions).initAux).2) (genericDFS (streettOps cs curRegions) succs edgeMarks expand initialStates
      (streettOps cs curRegions).initAux).2.witnessOpts := by
    refine ⟨fun o ho => ?_, fun i hi => ?_⟩
    · rw [hwo] at ho
      have hav := selectedOptions_available cs _ _ _ o ho
      have hlt : o < cs.numOptions := by
        simp only [optionAvailable, Bool.and_eq_true] at hav
        have h1 := hav.1
        rw [scanFrame, scanLetters, scanLabels_fst_testBit] at h1
        simpa [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one] using h1.1
      obtain ⟨hreg, hmk⟩ :=
        (optionAvailable_letters cs hcs
          (internalEdges succs (sccSetOf aux.live step.pos) (aux.live.toList.drop step.pos))
          o hlt).mp (by rw [← scanFrame]; exact hav)
      have hst : ∀ x, x ∈ aux.live.toList.drop step.pos ↔ x ∈ sccSetOf aux.live step.pos :=
        fun x => mem_sccSet.symm
      have hBS : ∀ x, x ∈ sccSetOf aux.live step.pos ↔ x ∈ streettSccHint _ := fun x =>
        ⟨fun hx => (hB x).mpr ((hst x).mpr hx), fun hx => (hst x).mp ((hB x).mp hx)⟩
      refine ⟨fun s hs t ht hsucc => ?_, fun g hg => ?_⟩
      · exact hreg (s, t) (mem_internalEdges.mpr
          ⟨(hst s).mpr ((hBS s).mpr hs), hsucc, (hBS t).mpr ht⟩)
      · obtain ⟨e, he, hge⟩ := hmk g hg
        obtain ⟨h1, h2, h3⟩ := mem_internalEdges.mp he
        exact ⟨e.1, (hBS e.1).mp ((hst e.1).mp h1), e.2, (hBS e.2).mp h3, h2, hge⟩
    · obtain ⟨o, ho, h1, h2, -, -⟩ := selectedOptions_covers hcs _ _ _ hfu i hi
      exact ⟨o, by rw [hwo]; exact ho, h1, h2⟩
  exact ⟨hconn.congr hmemF, hAF.mono (fun s hs => (hmemF s).mp hs), (hmemF anchor).mp hanchorF,
    genericDFS_stem_path (streettOps cs curRegions) succs edgeMarks expand hexp initialStates _ anchor stem hfound, hopts⟩

/-- A counterexample the search reports lies in an internally connected SCC covering every property mark, reached
by the reported stem. -/
theorem streett_sccHintSound (cs : CompiledSpec State L) (curRegions : Nat) (hcs : cs.WF)
    (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (initialStates : List State)
    (fr : FiniteReach initialStates succs) :
    SccHintSound (streettOps cs curRegions) succs edgeMarks expand cs.numMarks initialStates := by
  intro anchor stem hfound
  obtain ⟨h1, h2, h3, h4, -⟩ :=
    streettRun_found cs curRegions hcs succs edgeMarks expand hexp initialStates fr hfound
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
private theorem witnessCycle_eq (cs : CompiledSpec State L) (cycGraph : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (wit : Array State) (wopts : Array Nat) (anchor : State) :
    witnessCycle cs cycGraph edgeMarks wit wopts anchor =
      stitchCycleAt (witnessSet wit) (sccSuccs cycGraph (witnessSet wit))
        (witnessMarks cs edgeMarks (witnessExtra cs wopts)) (cs.numMarks + (witnessExtra cs wopts).size) anchor := by
  have hs : (fun s => match (wit.foldl (init := (∅ : Std.HashMap State (Array State)))
        fun m x => m.insert x ((cycGraph x).filter (witnessSet wit).contains))[s]? with
      | some a => a
      | none => (cycGraph s).filter (witnessSet wit).contains) = sccSuccs cycGraph (witnessSet wit) := by
    funext s
    rcases hm : (wit.foldl (init := (∅ : Std.HashMap State (Array State)))
        fun m x => m.insert x ((cycGraph x).filter (witnessSet wit).contains))[s]? with _ | v
    · rw [hm]; rfl
    · rw [hm]
      rw [← Array.foldl_toList] at hm
      exact foldl_insert_getElem?_eq (fun x => (cycGraph x).filter (witnessSet wit).contains) wit.toList ∅
        (by intro s' v' h'; simp at h') s v hm
  exact congrArg (fun g => stitchCycleAt (witnessSet wit) g (witnessMarks cs edgeMarks (witnessExtra cs wopts))
    (cs.numMarks + (witnessExtra cs wopts).size) anchor) hs

/-- A genuine find never degrades to `.empty`. -/
private theorem buildResult_ne_empty (cs : CompiledSpec State L) (hcs : cs.WF)
    {cycGraph : State → Array State} (succs : State → Array State)
    (hgsub : ∀ a b, b ∈ cycGraph a → b ∈ succs a)
    (hgsubR : ∀ a b, b ∈ cycGraph a → b ∈ cs.spec.regionSuccs cs.restrict a)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State)
    (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < cs.numMarks) {wit : Array State} {wopts : Array Nat}
    {anchor : State} {stem : List State} (explored : Nat)
    (hconn : InternallyConnected cycGraph (witnessSet wit))
    (hA : AcceptingMarks cycGraph edgeMarks cs.numMarks (witnessSet wit))
    (hanchor : anchor ∈ witnessSet wit)
    (hstem : ∃ hs : stem ≠ [], stem.head hs ∈ initialStates ∧
      (∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs (stem[i])) ∧ stem.getLast hs = anchor)
    (hopts : OptionsCover cs cycGraph (witnessSet wit) wopts) {n : Nat} :
    buildResult cs cycGraph succs edgeMarks initialStates wit wopts anchor stem explored ≠ .empty n := by
  have hmem' : ∀ s t m, m ∈ witnessMarks cs edgeMarks (witnessExtra cs wopts) s t ↔
      m ∈ edgeMarks s t ∨ ∃ j < (witnessExtra cs wopts).size,
        (witnessExtra cs wopts)[j]! (s, t) = true ∧ m = cs.numMarks + j := by
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
  have hA' : AcceptingMarks cycGraph (witnessMarks cs edgeMarks (witnessExtra cs wopts))
      (cs.numMarks + (witnessExtra cs wopts).size) (witnessSet wit) := by
    refine ⟨hA.1, fun m hm => ?_⟩
    by_cases hlt : m < cs.numMarks
    · obtain ⟨s, hs, t, ht, hst, hmk⟩ := hA.2 m hlt
      exact ⟨s, hs, t, ht, hst, (hmem' s t m).mpr (Or.inl hmk)⟩
    · have hj : m - cs.numMarks < (witnessExtra cs wopts).size := by omega
      obtain ⟨o, ho, hgo⟩ := (hextra _).mp (Array.getElem_mem hj)
      -- the mark now arrives already attached to an internal edge
      obtain ⟨s, hs, t, ht, hst, hgs⟩ := (hopts.1 o ho).2 _ hgo
      refine ⟨s, hs, t, ht, hst, (hmem' s t m).mpr (Or.inr ⟨m - cs.numMarks, hj, ?_, by omega⟩)⟩
      rwa [getElem!_pos (witnessExtra cs wopts) _ hj]
  obtain ⟨hs, hhead, hchain, hlast⟩ := hstem
  obtain ⟨ac, hacstem, haccycle⟩ :=
    stitchCycleAt_toTAcceptingCycle' hgsub hconn hA' hanchor hs hhead hchain hlast
  obtain ⟨hne0, -, hconf, hcchain, hcback, -⟩ :=
    stitchCycleAt_valid (witnessSet wit) (sccSuccs cycGraph (witnessSet wit))
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
  have hfair : cs.fairCycleOpts (cycleEdges ac.cycle) = true := by
    -- every cycle edge is an internal edge of the witness SCC
    have hedge : ∀ e ∈ cycleEdges ac.cycle,
        e.1 ∈ witnessSet wit ∧ e.2 ∈ witnessSet wit ∧ e.2 ∈ cycGraph e.1 := by
      intro e he
      obtain ⟨q, hq, rfl⟩ := mem_cycleEdges_iff.mp he
      have hq' : (q + 1) % ac.cycle.length < ac.cycle.length := Nat.mod_lt _ (by omega)
      have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos (by omega)
      refine ⟨?_, ?_, ?_⟩
      · rw [getElem!_pos ac.cycle q hq]
        exact Std.HashSet.mem_iff_contains.mpr (hconf _ (List.getElem_mem hq))
      · rw [getElem!_pos ac.cycle ((q + 1) % ac.cycle.length) hq']
        exact Std.HashSet.mem_iff_contains.mpr (hconf _ (List.getElem_mem hq'))
      · rw [getElem!_pos ac.cycle q hq, getElem!_pos ac.cycle ((q + 1) % ac.cycle.length) hq']
        rcases Nat.lt_or_ge (q + 1) ac.cycle.length with hlt | hge
        · have hmod : (q + 1) % ac.cycle.length = q + 1 := Nat.mod_eq_of_lt hlt
          simp only [hmod]
          exact (Array.mem_filter.mp (hcchain q hlt)).1
        · have hlen : q + 1 = ac.cycle.length := by omega
          have h0 : (q + 1) % ac.cycle.length = 0 := by rw [hlen]; exact Nat.mod_self _
          simp only [h0]
          have hhead : ac.cycle[0]'(by omega) = ac.cycle.head hne :=
            (List.head_eq_getElem hne).symm
          have hlast : ac.cycle[q]'hq = ac.cycle.getLast hne := by
            rw [List.getLast_eq_getElem hne]; congr 1; omega
          rw [hhead, hlast]
          exact (Array.mem_filter.mp hcback).1
    refine Bool.and_eq_true _ _ |>.mpr ⟨List.all_eq_true.mpr fun e he => ?_,
      List.all_eq_true.mpr fun i hi' => ?_⟩
    -- the hoisted clause: a cycle edge is an internal edge of the witness SCC, which the search walked
    -- inside the candidate's region
    · obtain ⟨h1, h2, h3⟩ := hedge e he
      exact Array.contains_iff_mem.mpr (hgsubR e.1 e.2 h3)
    have hi : i < cs.spec.conjuncts.size := List.mem_range.mp hi'
    obtain ⟨o, ho, hlo, hhi⟩ := hopts.2 i hi
    have hstep := hcs.start_succ i hi
    have holt : o < cs.numOptions := by
      have h1 := hcs.start_mono cs.spec.conjuncts.size (Nat.le_refl _) (i + 1) hi
      have h2 := hcs.numOptions_eq
      omega
    refine List.any_eq_true.mpr ⟨o, List.mem_range.mpr holt, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hlo, hhi⟩, List.all_eq_true.mpr fun e he => ?_⟩,
      Array.all_eq_true'.mpr fun g hg => ?_⟩
    -- the region admits every internal edge of the SCC, hence every cycle edge
    · obtain ⟨h1, h2, h3⟩ := hedge e he
      exact (hopts.1 o ho).1 e.1 h1 e.2 h2 h3
    -- each mark is an extended mark, carried by some cycle edge
    · obtain ⟨p, hp, hpg⟩ := Array.mem_iff_getElem.mp ((hextra g).mpr ⟨o, ho, hg⟩)
      obtain ⟨q, hq, hqm⟩ := ac.cycle_covers_marks (cs.numMarks + p) (by omega)
      rcases (hmem' _ _ _).mp hqm with hin | ⟨j, -, hjt, hjeq⟩
      · exact absurd (hmarksBound _ _ _ hin) (by omega)
      · have hjp : j = p := by omega
        rw [hjp, getElem!_pos (witnessExtra cs wopts) p hp, hpg] at hjt
        refine List.any_eq_true.mpr ⟨_, mem_cycleEdges_iff.mpr ⟨q, hq, rfl⟩, ?_⟩
        rw [getElem!_pos ac.cycle q hq,
          getElem!_pos ac.cycle ((q + 1) % ac.cycle.length) (Nat.mod_lt _ (by omega))]
        exact hjt
  intro hres
  rw [buildResult, (witnessCycle_eq cs cycGraph edgeMarks wit wopts anchor).trans haccycle.symm] at hres
  revert hne hvalid hfair hres
  generalize ac.cycle = c
  intro hne hvalid hfair hres
  cases c with
  | nil => exact hne rfl
  | cons x xs => simp [hvalid, hfair] at hres

/-- A search that reports nothing blames a conjunct for every maximal SCC covering the property marks. Either the candidate is
committed to an option of that conjunct whose marks are not witnessed, or it has queued the pruned candidate of every option of the
conjunct whose marks are witnessed, unless that candidate is empty, and the queued candidate commits to the candidate's options and
the new one only.

The marks are read on edges, a pair internal to `M` joined by an edge of the graph the search ran on, with one realization satisfying
both the option's region and the mark (`EdgeLabels.md` §6.5). The queued candidate keeps all of `M` and gains a region bit. `hgraph`
says the search's graph lies inside the region its bitmask denotes, so a committed option's region bit survives the scan, and a
committed option of the blamed conjunct is missing its marks. -/
theorem streettRun_none_pass (cs : CompiledSpec State L) (hcs : cs.WF) (curRegions : Nat)
    (hmono : cs.spec.Mono) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (initialStates : List State)
    (fr : FiniteReach initialStates succs) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < cs.numMarks)
    (hres : LePred (regionOf cs curRegions) cs.restrict)
    (hgraph : ∀ s t, t ∈ succs s → t ∈ cs.spec.regionSuccs (regionOf cs curRegions) s)
    (hnone : (streettRun cs curRegions succs edgeMarks expand initialStates).1 = none) :
    ∃ (sccs : List (Std.HashSet State)) (pick : Std.HashSet State → Array (StreettOption L)),
      SCCEnumerationSound initialStates succs sccs ∧
      (∀ M ∈ sccs, AcceptingMarks succs edgeMarks cs.numMarks M → pick M ∈ cs.spec.conjuncts) ∧
      ∀ M ∈ sccs, AcceptingMarks succs edgeMarks cs.numMarks M →
        (∃ k < cs.numOptions, curRegions.testBit k = true ∧ cs.letterOptions[k]! ∈ pick M ∧
          ¬ ∀ g ∈ (cs.letterOptions[k]!).marks, ∃ s ∈ M, ∃ t ∈ M, t ∈ succs s ∧
            t ∈ cs.spec.regionSuccs
              (fun l => cs.restrict l && (cs.letterOptions[k]!).region l && g l) s) ∨
        ∀ opt ∈ pick M,
          (∀ g ∈ opt.marks, ∃ s ∈ M, ∃ t ∈ M, t ∈ succs s ∧
              t ∈ cs.spec.regionSuccs (fun l => cs.restrict l && opt.region l && g l) s) →
            (∀ s, s ∉ M) ∨
              ∃ P ∈ (streettRun cs curRegions succs edgeMarks expand initialStates).2.pending,
                (∀ s, s ∈ P.states ↔ s ∈ M) ∧
                P.region cs = (fun l => regionOf cs curRegions l && opt.region l) ∧
                ∀ k < cs.numOptions, P.regions.testBit k = true →
                  curRegions.testBit k = true ∨ cs.letterOptions[k]! = opt := by
  have hrec := enumRun_recordedAt (streettOps cs curRegions) (streettView cs curRegions) (streettLowlinkLawful cs curRegions)
    (streettLawful cs curRegions hcs) streettInitAux_wf (streettMonotone cs curRegions) succs edgeMarks expand hexp initialStates fr hnone
  have hblame : ∀ M, ∃ c : Array (StreettOption L),
      M ∈ enumSCCs (streettOps cs curRegions) (streettView cs curRegions) succs edgeMarks expand initialStates →
      AcceptingMarks succs edgeMarks cs.numMarks M → c ∈ cs.spec.conjuncts ∧
        ((∃ k < cs.numOptions, curRegions.testBit k = true ∧ cs.letterOptions[k]! ∈ c ∧
          ¬ ∀ g ∈ (cs.letterOptions[k]!).marks, ∃ s ∈ M, ∃ t ∈ M, t ∈ succs s ∧
            t ∈ cs.spec.regionSuccs
              (fun l => cs.restrict l && (cs.letterOptions[k]!).region l && g l) s) ∨
        ∀ opt ∈ c,
          (∀ g ∈ opt.marks, ∃ s ∈ M, ∃ t ∈ M, t ∈ succs s ∧
              t ∈ cs.spec.regionSuccs (fun l => cs.restrict l && opt.region l && g l) s) →
            (∀ s, s ∉ M) ∨
              ∃ P ∈ (streettRun cs curRegions succs edgeMarks expand initialStates).2.pending,
                (∀ s, s ∈ P.states ↔ s ∈ M) ∧
                P.region cs = (fun l => regionOf cs curRegions l && opt.region l) ∧
                ∀ k < cs.numOptions, P.regions.testBit k = true →
                  curRegions.testBit k = true ∨ cs.letterOptions[k]! = opt) := by
    intro M
    by_cases hM : M ∈ enumSCCs (streettOps cs curRegions) (streettView cs curRegions) succs edgeMarks expand initialStates ∧
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
    have hpop' : streettPop cs curRegions succs p.2 step = ((streettPop cs curRegions succs p.2 step).1, false) := Prod.ext rfl hpop
    obtain ⟨opts, hfu, hq⟩ := streettPop_queues hcl hfull hpop'
    have hB : ∀ s, s ∈ p.1 ↔ s ∈ ((streettView cs curRegions).live p.2).toList.drop step.pos := by
      intro s
      rw [hflush, flushedSet]
      exact mem_sccSet
    have hmemsc : ∀ s, s ∈ sccSetOf ((streettView cs curRegions).live p.2) step.pos ↔ s ∈ p.1 :=
      fun s => mem_sccSet.trans (hB s).symm
    have hfu' : firstUnsatisfied cs curRegions
          (scanFrame cs succs ((streettView cs curRegions).live p.2) step.pos).1
          (scanFrame cs succs ((streettView cs curRegions).live p.2) step.pos).2 = some opts := hfu
    obtain ⟨c, hc, hoptlt, hcover⟩ := blamed_some_blames hcs hmono hres hgraph _ _ hB hfu'
    refine ⟨c, fun _ _ => ⟨hc, ?_⟩⟩
    rcases hcover with hcom | hcover
    · exact Or.inl hcom
    refine Or.inr fun opt hopt hpres => ?_
    obtain ⟨o, ho, hlet, -, -⟩ := hcover opt hopt hpres
    -- the blamed option was not already conjoined, so `streettPop` did not skip it
    have hofresh : curRegions.testBit o = false := blamed_bit_new hfu' ho
    rcases hq o ho with hempty | hbit | hin
    · refine Or.inl fun s hs => ?_
      rw [Std.HashSet.isEmpty_iff_forall_not_mem] at hempty
      exact hempty s ((hmemsc s).mpr hs)
    · exact absurd hbit (by rw [hofresh]; simp)
    · refine Or.inr ⟨_, hR _ hin, hmemsc, ?_, fun k _ hk => ?_⟩
      · show regionOf cs (curRegions ||| (1 <<< o)) = _
        rw [regionOf_or_shift (hoptlt o ho), hlet]
      · rcases testBit_or_shift.mp hk with hk' | rfl
        · exact Or.inl hk'
        · exact Or.inr hlet
  obtain ⟨pick, hpick⟩ := Classical.axiomOfChoice hblame
  exact ⟨enumSCCs (streettOps cs curRegions) (streettView cs curRegions) succs edgeMarks expand initialStates, pick,
    streettSCCs_sound cs hcs curRegions succs edgeMarks expand hexp initialStates fr,
    fun M hM hA => (hpick M hM hA).1, fun M hM hA => (hpick M hM hA).2⟩

omit [Inhabited State] [LawfulHashable State] in
private theorem finiteReach_sccSuccs (succs : State → Array State) (C : Std.HashSet State) :
    FiniteReach C.toList (sccSuccs succs C) :=
  ⟨C.toList, fun _ hs => Std.HashSet.mem_toList.mpr (mem_of_reachable_sccSuccs hs)⟩

omit [Inhabited State] [LawfulBEq State] [LawfulHashable State] in
/-- A candidate's graph is the abstract candidate graph at the region its bitmask denotes. Definitional,
but stating it keeps the two vocabularies visibly aligned. -/
theorem Candidate.graph_eq_candGraph (cs : CompiledSpec State L) (spec : RStreettSpec State L)
    (c : Candidate State) : c.graph cs spec = spec.candGraph (c.region cs) c.states := rfl

omit [Inhabited State] [LawfulHashable State] [BEq State] [Hashable State] [LawfulBEq State] in
/-- Marks survive the region restriction, so a bound on the ambient marks bounds every restricted one. -/
theorem regionMarks_lt {cs : CompiledSpec State L} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} (hcompat : cs.spec.Compat succs edgeMarks)
    (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < cs.numMarks) (r : L → Bool) :
    ∀ s t, ∀ m ∈ cs.spec.regionMarks r s t, m < cs.numMarks :=
  fun s t m hm => hmarksBound s t m (hcompat.marks_sub r s t m hm)

/-- A queue the prune drains without a report holds only refuted candidates, each at its own region and with its own commitments,
the conjunction and the options its bitmask denotes. -/
theorem pruneLoop_none_refuted (cs : CompiledSpec State L) (hcs : cs.WF) (hmono : cs.spec.Mono)
    (hrm : ∀ (r : L → Bool) s t, ∀ m ∈ cs.spec.regionMarks r s t, m < cs.numMarks) :
    ∀ e q r, pruneLoop cs cs.spec e q = some r → r.1 = none →
      ∀ C ∈ q, RRefuted cs.spec (committedOpts cs C.regions) (C.region cs) C.states := by
  refine pruneLoop.partial_correctness cs cs.spec
    (fun _ q r => r.1 = none →
      ∀ C ∈ q, RRefuted cs.spec (committedOpts cs C.regions) (C.region cs) C.states) ?_
  intro f ih e q r hr hnone
  cases q with
  | nil => intro C hC; simp at hC
  | cons C rest =>
    cases hrun : (candidateRun cs cs.spec C).1 with
    | some x =>
      simp [hrun] at hr
      rw [← hr] at hnone
      simp at hnone
    | none =>
      simp [hrun] at hr
      have hall := ih _ _ r hr hnone
      have hpend : ∀ P ∈ (candidateRun cs cs.spec C).2.pending,
          RRefuted cs.spec (committedOpts cs P.regions) (P.region cs) P.states :=
        fun P hP => hall P (List.mem_append_left _ (by simpa using hP))
      intro D hD
      rcases List.mem_cons.mp hD with rfl | hD'
      -- the candidate itself is one pass of the prune, its queued candidates refuted by the rest of the loop
      · obtain ⟨sccs, pick, henum, hpick, hrecq⟩ :=
          streettRun_none_pass (cs.atBits D.regions) (hcs.atBits D.regions) D.regions hmono
          (D.graph cs cs.spec) (cs.spec.regionMarks (D.region cs)) (D.expand cs cs.spec)
          (D.expand_coherent cs cs.spec) D.states.toList (finiteReach_sccSuccs _ D.states)
          (fun s t m hm => by
            rw [CompiledSpec.atBits_numMarks]; exact hrm (D.region cs) s t m hm)
          (by rw [CompiledSpec.atBits_restrict, regionOf_atBits]; exact LePred.refl _)
          (fun _ _ hst => by simpa [Candidate.region] using (Array.mem_filter.mp hst).1) hrun
        -- an SCC of the candidate's graph lies inside the candidate
        have hMsub : ∀ M ∈ sccs, ∀ s ∈ M, s ∈ D.states :=
          fun M hM s hs => mem_of_reachable_sccSuccs (henum.1 M hM s hs)
        simp only [CompiledSpec.atBits_numMarks, CompiledSpec.atBits_restrict,
          CompiledSpec.atBits_spec, CompiledSpec.atBits_numOptions, CompiledSpec.atBits_letterOptions,
          regionOf_atBits, Candidate.region_atBits] at hpick hrecq
        refine .pass sccs pick henum (fun M hM hA => hpick M hM (by rwa [hcs.numMarks_eq]))
          (fun M hM hA hguard opt hopt hpres => ?_)
        -- the abstract mark condition names an edge of the candidate's own graph
        have hpres' : ∀ o : StreettOption L, cs.spec.OptMarksIn (D.region cs) o M →
            ∀ g ∈ o.marks, ∃ s ∈ M, ∃ t ∈ M, t ∈ D.graph cs cs.spec s ∧
              t ∈ cs.spec.regionSuccs (fun l => Candidate.region cs D l && o.region l && g l) s := by
          intro o ho g hg
          obtain ⟨s, hs, t, ht, hst⟩ := ho g hg
          refine ⟨s, hs, t, ht, Array.mem_filter.mpr ⟨hmono.succs_mono (fun l hl => ?_) s t hst,
            Std.HashSet.mem_iff_contains.mp (hMsub M hM t ht)⟩, hst⟩
          exact (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hl).1).1
        rcases hrecq M hM (by rwa [hcs.numMarks_eq]) with ⟨k, hk, hbit, hkM, hmiss⟩ | hcover
        -- the guard witnesses the marks of a committed option of the blamed conjunct
        · exact absurd (hpres' _ (hguard _ (mem_committedOpts.mpr ⟨k, hk, hbit, rfl⟩) hkM)) hmiss
        · rcases hcover opt hopt (hpres' opt hpres) with hempty | ⟨P, hP, hPm, hPr, hPbits⟩
          · exact RRefuted.of_empty hempty
          -- the queued candidate commits to the candidate's options and to `opt`
          · have hsub : ∀ o ∈ committedOpts cs P.regions, o ∈ opt :: committedOpts cs D.regions := by
              intro o ho
              obtain ⟨k, hk, hbit, rfl⟩ := mem_committedOpts.mp ho
              exact List.mem_cons.mpr
                ((hPbits k hk hbit).symm.imp_right fun hD => mem_committedOpts.mpr ⟨k, hk, hD, rfl⟩)
            exact hPr ▸ ((hpend P hP).congr hPm).mono hsub
      · exact hall D (List.mem_append_right _ hD')

/-- When the whole-graph search reports nothing and the prune drains its queue without a report, the whole graph
is refuted. -/
theorem refutedFrom_of_none (cs : CompiledSpec State L) (hcs : cs.WF)
    (hbits0 : cs.restrict = fun _ => true) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (hcompat : cs.spec.Compat succs edgeMarks)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (initialStates : List State)
    (fr : FiniteReach initialStates succs) (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < cs.numMarks)
    (hnone : (streettRun cs 0 succs edgeMarks expand initialStates).1 = none) {e : Nat}
    {r : Option (State × Array State × Array Nat × Candidate State) × Nat}
    (hq : pruneLoop cs cs.spec e (streettRun cs 0 succs edgeMarks expand initialStates).2.pending.toList = some r)
    (hr : r.1 = none) :
    RRefutedFrom cs.spec succs edgeMarks initialStates := by
  -- the top-level search runs at the empty bitmask, which is the top region
  have htop : ∀ s t, t ∈ succs s → t ∈ cs.spec.regionSuccs (regionOf cs 0) s := by
    intro s t hst
    rw [regionOf_zero, hcompat.succs_top s]
    exact hst
  have hres : LePred (regionOf cs 0) cs.restrict := by
    rw [hbits0]; exact fun _ _ => rfl
  obtain ⟨sccs, pick, henum, hpick, hrecq⟩ :=
    streettRun_none_pass cs hcs 0 hcompat.toMono succs edgeMarks expand hexp initialStates fr
      hmarksBound hres htop hnone
  have hpend := pruneLoop_none_refuted cs hcs hcompat.toMono
    (regionMarks_lt hcompat hmarksBound) e _ r hq hr
  refine ⟨sccs, pick, henum, fun M hM hA => hpick M hM (by rwa [hcs.numMarks_eq]),
    fun M hM hA opt hopt hpres => ?_⟩
  have hpres' : ∀ g ∈ opt.marks, ∃ s ∈ M, ∃ t ∈ M, t ∈ succs s ∧
      t ∈ cs.spec.regionSuccs (fun l => cs.restrict l && opt.region l && g l) s := by
    intro g hg
    obtain ⟨s, hs, t, ht, hst⟩ := hpres g hg
    refine ⟨s, hs, t, ht, hcompat.succs_sub _ s t hst,
      hcompat.succs_mono (fun l hl => ?_) s t hst⟩
    rw [hbits0]
    simpa using hl
  -- at the top region the conjoined restriction is the option's own
  have hreg : (fun l => regionOf cs 0 l && opt.region l) = opt.region := by
    rw [regionOf_zero]
    funext l
    simp
  -- the empty bitmask commits to nothing, so the queued candidate commits to `opt` alone
  rcases hrecq M hM (by rwa [hcs.numMarks_eq]) with ⟨k, -, hbit, -⟩ | hcover
  · exact absurd hbit (by simp)
  · rcases hcover opt hopt hpres' with hempty | ⟨P, hP, hPm, hPr, hPbits⟩
    · exact RRefuted.of_empty hempty
    · have hsub : ∀ o ∈ committedOpts cs P.regions, o ∈ [opt] := by
        intro o ho
        obtain ⟨k, hk, hbit, rfl⟩ := mem_committedOpts.mp ho
        exact List.mem_singleton.mpr ((hPbits k hk hbit).resolve_left (by simp))
      exact hreg ▸ hPr ▸ ((hpend P (by simpa using hP)).congr hPm).mono hsub

/-- A search that reports nothing leaves every reachable state dead. -/
theorem streettRun_none_dead (cs : CompiledSpec State L) (hcs : cs.WF) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (initialStates : List State)
    (fr : FiniteReach initialStates succs) (hnone : (streettRun cs curRegions succs edgeMarks expand initialStates).1 = none) :
    ∀ s, Reachable initialStates succs s → s ∈ (streettRun cs curRegions succs edgeMarks expand initialStates).2.dead := by
  unfold streettRun at hnone ⊢
  intro s hs
  have hwf := (genericDFS_searchOutcome (streettOps cs curRegions) (streettView cs curRegions) (streettLowlinkLawful cs curRegions)
    (streettLawful cs curRegions hcs) streettInitAux_wf succs edgeMarks expand hexp initialStates fr).1 hnone
  have hexpl := genericDFS_returns_none_fully_explored (streettOps cs curRegions) succs edgeMarks expand hexp (streettLawful cs curRegions hcs)
    (Reachable initialStates succs)
    (fun aux q hq hw hu => dfsGo_ne_none (streettOps cs curRegions) succs edgeMarks expand hexp initialStates fr
      (streettLawful cs curRegions hcs) _ _ ((streettLawful cs curRegions hcs).wf_push aux q _ hu hw)
      (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; exact hexp.fst q)
      (fun st hst => by simp only [List.mem_singleton] at hst; subst hst; exact hq))
    initialStates (fun q hq => Reachable.base hq)
    (genericDFSGo_ne_none (streettOps cs curRegions) succs edgeMarks expand initialStates _)
    streettInitAux_wf (streettInitAux_unknown cs curRegions) hnone s hs
  set fin := (genericDFS (streettOps cs curRegions) succs edgeMarks expand initialStates (streettOps cs curRegions).initAux).2 with hfin
  -- no frame is open, so nothing is live
  have hlive : ((streettView cs curRegions).live fin).size = 0 := by
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

/-- A witness the prune reports comes from the run on one candidate, and that candidate lies in `Q`
whenever every queued candidate does. The candidate itself is returned, since its graph is where
`buildResult` has to rebuild the cycle. -/
theorem pruneLoop_found (cs : CompiledSpec State L) (hcs : cs.WF) (Q : State → Prop) :
    ∀ e q r, pruneLoop cs cs.spec e q = some r → (∀ C ∈ q, ∀ s ∈ C.states, Q s) →
      ∀ anchor wit wopts C, r.1 = some (anchor, wit, wopts, C) →
        (∀ s ∈ C.states, Q s) ∧ ∃ stem,
          (candidateRun cs cs.spec C).1 = some (anchor, stem) ∧
          (candidateRun cs cs.spec C).2.witness = wit ∧
          (candidateRun cs cs.spec C).2.witnessOpts = wopts := by
  refine pruneLoop.partial_correctness cs cs.spec
    (fun _ q r => (∀ C ∈ q, ∀ s ∈ C.states, Q s) → ∀ anchor wit wopts C,
      r.1 = some (anchor, wit, wopts, C) →
        (∀ s ∈ C.states, Q s) ∧ ∃ stem,
          (candidateRun cs cs.spec C).1 = some (anchor, stem) ∧
          (candidateRun cs cs.spec C).2.witness = wit ∧
          (candidateRun cs cs.spec C).2.witnessOpts = wopts) ?_
  intro f ih e q r hr hQ anchor wit wopts D hfound
  cases q with
  | nil =>
    simp at hr
    subst hr
    simp at hfound
  | cons C rest =>
    cases hrun : (candidateRun cs cs.spec C).1 with
    | some x =>
      obtain ⟨a, st⟩ := x
      simp [hrun] at hr
      subst hr
      simp at hfound
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hfound
      exact ⟨hQ C (by simp), st, hrun, rfl, rfl⟩
    | none =>
      simp [hrun] at hr
      refine ih _ _ r hr (fun P hP s hs => ?_) anchor wit wopts D hfound
      rcases List.mem_append.mp hP with hP | hP
      -- a candidate queued by this run lies inside the candidate it ran on
      · exact hQ C (by simp) s (mem_of_reachable_sccSuccs
          (streettRun_pending_reachable (cs.atBits C.regions) (hcs.atBits C.regions) C.regions
            (C.graph cs cs.spec) (cs.spec.regionMarks (C.region cs)) (C.expand cs cs.spec)
            (C.expand_coherent cs cs.spec) C.states.toList P (Array.mem_def.mpr hP) s hs))
      · exact hQ P (by simp [hP]) s hs

/-- An `.empty` answer means the search refuted the whole graph in the sense of `RRefutedFrom`. -/
theorem streettCheck_empty_refutes (spec : RStreettSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (hcompat : spec.Compat succs edgeMarks)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (initialStates : List State)
    (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < spec.numMarks)
    (fr : FiniteReach initialStates succs) {n : Nat}
    (h : streettCheck (CompiledSpec.of spec) succs edgeMarks expand initialStates = .empty n) :
    RRefutedFrom spec succs edgeMarks initialStates := by
  have hcs := CompiledSpec.of_wf spec
  have hbound : ∀ s t, ∀ m ∈ edgeMarks s t, m < (CompiledSpec.of spec).numMarks := hmarksBound
  rcases hrun : streettRun (CompiledSpec.of spec) 0 succs edgeMarks expand initialStates with
    ⟨_ | ⟨anchor, stem⟩, aux⟩
  · rcases hq : pruneLoop (CompiledSpec.of spec) (CompiledSpec.of spec).spec
        (aux.live.size + aux.dead.size) aux.pending.toList with _ | ⟨_ | ⟨anchor, wit, wopts, C⟩, n'⟩
    · exact absurd hq (pruneLoop_defined _ hcs _ _ _)
    · exact refutedFrom_of_none (CompiledSpec.of spec) hcs rfl succs edgeMarks hcompat expand hexp
        initialStates fr hbound (by rw [hrun]) (e := aux.live.size + aux.dead.size)
        (r := (none, n')) (by rw [hrun]; exact hq) rfl
    -- a genuine find in a pruned candidate never degrades to `.empty`
    · exfalso
      have hdead : ∀ s, Reachable initialStates succs s → s ∈ aux.dead := by
        have := streettRun_none_dead _ hcs succs edgeMarks expand hexp initialStates fr (by rw [hrun])
        rwa [hrun] at this
      have hpend : ∀ P ∈ aux.pending, ∀ s ∈ P.states, Reachable initialStates succs s := by
        have := streettRun_pending_reachable _ hcs 0 succs edgeMarks expand hexp initialStates
        rwa [hrun] at this
      -- the find comes from the run on one candidate, and every candidate is reachable
      obtain ⟨hCreach, stem', hfound, hwit, hwopts⟩ := pruneLoop_found _ hcs
        (Reachable initialStates succs) _ _ _ hq (fun P hP s hs => hpend P (by simpa using hP) s hs)
        anchor wit wopts C rfl
      simp only [candidateRun] at hfound hwit hwopts
      obtain ⟨hconn, hA, hanchor, hstem', hopts⟩ :=
        streettRun_found ((CompiledSpec.of spec).atBits C.regions) C.regions
          (hcs.atBits C.regions) (C.graph (CompiledSpec.of spec) (CompiledSpec.of spec).spec)
          ((CompiledSpec.of spec).spec.regionMarks (C.region (CompiledSpec.of spec)))
          (C.expand (CompiledSpec.of spec) (CompiledSpec.of spec).spec)
          (C.expand_coherent (CompiledSpec.of spec) (CompiledSpec.of spec).spec) C.states.toList
          (finiteReach_sccSuccs _ C.states) hfound
      rw [streettSccHint, hwit] at hconn hA hanchor
      rw [streettSccHint, hwit, hwopts] at hopts
      -- the anchor ends the candidate run's own stem, so it lies in the candidate
      have hanchorC : anchor ∈ C.states := by
        obtain ⟨hs, hhead, hchain, hlast⟩ := hstem'
        have hheadC : stem'.head hs ∈ C.states := by simpa using hhead
        rcases chain_reaches stem' hchain hs with heq | hp
        · rw [← hlast, ← heq]
          exact hheadC
        · rw [← hlast]
          exact hp.closed (P := (· ∈ C.states)) hheadC
            fun _ _ y hy => Std.HashSet.mem_iff_contains.mpr (Array.mem_filter.mp hy).2
      have hg : ∀ a b, b ∈ C.graph (CompiledSpec.of spec) (CompiledSpec.of spec).spec a → b ∈ succs a :=
        Candidate.graph_sub hcompat C
      -- the marks the candidate run saw are marks of the ambient graph
      -- the marks the candidate run saw are exactly the ones the report is validated against
      have hAamb : AcceptingMarks (C.graph (CompiledSpec.of spec) (CompiledSpec.of spec).spec)
          ((CompiledSpec.of spec).spec.regionMarks (C.region (CompiledSpec.of spec)))
          (CompiledSpec.of spec).numMarks (witnessSet wit) := hA
      have hbound' : ∀ s t, ∀ m ∈
          (CompiledSpec.of spec).spec.regionMarks (C.region (CompiledSpec.of spec)) s t,
          m < ((CompiledSpec.of spec).atBits C.regions).numMarks :=
        regionMarks_lt hcompat hbound _
      -- the BFS over the first run's dead states finds a stem to it
      obtain ⟨path, hpath, hstem⟩ := bfsFindPath_stem hdead (hCreach anchor hanchorC)
      rw [streettCheck, hrun] at h
      simp only [hq, hpath, Option.getD_some] at h
      exact buildResult_ne_empty _ (hcs.atBits C.regions) succs hg
        (fun _ _ hb => (Array.mem_filter.mp hb).1) _ initialStates hbound' _
        hconn hAamb hanchor hstem hopts h
  -- a genuine find on the whole graph never degrades to `.empty`
  · exfalso
    have hfound : (streettRun (CompiledSpec.of spec) 0 succs edgeMarks expand initialStates).1
        = some (anchor, stem) := by rw [hrun]
    obtain ⟨hconn, hA, hanchor, hstem, hopts⟩ :=
      streettRun_found _ 0 hcs succs edgeMarks expand hexp initialStates fr hfound
    rw [hrun] at hconn hA hanchor hopts
    rw [streettCheck, hrun] at h
    -- the top-level spec restricts nothing, so its region marks are the ambient ones
    have hreg : ∀ s t m, m ∈ (CompiledSpec.of spec).spec.regionMarks
        (CompiledSpec.of spec).restrict s t ↔ m ∈ edgeMarks s t := by
      intro s t m
      show m ∈ spec.regionMarks (fun _ => true) s t ↔ _
      exact hcompat.marks_top s t m
    refine buildResult_ne_empty _ hcs succs (fun _ _ hb => hb)
      (fun a b hb => by
        show b ∈ spec.regionSuccs (fun _ => true) a
        rw [hcompat.succs_top a]; exact hb)
      _ initialStates
      (fun s t m hm => hbound s t m ((hreg s t m).mp hm)) _ hconn
      (hA.mono_marks fun s t m hm => (hreg s t m).mpr hm) hanchor hstem hopts h

/-- Completeness: an `.empty` answer rules out every fair accepting SCC. -/
theorem streettCheck_empty_no_fairSCC (spec : RStreettSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (hcompat : spec.Compat succs edgeMarks)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (initialStates : List State)
    (hmarksBound : ∀ s t, ∀ m ∈ edgeMarks s t, m < spec.numMarks)
    (fr : FiniteReach initialStates succs) {n : Nat}
    (h : streettCheck (CompiledSpec.of spec) succs edgeMarks expand initialStates = .empty n)
    (A : RFairSCC initialStates succs spec) : False :=
  (streettCheck_empty_refutes spec succs edgeMarks hcompat expand hexp initialStates hmarksBound fr
    h).no_fairSCC hcompat A

end LTLLib
