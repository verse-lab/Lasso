/-
  VWAA to TGBA on the fly, `[GO01]` Step 2 with on-the-fly dominance `≼` and OR-merging of candidates sharing a target
  and marks. A TGBA state is a set of VWAA ids as a bitmask, explored by a worklist from the singleton of the initial id.

  `productTrans` is `[GO01]`'s `δ″ = ⊗_{q∈e} δ(q)`, dropping a combination as soon as its guard is unsatisfiable (as
  LTL3BA's `merge_to_prod` does), and records the finals of `e` whose chosen component does not loop in them,
  `[BKŘS12]` §6's modified `T_f`.
  `inTf` adds `[GO01]`'s own `T_f = {(O, α, O′) | f ∉ O′ or ∃(β, O″) ∈ δ(f), α ⊆ β, f ∉ O″ ⊆ O′}`, with `f ∉ target`
  per Remark 3, checked against the disjunction of every non-looping compatible alternative of `f` at once.
  Marks are bitmasks over the indices of `finals`. `reduceCandidates` merges and prunes a state's product transitions
  before any of their targets is explored, so a dominated or duplicate target never gets its own TGBA state.

  Defines:
  - `productTrans`: the VWAA transition product over a state mask
  - `inTf`, `computeMarks`, `markedProduct`: the acceptance marks of a product transition, and of a whole state
  - `candBeats`, `dominanceFilter`: `[GO01]` Step 2's `≼`, dropping a dominated candidate
  - `beatenIn`, `dominanceFilterFast`: `dominanceFilter` with dominators looked up by target sub-mask, the compiled version
  - `reduceCandidates`: OR-merging then dominance over one state's product transitions
  - `TGBAConstructState`, `exploreState`: the worklist exploration
  - `buildTGBA`: `ConcreteVWAA α → Option (TGBA α)`, one `TGBA.Transition` per non-contradictory cube
  - `canonicalTrans`, `canonicalTGBA`: the `SetTGBA` the construction denotes, ignoring numbering

  Proves:
  - `buildTGBA_ne_none`, `buildTGBA_wellFormed`: termination and well-formedness
  - `exploreState_injective`, `exploreState_denotes`: the worklist numbering is injective and every finished id
    records exactly its state's reduced candidates
  - `canonicalTrans_soundTrans`, `canonicalTrans_completeTransTight`: the construction meets `[GO01]` Theorem 2's
    (S) and tight (C) conditions
  - `dominanceFilter_eq_dominanceFilterFast` (`@[csimp]`): the indexed filter drops exactly the same candidates

  References:
  - `[GO01]` Gastin, Oddoux. Fast LTL to Büchi Automata Translation. CAV'01, Step 2, Theorem 2.
  - `[BKŘS12]` Babiak, Křetínský, Řehák, Strejček. LTL to Büchi Automata Translation: Fast and More
    Deterministic. TACAS'12, §6.
  - `[LTL3BA-1.1.3]` Babiak. LTL3BA 1.1.3, `generalized.cpp`, `AProd::merge_to_prod` and `cGTrans::add_trans`.
  - `[JN18]` Jantsch, Norrish. Verifying the LTL to Büchi Automata Translation via Very Weak Alternating
    Automata. ITP'18, the worklist termination argument.

  Sections:
  - Transition product
  - Acceptance marks
  - Reducing candidate transitions
  - Worklist exploration
  - Export
  - Termination
  - Well-formedness
  - Id-renumbering
  - The exported TGBA
  - Abstract correspondence
  - OR-merging and dominance preservation
  - The canonical `SetTGBA`
-/
import LTLLib.TGBA
import LTLLib.TGBABased.LTLtoTGBA.Label
import LTLLib.TGBABased.LTLtoTGBA.VWAA
import LTLLib.TGBABased.LTLtoTGBA.AbstractSpec.VWAAToTGBA

namespace LTLLib

variable {α : Type u} [BEq α] [Hashable α]

/-! ## Transition product -/

/-- One step of `productTrans`, extending every partial product by one alternative of `q`, dropping an unsatisfiable
combination. -/
def productStep (cv : ConcreteVWAA α) (acc : List (DNF α × Nat × Nat)) (q : Nat) : List (DNF α × Nat × Nat) :=
  acc.flatMap fun c => (cv.trans.getD q []).filterMap fun p =>
    let g := DNF.and c.1 p.1
    if DNF.isEmpty g then none
    else some (g, c.2.1 ||| p.2, if cv.final.getD q false && !p.2.testBit q then c.2.2 ||| bit q else c.2.2)

/-- `⊗_{q∈e} cv.trans[q]` over the ids of the mask `e`, the identity `(⊤, ∅, ∅)` when `e` is empty. The third component
is the mask of the finals of `e` whose chosen alternative does not loop in them, `[BKŘS12]` §6's modified `T_f`. -/
def productTrans (cv : ConcreteVWAA α) (e : Nat) : List (DNF α × Nat × Nat) :=
  (maskMembers e).foldl (productStep cv) [(DNF.top, 0, 0)]

/-! ## Acceptance marks -/

/-- `[GO01]` Definition 5's `T_f`: `f ∉ e'`, or `g` is covered by the disjunction of every transition of `f` that does
not loop in `f` and whose target lies inside `e'`, as distinct letters of `g` may escape through distinct alternatives. -/
def inTf (cv : ConcreteVWAA α) (f : Nat) (g : DNF α) (e' : Nat) : Bool :=
  !e'.testBit f || DNF.impliesFast g
    ((cv.trans.getD f []).flatMap fun p => if !p.2.testBit f && maskSub p.2 e' then p.1 else [])

/-- `computeMarks`'s per-index condition: the final `finals[i]` escaped its own loop, or `inTf` holds for it. -/
def marksCond (cv : ConcreteVWAA α) (finals : Array Nat) (g : DNF α) (e' escOwn : Nat) (i : Nat) : Bool :=
  escOwn.testBit (finals.getD i 0) || inTf cv (finals.getD i 0) g e'

/-- The marks of the product transition `(g, e')` whose own component choices escaped `escOwn`, bit `i` standing for
`finals[i]`. -/
def computeMarks (cv : ConcreteVWAA α) (finals : Array Nat) (g : DNF α) (e' escOwn : Nat) : Nat :=
  (List.range finals.size).foldl (fun acc i => if marksCond cv finals g e' escOwn i then acc ||| bit i else acc) 0

/-- Every product transition of `e` with its marks attached. -/
def markedProduct (cv : ConcreteVWAA α) (finals : Array Nat) (e : Nat) : List (DNF α × Nat × Nat) :=
  (productTrans cv e).map fun c => (c.1, c.2.1, computeMarks cv finals c.1 c.2.1 c.2.2)

/-! ## Reducing candidate transitions -/

/-- `c1` dominates `c2`: another target no larger, marks no fewer, guard implied, `[GO01]` Step 2's `≼`. -/
def candBeats (c1 c2 : DNF α × Nat × Nat) : Bool :=
  !(c2.2 == c1.2) && maskSub c1.2.1 c2.2.1 && maskSub c2.2.2 c1.2.2 && DNF.impliesFast c2.1 c1.1

/-- Drop every candidate dominated by a sibling candidate of the same state. -/
def dominanceFilter (l : List (DNF α × Nat × Nat)) : List (DNF α × Nat × Nat) :=
  l.filter fun c2 => !l.any fun c1 => candBeats c1 c2

/-- Some candidate of `l` beats `c2`, looked up in `byTarget` under the sub-masks of `c2`'s target when there are fewer
of those than the `n` candidates, since a dominator's target is a sub-mask of the dominated one's. -/
def beatenIn (l : List (DNF α × Nat × Nat)) (byTarget : Std.HashMap Nat (List (DNF α × Nat × Nat))) (n : Nat)
    (c2 : DNF α × Nat × Nat) : Bool :=
  if 2 ^ (maskMembers c2.2.1).length < n then
    (submasks c2.2.1).any fun s => (byTarget.getD s []).any (candBeats · c2)
  else l.any (candBeats · c2)

/-- `dominanceFilter` with dominators looked up by target, the version compiled code runs. -/
def dominanceFilterFast (l : List (DNF α × Nat × Nat)) : List (DNF α × Nat × Nat) :=
  let byTarget := groupByKey (fun c : DNF α × Nat × Nat => c.2.1) l
  let n := l.length
  l.filter fun c2 => !beatenIn l byTarget n c2

/-- OR-merge the candidates sharing a target and marks, then drop the dominated ones. -/
def reduceCandidates (l : List (DNF α × Nat × Nat)) : List (DNF α × Nat × Nat) :=
  dominanceFilter (mergeByTarget l)

/-! ## Worklist exploration -/

/-- The worklist state of `exploreState`. -/
structure TGBAConstructState (α : Type u) [BEq α] [Hashable α] where
  -- the state numbering
  visited : Std.HashMap Nat Nat
  nextId : Nat
  -- the outgoing transitions of every finished state, keyed by its number
  transitions : Std.HashMap Nat (Array (DNF α × Nat × Nat))

/-- Explore `e`, reusing its number if already visited, otherwise exploring every successor first and recording its
own transitions last. -/
def exploreState (cv : ConcreteVWAA α) (finals : Array Nat) (e : Nat) (st : TGBAConstructState α) :
    Option (Nat × TGBAConstructState α) := do
  match st.visited[e]? with
  | some id => pure (id, st)
  | none =>
    let id := st.nextId
    let st : TGBAConstructState α := { st with visited := st.visited.insert e id, nextId := id + 1 }
    let (transArr, st) ← (reduceCandidates (markedProduct cv finals e)).foldlM
      (init := ((#[] : Array (DNF α × Nat × Nat)), st)) fun (acc, st) (g, e', m) => do
        let (tid, st) ← exploreState cv finals e' st
        pure (acc.push (g, tid, m), st)
    pure (id, { st with transitions := st.transitions.insert id transArr })
partial_fixpoint

/-! ## Export -/

/-- The VWAA ids of `cv`'s final states, in increasing order, acceptance set `i` standing for `finalsOf cv`'s `i`-th. -/
def finalsOf (cv : ConcreteVWAA α) : Array Nat :=
  ((List.range cv.table.formulas.size).filter fun i => cv.final.getD i false).toArray

/-- The empty worklist state `buildTGBA` starts from. -/
def initConstructState : TGBAConstructState α :=
  { visited := Std.HashMap.emptyWithCapacity 16, nextId := 0, transitions := Std.HashMap.emptyWithCapacity 16 }

/-- The numbered `TGBA α` a finished worklist state denotes, one `TGBA.Transition` per non-contradictory cube of a
recorded transition's guard. -/
def exportTGBA (finals : Array Nat) (st : TGBAConstructState α) (initId : Nat) : TGBA α where
  states := Std.HashSet.ofList (st.visited.toList.map (·.2))
  initialStates := Std.HashSet.emptyWithCapacity 1 |>.insert initId
  successors := st.transitions.map fun _ arr =>
    arr.flatMap fun (g, tid, marks) =>
      let ms := Std.HashSet.ofList (maskMembers marks)
      (DNF.cubes g).toArray.map fun c =>
        ({ target := tid, positiveProps := c.pos, negativeProps := c.neg, acceptMarks := ms } : TGBA.Transition α)
  numAcceptSets := finals.size

/-- Explore from the singleton state of `cv`'s initial id and export, `none` only if the worklist does not terminate,
which never happens on a finite VWAA. -/
def buildTGBA (cv : ConcreteVWAA α) : Option (TGBA α) := do
  let (initId, st) ← exploreState cv (finalsOf cv) (bit cv.initial) initConstructState
  pure (exportTGBA (finalsOf cv) st initId)

/-! ## Termination

Every explored state is a mask below `2 ^ n`, and each fresh state marks one more of them as visited, `[JN18]`'s
`NoNodeProcessedTwice` argument (Schimpf et al. TPHOLs'09). -/

/-- Every partial product's target stays below `2 ^ n`, given every target of `cv`'s own transitions does. -/
private theorem productStep_target_lt {cv : ConcreteVWAA α} {n : Nat}
    (hbound : ∀ i g t, (g, t) ∈ cv.trans.getD i [] → ∀ j, t.testBit j = true → j < n)
    {acc : List (DNF α × Nat × Nat)} (hacc : ∀ c ∈ acc, c.2.1 < 2 ^ n) (q : Nat) :
    ∀ c ∈ productStep cv acc q, c.2.1 < 2 ^ n := by
  intro c hc
  obtain ⟨c1, hc1, hc'⟩ := List.mem_flatMap.mp hc
  obtain ⟨p, hp, heq⟩ := List.mem_filterMap.mp hc'
  dsimp only at heq
  split at heq
  · exact absurd heq (by simp)
  · rw [← Option.some.inj heq]
    exact Nat.or_lt_two_pow (hacc c1 hc1) (lt_two_pow_of_testBit (hbound q p.1 p.2 hp))

/-- Every product-transition target stays below `2 ^ n`, given every target of `cv`'s own transitions does. -/
theorem productTrans_target_lt {cv : ConcreteVWAA α} {n : Nat}
    (hbound : ∀ i g t, (g, t) ∈ cv.trans.getD i [] → ∀ j, t.testBit j = true → j < n) (e : Nat) :
    ∀ c ∈ productTrans cv e, c.2.1 < 2 ^ n := by
  unfold productTrans
  suffices H : ∀ (l : List Nat) (acc : List (DNF α × Nat × Nat)), (∀ c ∈ acc, c.2.1 < 2 ^ n) →
      ∀ c ∈ l.foldl (productStep cv) acc, c.2.1 < 2 ^ n by
    exact H _ _ fun c hc => by rw [List.mem_singleton] at hc; subst hc; exact Nat.two_pow_pos n
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons q qs ih => intro acc h; exact ih _ (productStep_target_lt hbound h q)

/-- Reduction never changes a candidate's target or marks. -/
theorem reduceCandidates_target_mem {l : List (DNF α × Nat × Nat)} {g : DNF α} {t m : Nat}
    (h : (g, t, m) ∈ reduceCandidates l) : ∃ g0, (g0, t, m) ∈ l :=
  mergeByTarget_key_mem (List.mem_filter.mp h).1

/-- A reduced candidate is a marked product transition. -/
theorem mem_markedProduct_of_reduce {cv : ConcreteVWAA α} {finals : Array Nat} {e : Nat} {g : DNF α} {t m : Nat}
    (h : (g, t, m) ∈ reduceCandidates (markedProduct cv finals e)) :
    ∃ c ∈ productTrans cv e, c.2.1 = t ∧ computeMarks cv finals c.1 c.2.1 c.2.2 = m := by
  obtain ⟨g0, hg0⟩ := reduceCandidates_target_mem h
  obtain ⟨c, hc, heq⟩ := List.mem_map.mp hg0
  simp only [Prod.mk.injEq] at heq
  exact ⟨c, hc, heq.2.1, heq.2.2⟩

/-- The finite universe of every state `exploreState` can ever produce with a size-`n` VWAA. -/
def validStates (n : Nat) : Finset Nat := Finset.range (2 ^ n)

/-- The number of valid states `visited` has not yet marked, `exploreState`'s termination measure. -/
def unexploredCardOf (n : Nat) (visited : Std.HashMap Nat Nat) : Nat :=
  ((validStates n).filter fun e => !visited.contains e).card

/-- A fresh valid state strictly shrinks the unexplored count. -/
theorem unexploredCardOf_insert_lt (n : Nat) {visited : Std.HashMap Nat Nat} {e : Nat}
    {id : Nat} (he : e ∈ validStates n) (hne : visited.contains e = false) :
    unexploredCardOf n (visited.insert e id) < unexploredCardOf n visited := by
  have heq : (validStates n).filter (fun x => !(visited.insert e id).contains x) =
      ((validStates n).filter (fun x => !visited.contains x)).erase e := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Std.HashMap.contains_insert]
    by_cases hxe : x = e
    · subst hxe; simp [hne]
    · simp [hxe, Ne.symm hxe]
  unfold unexploredCardOf
  rw [heq]
  exact Finset.card_erase_lt_of_mem (Finset.mem_filter.mpr ⟨he, by simp [hne]⟩)

/-- `exploreState` is total and never increases its measure. -/
theorem exploreState_spec (cv : ConcreteVWAA α) (n : Nat)
    (hbound : ∀ i g t, (g, t) ∈ cv.trans.getD i [] → ∀ j, t.testBit j = true → j < n) (finals : Array Nat) :
    ∀ m e, e ∈ validStates n → ∀ st, unexploredCardOf n st.visited ≤ m →
      ∃ r, exploreState cv finals e st = some r ∧
        unexploredCardOf n r.2.visited ≤ unexploredCardOf n st.visited := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro e he st hm
  rw [exploreState.eq_def]
  cases hvis : st.visited[e]? with
  | some id =>
    refine ⟨(id, st), ?_, le_refl _⟩
    simp only
    rfl
  | none =>
    simp only
    have hcontains : st.visited.contains e = false := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, hvis]
      rfl
    set st1 : TGBAConstructState α :=
      { st with visited := st.visited.insert e st.nextId, nextId := st.nextId + 1 } with hst1
    have hlt : unexploredCardOf n st1.visited < unexploredCardOf n st.visited :=
      unexploredCardOf_insert_lt n he hcontains
    have hmlt : unexploredCardOf n st1.visited < m := lt_of_lt_of_le hlt hm
    set candidates := markedProduct cv finals e with hcand
    suffices H : ∀ l : List (DNF α × Nat × Nat),
        (∀ g e' mk, (g, e', mk) ∈ l → e' ∈ validStates n) →
        ∀ (accInit : Array (DNF α × Nat × Nat)) (stf : TGBAConstructState α),
        unexploredCardOf n stf.visited ≤ unexploredCardOf n st1.visited →
        ∃ r : Array (DNF α × Nat × Nat) × TGBAConstructState α,
          l.foldlM (m := Option) (init := (accInit, stf))
            (fun (acc, st) ((g, e', mk) : DNF α × Nat × Nat) => do
              let (tid, st) ← exploreState cv finals e' st
              pure (acc.push (g, tid, mk), st)) = some r ∧
          unexploredCardOf n r.2.visited ≤ unexploredCardOf n stf.visited by
      obtain ⟨⟨transArr, stFinal⟩, hfold, hmono⟩ :=
        H (reduceCandidates candidates) (fun g e' mk hmk => by
          obtain ⟨c, hc, hct, -⟩ := mem_markedProduct_of_reduce hmk
          rw [← hct]
          exact Finset.mem_range.mpr (productTrans_target_lt hbound e c hc)) #[] st1 (le_refl _)
      refine ⟨(st.nextId, { stFinal with transitions := stFinal.transitions.insert st.nextId transArr }), ?_, ?_⟩
      · simp only [hfold]
        rfl
      · exact hmono.trans (le_of_lt hlt)
    intro l
    induction l with
    | nil =>
      intro _ accInit stf hstf
      exact ⟨(accInit, stf), rfl, le_refl _⟩
    | cons hd tl ihl =>
      intro hvalid accInit stf hstf
      obtain ⟨g, e', mk⟩ := hd
      have he'valid : e' ∈ validStates n := hvalid g e' mk (by simp)
      have hstfm : unexploredCardOf n stf.visited < m := lt_of_le_of_lt hstf hmlt
      obtain ⟨r1, hr1, hr1mono⟩ := ih (unexploredCardOf n stf.visited) hstfm e' he'valid stf (le_refl _)
      obtain ⟨tid, st2⟩ := r1
      have hstep : unexploredCardOf n st2.visited ≤ unexploredCardOf n st1.visited :=
        le_trans hr1mono hstf
      obtain ⟨r2, hr2, hr2mono⟩ :=
        ihl (fun g e' mk hmk => hvalid g e' mk (List.mem_cons_of_mem _ hmk)) (accInit.push (g, tid, mk)) st2 hstep
      refine ⟨r2, ?_, hr2mono.trans hr1mono⟩
      rw [List.foldlM_cons]
      simp only [hr1, Option.pure_def]
      exact hr2

theorem exploreState_ne_none (cv : ConcreteVWAA α) (n : Nat)
    (hbound : ∀ i g t, (g, t) ∈ cv.trans.getD i [] → ∀ j, t.testBit j = true → j < n) (finals : Array Nat)
    (e : Nat) (he : e ∈ validStates n) (st : TGBAConstructState α) :
    exploreState cv finals e st ≠ none := by
  obtain ⟨r, hr, _⟩ := exploreState_spec cv n hbound finals (unexploredCardOf n st.visited) e he st (le_refl _)
  rw [hr]
  simp

/-- `buildTGBA` always succeeds on a built VWAA. -/
theorem buildTGBA_ne_none [LawfulBEq α] [LawfulHashable α] (φ : NNF α) :
    buildTGBA (ConcreteVWAA.build φ) ≠ none := by
  have hinit : bit (ConcreteVWAA.build φ).initial ∈ validStates (ConcreteVWAA.build φ).trans.size := by
    unfold validStates bit
    rw [Finset.mem_range, Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by omega) (ConcreteVWAA.build_initial_lt_size φ)
  have hne := exploreState_ne_none (ConcreteVWAA.build φ) (ConcreteVWAA.build φ).trans.size
    (ConcreteVWAA.build_target_lt_size φ) (finalsOf (ConcreteVWAA.build φ)) _ hinit initConstructState
  unfold buildTGBA
  cases hex : exploreState (ConcreteVWAA.build φ) (finalsOf (ConcreteVWAA.build φ))
      (bit (ConcreteVWAA.build φ).initial) initConstructState with
  | none => exact absurd hex hne
  | some r => simp

/-! ## Well-formedness -/

private theorem testBit_foldl_marks (P : Nat → Bool) (l : List Nat) (acc i : Nat) :
    (l.foldl (fun acc j => if P j then acc ||| bit j else acc) acc).testBit i = true ↔
      acc.testBit i = true ∨ (i ∈ l ∧ P i = true) := by
  induction l generalizing acc with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih]
    by_cases hj : P j = true
    · simp only [hj, if_true, Nat.testBit_or, bit, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
        decide_eq_true_eq, List.mem_cons]
      grind
    · simp only [hj, Bool.false_eq_true, if_false, List.mem_cons]
      grind

/-- `computeMarks` is exact: bit `i` is set exactly when `i` indexes `finals` and `marksCond` holds there. -/
theorem testBit_computeMarks {cv : ConcreteVWAA α} {finals : Array Nat} {g : DNF α} {e' escOwn i : Nat} :
    (computeMarks cv finals g e' escOwn).testBit i = true ↔
      i < finals.size ∧ marksCond cv finals g e' escOwn i = true := by
  unfold computeMarks
  rw [testBit_foldl_marks]
  simp [List.mem_range]

/-- Every reduced candidate's marks index into `finals`. -/
theorem reduceCandidates_markedProduct_marks_lt {cv : ConcreteVWAA α} {finals : Array Nat} {e : Nat} {g : DNF α}
    {t m : Nat} (h : (g, t, m) ∈ reduceCandidates (markedProduct cv finals e)) :
    ∀ i, m.testBit i = true → i < finals.size := by
  obtain ⟨c, -, -, rfl⟩ := mem_markedProduct_of_reduce h
  exact fun i hi => (testBit_computeMarks.mp hi).1

private theorem getD_eq_getElem_of_lt {finals : Array Nat} {i : Nat} (h : i < finals.size) :
    finals.getD i 0 = finals[i] := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]

/-- The VWAA ids the mark mask `m` stands for, through `finals`'s indexing. -/
def idMarksOf (finals : Array Nat) (m : Nat) : Finset Nat :=
  ((maskMembers m).map (finals.getD · 0)).toFinset

/-- Read through a duplicate-free `finals`, an in-range mark mask marks `finals[i]` exactly when it has bit `i`. -/
theorem getElem_mem_idMarksOf_iff {finals : Array Nat} (hnd : finals.toList.Nodup) {m : Nat}
    (hm : ∀ j, m.testBit j = true → j < finals.size) {i : Nat} (hi : i < finals.size) :
    finals[i] ∈ idMarksOf finals m ↔ m.testBit i = true := by
  unfold idMarksOf
  simp only [List.mem_toFinset, List.mem_map, mem_maskMembers]
  constructor
  · rintro ⟨j, hj, hjeq⟩
    have hjlt := hm j hj
    rw [getD_eq_getElem_of_lt hjlt] at hjeq
    have hji : j = i := by
      have h1 : finals.toList[j]'(by simpa using hjlt) = finals.toList[i]'(by simpa using hi) := by
        simpa using hjeq
      exact (List.Nodup.getElem_inj_iff hnd).mp h1
    exact hji ▸ hj
  · intro h
    exact ⟨i, h, getD_eq_getElem_of_lt hi⟩

/-- `idMarksOf` is monotone: a bigger mark mask reads off a bigger set of VWAA ids. -/
theorem idMarksOf_mono {finals : Array Nat} {m1 m2 : Nat} (h : maskSub m1 m2 = true) :
    idMarksOf finals m1 ⊆ idMarksOf finals m2 := by
  unfold idMarksOf
  intro f hf
  simp only [List.mem_toFinset, List.mem_map, mem_maskMembers] at hf ⊢
  obtain ⟨i, hi, hif⟩ := hf
  exact ⟨i, maskSub_iff.mp h i hi, hif⟩

/-- The marks of `computeMarks`, read as VWAA ids, are exactly the finals `escOwn` has or `inTf` holds for. -/
theorem idMarksOf_computeMarks {cv : ConcreteVWAA α} {finals : Array Nat} {g : DNF α} {e' escOwn : Nat} :
    idMarksOf finals (computeMarks cv finals g e' escOwn) =
      (finals.toList.filter fun f => escOwn.testBit f || inTf cv f g e').toFinset := by
  unfold idMarksOf
  ext f
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, mem_maskMembers]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨hbound, hcond⟩ := testBit_computeMarks.mp hi
    unfold marksCond at hcond
    rw [getD_eq_getElem_of_lt hbound] at hcond ⊢
    exact ⟨Array.mem_def.mp (Array.getElem_mem hbound), hcond⟩
  · rintro ⟨hmem, hcond⟩
    obtain ⟨i, hilt, heq⟩ := List.mem_iff_getElem.mp hmem
    have hilt' : i < finals.size := by simpa using hilt
    have hival : finals.getD i 0 = f := by
      rw [getD_eq_getElem_of_lt hilt', ← Array.getElem_toList (h := hilt'), heq]
    refine ⟨i, testBit_computeMarks.mpr ⟨hilt', ?_⟩, hival⟩
    unfold marksCond
    rw [hival]; exact hcond

/-- `st'` extends `st`: every id `st` has already assigned persists unchanged in `st'`. -/
def Extends (st st' : TGBAConstructState α) : Prop :=
  ∀ (e : Nat) (id : Nat), st.visited[e]? = some id → st'.visited[e]? = some id

theorem Extends.refl (st : TGBAConstructState α) : Extends st st := fun _ _ h => h

theorem Extends.trans {a b c : TGBAConstructState α} (h1 : Extends a b) (h2 : Extends b c) :
    Extends a c :=
  fun e id h => h2 e id (h1 e id h)

/-- Every transition `st` has recorded targets an id `st` has itself assigned, with marks in range. -/
def TransitionsWF (finals : Array Nat) (st : TGBAConstructState α) : Prop :=
  ∀ (id0 : Nat) (arr : Array (DNF α × Nat × Nat)), st.transitions[id0]? = some arr →
    ∀ p ∈ arr.toList, (∃ e' : Nat, st.visited[e']? = some p.2.1) ∧ ∀ i, p.2.2.testBit i = true → i < finals.size

private def AccWF (finals : Array Nat) (st : TGBAConstructState α) (acc : Array (DNF α × Nat × Nat)) : Prop :=
  ∀ p ∈ acc.toList, (∃ e' : Nat, st.visited[e']? = some p.2.1) ∧ ∀ i, p.2.2.testBit i = true → i < finals.size

/-- `exploreState` only extends its state, returns an id it has assigned, and preserves `TransitionsWF`. -/
theorem exploreState_wf (cv : ConcreteVWAA α) (finals : Array Nat) :
    ∀ (e : Nat) (st : TGBAConstructState α) (r : Nat × TGBAConstructState α),
      exploreState cv finals e st = some r →
      Extends st r.2 ∧ (∃ e0 : Nat, r.2.visited[e0]? = some r.1) ∧
      (TransitionsWF finals st → TransitionsWF finals r.2) := by
  refine exploreState.partial_correctness cv finals
    (fun (e : Nat) (st : TGBAConstructState α) (r : Nat × TGBAConstructState α) =>
      Extends st r.2 ∧ (∃ e0 : Nat, r.2.visited[e0]? = some r.1) ∧
      (TransitionsWF finals st → TransitionsWF finals r.2)) ?_
  intro exploreState ih e st r hr
  have hfold : ∀ l : List (DNF α × Nat × Nat),
      (∀ g e' mk, (g, e', mk) ∈ l → ∀ i, mk.testBit i = true → i < finals.size) →
      ∀ (accInit : Array (DNF α × Nat × Nat)) (stf : TGBAConstructState α)
        (r : Array (DNF α × Nat × Nat) × TGBAConstructState α),
      AccWF finals stf accInit →
      l.foldlM (m := Option) (init := (accInit, stf))
        (fun ((acc, st) : Array (DNF α × Nat × Nat) × TGBAConstructState α)
            ((g, e', mk) : DNF α × Nat × Nat) => do
          let (tid, st) ← exploreState e' st
          pure (acc.push (g, tid, mk), st)) = some r →
      Extends stf r.2 ∧ AccWF finals r.2 r.1 ∧ (TransitionsWF finals stf → TransitionsWF finals r.2) := by
    intro l
    induction l with
    | nil =>
      intro _ accInit stf r haccWF hr
      simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hr
      subst hr
      exact ⟨Extends.refl stf, haccWF, fun h => h⟩
    | cons hd tl ihl =>
      intro hbound accInit stf r haccWF hr
      obtain ⟨g, e', mk⟩ := hd
      have hmkbound : ∀ i, mk.testBit i = true → i < finals.size := hbound g e' mk (by simp)
      rw [List.foldlM_cons] at hr
      cases hex : exploreState e' stf with
      | none => simp only [hex] at hr; exact absurd hr (by simp)
      | some r1 =>
        obtain ⟨tid, st2⟩ := r1
        obtain ⟨hext1, ⟨e0, he0⟩, htwf1⟩ := ih e' stf ⟨tid, st2⟩ hex
        simp only [hex, Option.pure_def] at hr
        have haccWF2 : AccWF finals st2 (accInit.push (g, tid, mk)) := by
          intro p hp
          rw [Array.toList_push, List.mem_append] at hp
          rcases hp with hp | hp
          · obtain ⟨e1, he1⟩ := (haccWF p hp).1
            exact ⟨⟨e1, hext1 e1 p.2.1 he1⟩, (haccWF p hp).2⟩
          · simp only [List.mem_singleton] at hp
            rw [hp]
            exact ⟨⟨e0, he0⟩, hmkbound⟩
        obtain ⟨hext2, haccWF3, htwf2⟩ := ihl (fun g e' mk hmk => hbound g e' mk (List.mem_cons_of_mem _ hmk))
          _ st2 r haccWF2 hr
        exact ⟨hext1.trans hext2, haccWF3, fun h => htwf2 (htwf1 h)⟩
  cases hvis : st.visited[e]? with
  | some id =>
    simp only [hvis, Option.pure_def, Option.some.injEq] at hr
    subst hr
    exact ⟨Extends.refl st, ⟨e, hvis⟩, fun h => h⟩
  | none =>
    simp only [hvis] at hr
    set st1 : TGBAConstructState α :=
      { st with visited := st.visited.insert e st.nextId, nextId := st.nextId + 1 } with hst1
    have hext1 : Extends st st1 := by
      intro e' id' h'
      rw [hst1]
      show (st.visited.insert e st.nextId)[e']? = some id'
      rw [Std.HashMap.getElem?_insert]
      by_cases heq : e == e'
      · exfalso
        rw [beq_iff_eq] at heq
        rw [← heq, hvis] at h'
        exact absurd h' (by simp)
      · simp only [heq]
        exact h'
    set candidates := markedProduct cv finals e with hcand
    have hcandbound : ∀ g e' mk, (g, e', mk) ∈ reduceCandidates candidates → ∀ i, mk.testBit i = true → i < finals.size :=
      fun _ _ _ hmem => reduceCandidates_markedProduct_marks_lt hmem
    obtain ⟨⟨transArr, stFinal⟩, hf, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨hext2, haccWF, htwf⟩ := hfold (reduceCandidates candidates) hcandbound #[] st1 (transArr, stFinal)
      (fun p hp => absurd hp (by simp)) hf
    simp only [Option.pure_def] at hr
    injection hr with hr
    subst hr
    have hext3 : Extends stFinal { stFinal with transitions := stFinal.transitions.insert st.nextId transArr } :=
      fun _ _ h => h
    refine ⟨hext1.trans (hext2.trans hext3), ⟨e, (hext2.trans hext3) e st.nextId (by
      rw [hst1]; exact Std.HashMap.getElem?_insert_self)⟩, ?_⟩
    intro htwfst
    have htwf_st1 : TransitionsWF finals st1 := by
      intro id0 arr h p hp
      obtain ⟨⟨e1, he1⟩, hbound⟩ := htwfst id0 arr h p hp
      exact ⟨⟨e1, hext1 e1 p.2.1 he1⟩, hbound⟩
    have htwf_stFinal : TransitionsWF finals stFinal := htwf htwf_st1
    intro id0 arr hmem
    have hmem' : (stFinal.transitions.insert st.nextId transArr)[id0]? = some arr := hmem
    rw [Std.HashMap.getElem?_insert] at hmem'
    by_cases hcase : st.nextId == id0
    · rw [if_pos hcase] at hmem'
      injection hmem' with hmem'
      subst hmem'
      exact haccWF
    · rw [if_neg hcase] at hmem'
      exact htwf_stFinal id0 arr hmem'

/-! ## Id-renumbering -/

/-- Every id `visited` assigns is strictly below the fresh-id counter. -/
def NextIdBound (st : TGBAConstructState α) : Prop :=
  ∀ (e : Nat) (id : Nat), st.visited[e]? = some id → id < st.nextId

/-- `visited` never maps two different states to the same id. -/
def VisitedInjective (st : TGBAConstructState α) : Prop :=
  ∀ (e1 e2 : Nat) (id : Nat), st.visited[e1]? = some id → st.visited[e2]? = some id → e1 = e2

private theorem visited_insert_bound {st : TGBAConstructState α} {e : Nat} (hbnd : NextIdBound st)
    {e0 : Nat} {id0 : Nat} (h0 : (st.visited.insert e st.nextId)[e0]? = some id0) :
    id0 < st.nextId + 1 := by
  rw [Std.HashMap.getElem?_insert] at h0
  by_cases heq0 : e == e0
  · rw [if_pos heq0] at h0; injection h0 with h0; omega
  · rw [if_neg heq0] at h0; exact lt_trans (hbnd e0 id0 h0) (by omega)

private theorem visited_insert_eq_or {st : TGBAConstructState α} {e : Nat}
    {e0 : Nat} {id0 : Nat} (h0 : (st.visited.insert e st.nextId)[e0]? = some id0) :
    (e0 = e ∧ id0 = st.nextId) ∨ st.visited[e0]? = some id0 := by
  rw [Std.HashMap.getElem?_insert] at h0
  by_cases heq0 : e == e0
  · rw [if_pos heq0] at h0
    injection h0 with h0
    rw [beq_iff_eq] at heq0
    exact Or.inl ⟨heq0.symm, h0.symm⟩
  · rw [if_neg heq0] at h0
    exact Or.inr h0

/-- `exploreState` only extends its state, assigns the returned id to `e`, and preserves `NextIdBound` and
`VisitedInjective`. -/
theorem exploreState_injective (cv : ConcreteVWAA α) (finals : Array Nat) :
    ∀ (e : Nat) (st : TGBAConstructState α) (r : Nat × TGBAConstructState α),
      exploreState cv finals e st = some r →
      Extends st r.2 ∧ r.2.visited[e]? = some r.1 ∧
      (NextIdBound st → NextIdBound r.2) ∧ (NextIdBound st → VisitedInjective st → VisitedInjective r.2) := by
  refine exploreState.partial_correctness cv finals
    (fun (e : Nat) (st : TGBAConstructState α) (r : Nat × TGBAConstructState α) =>
      Extends st r.2 ∧ r.2.visited[e]? = some r.1 ∧
      (NextIdBound st → NextIdBound r.2) ∧ (NextIdBound st → VisitedInjective st → VisitedInjective r.2)) ?_
  intro exploreState ih e st r hr
  have hfold : ∀ l : List (DNF α × Nat × Nat),
      ∀ (accInit : Array (DNF α × Nat × Nat)) (stf : TGBAConstructState α)
        (r : Array (DNF α × Nat × Nat) × TGBAConstructState α),
      l.foldlM (m := Option) (init := (accInit, stf))
        (fun ((acc, st) : Array (DNF α × Nat × Nat) × TGBAConstructState α)
            ((g, e', mk) : DNF α × Nat × Nat) => do
          let (tid, st) ← exploreState e' st
          pure (acc.push (g, tid, mk), st)) = some r →
      Extends stf r.2 ∧ (NextIdBound stf → NextIdBound r.2) ∧
      (NextIdBound stf → VisitedInjective stf → VisitedInjective r.2) := by
    intro l
    induction l with
    | nil =>
      intro accInit stf r hr
      simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hr
      subst hr
      exact ⟨Extends.refl stf, fun h => h, fun _ h => h⟩
    | cons hd tl ihl =>
      intro accInit stf r hr
      obtain ⟨g, e', mk⟩ := hd
      rw [List.foldlM_cons] at hr
      cases hex : exploreState e' stf with
      | none => simp only [hex] at hr; exact absurd hr (by simp)
      | some r1 =>
        obtain ⟨tid, st2⟩ := r1
        obtain ⟨hext1, he0, hbnd1, hinj1⟩ := ih e' stf ⟨tid, st2⟩ hex
        dsimp only at hext1 he0 hbnd1 hinj1
        simp only [hex, Option.pure_def] at hr
        obtain ⟨hext2, hbnd2, hinj2⟩ := ihl (accInit.push (g, tid, mk)) st2 r hr
        exact ⟨hext1.trans hext2, fun h => hbnd2 (hbnd1 h), fun h1 h2 => hinj2 (hbnd1 h1) (hinj1 h1 h2)⟩
  cases hvis : st.visited[e]? with
  | some id =>
    simp only [hvis, Option.pure_def, Option.some.injEq] at hr
    subst hr
    exact ⟨Extends.refl st, hvis, fun h => h, fun _ h => h⟩
  | none =>
    simp only [hvis] at hr
    set st1 : TGBAConstructState α :=
      { st with visited := st.visited.insert e st.nextId, nextId := st.nextId + 1 } with hst1
    have hext1 : Extends st st1 := by
      intro e' id' h'
      rw [hst1]
      show (st.visited.insert e st.nextId)[e']? = some id'
      rw [Std.HashMap.getElem?_insert]
      by_cases heq : e == e'
      · exfalso; rw [beq_iff_eq] at heq; rw [← heq, hvis] at h'; exact absurd h' (by simp)
      · simp only [heq]; exact h'
    have hvis1 : st1.visited[e]? = some st.nextId := by rw [hst1]; exact Std.HashMap.getElem?_insert_self
    obtain ⟨⟨transArr, stFinal⟩, hf, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨hext2, hbnd2, hinj2⟩ := hfold (reduceCandidates (markedProduct cv finals e)) #[] st1
      (transArr, stFinal) hf
    dsimp only at hext2 hbnd2 hinj2
    simp only [Option.pure_def] at hr
    injection hr with hr
    subst hr
    have hvisFinal : stFinal.visited[e]? = some st.nextId := hext2 e st.nextId hvis1
    refine ⟨hext1.trans hext2, hvisFinal, ?_, ?_⟩
    · intro hbndst
      apply hbnd2
      intro e0 id0 h0
      rw [hst1] at h0
      exact visited_insert_bound hbndst h0
    · intro hbndst hinjst
      apply hinj2
      · intro e0 id0 h0
        rw [hst1] at h0
        exact visited_insert_bound hbndst h0
      · intro e1 e2 id0 h1 h2
        rw [hst1] at h1 h2
        rcases visited_insert_eq_or h1 with ⟨heq1, hid1⟩ | h1
        · rcases visited_insert_eq_or h2 with ⟨heq2, -⟩ | h2
          · rw [heq1, heq2]
          · exact absurd (hid1 ▸ hbndst e2 id0 h2) (by omega)
        · rcases visited_insert_eq_or h2 with ⟨heq2, hid2⟩ | h2
          · exact absurd (hid2 ▸ hbndst e1 id0 h1) (by omega)
          · exact hinjst e1 e2 id0 h1 h2

/-- Every finished id records exactly its state's reduced candidates, every target explored and translated to its id
through `visited`. -/
def Denotes (finals : Array Nat) (cv : ConcreteVWAA α) (st : TGBAConstructState α) : Prop :=
  ∀ id arr, st.transitions[id]? = some arr → ∃ e, st.visited[e]? = some id ∧
    (∀ g e' m, (g, e', m) ∈ reduceCandidates (markedProduct cv finals e) → ∃ tid, st.visited[e']? = some tid) ∧
    arr.toList = (reduceCandidates (markedProduct cv finals e)).map fun (g, e', m) => (g, st.visited.getD e' 0, m)

/-- `exploreState` only extends its state, assigns the returned id to `e`, and preserves `Denotes`. -/
theorem exploreState_denotes (cv : ConcreteVWAA α) (finals : Array Nat) :
    ∀ (e : Nat) (st : TGBAConstructState α) (r : Nat × TGBAConstructState α),
      exploreState cv finals e st = some r →
      Extends st r.2 ∧ r.2.visited[e]? = some r.1 ∧
      (Denotes finals cv st → Denotes finals cv r.2) := by
  refine exploreState.partial_correctness cv finals
    (fun (e : Nat) (st : TGBAConstructState α) (r : Nat × TGBAConstructState α) =>
      Extends st r.2 ∧ r.2.visited[e]? = some r.1 ∧
      (Denotes finals cv st → Denotes finals cv r.2)) ?_
  intro exploreState ih e st r hr
  have hfold : ∀ l : List (DNF α × Nat × Nat),
      ∀ (accInit : Array (DNF α × Nat × Nat)) (processed : List (DNF α × Nat × Nat))
        (stf : TGBAConstructState α) (r : Array (DNF α × Nat × Nat) × TGBAConstructState α),
      (∀ p ∈ processed, ∃ tid, stf.visited[p.2.1]? = some tid) →
      accInit.toList = processed.map (fun (g, e', m) => (g, stf.visited.getD e' 0, m)) →
      l.foldlM (m := Option) (init := (accInit, stf))
        (fun ((acc, st) : Array (DNF α × Nat × Nat) × TGBAConstructState α)
            ((g, e', mk) : DNF α × Nat × Nat) => do
          let (tid, st) ← exploreState e' st
          pure (acc.push (g, tid, mk), st)) = some r →
      Extends stf r.2 ∧ (Denotes finals cv stf → Denotes finals cv r.2) ∧
      (∀ p ∈ processed ++ l, ∃ tid, r.2.visited[p.2.1]? = some tid) ∧
      r.1.toList = (processed ++ l).map (fun (g, e', m) => (g, r.2.visited.getD e' 0, m)) := by
    intro l
    induction l with
    | nil =>
      intro accInit processed stf r hproc hacc hr
      simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hr
      subst hr
      refine ⟨Extends.refl stf, fun h => h, ?_, ?_⟩
      · simpa using hproc
      · simpa using hacc
    | cons hd tl ihl =>
      intro accInit processed stf r hproc hacc hr
      obtain ⟨g, e', mk⟩ := hd
      rw [List.foldlM_cons] at hr
      cases hex : exploreState e' stf with
      | none => simp only [hex] at hr; exact absurd hr (by simp)
      | some r1 =>
        obtain ⟨tid, st2⟩ := r1
        obtain ⟨hext1, he0, hden1⟩ := ih e' stf ⟨tid, st2⟩ hex
        dsimp only at hext1 he0 hden1
        simp only [hex, Option.pure_def] at hr
        have hproc2 : ∀ p ∈ processed, ∃ tid, st2.visited[p.2.1]? = some tid := fun p hp => by
          obtain ⟨tid0, ht0⟩ := hproc p hp; exact ⟨tid0, hext1 p.2.1 tid0 ht0⟩
        have hproc3 : ∀ p ∈ processed ++ [(g, e', mk)], ∃ tid, st2.visited[p.2.1]? = some tid := by
          intro p hp
          rw [List.mem_append] at hp
          rcases hp with hp | hp
          · exact hproc2 p hp
          · simp only [List.mem_singleton] at hp
            rw [hp]; exact ⟨tid, he0⟩
        have hacc2 : (accInit.push (g, tid, mk)).toList =
            (processed ++ [(g, e', mk)]).map (fun (g, e', m) => (g, st2.visited.getD e' 0, m)) := by
          rw [Array.toList_push, hacc, List.map_append]
          congr 1
          · apply List.map_congr_left
            rintro ⟨pg, pe, pm⟩ hp
            obtain ⟨tid0, ht0⟩ := hproc _ hp
            dsimp only at ht0
            have h1 : stf.visited.getD pe 0 = tid0 := by
              rw [Std.HashMap.getD_eq_getD_getElem?, ht0]; rfl
            have h2 : st2.visited.getD pe 0 = tid0 := by
              rw [Std.HashMap.getD_eq_getD_getElem?, hext1 pe tid0 ht0]; rfl
            simp only [h1, h2]
          · simp only [List.map_singleton]
            have h3 : st2.visited.getD e' 0 = tid := by
              rw [Std.HashMap.getD_eq_getD_getElem?, he0]; rfl
            rw [h3]
        obtain ⟨hext2, hden2, hproc4, hacc3⟩ := ihl (accInit.push (g, tid, mk)) (processed ++ [(g, e', mk)]) st2 r
          hproc3 hacc2 hr
        refine ⟨hext1.trans hext2, fun h => hden2 (hden1 h), ?_, ?_⟩
        · simpa [List.append_assoc] using hproc4
        · simpa [List.append_assoc] using hacc3
  cases hvis : st.visited[e]? with
  | some id =>
    simp only [hvis, Option.pure_def, Option.some.injEq] at hr
    subst hr
    exact ⟨Extends.refl st, hvis, fun h => h⟩
  | none =>
    simp only [hvis] at hr
    set st1 : TGBAConstructState α :=
      { st with visited := st.visited.insert e st.nextId, nextId := st.nextId + 1 } with hst1
    have hext1 : Extends st st1 := by
      intro e' id' h'
      rw [hst1]
      show (st.visited.insert e st.nextId)[e']? = some id'
      rw [Std.HashMap.getElem?_insert]
      by_cases heq : e == e'
      · exfalso
        rw [beq_iff_eq] at heq
        rw [← heq, hvis] at h'
        exact absurd h' (by simp)
      · simp only [heq]
        exact h'
    have hvis1 : st1.visited[e]? = some st.nextId := by rw [hst1]; exact Std.HashMap.getElem?_insert_self
    set candidates := markedProduct cv finals e with hcand
    obtain ⟨⟨transArr, stFinal⟩, hf, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨hext2, hden2, hproc, hacc⟩ := hfold (reduceCandidates candidates) #[] [] st1 (transArr, stFinal)
      (fun p hp => absurd hp (by simp)) (by simp) hf
    simp only [List.nil_append] at hproc hacc
    simp only [Option.pure_def] at hr
    injection hr with hr
    subst hr
    have hvisFinal : stFinal.visited[e]? = some st.nextId := hext2 e st.nextId hvis1
    refine ⟨hext1.trans hext2, hext2 e st.nextId hvis1, ?_⟩
    intro hdenst
    have hdenst1 : Denotes finals cv st1 := by
      intro id arr harr
      obtain ⟨e0, hvise0, hexists0, heqarr⟩ := hdenst id arr harr
      refine ⟨e0, hext1 e0 id hvise0, fun g e' m hmem => ?_, ?_⟩
      · obtain ⟨tid0, ht0⟩ := hexists0 g e' m hmem
        exact ⟨tid0, hext1 e' tid0 ht0⟩
      · rw [heqarr]
        apply List.map_congr_left
        rintro ⟨pg, pe, pm⟩ hp
        obtain ⟨tid0, ht0⟩ := hexists0 pg pe pm hp
        have hne : ¬(e == pe) := by
          simp only [beq_iff_eq]
          intro heq
          rw [← heq, hvis] at ht0
          exact absurd ht0 (by simp)
        have h1 : st1.visited.getD pe 0 = st.visited.getD pe 0 := by
          rw [hst1, Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getD_eq_getD_getElem?]
          show (st.visited.insert e st.nextId)[pe]?.getD 0 = st.visited[pe]?.getD 0
          rw [Std.HashMap.getElem?_insert, if_neg hne]
        simp only [h1]
    have hdenFinal : Denotes finals cv stFinal := hden2 hdenst1
    intro id0 arr0 h0
    change (stFinal.transitions.insert st.nextId transArr)[id0]? = some arr0 at h0
    rw [Std.HashMap.getElem?_insert] at h0
    by_cases hcase : st.nextId == id0
    · rw [if_pos hcase] at h0
      injection h0 with h0
      subst h0
      rw [beq_iff_eq] at hcase
      subst hcase
      refine ⟨e, hvisFinal, ?_, ?_⟩
      · rw [← hcand]; exact fun g e' m hmem => hproc (g, e', m) hmem
      · rw [hacc, hcand]
    · rw [if_neg hcase] at h0
      exact hdenFinal id0 arr0 h0
private theorem mem_states_of_visited {visited : Std.HashMap Nat Nat} {e0 : Nat} {id : Nat}
    (h : visited[e0]? = some id) :
    (Std.HashSet.ofList (visited.toList.map (·.2))).contains id = true := by
  rw [← Std.HashSet.mem_iff_contains, Std.HashSet.mem_ofList, List.contains_iff_mem, List.mem_map]
  exact ⟨(e0, id), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h, rfl⟩

/-- Every id `visited` assigns has its transitions recorded, except those `pending` allows, the ids of the
states whose exploration is still in progress. -/
def FinishedExcept (st : TGBAConstructState α) (pending : Nat → Prop) : Prop :=
  ∀ (e : Nat) (id : Nat), st.visited[e]? = some id → (∃ arr, st.transitions[id]? = some arr) ∨ pending id

/-- `exploreState` records the transitions of every state it assigns an id to before returning. -/
theorem exploreState_finished (cv : ConcreteVWAA α) (finals : Array Nat) :
    ∀ (e : Nat) (st : TGBAConstructState α) (r : Nat × TGBAConstructState α),
      exploreState cv finals e st = some r →
      ∀ pending, FinishedExcept st pending → FinishedExcept r.2 pending := by
  refine exploreState.partial_correctness cv finals
    (fun (e : Nat) (st : TGBAConstructState α) (r : Nat × TGBAConstructState α) =>
      ∀ pending, FinishedExcept st pending → FinishedExcept r.2 pending) ?_
  intro exploreState ih e st r hr
  have hfold : ∀ l : List (DNF α × Nat × Nat),
      ∀ (accInit : Array (DNF α × Nat × Nat)) (stf : TGBAConstructState α)
        (r : Array (DNF α × Nat × Nat) × TGBAConstructState α),
      l.foldlM (m := Option) (init := (accInit, stf))
        (fun ((acc, st) : Array (DNF α × Nat × Nat) × TGBAConstructState α)
            ((g, e', mk) : DNF α × Nat × Nat) => do
          let (tid, st) ← exploreState e' st
          pure (acc.push (g, tid, mk), st)) = some r →
      ∀ pending, FinishedExcept stf pending → FinishedExcept r.2 pending := by
    intro l
    induction l with
    | nil =>
      intro accInit stf r hr pending h
      simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hr
      subst hr
      exact h
    | cons hd tl ihl =>
      intro accInit stf r hr pending h
      obtain ⟨g, e', mk⟩ := hd
      rw [List.foldlM_cons] at hr
      cases hex : exploreState e' stf with
      | none => simp only [hex] at hr; exact absurd hr (by simp)
      | some r1 =>
        obtain ⟨tid, st2⟩ := r1
        have h2 := ih e' stf ⟨tid, st2⟩ hex pending h
        simp only [hex, Option.pure_def] at hr
        exact ihl (accInit.push (g, tid, mk)) st2 r hr pending h2
  intro pending hst
  cases hvis : st.visited[e]? with
  | some id =>
    simp only [hvis, Option.pure_def, Option.some.injEq] at hr
    subst hr
    exact hst
  | none =>
    simp only [hvis] at hr
    set st1 : TGBAConstructState α :=
      { st with visited := st.visited.insert e st.nextId, nextId := st.nextId + 1 } with hst1
    have hst1f : FinishedExcept st1 (fun id => pending id ∨ id = st.nextId) := by
      intro e0 id0 h0
      rw [hst1] at h0
      rcases visited_insert_eq_or h0 with ⟨-, rfl⟩ | h0
      · exact Or.inr (Or.inr rfl)
      · rcases hst e0 id0 h0 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    obtain ⟨⟨transArr, stFinal⟩, hf, hr⟩ := Option.bind_eq_some_iff.mp hr
    have hfinal := hfold _ #[] st1 (transArr, stFinal) hf _ hst1f
    simp only [Option.pure_def] at hr
    injection hr with hr
    subst hr
    intro e0 id0 h0
    change stFinal.visited[e0]? = some id0 at h0
    by_cases hid : id0 = st.nextId
    · subst hid
      exact Or.inl ⟨transArr, Std.HashMap.getElem?_insert_self⟩
    · rcases hfinal e0 id0 h0 with ⟨arr, harr⟩ | h | h
      · refine Or.inl ⟨arr, ?_⟩
        change (stFinal.transitions.insert st.nextId transArr)[id0]? = some arr
        rw [Std.HashMap.getElem?_insert, if_neg (by simpa [beq_iff_eq] using Ne.symm hid)]
        exact harr
      · exact Or.inr h
      · exact absurd h hid

/-- A finished worklist state records the `SetTGBA` the construction denotes, up to the numbering `visited`. -/
structure Represents (cv : ConcreteVWAA α) (finals : Array Nat) (st : TGBAConstructState α) : Prop where
  -- every finished id records its state's reduced candidates, targets read through `visited`
  denotes : Denotes finals cv st
  -- states sharing an id have the same reduced candidates
  consistent : ∀ (e1 e2 : Nat) (id : Nat), st.visited[e1]? = some id → st.visited[e2]? = some id →
    reduceCandidates (markedProduct cv finals e1) = reduceCandidates (markedProduct cv finals e2)
  -- every visited id is finished
  finished : ∀ (e : Nat) (id : Nat), st.visited[e]? = some id → ∃ arr, st.transitions[id]? = some arr

/-- An exploration from the empty worklist state ends in a state representing the construction, with the
explored state assigned the returned id. -/
theorem exploreState_initial_represents {cv : ConcreteVWAA α} {finals : Array Nat} {e : Nat} {id : Nat}
    {st : TGBAConstructState α} (hex : exploreState cv finals e initConstructState = some (id, st)) :
    Represents cv finals st ∧ st.visited[e]? = some id := by
  obtain ⟨-, hvis, -, hinj⟩ := exploreState_injective cv finals e initConstructState (id, st) hex
  obtain ⟨-, -, hden⟩ := exploreState_denotes cv finals e initConstructState (id, st) hex
  have hfin := exploreState_finished cv finals e initConstructState (id, st) hex (fun _ => False)
    (fun _ _ h => absurd h (by simp [initConstructState]))
  refine ⟨⟨hden fun _ _ h => absurd h (by simp [initConstructState]), fun e1 e2 id0 h1 h2 => ?_,
    fun e0 id0 h0 => (hfin e0 id0 h0).resolve_right fun h => h⟩, hvis⟩
  rw [hinj (fun _ _ h => absurd h (by simp [initConstructState]))
    (fun _ _ _ h => absurd h (by simp [initConstructState])) e1 e2 id0 h1 h2]

/-! ## The exported TGBA -/

/-- `buildTGBA`'s output is the export of the worklist state `exploreState` returns from the initial state. -/
theorem buildTGBA_eq_some {cv : ConcreteVWAA α} {result : TGBA α} (hr : buildTGBA cv = some result) :
    ∃ initId st, exploreState cv (finalsOf cv) (bit cv.initial) initConstructState = some (initId, st) ∧
      result = exportTGBA (finalsOf cv) st initId := by
  unfold buildTGBA at hr
  cases hex : exploreState cv (finalsOf cv) (bit cv.initial) initConstructState with
  | none => simp [hex] at hr
  | some r =>
    obtain ⟨initId, st⟩ := r
    simp only [hex] at hr
    simp at hr
    exact ⟨initId, st, rfl, hr.symm⟩

/-- `finalsOf` lists each final id once. -/
theorem finalsOf_nodup (cv : ConcreteVWAA α) : (finalsOf cv).toList.Nodup := by
  unfold finalsOf
  rw [List.toList_toArray]
  exact List.nodup_range.filter _

/-- `finalsOf` holds exactly the final ids, given `cv.final` is no longer than the table. -/
theorem mem_finalsOf_iff {cv : ConcreteVWAA α} (hsize : cv.final.size ≤ cv.table.formulas.size) {f : Nat} :
    f ∈ (finalsOf cv).toList ↔ cv.final.getD f false = true := by
  unfold finalsOf
  rw [List.toList_toArray, List.mem_filter, List.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨Classical.byContradiction fun hlt => ?_, h⟩⟩
  have hnone : cv.final.getD f false = false := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl
  rw [hnone] at h
  exact absurd h (by simp)

/-- The export's only initial state is the id it is given. -/
theorem exportTGBA_isInitial_iff {finals : Array Nat} {st : TGBAConstructState α} {initId q : Nat} :
    (exportTGBA finals st initId).isInitial q = true ↔ q = initId := by
  show ((Std.HashSet.emptyWithCapacity 1).insert initId).contains q = true ↔ q = initId
  rw [Std.HashSet.contains_insert, Std.HashSet.contains_emptyWithCapacity, Bool.or_false, beq_iff_eq, eq_comm]

/-- An exported successor is one cube of one recorded transition, target and marks carried over. -/
theorem mem_exportTGBA_getSuccessors {finals : Array Nat} {st : TGBAConstructState α} {initId q : Nat}
    {t : TGBA.Transition α} :
    t ∈ (exportTGBA finals st initId).getSuccessors q ↔
      ∃ arr, st.transitions[q]? = some arr ∧ ∃ g tid marks, (g, tid, marks) ∈ arr.toList ∧ ∃ c ∈ DNF.cubes g,
        t = { target := tid, positiveProps := c.pos, negativeProps := c.neg,
              acceptMarks := Std.HashSet.ofList (maskMembers marks) } := by
  unfold TGBA.getSuccessors exportTGBA
  simp only [Std.HashMap.getElem?_map]
  cases hq : st.transitions[q]? with
  | none => simp
  | some arr =>
    simp only [Option.map_some, Option.getD_some, Option.some.injEq, exists_eq_left']
    constructor
    · intro ht
      obtain ⟨⟨g, tid, marks⟩, hgtm, ht'⟩ := Array.mem_flatMap.mp ht
      obtain ⟨c, hc, rfl⟩ := Array.mem_map.mp ht'
      exact ⟨g, tid, marks, Array.mem_def.mp hgtm, c, List.mem_toArray.mp hc, rfl⟩
    · rintro ⟨g, tid, marks, hgtm, c, hc, rfl⟩
      exact Array.mem_flatMap.mpr ⟨(g, tid, marks), Array.mem_def.mpr hgtm,
        Array.mem_map.mpr ⟨c, List.mem_toArray.mpr hc, rfl⟩⟩

/-- The export of a worklist state whose recorded transitions are well-formed, from an assigned initial id, is
well-formed. -/
theorem exportTGBA_wellFormed {finals : Array Nat} {st : TGBAConstructState α} {initId : Nat}
    (htwf : TransitionsWF finals st) (hinit : ∃ e0 : Nat, st.visited[e0]? = some initId) :
    (exportTGBA finals st initId).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    have hq' : q = initId := by
      have hq1 : q ∈ (exportTGBA finals st initId).initialStates := Std.HashSet.mem_iff_contains.mpr hq
      simp only [exportTGBA, Std.HashSet.mem_insert] at hq1
      rcases hq1 with hq1 | hq1
      · exact (beq_iff_eq.mp hq1).symm
      · exact absurd hq1 (by simp)
    obtain ⟨e0, he0⟩ := hinit
    rw [hq']
    exact mem_states_of_visited he0
  · intro q t _ ht
    obtain ⟨arr, hqt, g, tid, marks, hgtm, c, -, rfl⟩ := mem_exportTGBA_getSuccessors.mp ht
    obtain ⟨⟨e1, he1⟩, -⟩ := htwf q arr hqt (g, tid, marks) hgtm
    exact mem_states_of_visited he1
  · intro q t _ ht m hm
    obtain ⟨arr, hqt, g, tid, marks, hgtm, c, -, rfl⟩ := mem_exportTGBA_getSuccessors.mp ht
    exact (htwf q arr hqt (g, tid, marks) hgtm).2 m (mem_maskMembers.mp (by simpa using hm))

/-- Every exported transition's marks, at any state, index into `finals`. -/
theorem exportTGBA_marks_lt {finals : Array Nat} {st : TGBAConstructState α} {initId : Nat}
    (htwf : TransitionsWF finals st) :
    ∀ q t, t ∈ (exportTGBA finals st initId).getSuccessors q →
      ∀ m ∈ t.acceptMarks, m < (exportTGBA finals st initId).numAcceptSets := by
  intro q t ht m hm
  obtain ⟨arr, hqt, g, tid, marks, hgtm, c, -, rfl⟩ := mem_exportTGBA_getSuccessors.mp ht
  exact (htwf q arr hqt (g, tid, marks) hgtm).2 m (mem_maskMembers.mp (by simpa using hm))

/-- Every transition of `buildTGBA`'s output, at any state, has its marks below `numAcceptSets`. -/
theorem buildTGBA_marks_lt (cv : ConcreteVWAA α) (result : TGBA α) (hr : buildTGBA cv = some result) :
    ∀ q t, t ∈ result.getSuccessors q → ∀ m ∈ t.acceptMarks, m < result.numAcceptSets := by
  obtain ⟨initId, st, hex, rfl⟩ := buildTGBA_eq_some hr
  obtain ⟨-, -, htwf⟩ := exploreState_wf cv (finalsOf cv) (bit cv.initial) initConstructState (initId, st) hex
  exact exportTGBA_marks_lt (htwf fun _ _ h => absurd h (by simp [initConstructState]))

/-- `buildTGBA`'s output is well-formed. -/
theorem buildTGBA_wellFormed (cv : ConcreteVWAA α) (result : TGBA α) (hr : buildTGBA cv = some result) :
    result.WellFormed := by
  obtain ⟨initId, st, hex, rfl⟩ := buildTGBA_eq_some hr
  obtain ⟨-, hinit, htwf⟩ := exploreState_wf cv (finalsOf cv) (bit cv.initial) initConstructState (initId, st) hex
  exact exportTGBA_wellFormed (htwf fun _ _ h => absurd h (by simp [initConstructState])) hinit

/-! ## Abstract correspondence -/

private theorem foldl_and_congr {gf gf' : Nat → DNF α} {l : List Nat} (h : ∀ q ∈ l, gf q = gf' q)
    (g0 : DNF α) :
    l.foldl (fun acc q => DNF.and acc (gf q)) g0 = l.foldl (fun acc q => DNF.and acc (gf' q)) g0 := by
  induction l generalizing g0 with
  | nil => rfl
  | cons q qs ih =>
    rw [List.foldl_cons, List.foldl_cons, h q List.mem_cons_self, ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq')]

private theorem foldl_or_congr {Of Of' : Nat → Nat} {l : List Nat} (h : ∀ q ∈ l, Of q = Of' q) (t0 : Nat) :
    l.foldl (fun acc q => acc ||| Of q) t0 = l.foldl (fun acc q => acc ||| Of' q) t0 := by
  induction l generalizing t0 with
  | nil => rfl
  | cons q qs ih =>
    rw [List.foldl_cons, List.foldl_cons, h q List.mem_cons_self, ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq')]

private theorem foldl_esc_congr {cv : ConcreteVWAA α} {Of Of' : Nat → Nat} {l : List Nat}
    (h : ∀ q ∈ l, Of q = Of' q) (s0 : Nat) :
    l.foldl (fun acc q => if cv.final.getD q false && !(Of q).testBit q then acc ||| bit q else acc) s0 =
    l.foldl (fun acc q => if cv.final.getD q false && !(Of' q).testBit q then acc ||| bit q else acc) s0 := by
  induction l generalizing s0 with
  | nil => rfl
  | cons q qs ih =>
    rw [List.foldl_cons, List.foldl_cons, h q List.mem_cons_self, ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq')]

private theorem mem_foldl_productStep {cv : ConcreteVWAA α} :
    ∀ l : List Nat, l.Nodup → ∀ (acc0 : List (DNF α × Nat × Nat)) (g : DNF α) (t s : Nat),
      (g, t, s) ∈ l.foldl (productStep cv) acc0 →
        ∃ g0 t0 s0, (g0, t0, s0) ∈ acc0 ∧ ∃ (gf : Nat → DNF α) (Of : Nat → Nat),
          (∀ q ∈ l, (gf q, Of q) ∈ cv.trans.getD q []) ∧
          g = l.foldl (fun acc q => DNF.and acc (gf q)) g0 ∧
          t = l.foldl (fun acc q => acc ||| Of q) t0 ∧
          s = l.foldl (fun acc q => if cv.final.getD q false && !(Of q).testBit q then acc ||| bit q else acc) s0 := by
  intro l
  induction l with
  | nil =>
    intro _ acc0 g t s h
    exact ⟨g, t, s, h, fun _ => DNF.top, fun _ => 0, fun q hq => absurd hq List.not_mem_nil, rfl, rfl, rfl⟩
  | cons q qs ih =>
    intro hnodup acc0 g t s h
    have hqqs : q ∉ qs := (List.nodup_cons.mp hnodup).1
    rw [List.foldl_cons] at h
    obtain ⟨g0', t0', s0', hmem', gf', Of', hvalid', hg', ht', hs'⟩ := ih (List.nodup_cons.mp hnodup).2 _ g t s h
    obtain ⟨c, hc, hc'⟩ := List.mem_flatMap.mp hmem'
    obtain ⟨p, hp, heq⟩ := List.mem_filterMap.mp hc'
    dsimp only at heq
    split at heq
    · exact absurd heq (by simp)
    · simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨hg0eq, ht0eq, hs0eq⟩ := heq
      have hne : ∀ q' ∈ qs, q' ≠ q := fun q' hq' h => hqqs (h ▸ hq')
      refine ⟨c.1, c.2.1, c.2.2, hc, fun x => if x = q then p.1 else gf' x, fun x => if x = q then p.2 else Of' x,
        fun x hx => ?_, ?_, ?_, ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · simpa using hp
        · simpa [hne x hx] using hvalid' x hx
      · show g = qs.foldl (fun acc q' => DNF.and acc (if q' = q then p.1 else gf' q'))
          (DNF.and c.1 (if q = q then p.1 else gf' q))
        rw [if_pos rfl, hg', ← hg0eq]
        exact (foldl_and_congr (fun q' hq' => by simp [hne q' hq']) _).symm
      · show t = qs.foldl (fun acc q' => acc ||| (if q' = q then p.2 else Of' q')) (c.2.1 ||| (if q = q then p.2 else Of' q))
        rw [if_pos rfl, ht', ← ht0eq]
        exact (foldl_or_congr (fun q' hq' => by simp [hne q' hq']) _).symm
      · show s = qs.foldl (fun acc q' => if cv.final.getD q' false && !(if q' = q then p.2 else Of' q').testBit q' then
            acc ||| bit q' else acc)
          (if cv.final.getD q false && !(if q = q then p.2 else Of' q).testBit q then c.2.2 ||| bit q else c.2.2)
        rw [if_pos rfl, hs', ← hs0eq]
        exact (foldl_esc_congr (fun q' hq' => by simp [hne q' hq']) _).symm

/-- A product transition of `e` is a per-id component choice, guard the conjunction, target the union, and escaped-own
finals the members whose chosen alternative does not loop in them. -/
theorem mem_productTrans_of {cv : ConcreteVWAA α} {e : Nat} {g : DNF α} {t s : Nat}
    (h : (g, t, s) ∈ productTrans cv e) :
    ∃ (gf : Nat → DNF α) (Of : Nat → Nat), (∀ q ∈ maskMembers e, (gf q, Of q) ∈ cv.trans.getD q []) ∧
      g = (maskMembers e).foldl (fun acc q => DNF.and acc (gf q)) DNF.top ∧
      t = (maskMembers e).foldl (fun acc q => acc ||| Of q) 0 ∧
      s = (maskMembers e).foldl
        (fun acc q => if cv.final.getD q false && !(Of q).testBit q then acc ||| bit q else acc) 0 := by
  obtain ⟨g0, t0, s0, hmem, gf, Of, hvalid, hg, ht, hs⟩ :=
    mem_foldl_productStep _ (maskMembers_nodup e) _ g t s h
  simp only [List.mem_singleton, Prod.mk.injEq] at hmem
  obtain ⟨rfl, rfl, rfl⟩ := hmem
  exact ⟨gf, Of, hvalid, hg, ht, hs⟩

/-- A letter satisfies the left-folded conjunction exactly when it satisfies the seed and every chosen component's
guard. -/
theorem sat_foldl_and_iff [LawfulBEq α] [LawfulHashable α] (l : List Nat) (gf : Nat → DNF α) (g0 : DNF α)
    (v : α → Prop) :
    DNF.sat (l.foldl (fun acc q => DNF.and acc (gf q)) g0) v ↔ DNF.sat g0 v ∧ ∀ q ∈ l, DNF.sat (gf q) v := by
  induction l generalizing g0 with
  | nil => simp
  | cons q qs ih =>
    rw [List.foldl_cons, ih (DNF.and g0 (gf q)), DNF.sat_and]
    constructor
    · rintro ⟨⟨hg0, hgq⟩, hqs⟩
      exact ⟨hg0, fun q' hq' => by
        rcases List.mem_cons.mp hq' with rfl | hq'
        · exact hgq
        · exact hqs q' hq'⟩
    · rintro ⟨hg0, hall⟩
      exact ⟨⟨hg0, hall q List.mem_cons_self⟩, fun q' hq' => hall q' (List.mem_cons_of_mem _ hq')⟩

private theorem mem_foldl_productStep_of_sat [LawfulBEq α] [LawfulHashable α] {cv : ConcreteVWAA α}
    (gf : Nat → DNF α) (Of : Nat → Nat) (v : α → Prop) :
    ∀ l : List Nat, (∀ q ∈ l, (gf q, Of q) ∈ cv.trans.getD q []) →
      ∀ (acc0 : List (DNF α × Nat × Nat)) (g0 : DNF α) (t0 s0 : Nat), (g0, t0, s0) ∈ acc0 →
        DNF.sat (l.foldl (fun acc q => DNF.and acc (gf q)) g0) v →
        (l.foldl (fun acc q => DNF.and acc (gf q)) g0, l.foldl (fun acc q => acc ||| Of q) t0,
          l.foldl (fun acc q => if cv.final.getD q false && !(Of q).testBit q then acc ||| bit q else acc) s0) ∈
          l.foldl (productStep cv) acc0 := by
  intro l
  induction l with
  | nil => intro _ acc0 g0 t0 s0 h _; exact h
  | cons q qs ih =>
    intro hvalid acc0 g0 t0 s0 hmem hsat
    simp only [List.foldl_cons] at hsat ⊢
    refine ih (fun x hx => hvalid x (List.mem_cons_of_mem _ hx)) _ _ _ _ ?_ hsat
    have hne : DNF.isEmpty (DNF.and g0 (gf q)) = false := by
      have hs := ((sat_foldl_and_iff qs gf _ v).mp hsat).1
      cases h : DNF.isEmpty (DNF.and g0 (gf q))
      · rfl
      · exact absurd hs (DNF.not_sat_of_isEmpty _ h v)
    exact List.mem_flatMap.mpr ⟨(g0, t0, s0), hmem,
      List.mem_filterMap.mpr ⟨(gf q, Of q), hvalid q List.mem_cons_self, by simp [hne]⟩⟩

/-- Any component choice for `e` whose conjunction some letter satisfies is a product transition of `e`. -/
theorem mem_productTrans_of_sat [LawfulBEq α] [LawfulHashable α] {cv : ConcreteVWAA α} {e : Nat}
    (gf : Nat → DNF α) (Of : Nat → Nat) (v : α → Prop)
    (hvalid : ∀ q ∈ maskMembers e, (gf q, Of q) ∈ cv.trans.getD q [])
    (hsat : DNF.sat ((maskMembers e).foldl (fun acc q => DNF.and acc (gf q)) DNF.top) v) :
    ((maskMembers e).foldl (fun acc q => DNF.and acc (gf q)) DNF.top, (maskMembers e).foldl (fun acc q => acc ||| Of q) 0,
      (maskMembers e).foldl (fun acc q => if cv.final.getD q false && !(Of q).testBit q then acc ||| bit q else acc) 0) ∈
      productTrans cv e :=
  mem_foldl_productStep_of_sat gf Of v _ hvalid _ _ _ _ (List.mem_singleton_self _) hsat

/-- The escaped-own fold has bit `f` exactly when the seed has it, or `f` is a final member whose chosen alternative
does not loop in it. -/
theorem testBit_escFold {cv : ConcreteVWAA α} {Of : Nat → Nat} {l : List Nat} {s0 f : Nat} :
    (l.foldl (fun acc q => if cv.final.getD q false && !(Of q).testBit q then acc ||| bit q else acc) s0).testBit f =
        true ↔
      s0.testBit f = true ∨ (f ∈ l ∧ cv.final.getD f false = true ∧ (Of f).testBit f = false) := by
  rw [testBit_foldl_marks]
  simp [Bool.and_eq_true]

/-- The left-folded union of targets, read as a `Finset`. -/
theorem maskSet_foldl_or (l : List Nat) (Of : Nat → Nat) (t0 : Nat) :
    maskSet (l.foldl (fun acc q => acc ||| Of q) t0) = maskSet t0 ∪ l.toFinset.biUnion fun q => maskSet (Of q) := by
  induction l generalizing t0 with
  | nil => simp
  | cons q qs ih =>
    rw [List.foldl_cons, ih, maskSet_or, List.toFinset_cons, Finset.biUnion_insert]
    ext x
    simp only [Finset.mem_union]
    tauto

/-! ## OR-merging and dominance preservation -/

theorem candBeats_iff [LawfulBEq α] [LawfulHashable α] (c1 c2 : DNF α × Nat × Nat) :
    candBeats c1 c2 = true ↔ c2.2 ≠ c1.2 ∧ maskSub c1.2.1 c2.2.1 = true ∧ maskSub c2.2.2 c1.2.2 = true ∧
      DNF.implies c2.1 c1.1 = true := by
  unfold candBeats
  rw [DNF.impliesFast_eq]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
  tauto

theorem maskSub_of_candBeats {c1 c2 : DNF α × Nat × Nat} (h : candBeats c1 c2 = true) :
    maskSub c1.2.1 c2.2.1 = true := by
  unfold candBeats at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem beatenIn_eq (l : List (DNF α × Nat × Nat)) (n : Nat) (c2 : DNF α × Nat × Nat) :
    beatenIn l (groupByKey (fun c : DNF α × Nat × Nat => c.2.1) l) n c2 = l.any (candBeats · c2) := by
  unfold beatenIn
  split
  · apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨s, -, c1, hc1, hb⟩
      exact ⟨c1, ((mem_groupByKey _ l s c1).mp hc1).1, hb⟩
    · rintro ⟨c1, hc1, hb⟩
      exact ⟨c1.2.1, mem_submasks_of_maskSub (maskSub_of_candBeats hb), c1,
        (mem_groupByKey _ l _ c1).mpr ⟨hc1, rfl⟩, hb⟩
  · rfl

/-- The indexed filter drops exactly the same candidates, so compiled code runs it. -/
@[csimp] theorem dominanceFilter_eq_dominanceFilterFast : @dominanceFilter.{u} = @dominanceFilterFast.{u} := by
  funext α _ _ l
  unfold dominanceFilter dominanceFilterFast
  simp only [beatenIn_eq]

theorem mem_dominanceFilter_iff (l : List (DNF α × Nat × Nat)) (c : DNF α × Nat × Nat) :
    c ∈ dominanceFilter l ↔ c ∈ l ∧ ∀ c1 ∈ l, candBeats c1 c = false := by
  unfold dominanceFilter
  rw [List.mem_filter, Bool.not_eq_true', List.any_eq_false]
  simp only [Bool.not_eq_true]

private theorem candBeats_irrefl (c : DNF α × Nat × Nat) : candBeats c c = false := by
  unfold candBeats
  simp

theorem candBeats_trans [LawfulBEq α] [LawfulHashable α] {c1 c2 c3 : DNF α × Nat × Nat}
    (h12 : candBeats c1 c2 = true) (h23 : candBeats c2 c3 = true) : candBeats c1 c3 = true := by
  obtain ⟨hne12, ht12, hm12, hi12⟩ := (candBeats_iff c1 c2).mp h12
  obtain ⟨-, ht23, hm23, hi23⟩ := (candBeats_iff c2 c3).mp h23
  refine (candBeats_iff c1 c3).mpr ⟨fun h31 => hne12 ?_, maskSub_trans ht12 ht23, maskSub_trans hm23 hm12,
    DNF.implies_trans hi23 hi12⟩
  have ht31 : c3.2.1 = c1.2.1 := congrArg Prod.fst h31
  have hm31 : c3.2.2 = c1.2.2 := congrArg Prod.snd h31
  have ht : c2.2.1 = c1.2.1 := maskSub_antisymm (ht31 ▸ ht23) ht12
  have hm : c2.2.2 = c1.2.2 := maskSub_antisymm hm12 (hm31 ▸ hm23)
  exact Prod.ext ht hm

private theorem length_filter_le_of_impl {γ} {l : List γ} {P Q : γ → Bool} (h : ∀ x ∈ l, P x → Q x) :
    (l.filter P).length ≤ (l.filter Q).length := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have ihr := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.filter_cons]
    by_cases hPa : P a = true
    · have hQa : Q a = true := h a List.mem_cons_self hPa
      simp [hPa, hQa]; omega
    · by_cases hQa : Q a = true <;> simp [hPa, hQa] <;> omega

private theorem length_filter_lt_of_impl_of_mem_diff {γ} {l : List γ} {P Q : γ → Bool}
    (h : ∀ x ∈ l, P x → Q x) {t : γ} (ht : t ∈ l) (htQ : Q t = true) (htP : P t = false) :
    (l.filter P).length < (l.filter Q).length := by
  induction l with
  | nil => simp at ht
  | cons a rest ih =>
    have hmono := length_filter_le_of_impl (l := rest) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.mem_cons] at ht
    simp only [List.filter_cons]
    rcases ht with rfl | ht
    · rw [htP, htQ]; simpa using hmono
    · by_cases hPa : P a = true
      · have hQa : Q a = true := h a List.mem_cons_self hPa
        have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) ht
        simp [hPa, hQa]; omega
      · by_cases hQa : Q a = true
        · have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) ht
          simp [hPa, hQa]; omega
        · simpa [hPa, hQa] using ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) ht

/-- Every candidate has an undominated dominator in `l`, possibly itself, `[GO01]` Step 2's `≼`. -/
theorem exists_dominanceFilter_dominator_aux [LawfulBEq α] [LawfulHashable α] (l : List (DNF α × Nat × Nat))
    (c2 : DNF α × Nat × Nat) (hc2 : c2 ∈ l) :
    ∃ c1 ∈ l, (c1 = c2 ∨ (maskSub c1.2.1 c2.2.1 = true ∧ DNF.implies c2.1 c1.1 = true ∧
      maskSub c2.2.2 c1.2.2 = true)) ∧ ∀ c' ∈ l, candBeats c' c1 = false := by
  suffices h : ∀ n (c2 : DNF α × Nat × Nat), (l.filter (candBeats · c2)).length ≤ n → c2 ∈ l →
      ∃ c1 ∈ l, (c1 = c2 ∨ (maskSub c1.2.1 c2.2.1 = true ∧ DNF.implies c2.1 c1.1 = true ∧
        maskSub c2.2.2 c1.2.2 = true)) ∧ ∀ c' ∈ l, candBeats c' c1 = false by
    exact h _ c2 le_rfl hc2
  intro n
  induction n with
  | zero =>
    intro c2 hn hc2
    refine ⟨c2, hc2, Or.inl rfl, fun c' hc' => ?_⟩
    by_contra hbeat
    have hmem : c' ∈ l.filter (candBeats · c2) := List.mem_filter.mpr ⟨hc', by simpa using hbeat⟩
    have := List.length_pos_of_mem hmem
    omega
  | succ n ih =>
    intro c2 hn hc2
    by_cases hsurv : ∀ c' ∈ l, candBeats c' c2 = false
    · exact ⟨c2, hc2, Or.inl rfl, hsurv⟩
    · push_neg at hsurv
      obtain ⟨c1', hc1'mem, hc1'beats⟩ := hsurv
      have hc1'beats' : candBeats c1' c2 = true := by simpa using hc1'beats
      have hsub : ∀ x ∈ l, candBeats x c1' = true → candBeats x c2 = true :=
        fun _ _ hxc1' => candBeats_trans hxc1' hc1'beats'
      have hlt : (l.filter (candBeats · c1')).length < (l.filter (candBeats · c2)).length :=
        length_filter_lt_of_impl_of_mem_diff hsub hc1'mem hc1'beats' (candBeats_irrefl c1')
      obtain ⟨c1, hc1mem, hdom, hsurv1⟩ := ih c1' (by omega) hc1'mem
      refine ⟨c1, hc1mem, ?_, hsurv1⟩
      obtain ⟨-, ht1', hm1', hi1'⟩ := (candBeats_iff c1' c2).mp hc1'beats'
      rcases hdom with rfl | ⟨httgt, himp, hmsub⟩
      · exact Or.inr ⟨ht1', hi1', hm1'⟩
      · exact Or.inr ⟨maskSub_trans httgt ht1', DNF.implies_trans hi1' himp, maskSub_trans hm1' hmsub⟩

/-- Every candidate has a surviving dominator in `dominanceFilter l`, target no larger, marks no fewer, guard
implied. -/
theorem exists_dominanceFilter_dominator [LawfulBEq α] [LawfulHashable α] (l : List (DNF α × Nat × Nat))
    {g : DNF α} {t m : Nat} (h : (g, t, m) ∈ l) :
    ∃ g1 t1 m1, (g1, t1, m1) ∈ dominanceFilter l ∧ maskSub t1 t = true ∧ DNF.implies g g1 = true ∧
      maskSub m m1 = true := by
  obtain ⟨⟨g1, t1, m1⟩, hc1mem, hdom, hsurv⟩ := exists_dominanceFilter_dominator_aux l (g, t, m) h
  refine ⟨g1, t1, m1, (mem_dominanceFilter_iff l _).mpr ⟨hc1mem, hsurv⟩, ?_⟩
  rcases hdom with heq | ⟨ht, hi, hm⟩
  · simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨maskSub_refl _, DNF.implies_refl _, maskSub_refl _⟩
  · exact ⟨ht, hi, hm⟩

/-! ## The canonical `SetTGBA` -/

/-- The candidates a state `e` produces before reduction. -/
noncomputable def rawCandidates (cv : ConcreteVWAA α) (finals : Array Nat) (e : Finset Nat) :
    List (DNF α × Nat × Nat) :=
  markedProduct cv finals (maskOf e)

/-- The `SetTGBA Nat α` the concrete construction denotes, ignoring numbering. -/
noncomputable def canonicalTrans (cv : ConcreteVWAA α) (finals : Array Nat) (e : Finset Nat) :
    List (((α → Prop) → Prop) × Finset Nat × Finset Nat) :=
  (reduceCandidates (rawCandidates cv finals e)).map fun c => (DNF.sat c.1, maskSet c.2.1, idMarksOf finals c.2.2)

/-- The canonical `SetTGBA`, `Q := Nat`, one transition per surviving reduced candidate. -/
noncomputable def canonicalTGBA (cv : ConcreteVWAA α) (finals : Array Nat) : SetTGBA Nat α where
  trans := canonicalTrans cv finals
  initial := [{cv.initial}]
  finals := finals.toList.toFinset

/-- Every raw candidate marks every final outside its target. -/
theorem rawCandidates_target_exit {cv : ConcreteVWAA α} {finals : Array Nat} {e : Finset Nat} {g : DNF α} {t m : Nat}
    (h : (g, t, m) ∈ rawCandidates cv finals e) {f : Nat} (hf : f ∈ finals.toList) (hnmem : t.testBit f = false) :
    f ∈ idMarksOf finals m := by
  obtain ⟨c, -, heq⟩ := List.mem_map.mp h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨-, rfl, rfl⟩ := heq
  rw [idMarksOf_computeMarks]
  simp only [List.mem_toFinset, List.mem_filter]
  refine ⟨hf, ?_⟩
  have hitf : inTf cv f c.1 c.2.1 = true := by unfold inTf; rw [hnmem]; rfl
  rw [hitf, Bool.or_true]

/-- Membership in `canonicalTrans`, unfolded to a surviving reduced candidate. -/
theorem mem_canonicalTrans_iff (cv : ConcreteVWAA α) (finals : Array Nat) (e : Finset Nat)
    (g' : (α → Prop) → Prop) (e'' m' : Finset Nat) :
    (g', e'', m') ∈ canonicalTrans cv finals e ↔
      ∃ g t m, (g, t, m) ∈ reduceCandidates (rawCandidates cv finals e) ∧ g' = DNF.sat g ∧
        e'' = maskSet t ∧ m' = idMarksOf finals m := by
  unfold canonicalTrans
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨g, t, m⟩, hmem, heq⟩
    simp only [Prod.mk.injEq] at heq
    exact ⟨g, t, m, hmem, heq.1.symm, heq.2.1.symm, heq.2.2.symm⟩
  · rintro ⟨g, t, m, hmem, hg, he, hm⟩
    exact ⟨(g, t, m), hmem, by rw [hg, he, hm]⟩

private theorem sat_escapeGuard_iff (cv : ConcreteVWAA α) (f : Nat) (e' : Nat) (v : α → Prop) :
    DNF.sat ((cv.trans.getD f []).flatMap fun p => if !p.2.testBit f && maskSub p.2 e' then p.1 else []) v ↔
      ∃ p ∈ cv.trans.getD f [], (!p.2.testBit f && maskSub p.2 e') = true ∧ DNF.sat p.1 v := by
  unfold DNF.sat
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨c, ⟨p, hmem, hc⟩, hcsat⟩
    split at hc
    · rename_i hcond
      exact ⟨p, hmem, hcond, c, hc, hcsat⟩
    · exact absurd hc List.not_mem_nil
  · rintro ⟨p, hmem, hcond, c, hcmem, hcsat⟩
    exact ⟨c, ⟨p, hmem, by rw [if_pos hcond]; exact hcmem⟩, hcsat⟩

variable [LawfulBEq α] [LawfulHashable α]

/-- `inTf` is exact: it holds iff every letter `g` admits satisfies `VWAA.inTf` at `e'`, `[GO01]` Definition 5's `T_f`
for a whole guard. -/
theorem inTf_iff (cv : ConcreteVWAA α) (hveryWeak : cv.VeryWeak) (f : Nat) (g : DNF α) (e' : Nat) :
    inTf cv f g e' = true ↔ ∀ v, DNF.sat g v → (abstractOf cv hveryWeak).inTf v (maskSet e') f := by
  unfold inTf VWAA.inTf
  by_cases hf : e'.testBit f = true
  · simp only [hf, Bool.not_true, Bool.false_or]
    rw [DNF.impliesFast_eq, DNF.implies_iff]
    constructor
    · intro h v hv
      obtain ⟨⟨β, o⟩, hmem, hcond, hsat⟩ := (sat_escapeGuard_iff cv f e' v).mp (h v hv)
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      refine Or.inr ⟨DNF.sat β, maskSet o, List.mem_map.mpr ⟨(β, o), hmem, rfl⟩, hsat,
        fun hcon => by rw [mem_maskSet, hcond.1] at hcon; exact absurd hcon (by simp),
        maskSet_subset_of_maskSub hcond.2⟩
    · intro h v hv
      obtain hcon | ⟨g', O, hmem, hgv, hfO, hOe⟩ := h v hv
      · exact absurd (mem_maskSet.mpr hf) hcon
      · obtain ⟨⟨β, o⟩, hmemc, heq⟩ := List.mem_map.mp hmem
        injection heq with hgeq hOeq
        apply (sat_escapeGuard_iff cv f e' v).mpr
        refine ⟨(β, o), hmemc, ?_, hgeq ▸ hgv⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true']
        refine ⟨?_, maskSub_iff_subset.mpr (hOeq ▸ hOe)⟩
        cases h : o.testBit f
        · rfl
        · exact absurd (hOeq ▸ mem_maskSet.mpr h) hfO
  · have hf' : f ∉ maskSet e' := fun h => hf (mem_maskSet.mp h)
    constructor
    · intro _ v _
      exact Or.inl hf'
    · intro _
      simp [hf]

/-- Every reduced candidate satisfies (S): every letter its guard admits has a component choice into its target, and
every mark it carries is justified by `inTf` there. -/
theorem canonicalTrans_soundTrans (cv : ConcreteVWAA α) (finals : Array Nat) (hveryWeak : cv.VeryWeak)
    (e : Finset Nat) (g' : (α → Prop) → Prop) (e'' m' : Finset Nat) (h : (g', e'', m') ∈ canonicalTrans cv finals e) :
    SoundTrans (abstractOf cv hveryWeak) e g' e'' m' := by
  obtain ⟨g, t, m, hmem, hg', he'', hm'⟩ := (mem_canonicalTrans_iff cv finals e g' e'' m').mp h
  have hmemMerge : (g, t, m) ∈ mergeByTarget (rawCandidates cv finals e) := (List.mem_filter.mp hmem).1
  intro v hv
  rw [hg'] at hv
  obtain ⟨g0, hmem0, hsatg0⟩ := (mergeByTarget_sat _ (t, m) v).mp ⟨g, hmemMerge, hv⟩
  obtain ⟨c, hc, heq0⟩ := List.mem_map.mp hmem0
  simp only [Prod.mk.injEq] at heq0
  obtain ⟨hg0eq, htg0, hm0eq⟩ := heq0
  obtain ⟨gf, Of, hvalid, hgeq, hteq, hesceq⟩ := mem_productTrans_of (g := c.1) (t := c.2.1) (s := c.2.2) hc
  have hsatc : DNF.sat c.1 v := by rw [hg0eq]; exact hsatg0
  have hsatgf : ∀ q ∈ maskMembers (maskOf e), DNF.sat (gf q) v :=
    ((sat_foldl_and_iff _ gf DNF.top v).mp (hgeq ▸ hsatc)).2
  have heset : (maskMembers (maskOf e)).toFinset = e := maskSet_maskOf e
  have htarget : maskSet c.2.1 = e.biUnion fun q => maskSet (Of q) := by
    rw [hteq, maskSet_foldl_or, maskSet_zero, Finset.empty_union, heset]
  refine ⟨⟨fun q => DNF.sat (gf q), fun q => maskSet (Of q), ?_, ?_⟩, ?_⟩
  · intro q hq
    have hqe' : q ∈ maskMembers (maskOf e) := by rw [← List.mem_toFinset, heset]; exact hq
    exact ⟨List.mem_map.mpr ⟨(gf q, Of q), hvalid q hqe', rfl⟩, hsatgf q hqe'⟩
  · rw [he'', ← htg0, htarget]
  · intro f hf
    rw [hm', ← hm0eq, idMarksOf_computeMarks] at hf
    simp only [List.mem_toFinset, List.mem_filter, Bool.or_eq_true] at hf
    obtain ⟨-, hcond⟩ := hf
    rw [he'', ← htg0]
    rcases hcond with hesc | hinTf
    · -- `f`'s chosen component does not loop in it, the witness `[BKŘS12]` §6's modified `T_f` names
      rw [hesceq] at hesc
      rcases testBit_escFold.mp hesc with h0 | ⟨hfl, -, hfnl⟩
      · exact absurd h0 (by simp)
      · refine Or.inr ⟨DNF.sat (gf f), maskSet (Of f), List.mem_map.mpr ⟨(gf f, Of f), hvalid f hfl, rfl⟩,
          hsatgf f hfl, fun hcon => by rw [mem_maskSet, hfnl] at hcon; exact absurd hcon (by simp), ?_⟩
        rw [htarget]
        exact fun x hx => Finset.mem_biUnion.mpr ⟨f, heset ▸ List.mem_toFinset.mpr hfl, hx⟩
    · exact (inTf_iff cv hveryWeak f c.1 c.2.1).mp hinTf v hsatc

/-- The construction satisfies tight (C): every component choice for `e` admitting `v` is refined by a surviving reduced
candidate marking every final of `e` whose chosen component does not loop in it and every final outside its target. -/
theorem canonicalTrans_completeTransTight (cv : ConcreteVWAA α) (finals : Array Nat) (hveryWeak : cv.VeryWeak)
    (hfinals : ∀ f ∈ finals.toList, cv.final.getD f false = true) (e : Finset Nat) :
    CompleteTransTight (canonicalTGBA cv finals) (abstractOf cv hveryWeak) e := by
  classical
  intro v gf Of hgfOf
  have heset : (maskMembers (maskOf e)).toFinset = e := maskSet_maskOf e
  -- Concretize the abstract choice functions to concrete alternatives.
  have hconcretize : ∀ q ∈ maskMembers (maskOf e),
      ∃ β o, (β, o) ∈ cv.trans.getD q [] ∧ DNF.sat β = gf q ∧ maskSet o = Of q := by
    intro q hq
    have hqe : q ∈ e := by rw [← heset]; exact List.mem_toFinset.mpr hq
    obtain ⟨hmem, -⟩ := hgfOf q hqe
    obtain ⟨⟨β, o⟩, hmem2, heq2⟩ := List.mem_map.mp hmem
    injection heq2 with h1 h2
    exact ⟨β, o, hmem2, h1, h2⟩
  choose! gfc Ofc hvalidc hgeqc hOeqc using hconcretize
  set g0 := (maskMembers (maskOf e)).foldl (fun acc q => DNF.and acc (gfc q)) DNF.top with hg0def
  set t0 := (maskMembers (maskOf e)).foldl (fun acc q => acc ||| Ofc q) 0 with ht0def
  set esc0 := (maskMembers (maskOf e)).foldl
    (fun acc q => if cv.final.getD q false && !(Ofc q).testBit q then acc ||| bit q else acc) 0 with hesc0def
  have hsatg0 : DNF.sat g0 v := by
    rw [hg0def]
    apply (sat_foldl_and_iff (maskMembers (maskOf e)) gfc DNF.top v).mpr
    refine ⟨DNF.sat_top v, fun q hq => ?_⟩
    have hqe : q ∈ e := by rw [← heset]; exact List.mem_toFinset.mpr hq
    rw [hgeqc q hq]; exact (hgfOf q hqe).2
  have hmemProd : (g0, t0, esc0) ∈ productTrans cv (maskOf e) :=
    mem_productTrans_of_sat gfc Ofc v hvalidc hsatg0
  set m0 := computeMarks cv finals g0 t0 esc0 with hm0def
  have htarget : maskSet t0 = e.biUnion Of := by
    rw [ht0def, maskSet_foldl_or, maskSet_zero, Finset.empty_union, heset]
    apply Finset.biUnion_congr rfl
    intro q hq
    exact hOeqc q (List.mem_toFinset.mp (heset.symm ▸ hq))
  have hmemRaw : (g0, t0, m0) ∈ rawCandidates cv finals e := List.mem_map.mpr ⟨(g0, t0, esc0), hmemProd, rfl⟩
  obtain ⟨g', hg'mem, himplies1⟩ := exists_mergeByTarget_of_mem hmemRaw
  obtain ⟨g'', t'', m'', hg''mem, htsub, himplies2, hmsub⟩ :=
    exists_dominanceFilter_dominator (mergeByTarget (rawCandidates cv finals e)) hg'mem
  refine ⟨DNF.sat g'', maskSet t'', idMarksOf finals m'',
    (mem_canonicalTrans_iff cv finals e (DNF.sat g'') (maskSet t'') (idMarksOf finals m'')).mpr
      ⟨g'', t'', m'', hg''mem, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact (DNF.implies_iff _ _).mp himplies2 v (himplies1 v hsatg0)
  · rw [← htarget]; exact maskSet_subset_of_maskSub htsub
  · intro f hf hfe hfOf
    have hf' : f ∈ finals.toList := List.mem_toFinset.mp hf
    have hfl : f ∈ maskMembers (maskOf e) := by rw [← List.mem_toFinset, heset]; exact hfe
    have hnl : (Ofc f).testBit f = false := by
      have hnot : f ∉ maskSet (Ofc f) := by rw [hOeqc f hfl]; exact hfOf
      cases h : (Ofc f).testBit f
      · rfl
      · exact absurd (mem_maskSet.mpr h) hnot
    have hesc : esc0.testBit f = true := testBit_escFold.mpr (Or.inr ⟨hfl, hfinals f hf', hnl⟩)
    apply idMarksOf_mono hmsub
    rw [hm0def, idMarksOf_computeMarks]
    simp only [List.mem_toFinset, List.mem_filter]
    exact ⟨hf', by rw [hesc, Bool.true_or]⟩
  · intro f hf hnmem
    obtain ⟨g0c, hg0c⟩ := reduceCandidates_target_mem hg''mem
    have hf' : f ∈ finals.toList := List.mem_toFinset.mp hf
    have hnmem' : t''.testBit f = false := by
      cases h : t''.testBit f
      · rfl
      · exact absurd (mem_maskSet.mpr h) hnmem
    exact rawCandidates_target_exit hg0c hf' hnmem'

end LTLLib
