/-
  The product's fused expansion with option bits, for the Streett prune's fast path.

  `EdgeLabels.md` §13.20 (the executable) and §13.22 (the proof). The bits are computed where `base` and
  `steps` are already in hand, from the per-source work `expand` does anyway, so the scan that reads them
  makes no callback. What each bit means is fixed by `StreettOption.onEdges`: option `o` admits the edge
  `(s, t)` iff `(spec.regionSuccs opt.region s).contains t`, i.e. iff *some* realization of the edge reads
  a letter satisfying `opt.region` — decided on every step out of `s`, not only on the steps a candidate's
  region has kept. `optBitsFor` computes exactly that, edge by edge, which is why a candidate's restricted
  expansion still takes its bits from the source's full steps.

  Defines:
  - `optBitsFor`: the packed bits of each successor, from the source's letter and steps
  - `expandWithOpts`, `keptExpandWithOpts`: `expand` and `keptExpand` with the payload filled

  Proves:
  - `edgeBits_testBit_iff`: a product edge's `edgeBits` are the `|||` of `letterBits` over the letters
    its realizations read
  - `optBitsFor_eq`: `optBitsFor` is `edgeBits` mapped over the successors, in both of its branches
  - `expandWithOpts_coherent`/`_bits`, `keptExpandWithOpts_coherent`/`_bits`: what `streettCheckF_eq`
    asks of the two expansions
-/
import LTLLib.TGBABased.Product
import LTLLib.TGBABased.SCC.StreettPruneFast
import LTLLib.Tactic.Set

namespace LTLLib.TGBAProduct

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α] [BEq SysState] [Hashable SysState]

/-- The packed option bits of each successor in `out`, from the source's full `steps`.

Two shapes, as in `succsFrom`. When no step carries a letter of its own every realization of every edge
reads `base`, so the bits are one `letterBits` per *source*, shared by its successors:
`Array.replicate` of a small `Nat`, one allocation and nothing per entry. Otherwise an edge's bits are
the `|||` over its realizations — the existential of `StreettOption.onEdges` — walked the way
`edgeMarksFromShared`'s general path walks them; no wired route reaches this branch today. With no
options at all the payload is empty, by §13.18's rule, and `scanFrameF` never reads it. -/
def optBitsFor (tgba : TGBA α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α)) (q : Nat)
    (base : Std.HashSet α) (steps : Array (LStep α SysState)) (out : Array (SysState × Nat)) :
    Array Nat :=
  if cs.numOptions == 0 then #[]
  else if steps.all (·.1.isEmpty) then
    Array.replicate out.size (cs.letterBits base)
  else
    let ts := tgba.getSuccessors q
    -- PERF: each step's letter and its option bits are invariant in `out`, but were computed in the
    -- innermost position — twice, since the compatibility test and the `|||` each recomputed them. With
    -- an out-degree of `d` that is `2·d·|steps|` `HashSet` allocations per product state against
    -- `|steps|`. `EdgeLabels.md` §12.10 (b): the guard above only spares a property with *no* edge
    -- atoms, so every `T(a)` property paid this in full.
    let info := steps.map fun st =>
      let lbl := LSys.letter base st.1
      (st.2, lbl, cs.letterBits lbl)
    out.map fun p' =>
      info.foldl (init := 0) fun acc si =>
        if si.1 == p'.1 &&
            ts.any (fun t => t.target == p'.2 && transCompatible t si.2.1) then
          acc ||| si.2.2
        else acc

/-- **One pass over (step, transition), then merge by target.** `EdgeLabels.md` §12.12.

`out` is generated as exactly the compatible (step, transition) pairs, so each pair's marks and option
bits are known *as it is generated*. What made an edge-atom property expensive was asking for them again
afterwards, once per successor, by re-scanning every step and every transition — `|out| x |steps| x |ts|`
in `optBitsFor` and the same again through `realizationsFrom`, ~3500 `transCompatible` calls per product
state where `|steps| x |ts|` is ~72.

The letter and its option bits are computed once per *step*; the triples are emitted in `succsFrom`'s own
order, so `out` is that array's first projection; and the per-target union of marks and `|||` of bits is
one fold over the triples. Only the edge-atom branch needs this — a state-labelled source keeps
`marksTableGen`'s `Nat`-keyed table, which is cheaper still because it never hashes a `SysState`. -/
def fusedExpandWithOpts (tgba : TGBA α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (q : Nat) (base : Std.HashSet α) (steps : Array (LStep α SysState)) :
    Array (SysState × Nat) × Array (Std.HashSet Nat) × Array Nat :=
  let ts := tgba.getSuccessors q
  let triples : Array ((SysState × Nat) × Std.HashSet Nat × Nat) :=
    steps.flatMap fun st =>
      let lbl := LSys.letter base st.1
      let bits := if cs.numOptions == 0 then 0 else cs.letterBits lbl
      ts.filterMap fun t =>
        if transCompatible t lbl then some ((st.2, t.target), t.acceptMarks, bits) else none
  -- The accumulator starts at `(∅, 0)` and always `union`s / `|||`s, so a target's entry is *literally*
  -- the fold `edgeMarksFrom`/`optBitsFor` perform over that target's realizations — `realizationsFrom`
  -- enumerates (step, transition) in the order the triples are emitted. Seeding with the first triple's
  -- own payload instead would give the same *elements* but not the same `Std.HashSet` value, and
  -- `ExpandCoherent` asks for equality of the marks array, not equi-membership.
  let tbl : Std.HashMap (SysState × Nat) (Std.HashSet Nat × Nat) :=
    triples.foldl (init := ∅) fun m e =>
      let cur := m.getD e.1 (Std.HashSet.emptyWithCapacity 0, 0)
      m.insert e.1 (cur.1.union e.2.1, cur.2 ||| e.2.2)
  let out := triples.map (·.1)
  (out,
   out.map fun p' => (tbl.getD p' (Std.HashSet.emptyWithCapacity 0, 0)).1,
   if cs.numOptions == 0 then #[]
   else out.map fun p' => (tbl.getD p' (Std.HashSet.emptyWithCapacity 0, 0)).2)

/-- `expand` with the option payload filled. The same per-source work: one `sysLabel`, one `sysSucc`. -/
def expandWithOpts (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (p : SysState × Nat) : Array (SysState × Nat) × Array (Std.HashSet Nat) × Array Nat :=
  let base := sysLabel p.1
  let steps := LSys.totalize sysSucc p.1
  if steps.all (·.1.isEmpty) then
    let byTgt? := marksTableGen tgba p.2 base steps
    let out := succsFrom tgba p.2 base steps
    (out, out.map fun p' => genMarksFromShared tgba p.2 base steps byTgt? p',
      optBitsFor tgba cs p.2 base steps out)
  else fusedExpandWithOpts tgba cs p.2 base steps

/-- `keptExpand` with the option payload filled.

Successors, marks **and bits** are all decided on the *kept* steps. Deciding the bits on all of the
source's steps — which is what this did while `cs.regions` was the unrestricted reading — is the
`EdgeLabels.md` §6.3 failure one level up: it lets an option's mark be witnessed by a realization the
candidate's region excludes, so two conjuncts come out available through realizations no single run can
take. Restricting the letters that contribute is exactly what makes `cs.letterBits` compute the
*restricted* reading, since every kept letter satisfies the region by construction. -/
def keptExpandWithOpts (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (keep : Std.HashSet α → Bool) (p : SysState × Nat) :
    Array (SysState × Nat) × Array (Std.HashSet Nat) × Array Nat :=
  let base := sysLabel p.1
  let steps := LSys.totalize sysSucc p.1
  let kept := keptStepsFrom base steps keep
  if kept.all (·.1.isEmpty) then
    let byTgt? := marksTableGen tgba p.2 base kept
    let out := succsFrom tgba p.2 base kept
    (out, out.map fun p' => genMarksFromShared tgba p.2 base kept byTgt? p',
      optBitsFor tgba cs p.2 base kept out)
  else fusedExpandWithOpts tgba cs p.2 base kept

/-! ## The same expansions, from one system callback

`LSys.StepFn` in place of the `sysSucc`/`sysLabel` pair, so a source's transitions are computed once.
Same expressions, so both bridges are `rfl`. See `Product.lean`'s `OfStep` section and `EdgeLabels.md`
§15. -/

def expandWithOptsOfStep (tgba : TGBA α) (sysStep : LSys.StepFn α SysState)
    (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (p : SysState × Nat) : Array (SysState × Nat) × Array (Std.HashSet Nat) × Array Nat :=
  let r := sysStep p.1
  let base := r.2
  let steps := LSys.totalizeAt r.1 p.1
  if steps.all (·.1.isEmpty) then
    let byTgt? := marksTableGen tgba p.2 base steps
    let out := succsFrom tgba p.2 base steps
    (out, out.map fun p' => genMarksFromShared tgba p.2 base steps byTgt? p',
      optBitsFor tgba cs p.2 base steps out)
  else fusedExpandWithOpts tgba cs p.2 base steps

def keptExpandWithOptsOfStep (tgba : TGBA α) (sysStep : LSys.StepFn α SysState)
    (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (keep : Std.HashSet α → Bool) (p : SysState × Nat) :
    Array (SysState × Nat) × Array (Std.HashSet Nat) × Array Nat :=
  let r := sysStep p.1
  let base := r.2
  let steps := LSys.totalizeAt r.1 p.1
  let kept := keptStepsFrom base steps keep
  if kept.all (·.1.isEmpty) then
    let byTgt? := marksTableGen tgba p.2 base kept
    let out := succsFrom tgba p.2 base kept
    (out, out.map fun p' => genMarksFromShared tgba p.2 base kept byTgt? p',
      optBitsFor tgba cs p.2 base kept out)
  else fusedExpandWithOpts tgba cs p.2 base kept

theorem expandWithOptsOfStep_eq (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (cs : CompiledSpec (SysState × Nat) (Std.HashSet α)) :
    expandWithOptsOfStep tgba (fun s => (sysSucc s, sysLabel s)) cs
      = expandWithOpts tgba sysSucc sysLabel cs := rfl

theorem keptExpandWithOptsOfStep_eq (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (cs : CompiledSpec (SysState × Nat) (Std.HashSet α)) (keep : Std.HashSet α → Bool) :
    keptExpandWithOptsOfStep tgba (fun s => (sysSucc s, sysLabel s)) cs keep
      = keptExpandWithOpts tgba sysSucc sysLabel cs keep := rfl

/-! ## Proof: the bits are the spec's edge predicates -/

section Proof

omit [BEq SysState] [Hashable SysState] in
/-- Membership in a region's restricted successors: some step whose letter satisfies the region
realizes the edge. -/
theorem mem_keptSuccsFrom_iff (tgba : TGBA α) (q : Nat) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) (keep : Std.HashSet α → Bool) (p' : SysState × Nat) :
    p' ∈ keptSuccsFrom tgba q base steps keep ↔
      ∃ st ∈ steps, keep (LSys.letter base st.1) = true ∧ ∃ t ∈ tgba.getSuccessors q,
        transCompatible t (LSys.letter base st.1) = true ∧ st.2 = p'.1 ∧ t.target = p'.2 := by
  rw [keptSuccsFrom, succsFrom_mem_iff]
  simp only [keptStepsFrom, Array.mem_filter]
  constructor
  · rintro ⟨st, ⟨hst, hk⟩, t, ht, hc, h1, h2⟩
    exact ⟨st, hst, hk, t, ht, hc, h1, h2⟩
  · rintro ⟨st, hst, hk, t, ht, hc, h1, h2⟩
    exact ⟨st, ⟨hst, hk⟩, t, ht, hc, h1, h2⟩

omit [BEq SysState] [Hashable SysState] in
/-- The system step `st` realizes the product edge into `p'` out of a source with letter `base`, steps
`steps` and automaton state `q`. -/
abbrev Realizes (tgba : TGBA α) (base : Std.HashSet α) (steps : Array (LStep α SysState)) (q : Nat)
    (p' : SysState × Nat) (st : LStep α SysState) : Prop :=
  st ∈ steps ∧ st.2 = p'.1 ∧ ∃ t ∈ tgba.getSuccessors q,
    transCompatible t (LSys.letter base st.1) = true ∧ t.target = p'.2

omit [BEq α] [Hashable α] [BEq SysState] [Hashable SysState] in
private theorem foldl_or_testBit {β : Type w} (cond : β → Bool) (g : β → Nat) (b : Nat) :
    ∀ (l : List β) (init : Nat),
      (l.foldl (fun acc x => if cond x then acc ||| g x else acc) init).testBit b = true ↔
        init.testBit b = true ∨ ∃ x ∈ l, cond x = true ∧ (g x).testBit b = true
  | [], init => by simp
  | x :: l, init => by
    rw [List.foldl_cons, foldl_or_testBit cond g b l]
    by_cases hc : cond x = true
    · simp only [hc, if_true, Nat.testBit_or, Bool.or_eq_true, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨y, hy, hcy, hby⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x, Or.inl rfl, hc, h⟩
        · exact Or.inr ⟨y, Or.inr hy, hcy, hby⟩
      · rintro (h | ⟨y, (rfl | hy), hcy, hby⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr hby)
        · exact Or.inr ⟨y, hy, hcy, hby⟩
    · simp only [hc, List.mem_cons]
      constructor
      · rintro (h | ⟨y, hy, hcy, hby⟩)
        · exact Or.inl h
        · exact Or.inr ⟨y, Or.inr hy, hcy, hby⟩
      · rintro (h | ⟨y, (rfl | hy), hcy, hby⟩)
        · exact Or.inl h
        · exact absurd hcy hc
        · exact Or.inr ⟨y, hy, hcy, hby⟩

variable [LawfulBEq SysState] [LawfulHashable SysState]

omit [Hashable SysState] [LawfulBEq SysState] in
/-- `optMarks[o]` of a well-formed spec is option `o`'s marks read on edges. -/
theorem optMarks_getElem (cs : CompiledSpec (SysState × Nat) (Std.HashSet α)) (hwf : cs.WF) {o : Nat}
    (ho : o < cs.numOptions) :
    cs.optMarks[o]! = ((cs.letterOptions[o]!).onEdgesIn cs.spec cs.restrict).marks := by
  have ho' : o < cs.letterOptions.size := by rw [hwf.letterOptions_size]; exact ho
  rw [hwf.optMarks_eq, getElem!_pos _ o (by simpa using ho'), getElem!_pos _ o ho', Array.getElem_map]

omit [Hashable SysState] [LawfulHashable SysState] in
/-- Option `o`'s region admits the edge `(p, p')` iff a realization of it reads a letter in the region. -/
theorem region_edge_iff (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (hwf : cs.WF) (hspec : ∀ r, cs.spec.regionSuccs r = keptSuccs tgba sysSucc sysLabel r)
    {o : Nat} (ho : o < cs.numOptions) (p p' : SysState × Nat) :
    cs.regions[o]! (p, p') = true ↔
      ∃ st, Realizes tgba (sysLabel p.1) (LSys.totalize sysSucc p.1) p.2 p' st ∧
        (cs.restrict (LSys.letter (sysLabel p.1) st.1) &&
          (cs.letterOptions[o]!).region (LSys.letter (sysLabel p.1) st.1)) = true := by
  rw [hwf.regions_getElem ho]
  show (cs.spec.regionSuccs _ p).contains p' = true ↔ _
  rw [hspec, Array.contains_iff_mem]
  show p' ∈ keptSuccsFrom tgba p.2 (sysLabel p.1) (LSys.totalize sysSucc p.1) _ ↔ _
  rw [mem_keptSuccsFrom_iff]
  constructor
  · rintro ⟨st, hst, hk, t, ht, hc, h1, h2⟩
    exact ⟨st, ⟨hst, h1, t, ht, hc, h2⟩, hk⟩
  · rintro ⟨st, ⟨hst, h1, t, ht, hc, h2⟩, hk⟩
    exact ⟨st, hst, hk, t, ht, hc, h1, h2⟩

omit [Hashable SysState] [LawfulHashable SysState] in
/-- Option `o`'s mark `k` is carried by the edge `(p, p')` iff a realization of it reads a letter in the
region that also satisfies the mark. -/
theorem mark_edge_iff (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (hwf : cs.WF) (hspec : ∀ r, cs.spec.regionSuccs r = keptSuccs tgba sysSucc sysLabel r)
    {o : Nat} (ho : o < cs.numOptions) {k : Nat} (hk : k < (cs.optMarks[o]!).size)
    (p p' : SysState × Nat) :
    (cs.optMarks[o]!)[k]! (p, p') = true ↔
      ∃ st, Realizes tgba (sysLabel p.1) (LSys.totalize sysSucc p.1) p.2 p' st ∧
        (cs.restrict (LSys.letter (sysLabel p.1) st.1) &&
          (cs.letterOptions[o]!).region (LSys.letter (sysLabel p.1) st.1) &&
          ((cs.letterOptions[o]!).marks)[k]! (LSys.letter (sysLabel p.1) st.1)) = true := by
  rw [optMarks_getElem cs hwf ho] at hk ⊢
  have hk' : k < (cs.letterOptions[o]!).marks.size := by
    simpa [StreettOption.onEdgesIn] using hk
  rw [getElem!_pos _ k hk]
  simp only [StreettOption.onEdgesIn, Array.getElem_map]
  rw [hspec, Array.contains_iff_mem]
  show p' ∈ keptSuccsFrom tgba p.2 (sysLabel p.1) (LSys.totalize sysSucc p.1) _ ↔ _
  rw [mem_keptSuccsFrom_iff]
  simp only [getElem!_pos (cs.letterOptions[o]!).marks k hk']
  constructor
  · rintro ⟨st, hst, hk, t, ht, hc, h1, h2⟩
    exact ⟨st, ⟨hst, h1, t, ht, hc, h2⟩, hk⟩
  · rintro ⟨st, ⟨hst, h1, t, ht, hc, h2⟩, hk⟩
    exact ⟨st, hst, hk, t, ht, hc, h1, h2⟩

omit [Hashable SysState] [LawfulHashable SysState] in
/-- A product edge's `edgeBits`, bit by bit: the `|||` of `letterBits` over the letters its
realizations read. -/
theorem edgeBits_testBit_iff (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (hwf : cs.WF) (hspec : ∀ r, cs.spec.regionSuccs r = keptSuccs tgba sysSucc sysLabel r)
    (p p' : SysState × Nat) (b : Nat) :
    (cs.edgeBits (p, p')).testBit b = true ↔
      ∃ st, Realizes tgba (sysLabel p.1) (LSys.totalize sysSucc p.1) p.2 p' st ∧
        (cs.letterBits (LSys.letter (sysLabel p.1) st.1)).testBit b = true := by
  by_cases hb : b < cs.numOptions
  · rw [cs.edgeBits_testBit_lt _ hb, region_edge_iff tgba sysSucc sysLabel cs hwf hspec hb]
    constructor
    · rintro ⟨st, hr, hk⟩
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hk
      exact ⟨st, hr, (cs.letterBits_testBit hwf _ _).mpr ⟨h1, Or.inl ⟨hb, h2⟩⟩⟩
    · rintro ⟨st, hr, hbit⟩
      obtain ⟨hres, hcase⟩ := (cs.letterBits_testBit hwf _ _).mp hbit
      rcases hcase with ⟨_, hk⟩ | ⟨_, _, _, _, _, hbk, _⟩
      · exact ⟨st, hr, Bool.and_eq_true _ _ |>.mpr ⟨hres, hk⟩⟩
      · omega
  · obtain ⟨b', rfl⟩ : ∃ b', b = cs.numOptions + b' := ⟨b - cs.numOptions, by omega⟩
    rw [cs.edgeBits_testBit_ge hwf]
    constructor
    · rintro ⟨o, ho, k, hk, hbk, hmk⟩
      obtain ⟨st, hr, hok⟩ := (mark_edge_iff tgba sysSucc sysLabel cs hwf hspec ho hk p p').mp hmk
      simp only [Bool.and_eq_true] at hok
      have hk' : k < (cs.letterOptions[o]!).marks.size := by
        rw [optMarks_getElem cs hwf ho] at hk
        simpa [StreettOption.onEdgesIn] using hk
      exact ⟨st, hr, (cs.letterBits_testBit hwf _ _).mpr
        ⟨hok.1.1, Or.inr ⟨o, ho, hok.1.2, k, hk', by omega, hok.2⟩⟩⟩
    · rintro ⟨st, hr, hbit⟩
      obtain ⟨hres, hcase⟩ := (cs.letterBits_testBit hwf _ _).mp hbit
      rcases hcase with ⟨hlt, _⟩ | ⟨o, ho, hreg, k, hk', hbk, hmk⟩
      · omega
      · have hk : k < (cs.optMarks[o]!).size := by
          rw [optMarks_getElem cs hwf ho]
          simpa [StreettOption.onEdgesIn] using hk'
        refine ⟨o, ho, k, hk, by omega, ?_⟩
        exact (mark_edge_iff tgba sysSucc sysLabel cs hwf hspec ho hk p p').mpr
          ⟨st, hr, by simp only [Bool.and_eq_true]; exact ⟨⟨hres, hreg⟩, hmk⟩⟩

omit [Hashable SysState] [LawfulHashable SysState] in
/-- **`optBitsFor` is `edgeBits`**, mapped over any successors that are successors of the source. -/
theorem optBitsFor_eq (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (hwf : cs.WF) (hspec : ∀ r, cs.spec.regionSuccs r = keptSuccs tgba sysSucc sysLabel r)
    (hn : cs.numOptions ≠ 0) (p : SysState × Nat) (out : Array (SysState × Nat))
    (hout : ∀ p' ∈ out, p' ∈ succsFrom tgba p.2 (sysLabel p.1) (LSys.totalize sysSucc p.1)) :
    optBitsFor tgba cs p.2 (sysLabel p.1) (LSys.totalize sysSucc p.1) out =
      out.map fun p' => cs.edgeBits (p, p') := by
  unfold optBitsFor
  rw [if_neg (by simpa using hn)]
  by_cases hall : (LSys.totalize sysSucc p.1).all (·.1.isEmpty) = true
  · rw [if_pos hall]
    have hbase : ∀ st ∈ LSys.totalize sysSucc p.1, LSys.letter (sysLabel p.1) st.1 = sysLabel p.1 :=
      fun st hst => by rw [LSys.letter, if_pos (by simpa using Array.all_eq_true'.mp hall st hst)]
    apply Array.ext
    · simp
    · intro k hk1 hk2
      have hk : k < out.size := by simpa using hk2
      rw [Array.getElem_replicate, Array.getElem_map]
      apply Nat.eq_of_testBit_eq; intro b
      apply Bool.eq_iff_iff.mpr
      rw [edgeBits_testBit_iff tgba sysSucc sysLabel cs hwf hspec]
      have hmem := hout out[k] (Array.getElem_mem _)
      constructor
      · intro hbit
        obtain ⟨st, hst, t, ht, hc, h1, h2⟩ := (succsFrom_mem_iff _ _ _ _ _).mp hmem
        exact ⟨st, ⟨hst, h1, t, ht, hc, h2⟩, by rw [hbase st hst]; exact hbit⟩
      · rintro ⟨st, ⟨hst, _⟩, hbit⟩
        rw [hbase st hst] at hbit
        exact hbit
  · rw [if_neg hall]
    apply Array.ext
    · simp
    · intro k hk1 hk2
      have hk : k < out.size := by simpa using hk2
      simp only [Array.getElem_map]
      apply Nat.eq_of_testBit_eq; intro b
      apply Bool.eq_iff_iff.mpr
      -- the fold now walks the per-step `(target, letter, bits)` triples; `Array.toList_map` plus
      -- `List.foldl_map` puts it back over the steps themselves, at which point this is the pre-hoist
      -- proof unchanged
      rw [edgeBits_testBit_iff tgba sysSucc sysLabel cs hwf hspec, ← Array.foldl_toList,
        Array.toList_map, List.foldl_map,
        foldl_or_testBit
          (fun st : LStep α SysState => st.2 == out[k].1 &&
            (tgba.getSuccessors p.2).any (fun t => t.target == out[k].2 &&
              transCompatible t (LSys.letter (sysLabel p.1) st.1)))
          (fun st : LStep α SysState => cs.letterBits (LSys.letter (sysLabel p.1) st.1))]
      simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, ← Array.mem_def, Bool.and_eq_true,
        beq_iff_eq, Array.any_eq_true]
      constructor
      · rintro ⟨st, hst, ⟨h1, i, hi, ht⟩, hbit⟩
        obtain ⟨ht1, ht2⟩ : (tgba.getSuccessors p.2)[i].target = out[k].2 ∧
            transCompatible (tgba.getSuccessors p.2)[i] (LSys.letter (sysLabel p.1) st.1) = true := by
          simpa using ht
        exact ⟨st, ⟨hst, h1, _, Array.getElem_mem hi, ht2, ht1⟩, hbit⟩
      · rintro ⟨st, ⟨hst, h1, t, ht, hc, h2⟩, hbit⟩
        obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ht
        refine ⟨st, hst, ⟨h1, i, hi, ?_⟩, hbit⟩
        simpa using And.intro h2 hc


/-- `foldl_or_testBit` for an unconditional `|||` fold, which is what a target's entry accumulates. -/
private theorem foldl_or_testBit' {β : Type w} (g : β → Nat) (b : Nat) :
    ∀ (l : List β) (init : Nat),
      (l.foldl (fun acc x => acc ||| g x) init).testBit b = true ↔
        init.testBit b = true ∨ ∃ x ∈ l, (g x).testBit b = true
  | [], init => by simp
  | x :: l, init => by
    rw [List.foldl_cons, foldl_or_testBit' g b l]
    simp only [Nat.testBit_or, Bool.or_eq_true, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨y, hy, hby⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, Or.inl rfl, h⟩
      · exact Or.inr ⟨y, Or.inr hy, hby⟩
    · rintro (h | ⟨y, (rfl | hy), hby⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr hby)
      · exact Or.inr ⟨y, hy, hby⟩

/-- A table built by folding `insert`s that accumulate, read back at one key, is the accumulation over
exactly that key's entries — the rest of the fold never touches it. This is what lets the fused pass be
compared against the per-successor folds `edgeMarksFrom` and `optBitsFor` perform: the two run over the
same (step, transition) pairs, in the same order, from the same seed. -/
private theorem foldl_insert_getD [LawfulBEq SysState] (p' : SysState × Nat)
    (d : Std.HashSet Nat × Nat) :
    ∀ (l : List ((SysState × Nat) × Std.HashSet Nat × Nat))
      (m : Std.HashMap (SysState × Nat) (Std.HashSet Nat × Nat)),
      (l.foldl (init := m) fun m e =>
          let cur := m.getD e.1 d
          m.insert e.1 (cur.1.union e.2.1, cur.2 ||| e.2.2)).getD p' d
        = (l.filter (fun e => e.1 == p')).foldl (init := m.getD p' d)
            (fun acc e => (acc.1.union e.2.1, acc.2 ||| e.2.2)) := by
  intro l
  induction l with
  | nil => intro m; simp
  | cons e l ih =>
    intro m
    rw [List.foldl_cons, List.filter_cons, ih]
    by_cases he : (e.1 == p') = true
    · obtain rfl : e.1 = p' := by simpa using he
      rw [if_pos he, List.foldl_cons]
      congr 1
      simp [Std.HashMap.getD_insert_self]
    · rw [if_neg he]
      congr 1
      rw [Std.HashMap.getD_insert]
      simp [he]

/-- The second component of a pairwise fold is the fold of the second components. -/
private theorem foldl_pair_snd {γ : Type w} {δ : Type w'} (h : Std.HashSet Nat → δ → Std.HashSet Nat)
    (f : γ → δ → γ) :
    ∀ (l : List δ) (a : Std.HashSet Nat) (c : γ),
      (l.foldl (init := (a, c)) fun acc e => (h acc.1 e, f acc.2 e)).2
        = l.foldl (init := c) fun x e => f x e
  | [], _, _ => rfl
  | e :: l, a, c => foldl_pair_snd h f l _ _

/-- The first component, likewise. -/
private theorem foldl_pair_fst {γ : Type w} {δ : Type w'} (h : Std.HashSet Nat → δ → Std.HashSet Nat)
    (f : γ → δ → γ) :
    ∀ (l : List δ) (a : Std.HashSet Nat) (c : γ),
      (l.foldl (init := (a, c)) fun acc e => (h acc.1 e, f acc.2 e)).1
        = l.foldl (init := a) fun x e => h x e
  | [], _, _ => rfl
  | e :: l, a, c => foldl_pair_fst h f l _ _

/-! ### The fused branch's obligations

Three of them: `out` is `succsFrom`'s array (`fusedExpandWithOpts_fst`), entry `i`'s marks are the edge's
marks (`_snd`), entry `i`'s bits are its `edgeBits` (`_thd`). The marks and the bits need different
arguments: the bits are a `Nat`, so `|||` being idempotent makes a bit-level extensionality argument
enough, while the marks are a `Std.HashSet` that `ExpandCoherent` compares by *value*, so they need the
triples reaching a target to be that target's realizations in the same order. -/

/-- Membership in the fused pass's triples: exactly the compatible (step, transition) pairs. Generic in
the payload, so it applies whatever `simp` has made of the option-bit `if`. -/
private theorem mem_fusedTriples {γ : Type w} (tgba : TGBA α)
    (q : Nat) (base : Std.HashSet α) (steps : Array (LStep α SysState))
    (mk : LStep α SysState → TGBA.Transition α → γ) (e : (SysState × Nat) × γ) :
    (e ∈ steps.flatMap fun st =>
        (tgba.getSuccessors q).filterMap fun t =>
          if transCompatible t (LSys.letter base st.1) then some ((st.2, t.target), mk st t) else none)
      ↔ ∃ st ∈ steps, ∃ t ∈ tgba.getSuccessors q,
          transCompatible t (LSys.letter base st.1) = true ∧ e = ((st.2, t.target), mk st t) := by
  rw [Array.mem_flatMap]
  constructor
  · rintro ⟨st, hst, hmem⟩
    obtain ⟨t, ht, hte⟩ := Array.mem_filterMap.mp hmem
    split at hte
    · exact ⟨st, hst, t, ht, by assumption, by simpa using hte.symm⟩
    · exact absurd hte (by simp)
  · rintro ⟨st, hst, t, ht, hc, rfl⟩
    exact ⟨st, hst, Array.mem_filterMap.mpr ⟨t, ht, by rw [if_pos hc]⟩⟩

/-- One step's contribution, when it does reach `p'`: the transitions it is compatible with that land on
`p'.2`, in order. Proved on the transition list, elementwise, so neither side has to be coaxed into the
other's normal form (the left is a `filterMap`, the right a `map` of a `filter`). -/
private theorem step_payload {γ : Type w} (lbl : Std.HashSet α) (tgt : SysState)
    (mk : TGBA.Transition α → γ) (p' : SysState × Nat) (hs : tgt = p'.1)
    (l : List (TGBA.Transition α)) :
    (((l.filterMap fun t =>
          if transCompatible t lbl then some ((tgt, t.target), mk t) else none).filter
            (fun e => e.1 == p')).map (fun e => e.2))
      = (l.filter fun t => t.target == p'.2 && transCompatible t lbl).map (fun t => mk t) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    by_cases hc : transCompatible t lbl = true
    · rw [List.filterMap_cons_some (b := ((tgt, t.target), mk t)) (by simp [hc])]
      by_cases htt : (t.target == p'.2) = true
      · have htt' : t.target = p'.2 := by simpa using htt
        rw [List.filter_cons_of_pos (by simp [Prod.ext_iff, hs, htt']), List.map_cons, ih,
          List.filter_cons_of_pos (by simp [htt, hc]), List.map_cons]
      · rw [List.filter_cons_of_neg (by simp [Prod.ext_iff]; intro _; simpa using htt), ih,
          List.filter_cons_of_neg (by simp [htt])]
    · rw [List.filterMap_cons_none (by simp [hc]), ih, List.filter_cons_of_neg (by simp [hc])]

/-- The triples that reach `p'`, payload by payload, are `p'`'s realizations, in the same order.

`realizationsFrom` filters the *steps* before descending into the transitions, while the fused pass keeps
every step and filters inside; a step that reaches a different target contributes an empty inner array
either way, so `flatMap` sees the same sequence. That the sequences match *in order* is what makes the
marks equal as `Std.HashSet` **values** — `ExpandCoherent` asks for equality, and a union fold is only
order-insensitive up to membership. -/
private theorem fusedTriples_filter_payload {γ : Type w} (tgba : TGBA α)
    (q : Nat) (base : Std.HashSet α) (steps : Array (LStep α SysState))
    (mk : LStep α SysState → TGBA.Transition α → γ) (p' : SysState × Nat) :
    ((steps.flatMap fun st =>
        (tgba.getSuccessors q).filterMap fun t =>
          if transCompatible t (LSys.letter base st.1) then some ((st.2, t.target), mk st t)
          else none).filter (fun e => e.1 == p')).map (·.2)
      = (realizationsFrom tgba q base steps p').map (fun r => mk r.1 r.2) := by
  apply Array.ext'
  rw [realizationsFrom]
  simp only [Array.toList_map, Array.toList_filter, Array.toList_flatMap, Array.toList_filterMap,
    List.filter_flatMap, List.map_flatMap]
  -- both sides are now a `List.flatMap` over the steps; the right filters them first, the left lets a
  -- step that reaches another target contribute nothing
  induction steps.toList with
  | nil => simp
  | cons st l ih =>
    simp only [List.flatMap_cons, List.filter_cons, ih]
    by_cases hs : (st.2 == p'.1) = true
    · have hs' : st.2 = p'.1 := by simpa using hs
      rw [if_pos hs, List.flatMap_cons]
      congr 1
      simp only [Array.toList_map, List.map_map, Function.comp_def]
      exact step_payload (LSys.letter base st.1) st.2
        (fun t => mk st t) p' hs' (tgba.getSuccessors q).toList

    · rw [if_neg hs]
      have hnil : List.map (fun e => e.2) (List.filter (fun e => e.1 == p')
          (List.filterMap (fun t =>
            if transCompatible t (LSys.letter base st.1) then some ((st.2, t.target), mk st t)
            else none) (tgba.getSuccessors q).toList)) = [] := by
        simp only [List.filter_filterMap, List.map_filterMap]
        refine List.filterMap_eq_nil_iff.mpr fun t _ => ?_
        by_cases hc : transCompatible t (LSys.letter base st.1) = true
        · have hne : ¬ (st.2 = p'.1) := by simpa using hs
          simp [hc, Prod.ext_iff, hne]
        · simp [hc]
      rw [hnil, List.nil_append]

/-- The fused pass produces `succsFrom`'s successors, in its order.

Stated on the branch that uses it: `succsFrom` keeps its own fast path for a source all of whose steps
read the source's label, and `expandWithOpts` only reaches the fused pass when that guard fails. -/
theorem fusedExpandWithOpts_fst (tgba : TGBA α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (q : Nat) (base : Std.HashSet α) (steps : Array (LStep α SysState))
    (h : ¬ (steps.all (·.1.isEmpty) = true)) :
    (fusedExpandWithOpts tgba cs q base steps).1 = succsFrom tgba q base steps := by
  rw [fusedExpandWithOpts, succsFrom, if_neg h]
  simp only [Array.map_flatMap, Array.map_filterMap]
  congr 1
  funext st
  congr 1
  funext t
  split <;> rfl

/-- Its marks agree with the spec's, edge by edge.

Unlike the bits, the marks have to agree as `Std.HashSet` **values**, not just up to membership —
`ExpandCoherent` is an array equality and `Std.HashSet` equality is not extensional. So this cannot be a
bit-level argument like `fusedExpandWithOpts_thd`; it goes through `fusedTriples_filter_payload`, which
says the triples reaching `p'` are `p'`'s realizations *in the same order*, and then the two unions are
the same fold over the same list. -/
theorem fusedExpandWithOpts_snd (tgba : TGBA α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (q : Nat) (base : Std.HashSet α) (steps : Array (LStep α SysState))
    (h : ¬ (steps.all (·.1.isEmpty) = true)) :
    (fusedExpandWithOpts tgba cs q base steps).2.1
      = (succsFrom tgba q base steps).map (edgeMarksFrom tgba q base steps) := by
  rw [← fusedExpandWithOpts_fst tgba cs q base steps h, fusedExpandWithOpts]
  refine Array.map_congr_left fun p' _ => ?_
  rw [← Array.foldl_toList, foldl_insert_getD p' _ _ ∅]
  rw [foldl_pair_fst (fun (x : Std.HashSet Nat) (e : (SysState × Nat) × Std.HashSet Nat × Nat) =>
      x.union e.2.1)
    (fun (a : Nat) (e : (SysState × Nat) × Std.HashSet Nat × Nat) => a ||| e.2.2)]
  -- the fused branch is only reached when some step carries its own letter, so the spec's marks are the
  -- unguarded fold over the realizations
  rw [edgeMarksFrom, marksTable, if_neg h]
  show _ = (realizationsFrom tgba q base steps p').foldl
    (init := Std.HashSet.emptyWithCapacity 0) (fun acc r => acc.union r.2.acceptMarks)
  rw [← Array.foldl_toList]
  simp only [Std.HashMap.getD_empty]
  have key := fusedTriples_filter_payload tgba q base steps
    (fun st t => (t.acceptMarks,
      if cs.numOptions == 0 then 0 else cs.letterBits (LSys.letter base st.1))) p'
  have hfold : ∀ (l₁ : List ((SysState × Nat) × Std.HashSet Nat × Nat)),
      l₁.foldl (init := Std.HashSet.emptyWithCapacity 0) (fun x e => x.union e.2.1)
        = (l₁.map (fun e => e.2)).foldl (init := Std.HashSet.emptyWithCapacity 0)
            (fun x v => x.union v.1) := fun l₁ => by rw [List.foldl_map]
  rw [hfold, ← Array.toList_map, ← Array.toList_filter, key]
  rw [Array.toList_map, List.foldl_map]

/-- Its option bits are `optBitsFor`'s.

`optBitsFor` `|||`s a step's bits once per *step*, guarded by "some compatible transition reaches `p'`",
while the table does it once per *realization*. The two therefore agree only because `|||` is idempotent
— which is exactly what a bit-level argument gives for free: bit `b` is set on either side iff some step
reaching `p'` has it, however many times it is contributed. Generic in `(q, base, steps)`, so it serves
the kept-steps expansion as well as the source's own. -/
theorem fusedExpandWithOpts_thd (tgba : TGBA α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (q : Nat) (base : Std.HashSet α) (steps : Array (LStep α SysState))
    (h : ¬ (steps.all (·.1.isEmpty) = true)) :
    (fusedExpandWithOpts tgba cs q base steps).2.2
      = optBitsFor tgba cs q base steps (succsFrom tgba q base steps) := by
  by_cases hn : cs.numOptions = 0
  · rw [fusedExpandWithOpts, optBitsFor]
    simp [hn]
  · rw [optBitsFor, if_neg (by simpa using hn), if_neg h,
      ← fusedExpandWithOpts_fst tgba cs q base steps h, fusedExpandWithOpts]
    simp only [beq_iff_eq, if_neg hn]
    refine Array.map_congr_left fun p' _ => ?_
    rw [← Array.foldl_toList, foldl_insert_getD p' _ _ ∅]
    rw [foldl_pair_snd (fun (x : Std.HashSet Nat) (e : (SysState × Nat) × Std.HashSet Nat × Nat) =>
        x.union e.2.1)
      (fun (a : Nat) (e : (SysState × Nat) × Std.HashSet Nat × Nat) => a ||| e.2.2)]
    refine Nat.eq_of_testBit_eq fun b => ?_
    rw [Bool.eq_iff_iff,
      foldl_or_testBit' (fun (e : (SysState × Nat) × Std.HashSet Nat × Nat) => e.2.2) b,
      ← Array.foldl_toList,
      foldl_or_testBit
        (fun si : SysState × Std.HashSet α × Nat => si.1 == p'.1 &&
          (tgba.getSuccessors q).any (fun t => t.target == p'.2 && transCompatible t si.2.1))
        (fun si : SysState × Std.HashSet α × Nat => si.2.2)]
    simp only [Std.HashMap.getD_empty, Nat.zero_testBit, Bool.false_eq_true, false_or,
      List.mem_filter, ← Array.mem_def, Array.mem_map, Bool.and_eq_true, beq_iff_eq,
      Array.any_eq_true]
    have hmk : ∀ e : (SysState × Nat) × Std.HashSet Nat × Nat,
        (e ∈ steps.flatMap fun st =>
            (tgba.getSuccessors q).filterMap fun t =>
              if transCompatible t (LSys.letter base st.1) then
                some ((st.2, t.target), t.acceptMarks, cs.letterBits (LSys.letter base st.1))
              else none)
          ↔ ∃ st ∈ steps, ∃ t ∈ tgba.getSuccessors q,
              transCompatible t (LSys.letter base st.1) = true ∧
              e = ((st.2, t.target), t.acceptMarks, cs.letterBits (LSys.letter base st.1)) :=
      fun e => mem_fusedTriples tgba q base steps
        (fun st t => (t.acceptMarks, cs.letterBits (LSys.letter base st.1))) e
    constructor
    · rintro ⟨e, ⟨hmem, hp⟩, hbit⟩
      obtain ⟨st, hst, t, ht, hc, rfl⟩ := (hmk e).mp hmem
      simp only at hp
      subst hp
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ht
      refine ⟨_, ⟨st, hst, rfl⟩, ⟨rfl, i, hi, ?_⟩, hbit⟩
      simpa using hc
    · rintro ⟨si, ⟨st, hst, rfl⟩, ⟨h1, i, hi, ht⟩, hbit⟩
      obtain ⟨ht1, ht2⟩ : (tgba.getSuccessors q)[i].target = p'.2 ∧
          transCompatible (tgba.getSuccessors q)[i] (LSys.letter base st.1) = true := by
        simpa using ht
      refine ⟨((st.2, (tgba.getSuccessors q)[i].target),
          (tgba.getSuccessors q)[i].acceptMarks, cs.letterBits (LSys.letter base st.1)),
        ⟨(hmk _).mpr ⟨st, hst, _, Array.getElem_mem hi, ht2, rfl⟩, ?_⟩, hbit⟩
      have h1' : st.2 = p'.1 := by simpa using h1
      show ((st.2, (tgba.getSuccessors q)[i].target) : SysState × Nat) = p'
      rw [h1', ht1]

/-! ## What the router needs -/

theorem expandWithOpts_coherent (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α)) :
    ExpandCoherent (getSuccessors tgba sysSucc sysLabel) (edgeMarks tgba sysSucc sysLabel)
      (expandWithOpts tgba sysSucc sysLabel cs) := by
  intro p
  simp only [expandWithOpts]
  split
  · refine Prod.ext rfl ?_
    exact Array.map_congr_left fun p' hp' => genMarksFromShared_eq tgba p.2 _ _ hp'
  · refine Prod.ext (fusedExpandWithOpts_fst _ _ _ _ _ ‹_›) ?_
    rw [fusedExpandWithOpts_snd _ _ _ _ _ (by assumption)]
    rfl

omit [LawfulHashable SysState] in
theorem expandWithOpts_bits (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (hwf : cs.WF) (hspec : ∀ r, cs.spec.regionSuccs r = keptSuccs tgba sysSucc sysLabel r)
    (hn : cs.numOptions ≠ 0) (p : SysState × Nat) :
    (expandWithOpts tgba sysSucc sysLabel cs p).2.2 =
      (getSuccessors tgba sysSucc sysLabel p).map fun t => cs.edgeBits (p, t) := by
  simp only [expandWithOpts]
  split
  · exact optBitsFor_eq tgba sysSucc sysLabel cs hwf hspec hn p _ (fun _ h => h)
  · rw [fusedExpandWithOpts_thd tgba cs p.2 (sysLabel p.1) (LSys.totalize sysSucc p.1) ‹_›]
    exact optBitsFor_eq tgba sysSucc sysLabel cs hwf hspec hn p _ (fun _ h => h)

theorem keptExpandWithOpts_coherent (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (keep : Std.HashSet α → Bool) :
    ExpandCoherent (keptSuccs tgba sysSucc sysLabel keep) (keptEdgeMarks tgba sysSucc sysLabel keep)
      (keptExpandWithOpts tgba sysSucc sysLabel cs keep) := by
  intro p
  simp only [keptExpandWithOpts]
  split
  · refine Prod.ext rfl ?_
    exact Array.map_congr_left fun p' hp' => genMarksFromShared_eq tgba p.2 _ _ hp'
  · refine Prod.ext (fusedExpandWithOpts_fst _ _ _ _ _ ‹_›) ?_
    rw [fusedExpandWithOpts_snd _ _ _ _ _ (by assumption)]
    rfl

omit [LawfulHashable SysState] in
/-- A candidate's payload carries the bits of the *recompiled* spec.

The bits are folded over the kept steps only, and an option read inside the candidate's region is
satisfied exactly by an in-region realization — so the two sides quantify over the same steps. What makes
this work without a case split on which realization was chosen is `letterBits`' hoisted region test: a
letter outside the region contributes `0`, so the existential over *all* realizations that
`edgeBits_testBit_iff` produces collapses to one over the kept ones. -/
theorem keptExpandWithOpts_bits (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (hwf : cs.WF) (hspec : ∀ r, cs.spec.regionSuccs r = keptSuccs tgba sysSucc sysLabel r)
    (htop : ∀ l, cs.restrict l = true)
    (hn : cs.numOptions ≠ 0) (bits : Nat) (p : SysState × Nat) :
    (keptExpandWithOpts tgba sysSucc sysLabel cs (regionOf cs bits) p).2.2 =
      (keptSuccs tgba sysSucc sysLabel (regionOf cs bits) p).map fun t =>
        (cs.atBits bits).edgeBits (p, t) := by
  set keep := regionOf cs bits with hkeep
  set base := sysLabel p.1 with hbase
  set steps := LSys.totalize sysSucc p.1 with hsteps
  set kept := keptStepsFrom base steps keep with hkept
  set out := succsFrom tgba p.2 base kept with hout
  simp only [keptExpandWithOpts]
  -- Both branches owe the same thing: the bits are `optBitsFor` over the kept steps. The fused branch
  -- reaches it through `fusedExpandWithOpts_thd`, the state-labelled one has it by construction. The
  -- argument itself is about the candidate's region, not the expansion, so it is shared.
  have key : optBitsFor tgba cs p.2 base kept out
      = out.map fun p' => (cs.atBits bits).edgeBits (p, p') := by
    -- a letter outside the candidate's region contributes nothing, at either spec
    have hzero : ∀ l, keep l = false → (cs.atBits bits).letterBits l = 0 := by
      intro l hl
      have : ((cs.atBits bits).restrict l) = false := by
        rw [CompiledSpec.atBits_restrict, ← hkeep]; exact hl
      rw [CompiledSpec.letterBits, if_neg (by rw [this]; simp)]
    have hagree : ∀ l, keep l = true → (cs.atBits bits).letterBits l = cs.letterBits l :=
      fun l hl => CompiledSpec.letterBits_atBits cs hwf bits (by rw [← hkeep]; exact hl) (htop l)
    -- the two existentials range over the same realizations
    have hmain : ∀ p' b, (∃ st ∈ kept, (st.2 = p'.1 ∧ ∃ t ∈ tgba.getSuccessors p.2,
          transCompatible t (LSys.letter base st.1) = true ∧ t.target = p'.2) ∧
          (cs.letterBits (LSys.letter base st.1)).testBit b = true) ↔
        ∃ st, Realizes tgba base steps p.2 p' st ∧
          ((cs.atBits bits).letterBits (LSys.letter base st.1)).testBit b = true := by
      intro p' b
      constructor
      · rintro ⟨st, hst, ⟨h1, t, ht, hc, h2⟩, hbit⟩
        obtain ⟨hstm, hk⟩ := Array.mem_filter.mp hst
        exact ⟨st, ⟨hstm, h1, t, ht, hc, h2⟩, by rw [hagree _ hk]; exact hbit⟩
      · rintro ⟨st, ⟨hstm, h1, t, ht, hc, h2⟩, hbit⟩
        by_cases hk : keep (LSys.letter base st.1) = true
        · exact ⟨st, Array.mem_filter.mpr ⟨hstm, hk⟩, ⟨h1, t, ht, hc, h2⟩,
            by rw [← hagree _ hk]; exact hbit⟩
        · rw [hzero _ (by simpa using hk)] at hbit
          simp at hbit
    unfold optBitsFor
    rw [if_neg (by simpa using hn)]
    by_cases hall : kept.all (·.1.isEmpty) = true
    · rw [if_pos hall]
      have hbl : ∀ st ∈ kept, LSys.letter base st.1 = base :=
        fun st hst => by rw [LSys.letter, if_pos (by simpa using Array.all_eq_true'.mp hall st hst)]
      apply Array.ext
      · simp
      · intro k hk1 hk2
        have hk : k < out.size := by simpa using hk2
        rw [Array.getElem_replicate, Array.getElem_map]
        apply Nat.eq_of_testBit_eq; intro b
        apply Bool.eq_iff_iff.mpr
        rw [edgeBits_testBit_iff tgba sysSucc sysLabel _ (hwf.atBits bits) hspec, ← hmain]
        have hmem : out[k] ∈ succsFrom tgba p.2 base kept := by
          rw [← hout]; exact Array.getElem_mem _
        rw [succsFrom_mem_iff] at hmem
        obtain ⟨st, hst, t, ht, hc, h1, h2⟩ := hmem
        constructor
        · intro hbit
          exact ⟨st, hst, ⟨h1, t, ht, hc, h2⟩, by rw [hbl st hst]; exact hbit⟩
        · rintro ⟨st', hst', -, hbit⟩
          rw [hbl st' hst'] at hbit
          exact hbit
    · rw [if_neg hall]
      apply Array.ext
      · simp
      · intro k hk1 hk2
        have hk : k < out.size := by simpa using hk2
        simp only [Array.getElem_map]
        apply Nat.eq_of_testBit_eq; intro b
        apply Bool.eq_iff_iff.mpr
        rw [edgeBits_testBit_iff tgba sysSucc sysLabel _ (hwf.atBits bits) hspec, ← hmain,
          ← Array.foldl_toList, Array.toList_map, List.foldl_map,
          foldl_or_testBit
            (fun st : LStep α SysState => st.2 == out[k].1 &&
              (tgba.getSuccessors p.2).any (fun t => t.target == out[k].2 &&
                transCompatible t (LSys.letter base st.1)))
            (fun st : LStep α SysState => cs.letterBits (LSys.letter base st.1))]
        simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, ← Array.mem_def, Bool.and_eq_true,
          beq_iff_eq, Array.any_eq_true]
        constructor
        · rintro ⟨st, hst, ⟨h1, i, hi, ht⟩, hbit⟩
          obtain ⟨ht1, ht2⟩ : (tgba.getSuccessors p.2)[i].target = out[k].2 ∧
              transCompatible (tgba.getSuccessors p.2)[i] (LSys.letter base st.1) = true := by
            simpa using ht
          exact ⟨st, hst, ⟨h1, _, Array.getElem_mem hi, ht2, ht1⟩, hbit⟩
        · rintro ⟨st, hst, ⟨h1, t, ht, hc, h2⟩, hbit⟩
          obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ht
          refine ⟨st, hst, ⟨h1, i, hi, ?_⟩, hbit⟩
          simpa using And.intro h2 hc
  split
  case isTrue => exact key
  case isFalse =>
    rw [fusedExpandWithOpts_thd tgba cs p.2 base kept ‹_›]
    exact key

end Proof

end LTLLib.TGBAProduct
