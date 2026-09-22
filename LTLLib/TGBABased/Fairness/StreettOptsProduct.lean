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
    out.map fun p' =>
      steps.foldl (init := 0) fun acc st =>
        if st.2 == p'.1 &&
            ts.any (fun t => t.target == p'.2 && transCompatible t (LSys.letter base st.1)) then
          acc ||| cs.letterBits (LSys.letter base st.1)
        else acc

/-- `expand` with the option payload filled. The same per-source work: one `sysLabel`, one `sysSucc`. -/
def expandWithOpts (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (p : SysState × Nat) : Array (SysState × Nat) × Array (Std.HashSet Nat) × Array Nat :=
  let base := sysLabel p.1
  let steps := LSys.totalize sysSucc p.1
  let byTgt? := marksTableGen tgba p.2 base steps
  let out := succsFrom tgba p.2 base steps
  (out, out.map fun p' => genMarksFromShared tgba p.2 base steps byTgt? p',
    optBitsFor tgba cs p.2 base steps out)

/-- `keptExpand` with the option payload filled. Successors and marks are those of the kept steps; the
bits are decided on all of the source's steps, as `cs.regions` is. -/
def keptExpandWithOpts (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (keep : Std.HashSet α → Bool) (p : SysState × Nat) :
    Array (SysState × Nat) × Array (Std.HashSet Nat) × Array Nat :=
  let base := sysLabel p.1
  let steps := LSys.totalize sysSucc p.1
  let kept := keptStepsFrom base steps keep
  let byTgt? := marksTableGen tgba p.2 base kept
  let out := succsFrom tgba p.2 base kept
  (out, out.map fun p' => genMarksFromShared tgba p.2 base kept byTgt? p',
    optBitsFor tgba cs p.2 base steps out)

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
    cs.optMarks[o]! = ((cs.letterOptions[o]!).onEdges cs.spec).marks := by
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
        (cs.letterOptions[o]!).region (LSys.letter (sysLabel p.1) st.1) = true := by
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
        ((cs.letterOptions[o]!).region (LSys.letter (sysLabel p.1) st.1) &&
          ((cs.letterOptions[o]!).marks)[k]! (LSys.letter (sysLabel p.1) st.1)) = true := by
  rw [optMarks_getElem cs hwf ho] at hk ⊢
  have hk' : k < (cs.letterOptions[o]!).marks.size := by
    simpa [StreettOption.onEdges] using hk
  rw [getElem!_pos _ k hk]
  simp only [StreettOption.onEdges, Array.getElem_map]
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
      exact ⟨st, hr, (cs.letterBits_testBit hwf _ _).mpr (Or.inl ⟨hb, hk⟩)⟩
    · rintro ⟨st, hr, hbit⟩
      rcases (cs.letterBits_testBit hwf _ _).mp hbit with ⟨_, hk⟩ | ⟨_, _, _, _, _, hbk, _⟩
      · exact ⟨st, hr, hk⟩
      · omega
  · obtain ⟨b', rfl⟩ : ∃ b', b = cs.numOptions + b' := ⟨b - cs.numOptions, by omega⟩
    rw [cs.edgeBits_testBit_ge hwf]
    constructor
    · rintro ⟨o, ho, k, hk, hbk, hmk⟩
      obtain ⟨st, hr, hok⟩ := (mark_edge_iff tgba sysSucc sysLabel cs hwf hspec ho hk p p').mp hmk
      simp only [Bool.and_eq_true] at hok
      have hk' : k < (cs.letterOptions[o]!).marks.size := by
        rw [optMarks_getElem cs hwf ho] at hk
        simpa [StreettOption.onEdges] using hk
      exact ⟨st, hr, (cs.letterBits_testBit hwf _ _).mpr
        (Or.inr ⟨o, ho, hok.1, k, hk', by omega, hok.2⟩)⟩
    · rintro ⟨st, hr, hbit⟩
      rcases (cs.letterBits_testBit hwf _ _).mp hbit with ⟨hlt, _⟩ | ⟨o, ho, hreg, k, hk', hbk, hmk⟩
      · omega
      · have hk : k < (cs.optMarks[o]!).size := by
          rw [optMarks_getElem cs hwf ho]
          simpa [StreettOption.onEdges] using hk'
        refine ⟨o, ho, k, hk, by omega, ?_⟩
        exact (mark_edge_iff tgba sysSucc sysLabel cs hwf hspec ho hk p p').mpr
          ⟨st, hr, by simp only [Bool.and_eq_true]; exact ⟨hreg, hmk⟩⟩

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
      rw [edgeBits_testBit_iff tgba sysSucc sysLabel cs hwf hspec, ← Array.foldl_toList,
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

/-! ## What the router needs -/

theorem expandWithOpts_coherent (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α)) :
    ExpandCoherent (getSuccessors tgba sysSucc sysLabel) (edgeMarks tgba sysSucc sysLabel)
      (expandWithOpts tgba sysSucc sysLabel cs) := by
  intro p
  refine Prod.ext rfl ?_
  exact Array.map_congr_left fun p' hp' => genMarksFromShared_eq tgba p.2 _ _ hp'

omit [LawfulHashable SysState] in
theorem expandWithOpts_bits (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (hwf : cs.WF) (hspec : ∀ r, cs.spec.regionSuccs r = keptSuccs tgba sysSucc sysLabel r)
    (hn : cs.numOptions ≠ 0) (p : SysState × Nat) :
    (expandWithOpts tgba sysSucc sysLabel cs p).2.2 =
      (getSuccessors tgba sysSucc sysLabel p).map fun t => cs.edgeBits (p, t) :=
  optBitsFor_eq tgba sysSucc sysLabel cs hwf hspec hn p _ (fun _ h => h)

theorem keptExpandWithOpts_coherent (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (keep : Std.HashSet α → Bool) :
    ExpandCoherent (keptSuccs tgba sysSucc sysLabel keep) (keptEdgeMarks tgba sysSucc sysLabel keep)
      (keptExpandWithOpts tgba sysSucc sysLabel cs keep) := by
  intro p
  refine Prod.ext rfl ?_
  exact Array.map_congr_left fun p' hp' => genMarksFromShared_eq tgba p.2 _ _ hp'

omit [LawfulHashable SysState] in
theorem keptExpandWithOpts_bits (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (cs : CompiledSpec (SysState × Nat) (Std.HashSet α))
    (hwf : cs.WF) (hspec : ∀ r, cs.spec.regionSuccs r = keptSuccs tgba sysSucc sysLabel r)
    (hn : cs.numOptions ≠ 0) (keep : Std.HashSet α → Bool) (p : SysState × Nat) :
    (keptExpandWithOpts tgba sysSucc sysLabel cs keep p).2.2 =
      (keptSuccs tgba sysSucc sysLabel keep p).map fun t => cs.edgeBits (p, t) :=
  optBitsFor_eq tgba sysSucc sysLabel cs hwf hspec hn p _ (fun p' hp' => by
    rw [succsFrom_mem_iff] at hp' ⊢
    obtain ⟨st, hst, t, ht, hc, h1, h2⟩ := hp'
    exact ⟨st, (Array.mem_filter.mp hst).1, t, ht, hc, h1, h2⟩)

end Proof

end LTLLib.TGBAProduct
