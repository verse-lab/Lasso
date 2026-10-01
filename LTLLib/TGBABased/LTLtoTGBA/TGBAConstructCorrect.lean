/-
  `buildTGBA`'s numbered output accepts exactly what the VWAA it is built from accepts. Runs of the exported TGBA and runs
  of `canonicalTGBA`, the `FinSet Nat`-indexed `SetTGBA` the construction denotes, determine each other whenever the
  worklist state `Represents` the construction, and `canonicalTGBA` meets (S) and tight (C) of `[GO01]` Theorem 2.
  Unlike `[JN18]` §4.5, which relates concrete and abstract GBA by an abstraction function, the relation here is a run
  correspondence, since the statement is about the numbered automaton's own language.

  Proves:
  - `exportTGBA_accepts_iff`: a represented worklist state's export accepts exactly what `canonicalTGBA` does
  - `buildTGBA_accepts_iff`: `buildTGBA cv` accepts exactly what `abstractOf cv` accepts from `{cv.initial}`
  - `buildTGBA_build_accepts_iff`: `buildTGBA (ConcreteVWAA.build φ)` accepts exactly the models of `φ`

  References:
  - `[GO01]` Gastin, Oddoux. Fast LTL to Büchi Automata Translation. CAV'01, Theorem 2.
  - `[JN18]` Jantsch, Norrish. Verifying the LTL to Büchi Automata Translation via Very Weak Alternating
    Automata. ITP'18, §4.5.

  Sections:
  - One step of the correspondence
  - Numbered runs to canonical runs
  - Canonical runs to numbered runs
  - Correctness of `buildTGBA`
-/
import LTLLib.TGBA
import LTLLib.LTL.Semantics
import LTLLib.TGBABased.AbstractSpec.Acceptance
import LTLLib.TGBABased.LTLtoTGBA.Label
import LTLLib.TGBABased.LTLtoTGBA.VWAA
import LTLLib.TGBABased.LTLtoTGBA.TGBAConstruct
import LTLLib.TGBABased.LTLtoTGBA.AbstractSpec.SetTGBA
import LTLLib.TGBABased.LTLtoTGBA.AbstractSpec.VWAAToTGBA
import LTLLib.Data.FinSet

namespace LTLLib

variable {α : Type u} [BEq α] [Hashable α]

/-! ## One step of the correspondence -/

/-- An exported edge leaving a state's id is one cube of one of that state's reduced candidates, its target the
candidate target's id. -/
theorem exists_candidate_of_mem_getSuccessors {cv : ConcreteVWAA α} {finals : Array Nat}
    {st : TGBAConstructState α} {initId : Nat} (hrep : Represents cv finals st) {e : Nat} {id : Nat}
    (he : st.visited[e]? = some id) {t : TGBA.Transition α}
    (ht : t ∈ (exportTGBA finals st initId).getSuccessors id) :
    ∃ g e' marks c, (g, e', marks) ∈ reduceCandidates (markedProduct cv finals e) ∧
      st.visited[e']? = some t.target ∧ t.acceptMarks = Std.HashSet.ofList (maskMembers marks) ∧ c ∈ DNF.cubes g ∧
      t.positiveProps = c.pos ∧ t.negativeProps = c.neg := by
  obtain ⟨arr, harr, g, tid, marks, hgtm, c, hc, rfl⟩ := mem_exportTGBA_getSuccessors.mp ht
  obtain ⟨e0, he0, hexpl, hlist⟩ := hrep.denotes id arr harr
  rw [hlist] at hgtm
  obtain ⟨⟨g1, e', m1⟩, hmem, heq⟩ := List.mem_map.mp hgtm
  obtain ⟨tid', htid'⟩ := hexpl g1 e' m1 hmem
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hg, htid, hm⟩ := heq
  have hgetD : st.visited.getD e' 0 = tid' := by rw [Std.HashMap.getD_eq_getD_getElem?, htid']; rfl
  rw [hrep.consistent e0 e id he0 he, hg, hm] at hmem
  exact ⟨g, e', marks, c, hmem, by rw [← htid, hgetD]; exact htid', rfl, hc, rfl, rfl⟩

/-- A reduced candidate of a visited state gives, for each cube of its guard, an exported edge from the state's id
to the candidate target's id. -/
theorem exists_edge_of_candidate {cv : ConcreteVWAA α} {finals : Array Nat} {st : TGBAConstructState α}
    {initId : Nat} (hrep : Represents cv finals st) {e : Nat} {id : Nat} (he : st.visited[e]? = some id)
    {g : DNF α} {e' : Nat} {m : Nat}
    (hmem : (g, e', m) ∈ reduceCandidates (markedProduct cv finals e)) {c : Cube α} (hc : c ∈ DNF.cubes g) :
    ∃ tid, st.visited[e']? = some tid ∧
      ({ target := tid, positiveProps := c.pos, negativeProps := c.neg,
         acceptMarks := Std.HashSet.ofList (maskMembers m) } : TGBA.Transition α) ∈
        (exportTGBA finals st initId).getSuccessors id := by
  obtain ⟨arr, harr⟩ := hrep.finished e id he
  obtain ⟨e0, he0, hexpl, hlist⟩ := hrep.denotes id arr harr
  rw [hrep.consistent e e0 id he he0] at hmem
  obtain ⟨tid, htid⟩ := hexpl g e' m hmem
  have hgetD : st.visited.getD e' 0 = tid := by rw [Std.HashMap.getD_eq_getD_getElem?, htid]; rfl
  refine ⟨tid, htid, mem_exportTGBA_getSuccessors.mpr ⟨arr, harr, g, tid, m, ?_, c, hc, rfl⟩⟩
  rw [hlist]
  exact List.mem_map.mpr ⟨(g, e', m), hmem, by simp only [hgetD]⟩

private theorem getD_eq_toList_getElem {finals : Array Nat} {i : Nat} (hi : i < finals.size) :
    finals.getD i 0 = finals.toList[i]'(by simpa using hi) := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]

/-! ## Numbered runs to canonical runs -/

/-- A run of the export gives a run of `canonicalTGBA` from `{cv.initial}` along the same word. -/
theorem canonical_acceptsFrom_of_export_accepts [LawfulBEq α] {cv : ConcreteVWAA α} {finals : Array Nat}
    {st : TGBAConstructState α} {initId : Nat} (hrep : Represents cv finals st)
    (hinit : st.visited[bit cv.initial]? = some initId) {ξ : OmegaWord α}
    (h : (exportTGBA finals st initId).toSpec.accepts ξ) :
    (canonicalTGBA cv finals).AcceptsFrom {cv.initial} ξ := by
  classical
  obtain ⟨σ, hrun, hcompat, hacc⟩ := h
  -- a state is admissible at position `n` when it is numbered by `σ n`'s source
  -- the successor id is chosen for every `e`, admissible or not, so that `nxt` needs no admissibility proof
  have hstep : ∀ n (e : Nat), ∃ e' : Nat, st.visited[e]? = some (σ n).1 →
      st.visited[e']? = some (σ (n + 1)).1 ∧
        ∃ g marks c, (g, e', marks) ∈ reduceCandidates (markedProduct cv finals e) ∧
          (σ n).2.acceptMarks = Std.HashSet.ofList (maskMembers marks) ∧ c ∈ DNF.cubes g ∧
          (σ n).2.positiveProps = c.pos ∧ (σ n).2.negativeProps = c.neg := by
    intro n e
    by_cases he : st.visited[e]? = some (σ n).1
    · obtain ⟨g, e', marks, c, hmem, hvis, hmarks, hc, hpos, hneg⟩ :=
        exists_candidate_of_mem_getSuccessors (initId := initId) hrep he (hrun.2 n).1
      refine ⟨e', fun _ => ⟨?_, g, marks, c, hmem, hmarks, hc, hpos, hneg⟩⟩
      rw [hvis]
      exact congrArg some (hrun.2 n).2
    · exact ⟨0, fun h => absurd h he⟩
  obtain ⟨nxt, hnxt⟩ := Classical.axiomOfChoice fun n => Classical.axiomOfChoice (hstep n)
  let A : Nat → Nat := fun n => Nat.rec (motive := fun _ => Nat) (bit cv.initial) nxt n
  have hA : ∀ n, st.visited[A n]? = some (σ n).1 := by
    intro n
    induction n with
    | zero =>
      have h0 : (σ 0).1 = initId := exportTGBA_isInitial_iff.mp hrun.1
      rw [h0]; exact hinit
    | succ n ih => exact (hnxt n (A n) ih).1
  obtain ⟨gs, hgs⟩ := Classical.axiomOfChoice fun n => (hnxt n (A n) (hA n)).2
  obtain ⟨ms, hgs⟩ := Classical.axiomOfChoice hgs
  obtain ⟨cs, hgs⟩ := Classical.axiomOfChoice hgs
  refine ⟨⟨fun n => maskSet (A n), fun n => idMarksOf finals (ms n)⟩, ⟨?_, fun n => ?_⟩, ?_⟩
  · exact maskSet_bit cv.initial
  · obtain ⟨hmem, -, hc, hpos, hneg⟩ := hgs n
    refine ⟨DNF.sat (gs n), (mem_canonicalTrans_iff cv finals _ _ _ _).mpr
      ⟨gs n, A (n + 1), ms n, ?_, rfl, rfl, rfl⟩, ?_⟩
    · show (gs n, nxt n (A n), ms n) ∈ reduceCandidates (markedProduct cv finals (maskOf (maskSet (A n))))
      rw [maskOf_maskSet]
      exact hmem
    · refine (DNF.sat_cubes (gs n) (ξ n)).mp ⟨cs n, hc, fun a ha => ?_, fun a ha => ?_⟩
      · exact (hcompat n).1 a (by rw [hpos]; exact ha)
      · exact (hcompat n).2 a (by rw [hneg]; exact ha)
  · intro f hf
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinSet.mp hf)
    have hi' : i < finals.size := by simpa using hi
    refine FinitePred.not_of_forall_exists_gt fun a => ?_
    obtain ⟨j, hj⟩ := hacc ⟨i, hi'⟩ (a + 1)
    refine ⟨a + 1 + j, ?_, by omega⟩
    show finals.toList[i] ∈ idMarksOf finals (ms (a + 1 + j))
    change (σ (a + 1 + j)).2.acceptMarks.contains i = true at hj
    rw [(hgs (a + 1 + j)).2.1, Std.HashSet.contains_ofList, List.contains_iff_mem] at hj
    unfold idMarksOf
    exact List.mem_toFinSet.mpr (List.mem_map.mpr ⟨i, hj, getD_eq_toList_getElem hi'⟩)

/-! ## Canonical runs to numbered runs -/

/-- A run of `canonicalTGBA` from `{cv.initial}` gives a run of the export along the same word. -/
theorem export_accepts_of_canonical_acceptsFrom [LawfulBEq α] {cv : ConcreteVWAA α} {finals : Array Nat}
    {st : TGBAConstructState α} {initId : Nat} (hrep : Represents cv finals st)
    (hinit : st.visited[bit cv.initial]? = some initId) (hnd : finals.toList.Nodup) {ξ : OmegaWord α}
    (h : (canonicalTGBA cv finals).AcceptsFrom {cv.initial} ξ) :
    (exportTGBA finals st initId).toSpec.accepts ξ := by
  classical
  obtain ⟨r, hv, hacc⟩ := h
  let A : Nat → Nat := fun n => maskOf (r.state n)
  have hA0 : A 0 = bit cv.initial := by
    show maskOf (r.state 0) = _
    rw [hv.init, maskOf_singleton]
  have hstep : ∀ n, ∃ (g : DNF α) (m : Nat) (c : Cube α),
      (g, A (n + 1), m) ∈ reduceCandidates (markedProduct cv finals (A n)) ∧ r.mark n = idMarksOf finals m ∧
        c ∈ DNF.cubes g ∧ c.sat (ξ n) := by
    intro n
    obtain ⟨g', hmemT, hg'⟩ := hv.step n
    obtain ⟨g, t, m, hmem, rfl, htgt, hmk⟩ := (mem_canonicalTrans_iff cv finals _ _ _ _).mp hmemT
    have hA1 : A (n + 1) = t := by
      show maskOf (r.state (n + 1)) = t
      rw [htgt, maskOf_maskSet]
    obtain ⟨c, hc, hcs⟩ := (DNF.sat_cubes g (ξ n)).mpr hg'
    exact ⟨g, m, c, by rw [hA1]; exact hmem, hmk, hc, hcs⟩
  obtain ⟨gs, hgs⟩ := Classical.axiomOfChoice hstep
  obtain ⟨ms, hgs⟩ := Classical.axiomOfChoice hgs
  obtain ⟨cs, hgs⟩ := Classical.axiomOfChoice hgs
  have hvis : ∀ n, ∃ id, st.visited[A n]? = some id := by
    intro n
    induction n with
    | zero => exact ⟨initId, by rw [hA0]; exact hinit⟩
    | succ n ih =>
      obtain ⟨id, hid⟩ := ih
      obtain ⟨tid, htid, -⟩ := exists_edge_of_candidate (initId := initId) hrep hid (hgs n).1 (hgs n).2.2.1
      exact ⟨tid, htid⟩
  let ids : Nat → Nat := fun n => st.visited.getD (A n) 0
  have hids : ∀ n, st.visited[A n]? = some (ids n) := by
    intro n
    obtain ⟨id, hid⟩ := hvis n
    show _ = some (st.visited.getD (A n) 0)
    rw [Std.HashMap.getD_eq_getD_getElem?, hid]
    rfl
  refine ⟨fun n => ⟨ids n, TGBA.Transition.mk (ids (n + 1)) (cs n).pos (cs n).neg
      (Std.HashSet.ofList (maskMembers (ms n)))⟩, ⟨?_, fun n => ⟨?_, rfl⟩⟩, fun n => (hgs n).2.2.2, ?_⟩
  · have h0 : ids 0 = initId := by
      have := hids 0
      rw [hA0, hinit] at this
      exact (Option.some.inj this).symm
    exact exportTGBA_isInitial_iff.mpr h0
  · obtain ⟨tid, htid, hmemE⟩ := exists_edge_of_candidate (initId := initId) hrep (hids n) (hgs n).1 (hgs n).2.2.1
    have htid' : tid = ids (n + 1) := Option.some.inj (htid.symm.trans (hids (n + 1)))
    rw [htid'] at hmemE
    exact hmemE
  · intro i n
    have hi : i.val < finals.size := i.isLt
    have hmemf : finals[i.val] ∈ (canonicalTGBA cv finals).finals :=
      List.mem_toFinSet.mpr (Array.getElem_mem_toList hi)
    obtain ⟨b, hb, hnb⟩ := FinitePred.exists_gt_of_not (hacc _ hmemf) n
    refine ⟨b - n, ?_⟩
    have hbn : n + (b - n) = b := by omega
    show (Std.HashSet.ofList (maskMembers (ms (n + (b - n))))).contains i.val = true
    rw [hbn, Std.HashSet.contains_ofList, List.contains_iff_mem, mem_maskMembers]
    have hmb : finals[i.val] ∈ idMarksOf finals (ms b) := by rw [← (hgs b).2.1]; exact hb
    exact (getElem_mem_idMarksOf_iff hnd (reduceCandidates_markedProduct_marks_lt (hgs b).1) hi).mp hmb

/-! ## Correctness of `buildTGBA` -/

/-- A represented worklist state's export accepts exactly the words `canonicalTGBA` accepts from `{cv.initial}`. -/
theorem exportTGBA_accepts_iff [LawfulBEq α] {cv : ConcreteVWAA α} {finals : Array Nat}
    {st : TGBAConstructState α} {initId : Nat} (hrep : Represents cv finals st)
    (hinit : st.visited[bit cv.initial]? = some initId) (hnd : finals.toList.Nodup) (ξ : OmegaWord α) :
    (exportTGBA finals st initId).toSpec.accepts ξ ↔ (canonicalTGBA cv finals).AcceptsFrom {cv.initial} ξ :=
  ⟨canonical_acceptsFrom_of_export_accepts hrep hinit, export_accepts_of_canonical_acceptsFrom hrep hinit hnd⟩

/-- `buildTGBA cv` accepts exactly the words `cv`'s VWAA accepts from its initial state, `[GO01]` Theorem 2 for the
concrete construction. -/
theorem buildTGBA_accepts_iff [LawfulBEq α] [LawfulHashable α] (cv : ConcreteVWAA α)
    (hveryWeak : cv.VeryWeak)
    (hsize : cv.final.size ≤ cv.table.formulas.size) {result : TGBA α} (hr : buildTGBA cv = some result)
    (ξ : OmegaWord α) :
    result.toSpec.accepts ξ ↔ (abstractOf cv hveryWeak).AcceptsFrom {cv.initial} ξ := by
  obtain ⟨initId, st, hex, rfl⟩ := buildTGBA_eq_some hr
  obtain ⟨hrep, hinit⟩ := exploreState_initial_represents hex
  rw [exportTGBA_accepts_iff hrep hinit (finalsOf_nodup cv) ξ]
  have hfin : ∀ f ∈ (finalsOf cv).toList, cv.final.getD f false = true := fun f hf => (mem_finalsOf_iff hsize).mp hf
  have hsc : SoundCompleteTight (canonicalTGBA cv (finalsOf cv)) (abstractOf cv hveryWeak) :=
    ⟨fun f => by
        show f ∈ (finalsOf cv).toList.toFinSet ↔ cv.final.getD f false = true
        rw [List.mem_toFinSet]
        exact mem_finalsOf_iff hsize,
      fun e _ g e' m h => canonicalTrans_soundTrans cv (finalsOf cv) hveryWeak e g e' m h,
      fun e _ => canonicalTrans_completeTransTight cv (finalsOf cv) hveryWeak hfin e⟩
  exact vwaaToTgba_correct' hsc ⟨{cv.initial}, List.mem_singleton_self _, .refl⟩

/-- `buildTGBA (ConcreteVWAA.build φ)` accepts exactly the models of `φ`. -/
theorem buildTGBA_build_accepts_iff [DecidableEq α] [LawfulBEq α] [LawfulHashable α] (φ : NNF α)
    {result : TGBA α} (hr : buildTGBA (ConcreteVWAA.build φ) = some result) (ξ : OmegaWord α) :
    result.toSpec.accepts ξ ↔ φ.satisfies ξ :=
  (buildTGBA_accepts_iff _ (ConcreteVWAA.build_veryWeak φ) (ConcreteVWAA.build_final_size φ) hr ξ).trans
    (ConcreteVWAA.build_correct φ ξ)

end LTLLib
