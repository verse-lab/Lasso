module

/-
  The recursive fairness check of [SLDP09] as a specification, and the Emerson-Lei argument [EL87] that it misses
  nothing — with the hoisted regions restricting *steps* rather than states.

  `RRefuted spec com r C` is a derivation that the check found no fair SCC inside the candidate `C` once the
  letters have been narrowed to `r` and the options `com` have been committed to. One step enumerates the maximal
  SCCs of `C`'s `r`-restricted subgraph and, for each one that covers the property marks, names a conjunct. If a
  committed option of that conjunct has a mark not witnessed there, nothing more is required. Otherwise every
  option of the conjunct whose marks are witnessed is refuted after conjoining its region and committing to it.

  ```
  check(r, C):                                  -- B ranges over the maximal SCCs of (regionSuccs r ∩ C²)
    if B covers the property marks and every conjunct has an available option:  report B
    if B misses a property mark:  discard B     -- marks are monotone downward
    let i be the first conjunct with no available option
    if i has a committed option then discard B  -- its marks are missing, and its live siblings were branched on
    live := its options whose marks are all witnessed inside B
    if live = ∅ then discard B                  -- no subgraph can satisfy conjunct i either
    for each option opt in live:  check(r ∧ opt.region, B)
  ```

  Two things differ from the state-labelled reading in `StreettSCC.lean`, both forced by §6.3 of `EdgeLabels.md`:

  - A prune step keeps *all* of `B` and narrows the region instead of deleting states. An edge prune need not
    remove a state, so recursion on the state set alone would not progress; the implementation carries the
    conjoined options as a bitmask and decreases on that (`Candidate.measure`).
  - An option's marks are witnessed at the *conjoined* predicate `r ∧ opt.region ∧ g`, so the region and the mark
    are answered on one realization. Reading them on different realizations of the same endpoint pair is the
    unsoundness §6.3 refutes.

  Defines:
  - `RRefuted`: the check's refusal of a candidate, one constructor per pass
  - `RRefutedFrom`: the same for the first pass, which runs on the whole graph at the top region

  Proves:
  - `RRefuted.no_fairSCC`, `RRefutedFrom.no_fairSCC`: a refuted candidate holds no `RFairSCC`
  - `RRefuted.congr`, `RRefuted.of_empty`: a refusal depends only on the candidate's members, and an empty
    candidate is refused
  - `RRefuted.mono`: a refusal stays one when more options count as committed

  References:
  - [SLDP09] Sun, Liu, Dong, Pang. PAT: Towards Flexible Verification under Fairness. CAV 2009.
  - [EL87] Emerson, Lei. Modalities for model checking: branching time logic strikes back. Sci. Comput. Program.
    8(3), 1987.
  - [LSFZ16] Li, Song, Feng, Zhang. Verify LTL with Fairness Assumptions Efficiently. arXiv:1606.08116, 2016.

  Sections:
  - Refutation
  - Correctness
  - The first pass
-/
public import LTLLib.TGBABased.AbstractSpec.StreettSCCRegion

public section

namespace LTLLib

variable {State : Type u} {L : Type w} [BEq State] [Hashable State] [LawfulBEq State]
  [LawfulHashable State]

/-! ## Refutation -/

/-- The subgraph a candidate induces: the spec's `r`-restricted steps, confined to `C`. This is exactly the
graph the implementation's `Candidate.graph` builds. -/
@[expose] def RStreettSpec.candGraph (spec : RStreettSpec State L) (r : L → Bool) (C : Std.HashSet State) :
    State → Array State :=
  sccSuccs (spec.regionSuccs r) C

/-- The marks an option must have witnessed inside `M` before the pass recurses on it: for each `g`, an
internal pair of `M` with a realization satisfying the candidate's region, the option's region **and** `g`
at once. Conjoining `r` is what lets the implementation find the witness among the edges it actually
scanned — those of the restricted graph. -/
@[expose] def RStreettSpec.OptMarksIn (spec : RStreettSpec State L) (r : L → Bool)
    (opt : StreettOption L) (M : Std.HashSet State) : Prop :=
  ∀ g ∈ opt.marks, ∃ s ∈ M, ∃ t ∈ M,
    t ∈ spec.regionSuccs (fun l => r l && opt.region l && g l) s

/-- The check's refusal of a candidate. `pick M` is the conjunct the pass blames for `M` and `com` the options
already committed to. Nothing is required of an `M` that misses a property mark, nor of one where a committed
option of `pick M` has a mark not witnessed. Otherwise every option of `pick M` whose marks are witnessed is
refuted with its region conjoined and itself committed. -/
inductive RRefuted (spec : RStreettSpec State L) :
    List (StreettOption L) → (L → Bool) → Std.HashSet State → Prop where
  | pass {com : List (StreettOption L)} {r : L → Bool} {C : Std.HashSet State}
      (sccs : List (Std.HashSet State))
      (pick : Std.HashSet State → Array (StreettOption L))
      (henum : SCCEnumerationSound C.toList (spec.candGraph r C) sccs)
      (hpick : ∀ M ∈ sccs,
        AcceptingMarks (spec.candGraph r C) (spec.regionMarks r) spec.numMarks M →
          pick M ∈ spec.conjuncts)
      (hrec : ∀ M ∈ sccs,
        AcceptingMarks (spec.candGraph r C) (spec.regionMarks r) spec.numMarks M →
        (∀ o ∈ com, o ∈ pick M → spec.OptMarksIn r o M) →
        ∀ opt ∈ pick M, spec.OptMarksIn r opt M →
          RRefuted spec (opt :: com) (fun l => r l && opt.region l) M) :
      RRefuted spec com r C

omit [LawfulHashable State] in
/-- A refusal depends only on the members of the candidate. -/
theorem RRefuted.congr {spec : RStreettSpec State L} {com : List (StreettOption L)} {r : L → Bool}
    {C C' : Std.HashSet State}
    (h : RRefuted spec com r C) (hmem : ∀ s, s ∈ C ↔ s ∈ C') : RRefuted spec com r C' := by
  cases h with
  | pass sccs pick henum hpick hrec =>
    rw [RStreettSpec.candGraph, sccSuccs_congr hmem, ← RStreettSpec.candGraph] at henum hpick hrec
    exact .pass sccs pick
      (henum.congr_init fun s => by simpa only [Std.HashSet.mem_toList] using hmem s) hpick hrec

omit [LawfulHashable State] in
/-- An empty candidate is refuted, since it has no SCC to report. -/
theorem RRefuted.of_empty {spec : RStreettSpec State L} {com : List (StreettOption L)} {r : L → Bool}
    {C : Std.HashSet State}
    (h : ∀ s, s ∉ C) : RRefuted spec com r C := by
  refine .pass [] (fun _ => #[]) ⟨by simp, by simp, fun D ⟨s, hs⟩ _ hreach => ?_⟩ (by simp) (by simp)
  exact absurd (mem_of_reachable_sccSuccs (hreach s hs)) (h s)

omit [LawfulBEq State] [LawfulHashable State] in
/-- A refusal stays one when more options count as committed: the guard on the committed options only gets
harder to meet. -/
theorem RRefuted.mono {spec : RStreettSpec State L} {com : List (StreettOption L)} {r : L → Bool}
    {C : Std.HashSet State} (h : RRefuted spec com r C) :
    ∀ {com' : List (StreettOption L)}, (∀ o ∈ com, o ∈ com') → RRefuted spec com' r C := by
  induction h with
  | pass sccs pick henum hpick hrec ih =>
    intro com' hsub
    refine .pass sccs pick henum hpick fun M hM hA hcom' opt hopt hpres => ?_
    exact ih M hM hA (fun o ho hoM => hcom' o (hsub o ho) hoM) opt hopt hpres
      (fun o ho => by
        rcases List.mem_cons.mp ho with rfl | ho'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub o ho'))

/-! ## Correctness -/

variable {spec : RStreettSpec State L} {succs : State → Array State}
  {edgeMarks : State → State → Std.HashSet Nat}

omit [LawfulBEq State] [LawfulHashable State] in
/-- A selection available on `B` is available on `B` read inside a candidate: the SCC is connected in, and
covers its marks in, the candidate's own graph. The selection's region entails the candidate's, so every
edge the selection admits is one the candidate keeps. -/
private theorem available_in_candGraph (hcompat : spec.Compat succs edgeMarks)
    {sel : List (StreettOption L)} {r : L → Bool} (hle : LePred (selRegion sel) r)
    {B C : Std.HashSet State} (hB : ∀ s ∈ B, s ∈ C) (hav : spec.AvailableWith sel B) :
    InternallyConnected (spec.candGraph r C) B ∧
      AcceptingMarks (spec.candGraph r C) (spec.regionMarks r) spec.numMarks B := by
  have hg : ∀ a b, b ∈ spec.regionSuccs (selRegion sel) a → b ∈ spec.regionSuccs r a :=
    fun a b hb => hcompat.succs_mono hle a b hb
  exact ⟨hav.connected.restrict hg hB,
    (hav.covers.mono_marks fun s t m hm => hcompat.marks_mono hle s t m hm).restrict hg hB⟩

omit [LawfulHashable State] in
/-- A refuted candidate holds no fair SCC whose selection is narrower than the candidate's region and contains
every committed option, [SLDP09]'s prune read through [EL87]'s argument.

The selection travels with the induction: with step regions, availability does not compose across
conjuncts (`StreettSCCRegion.lean`), so the fair SCC's own selection is what has to entail the region at
every level of the recursion. Containing the committed options is what makes the guard of `RRefuted.pass`
hold: each of them is available on the fair SCC, so its marks are witnessed. -/
theorem RRefuted.no_fairSCC (hcompat : spec.Compat succs edgeMarks) {com : List (StreettOption L)}
    {r : L → Bool} {C : Std.HashSet State} (h : RRefuted spec com r C) :
    ∀ {sel : List (StreettOption L)}, (∀ c ∈ spec.conjuncts, ∃ opt ∈ sel, opt ∈ c) →
      (∀ o ∈ com, o ∈ sel) →
      LePred (selRegion sel) r → ∀ {B : Std.HashSet State}, (∀ s ∈ B, s ∈ C) → (∃ s, s ∈ B) →
      spec.AvailableWith sel B → False := by
  induction h with
  | @pass com r C sccs pick henum hpick hrec ih =>
    intro sel hsel hcom hle B hB hne hav
    obtain ⟨hconn, hcov⟩ := available_in_candGraph hcompat hle hB hav
    -- the fair SCC lies inside one enumerated maximal SCC, which inherits its marks
    obtain ⟨M, hM, hsub⟩ := henum.2.2 B hne hconn
      fun s hs => .base (by simpa using hB s hs)
    have hAM := hcov.mono hsub
    -- an option of the selection has its marks witnessed in `M`, read jointly with `r` and its own region
    have hpresOf : ∀ o ∈ sel, spec.OptMarksIn r o M := by
      intro o hoSel g hg
      have hoR : LePred (selRegion sel) o.region := selRegion_le hoSel
      obtain ⟨s, hs, t, ht, hst⟩ := hav.optMarks o hoSel g hg
      refine ⟨s, hsub s hs, t, hsub t ht, hcompat.succs_mono (fun l hl => ?_) s t hst⟩
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hl
      exact Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨hle l h1, hoR l h1⟩, h2⟩
    obtain ⟨opt, hoptSel, hoptC⟩ := hsel (pick M) (hpick M hM hAM)
    have hoptR : LePred (selRegion sel) opt.region := selRegion_le hoptSel
    exact ih M hM hAM (fun o ho _ => hpresOf o (hcom o ho)) opt hoptC (hpresOf opt hoptSel) hsel
      (fun o ho => by
        rcases List.mem_cons.mp ho with rfl | ho'
        · exact hoptSel
        · exact hcom o ho')
      (fun l hl => Bool.and_eq_true _ _ |>.mpr ⟨hle l hl, hoptR l hl⟩) hsub hne hav

/-! ## The first pass -/

/-- The same refusal for the search's first pass, which runs on the whole graph at the top region rather
than on a candidate. -/
@[expose] def RRefutedFrom (spec : RStreettSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) : Prop :=
  ∃ (sccs : List (Std.HashSet State)) (pick : Std.HashSet State → Array (StreettOption L)),
    SCCEnumerationSound initialStates succs sccs ∧
    (∀ M ∈ sccs, AcceptingMarks succs edgeMarks spec.numMarks M → pick M ∈ spec.conjuncts) ∧
    ∀ M ∈ sccs, AcceptingMarks succs edgeMarks spec.numMarks M → ∀ opt ∈ pick M,
      (∀ g ∈ opt.marks, ∃ s ∈ M, ∃ t ∈ M,
        t ∈ spec.regionSuccs (fun l => opt.region l && g l) s) →
      RRefuted spec [opt] opt.region M

omit [LawfulHashable State] in
/-- The whole check misses no fair SCC of the whole graph. -/
theorem RRefutedFrom.no_fairSCC (hcompat : spec.Compat succs edgeMarks) {initialStates : List State}
    (h : RRefutedFrom spec succs edgeMarks initialStates)
    (A : RFairSCC initialStates succs spec) : False := by
  obtain ⟨sccs, pick, henum, hpick, hrec⟩ := h
  obtain ⟨sel, hsel, hav⟩ := A.fair
  -- read the SCC in the ambient graph, which is the top region
  have hconn : InternallyConnected succs A.scc :=
    hav.connected.mono_graph fun a b hb => hcompat.succs_sub _ a b hb
  have hcov : AcceptingMarks succs edgeMarks spec.numMarks A.scc :=
    (hav.covers.mono_graph fun a b hb => hcompat.succs_sub _ a b hb).mono_marks
      fun s t m hm => hcompat.marks_sub _ s t m hm
  obtain ⟨M, hM, hsub⟩ := henum.2.2 A.scc A.nonempty hconn A.reachable
  have hAM := hcov.mono hsub
  obtain ⟨opt, hoptSel, hoptC⟩ := hsel (pick M) (hpick M hM hAM)
  have hoptR : LePred (selRegion sel) opt.region := selRegion_le hoptSel
  have hpres : ∀ g ∈ opt.marks, ∃ s ∈ M, ∃ t ∈ M,
      t ∈ spec.regionSuccs (fun l => opt.region l && g l) s := by
    intro g hg
    obtain ⟨s, hs, t, ht, hst⟩ := hav.optMarks opt hoptSel g hg
    refine ⟨s, hsub s hs, t, hsub t ht, hcompat.succs_mono (fun l hl => ?_) s t hst⟩
    obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hl
    exact Bool.and_eq_true _ _ |>.mpr ⟨hoptR l h1, h2⟩
  exact (hrec M hM hAM opt hoptC hpres).no_fairSCC hcompat hsel
    (fun o ho => by rw [List.mem_singleton.mp ho]; exact hoptSel) hoptR hsub A.nonempty hav

end LTLLib
