/-
  The recursive fairness check of [SLDP09] as a specification, and the Emerson-Lei argument that it misses
  nothing.

  `Refuted C` is a derivation that the check found no fair SCC inside the candidate `C`. One step enumerates
  `C`'s maximal SCCs and, for each one that covers the property marks, names a conjunct and requires every
  option of it whose marks are present in the SCC to be refuted on that option's pruned candidate. Reporting a
  fair SCC is the absence of such a derivation, so a derivation is a refusal.

  What makes the recursion sound is that a fair SCC survives every prune step. It lies inside one of the
  maximal SCCs, which therefore covers the property marks, and it satisfies the named conjunct through one of
  its own options, whose marks are then present in the enclosing SCC and whose region holds everywhere on it.
  So it lies inside that option's pruned candidate, and the derivation's own well-foundedness closes the
  argument, no separate measure needed.

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
  - `Refuted`: the check's refusal of a candidate, one constructor per pass
  - `RefutedFrom`: the same for the first pass, which runs on the whole graph

  Proves:
  - `Refuted.no_fairSCC`, `RefutedFrom.no_fairSCC`: a refuted candidate holds no `FairSCC`
  - `Refuted.congr`, `Refuted.of_empty`: a refusal depends only on the candidate's members, and an empty
    candidate is refused

  References:
  - [SLDP09] Sun, Liu, Dong, Pang. PAT: Towards Flexible Verification under Fairness. CAV 2009.
  - [EL87] Emerson, Lei. Efficient model checking in fragments of the propositional mu-calculus. LICS 1986.
  - [LSFZ16] Li, Song, Feng, Zhang. Verify LTL with Fairness Assumptions Efficiently. arXiv:1606.08116, 2016.

  Sections:
  - Refutation
  - Correctness
  - The first pass
-/
import LTLLib.TGBABased.AbstractSpec.StreettSCC

namespace LTLLib

variable {State : Type u} {L : Type w} [BEq State] [Hashable State] [LawfulBEq State]
  [LawfulHashable State]

/-! ## Refutation -/

/-- The check's refusal of a candidate. `pick M` is the conjunct the pass blames for `M`, which the
implementation takes to be the first one with no available option, and the recursion is required only of the
options whose marks are present, since an option missing a mark in `M` misses it in every subgraph too.

Nothing is required of an `M` that misses a property mark, which is the discard branch, and an `M` that passes
admits no derivation at all, which is the report. -/
inductive Refuted (spec : StreettSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) : Std.HashSet State → Prop where
  | pass {C : Std.HashSet State} (sccs : List (Std.HashSet State))
      (pick : Std.HashSet State → Array (StreettOption L))
      (henum : SCCEnumerationSound C.toList (sccSuccs succs C) sccs)
      (hpick : ∀ M ∈ sccs, AcceptingMarks (sccSuccs succs C) edgeMarks spec.numMarks M →
        pick M ∈ spec.conjuncts)
      (hrec : ∀ M ∈ sccs, AcceptingMarks (sccSuccs succs C) edgeMarks spec.numMarks M →
        ∀ opt ∈ pick M, opt.marksPresent spec.label M →
          Refuted spec succs edgeMarks (opt.prune spec.label M)) :
      Refuted spec succs edgeMarks C

/-- A refusal depends only on the members of the candidate. -/
theorem Refuted.congr {spec : StreettSpec State L} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {C C' : Std.HashSet State}
    (h : Refuted spec succs edgeMarks C) (hmem : ∀ s, s ∈ C ↔ s ∈ C') : Refuted spec succs edgeMarks C' := by
  cases h with
  | pass sccs pick henum hpick hrec =>
    rw [sccSuccs_congr hmem] at henum hpick hrec
    exact .pass sccs pick (henum.congr_init fun s => by simpa only [Std.HashSet.mem_toList] using hmem s)
      hpick hrec

/-- An empty candidate is refuted, since it has no SCC to report. -/
theorem Refuted.of_empty {spec : StreettSpec State L} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {C : Std.HashSet State} (h : ∀ s, s ∉ C) :
    Refuted spec succs edgeMarks C := by
  refine .pass [] (fun _ => #[]) ⟨by simp, by simp, fun D ⟨s, hs⟩ _ hreach => ?_⟩ (by simp) (by simp)
  exact absurd (mem_of_reachable_sccSuccs (hreach s hs)) (h s)

/-! ## Correctness -/

/-- One pass, with the recursion's conclusion supplied rather than derived. A fair SCC of the graph the pass
ran on lies inside one of the enumerated SCCs, which therefore covers the property marks, and it satisfies the
blamed conjunct through an option of its own, so it survives into that option's pruned candidate. `g` is the
graph the pass ran on, which only has to admit ambient edges. -/
private theorem pass_no_fairSCC {spec : StreettSpec State L} {succs g : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    {sccs : List (Std.HashSet State)} {pick : Std.HashSet State → Array (StreettOption L)}
    (hg : ∀ a b, b ∈ g a → b ∈ succs a) (henum : SCCEnumerationSound initialStates g sccs)
    (hpick : ∀ M ∈ sccs, AcceptingMarks g edgeMarks spec.numMarks M → pick M ∈ spec.conjuncts)
    (hrec : ∀ M ∈ sccs, AcceptingMarks g edgeMarks spec.numMarks M → ∀ opt ∈ pick M,
      opt.marksPresent spec.label M →
        ∀ _A : FairSCC (opt.prune spec.label M).toList (sccSuccs succs (opt.prune spec.label M))
          edgeMarks spec, False)
    (A : FairSCC initialStates g edgeMarks spec) : False := by
  obtain ⟨M, hM, hAM⟩ := henum.2.2 A.scc A.nonempty A.connected A.reachable
  have hmarks := A.covers.mono hAM
  obtain ⟨opt, hopt, hregion, hpresent⟩ := A.fair (pick M) (hpick M hM hmarks)
  exact hrec M hM hmarks opt hopt (marksPresent_mono hAM hpresent)
    (A.restrict hg fun s hs => StreettOption.mem_prune.mpr ⟨hAM s hs, hregion s hs⟩)

/-- A refuted candidate holds no fair SCC, which is [SLDP09]'s prune read through [EL87]'s argument. The
derivation's own well-foundedness is the termination argument, so no measure on the candidate is needed. -/
theorem Refuted.no_fairSCC {spec : StreettSpec State L} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {C : Std.HashSet State}
    (h : Refuted spec succs edgeMarks C) :
    ∀ _A : FairSCC C.toList (sccSuccs succs C) edgeMarks spec, False := by
  induction h with
  | pass sccs pick henum hpick _ ih =>
    exact pass_no_fairSCC (fun _ _ hb => (Array.mem_filter.mp hb).1) henum hpick ih

/-! ## The first pass -/

/-- The same refusal for the search's first pass, which runs on the whole graph rather than on a candidate. -/
def RefutedFrom (spec : StreettSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (initialStates : List State) : Prop :=
  ∃ (sccs : List (Std.HashSet State)) (pick : Std.HashSet State → Array (StreettOption L)),
    SCCEnumerationSound initialStates succs sccs ∧
    (∀ M ∈ sccs, AcceptingMarks succs edgeMarks spec.numMarks M → pick M ∈ spec.conjuncts) ∧
    ∀ M ∈ sccs, AcceptingMarks succs edgeMarks spec.numMarks M → ∀ opt ∈ pick M,
      opt.marksPresent spec.label M → Refuted spec succs edgeMarks (opt.prune spec.label M)

/-- The whole check misses no fair SCC of the whole graph. -/
theorem RefutedFrom.no_fairSCC {spec : StreettSpec State L} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    (h : RefutedFrom spec succs edgeMarks initialStates)
    (A : FairSCC initialStates succs edgeMarks spec) : False := by
  obtain ⟨sccs, pick, henum, hpick, hrec⟩ := h
  exact pass_no_fairSCC (fun _ _ hb => hb) henum hpick
    (fun M hM hm opt ho hp => (hrec M hM hm opt ho hp).no_fairSCC) A

end LTLLib
