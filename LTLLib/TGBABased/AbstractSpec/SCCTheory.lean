/-
  Accepting-SCC sufficiency for transition-based acceptance: a `TAcceptingCycle` exists iff some reachable, internally
  strongly connected subset covers every acceptance mark on its internal edges. `AcceptingMarks` follows [RDKP13] §2, an
  SCC is accepting iff the union of marks over its internal edges `(S×S)∩δ` equals `F`. `InternallyConnected` requires
  the connecting paths to stay inside the set. This is stronger than mutual reachability but equal to it for maximal
  SCCs, and the subsets here need not be maximal, since the algorithms can exit early.

  Defines:
  - `AcceptingMarks`, `InternallyConnected`, `AcceptingSCC`
  - `SCCEnumerationSound`: the contract an SCC enumeration owes a prune-based check

  Proves:
  - `acceptingSCC_iff_acceptingCycle`: a reachable accepting SCC exists iff a `TAcceptingCycle` does
  - `chain_glue`, `chain_covers_persist`, `mark_pos_dropLast`: general chain-gluing and mark-position lemmas
  - `InternallyConnected.chain_merge`: a forward-chained run of internally connected ranges, closed by one back-edge
    from the last range to the first, merges into a single internally connected union
  - `AcceptingMarks.mono`, `InternallyConnected.restrict`, `AcceptingMarks.restrict`: an SCC keeps its properties when
    the candidate it sits in changes
  - `sccSuccs_congr`, `InternallyConnected.congr`: both depend only on the members of the set
  - `InternallyConnected.exists_succ`: with one internal edge, every member has a successor inside the set
  - `InternallyConnected.mono_graph`, `AcceptingMarks.mono_graph`: both survive adding edges to the graph
  - `SCCEnumerationSound.congr_init`: an enumeration depends only on the members of the initial list

  References:
  - [RDKP13] Renault, Duret-Lutz, Kordon, Poitrenaud. Three SCC-based Emptiness Checks for Generalized Büchi
    Automata. LPAR-19, 2013.

  Sections:
  - Accepting SCC
  - SCC to cycle
  - Cycle to SCC
  - Sufficiency
-/
import LTLLib.TGBABased.AbstractSpec.EmptinessCheck
import LTLLib.AbstractSpec.GraphPaths

namespace LTLLib

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-! ## Accepting SCC -/

/-- The `succs` graph restricted to `scc`. -/
def sccSuccs (succs : State → Array State) (scc : Std.HashSet State) : State → Array State :=
  fun s => (succs s).filter scc.contains

/-- Marks on `scc`'s internal edges (`(S×S)∩δ`, [RDKP13] §2) cover every mark `< numMarks`, and `scc` has at least
one internal edge, so a trivial SCC without a self-loop cannot vacuously satisfy `numMarks = 0`. -/
def AcceptingMarks (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (numMarks : Nat) (scc : Std.HashSet State) : Prop :=
  (∃ s ∈ scc, ∃ t ∈ scc, t ∈ succs s) ∧
  ∀ m, m < numMarks → ∃ s ∈ scc, ∃ t ∈ scc, t ∈ succs s ∧ m ∈ edgeMarks s t

omit [LawfulBEq State] in
/-- `AcceptingMarks` transports to the `scc`-filtered `sccSuccs`. -/
theorem AcceptingMarks.sccSuccs {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat}
    {numMarks : Nat} {scc : Std.HashSet State} (h : AcceptingMarks succs edgeMarks numMarks scc) :
    AcceptingMarks (LTLLib.sccSuccs succs scc) edgeMarks numMarks scc := by
  obtain ⟨⟨s, hs, t, ht, hedge⟩, hcov⟩ := h
  refine ⟨⟨s, hs, t, ht, Array.mem_filter.mpr ⟨hedge, ht⟩⟩, fun m hm => ?_⟩
  obtain ⟨s, hs, t, ht, hedge, hmark⟩ := hcov m hm
  exact ⟨s, hs, t, ht, Array.mem_filter.mpr ⟨hedge, ht⟩, hmark⟩

omit [LawfulBEq State] in
/-- Marks covered on a subset's internal edges are covered on the whole set's. -/
theorem AcceptingMarks.mono {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat}
    {numMarks : Nat} {scc scc' : Std.HashSet State} (hsub : ∀ s ∈ scc, s ∈ scc')
    (h : AcceptingMarks succs edgeMarks numMarks scc) :
    AcceptingMarks succs edgeMarks numMarks scc' := by
  obtain ⟨⟨s, hs, t, ht, hedge⟩, hcov⟩ := h
  refine ⟨⟨s, hsub s hs, t, hsub t ht, hedge⟩, fun m hm => ?_⟩
  obtain ⟨s, hs, t, ht, hedge, hmark⟩ := hcov m hm
  exact ⟨s, hsub s hs, t, hsub t ht, hedge, hmark⟩

/-- Any two members of `scc` are connected by a path staying entirely inside `scc`. -/
def InternallyConnected (succs : State → Array State) (scc : Std.HashSet State) : Prop :=
  ∀ s ∈ scc, ∀ t ∈ scc, s = t ∨ PathTo (sccSuccs succs scc) (fun _ => False) s t

omit [LawfulBEq State] in
/-- `InternallyConnected`'s paths also hold in the domain-blocked form, every state outside `scc` blocked. -/
theorem InternallyConnected.domainBlocked {succs : State → Array State} {scc : Std.HashSet State}
    (h : InternallyConnected succs scc) :
    ∀ s, scc.contains s → ∀ t, scc.contains t →
      s = t ∨ PathTo (sccSuccs succs scc) (fun x => ¬ scc.contains x) s t :=
  fun s hs t ht => (h s hs t ht).imp id fun hp =>
    hp.confine (P := fun x => scc.contains x) fun {_ _} hab => (Array.mem_filter.mp hab).2

omit [LawfulBEq State] in
/-- A path between two members of a set whose edges only ever leave it for a sink it cannot come back from
stays inside the set. -/
theorem pathTo_within {succs : State → Array State} {scc sink : Std.HashSet State}
    (hout : ∀ x ∈ scc, ∀ y ∈ succs x, y ∈ scc ∨ y ∈ sink)
    (hsink : ∀ x ∈ sink, ∀ y ∈ succs x, y ∈ sink) (hdisj : ∀ x ∈ scc, x ∉ sink) {s t : State}
    (h : PathTo succs (fun _ => False) s t) :
    s ∈ scc → t ∈ scc → PathTo (sccSuccs succs scc) (fun _ => False) s t := by
  induction h with
  | @direct a b hab =>
    intro _ hb
    exact .direct (by
      simp only [sccSuccs]
      exact Array.mem_filter.mpr ⟨hab, Std.HashSet.mem_iff_contains.mp hb⟩)
  | @through a mid b hmid _ hpath ih =>
    intro ha hb
    have hmidS : mid ∈ scc := by
      rcases hout a ha mid hmid with hm | hm
      · exact hm
      · exact absurd (hpath.closed hm hsink) (hdisj b hb)
    exact .through (by
      simp only [sccSuccs]
      exact Array.mem_filter.mpr ⟨hmid, Std.HashSet.mem_iff_contains.mp hmidS⟩)
      (fun hx => hx) (ih hmidS hb)

omit [LawfulBEq State] in
/-- `sccSuccs` widens monotonically with `scc` itself. -/
theorem sccSuccs_mono {succs : State → Array State} {scc1 scc2 : Std.HashSet State}
    (hsub : ∀ x, x ∈ scc1 → x ∈ scc2) {a b : State} (hb : b ∈ sccSuccs succs scc1 a) :
    b ∈ sccSuccs succs scc2 a := by
  unfold sccSuccs at hb ⊢
  obtain ⟨hbsucc, hbcontains⟩ := Array.mem_filter.mp hb
  exact Array.mem_filter.mpr ⟨hbsucc, Std.HashSet.mem_iff_contains.mp (hsub b (Std.HashSet.mem_iff_contains.mpr hbcontains))⟩

omit [LawfulBEq State] in
/-- Sets with the same members restrict `succs` identically. -/
theorem sccSuccs_congr {succs : State → Array State} {scc1 scc2 : Std.HashSet State}
    (h : ∀ x, x ∈ scc1 ↔ x ∈ scc2) : sccSuccs succs scc1 = sccSuccs succs scc2 := by
  have hc : scc1.contains = scc2.contains :=
    funext fun x => Bool.eq_iff_iff.mpr (by simpa only [Std.HashSet.mem_iff_contains] using h x)
  unfold sccSuccs
  rw [hc]

omit [LawfulBEq State] in
/-- `InternallyConnected` depends only on the members of the set. -/
theorem InternallyConnected.congr {succs : State → Array State} {scc1 scc2 : Std.HashSet State}
    (h : InternallyConnected succs scc1) (hmem : ∀ x, x ∈ scc1 ↔ x ∈ scc2) :
    InternallyConnected succs scc2 := by
  intro s hs t ht
  rw [← sccSuccs_congr hmem]
  exact h s ((hmem s).mpr hs) t ((hmem t).mpr ht)

omit [LawfulBEq State] in
/-- In an internally connected set with an internal edge, every member has a successor inside the set. -/
theorem InternallyConnected.exists_succ {succs : State → Array State} {scc : Std.HashSet State}
    (h : InternallyConnected succs scc) (hedge : ∃ s ∈ scc, ∃ t ∈ scc, t ∈ succs s) :
    ∀ u ∈ scc, ∃ t ∈ scc, t ∈ succs u := by
  obtain ⟨s, hs, t, ht, hst⟩ := hedge
  intro u hu
  rcases h u hu s hs with rfl | hp
  · exact ⟨t, ht, hst⟩
  · have hfirst : ∃ v, v ∈ sccSuccs succs scc u := by
      cases hp with
      | direct hv => exact ⟨_, hv⟩
      | through hv _ _ => exact ⟨_, hv⟩
    obtain ⟨v, hv⟩ := hfirst
    obtain ⟨hv1, hv2⟩ := Array.mem_filter.mp hv
    exact ⟨v, Std.HashSet.mem_iff_contains.mpr hv2, hv1⟩

omit [LawfulBEq State] in
/-- Connectivity inside a set survives adding edges to the graph. -/
theorem InternallyConnected.mono_graph {g succs : State → Array State} {scc : Std.HashSet State}
    (hg : ∀ a b, b ∈ g a → b ∈ succs a) (h : InternallyConnected g scc) : InternallyConnected succs scc :=
  fun s hs t ht => (h s hs t ht).imp id fun hp => hp.mono_succs fun a b hb => by
    obtain ⟨hb1, hb2⟩ := Array.mem_filter.mp hb
    exact Array.mem_filter.mpr ⟨hg a b hb1, hb2⟩

omit [LawfulBEq State] in
/-- The same for the marks on a set's internal edges. -/
theorem AcceptingMarks.mono_graph {g succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} {scc : Std.HashSet State}
    (hg : ∀ a b, b ∈ g a → b ∈ succs a) (h : AcceptingMarks g edgeMarks numMarks scc) :
    AcceptingMarks succs edgeMarks numMarks scc := by
  obtain ⟨⟨s, hs, t, ht, hedge⟩, hcov⟩ := h
  refine ⟨⟨s, hs, t, ht, hg _ _ hedge⟩, fun m hm => ?_⟩
  obtain ⟨s, hs, t, ht, hedge, hmark⟩ := hcov m hm
  exact ⟨s, hs, t, ht, hg _ _ hedge, hmark⟩

omit [LawfulBEq State] in
private theorem chain_forward {succs : State → Array State} {rng : Nat → Std.HashSet State}
    {big : Std.HashSet State} {lo hi : Nat}
    (hmem : ∀ i, lo ≤ i → i ≤ hi → ∀ x ∈ rng i, x ∈ big)
    (hconn : ∀ i, lo ≤ i → i ≤ hi → InternallyConnected succs (rng i))
    (hchain : ∀ i, lo ≤ i → i < hi → ∃ s ∈ rng i, ∃ t ∈ rng (i + 1), t ∈ succs s) :
    ∀ i, lo ≤ i → i ≤ hi → ∀ j, i ≤ j → j ≤ hi → ∀ s ∈ rng i, ∀ t ∈ rng j,
      s = t ∨ PathTo (sccSuccs succs big) (fun _ => False) s t := by
  intro i hloi hihi j hij
  induction j, hij using Nat.le_induction with
  | base =>
    intro _ s hs t ht
    rcases hconn i hloi hihi s hs t ht with heq | hp
    · exact Or.inl heq
    · exact Or.inr (hp.mono_succs fun a b hab => sccSuccs_mono (hmem i hloi hihi) hab)
  | succ j hij ih =>
    intro hjhi1 s hs t ht
    have hjhi : j ≤ hi := by omega
    obtain ⟨s', hs', t', ht', hedge⟩ := hchain j (hloi.trans hij) (by omega)
    have hmidedge : t' ∈ sccSuccs succs big s' := by
      unfold sccSuccs
      exact Array.mem_filter.mpr ⟨hedge, Std.HashSet.mem_iff_contains.mp (hmem (j + 1) (by omega) hjhi1 t' ht')⟩
    have hstep3 : t' = t ∨ PathTo (sccSuccs succs big) (fun _ => False) t' t := by
      rcases hconn (j + 1) (by omega) hjhi1 t' ht' t ht with heq | hp
      · exact Or.inl heq
      · exact Or.inr (hp.mono_succs fun a b hab => sccSuccs_mono (hmem (j + 1) (by omega) hjhi1) hab)
    rcases ih hjhi s hs s' hs' with heq1 | hp1
    · subst heq1
      rcases hstep3 with heq3 | hp3
      · exact Or.inr (heq3 ▸ .direct hmidedge)
      · exact Or.inr (.through hmidedge (fun h => h) hp3)
    · rcases hstep3 with heq3 | hp3
      · exact Or.inr (heq3 ▸ hp1.trans (.direct hmidedge))
      · exact Or.inr (hp1.trans (.through hmidedge (fun h => h) hp3))

omit [LawfulBEq State] in
/-- A forward-chained run of internally-connected ranges, closed by one back-edge from the last to the first,
merges into a single internally-connected union. -/
theorem InternallyConnected.chain_merge {succs : State → Array State} {rng : Nat → Std.HashSet State}
    {big : Std.HashSet State} {lo hi : Nat}
    (hmem : ∀ i, lo ≤ i → i ≤ hi → ∀ x ∈ rng i, x ∈ big)
    (hconn : ∀ i, lo ≤ i → i ≤ hi → InternallyConnected succs (rng i))
    (hchain : ∀ i, lo ≤ i → i < hi → ∃ s ∈ rng i, ∃ t ∈ rng (i + 1), t ∈ succs s)
    (hback : ∃ s ∈ rng hi, ∃ t ∈ rng lo, t ∈ succs s) :
    ∀ i, lo ≤ i → i ≤ hi → ∀ j, lo ≤ j → j ≤ hi → ∀ s ∈ rng i, ∀ t ∈ rng j,
      s = t ∨ PathTo (sccSuccs succs big) (fun _ => False) s t := by
  intro i hloi hihi j hloj hjhi s hs t ht
  by_cases hij : i ≤ j
  · exact chain_forward hmem hconn hchain i hloi hihi j hij hjhi s hs t ht
  · -- wrap around: `s` forward to `rng hi`, the back-edge to `rng lo`, then forward again to `t`.
    obtain ⟨s', hs', t', ht', hedge⟩ := hback
    have hstep1 := chain_forward hmem hconn hchain i hloi hihi hi (by omega) (le_refl _) s hs s' hs'
    have hmidedge : t' ∈ sccSuccs succs big s' := by
      unfold sccSuccs
      exact Array.mem_filter.mpr ⟨hedge, Std.HashSet.mem_iff_contains.mp (hmem lo (le_refl _) (hloi.trans hihi) t' ht')⟩
    have hstep3 := chain_forward hmem hconn hchain lo (le_refl _) (hloi.trans hihi) j (by omega) hjhi t' ht' t ht
    rcases hstep1 with heq1 | hp1
    · subst heq1
      rcases hstep3 with heq3 | hp3
      · exact Or.inr (heq3 ▸ .direct hmidedge)
      · exact Or.inr (.through hmidedge (fun h => h) hp3)
    · rcases hstep3 with heq3 | hp3
      · exact Or.inr (heq3 ▸ hp1.trans (.direct hmidedge))
      · exact Or.inr (hp1.trans (.through hmidedge (fun h => h) hp3))

omit [LawfulBEq State] in
/-- An SCC found in a graph that only admits ambient edges is internally connected in every candidate that
contains it. -/
theorem InternallyConnected.restrict {g succs : State → Array State} {D scc : Std.HashSet State}
    (hg : ∀ a b, b ∈ g a → b ∈ succs a) (hD : ∀ s ∈ scc, s ∈ D)
    (h : InternallyConnected g scc) : InternallyConnected (sccSuccs succs D) scc :=
  fun s hs t ht => (h s hs t ht).imp id fun hp => hp.mono_succs fun a b hb => by
    obtain ⟨hb1, hb2⟩ := Array.mem_filter.mp hb
    exact Array.mem_filter.mpr ⟨Array.mem_filter.mpr ⟨hg a b hb1,
      Std.HashSet.mem_iff_contains.mp (hD b (Std.HashSet.mem_iff_contains.mpr hb2))⟩, hb2⟩

omit [LawfulBEq State] in
/-- The same for the marks on those edges. -/
theorem AcceptingMarks.restrict {g succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} {D scc : Std.HashSet State}
    (hg : ∀ a b, b ∈ g a → b ∈ succs a) (hD : ∀ s ∈ scc, s ∈ D)
    (h : AcceptingMarks g edgeMarks numMarks scc) :
    AcceptingMarks (LTLLib.sccSuccs succs D) edgeMarks numMarks scc := by
  obtain ⟨⟨s, hs, t, ht, hedge⟩, hcov⟩ := h
  have hstep : ∀ {a b : State}, b ∈ scc → b ∈ g a → b ∈ LTLLib.sccSuccs succs D a :=
    fun hbscc hb => Array.mem_filter.mpr ⟨hg _ _ hb,
      Std.HashSet.mem_iff_contains.mp (hD _ hbscc)⟩
  refine ⟨⟨s, hs, t, ht, hstep ht hedge⟩, fun m hm => ?_⟩
  obtain ⟨s, hs, t, ht, hedge, hmark⟩ := hcov m hm
  exact ⟨s, hs, t, ht, hstep ht hedge, hmark⟩

/-- A candidate's own graph never leaves the candidate, so everything it reaches is inside it. -/
theorem mem_of_reachable_sccSuccs {succs : State → Array State} {C : Std.HashSet State} {s : State}
    (h : Reachable C.toList (sccSuccs succs C) s) : s ∈ C := by
  induction h with
  | base hi => simpa using hi
  | step _ ht _ => exact Std.HashSet.mem_iff_contains.mpr (Array.mem_filter.mp ht).2

/-- A reachable, internally strongly connected, mark-covering subset, not required to be a maximal SCC. -/
structure AcceptingSCC (initialStates : List State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat) where
  scc : Std.HashSet State
  nonempty : ∃ s, s ∈ scc
  connected : InternallyConnected succs scc
  covers : AcceptingMarks succs edgeMarks numMarks scc
  reachable : ∀ s ∈ scc, Reachable initialStates succs s

omit [LawfulBEq State] in
private theorem connect_toChain {succs : State → Array State} {scc : Std.HashSet State}
    {s t : State} (h : s = t ∨ PathTo (sccSuccs succs scc) (fun _ => False) s t) :
    ∃ l : List State, ∃ hne : l ≠ [], l.head hne = s ∧ l.getLast hne = t ∧
      ∀ i, (hi : i + 1 < l.length) → l[i + 1] ∈ sccSuccs succs scc (l[i]) := by
  rcases h with rfl | hp
  · exact ⟨[s], by simp, rfl, by simp, by simp⟩
  · exact hp.toChain

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- A mark-covering position in `l` is still a mark-covering position after appending anything. -/
theorem chain_covers_persist {edgeMarks : State → State → Std.HashSet Nat}
    (l suffix : List State) {m : Nat}
    (h : ∃ (i : Nat) (hi : i + 1 < l.length), m ∈ edgeMarks (l[i]) (l[i + 1])) :
    ∃ (i : Nat) (hi : i + 1 < (l ++ suffix).length),
      m ∈ edgeMarks ((l ++ suffix)[i]) ((l ++ suffix)[i + 1]) := by
  obtain ⟨i, hi, hm⟩ := h
  refine ⟨i, by simp only [List.length_append]; omega, ?_⟩
  rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
  exact hm

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- Glue two chains sharing an endpoint (`p.head = l.getLast`, not an edge between them) into one chain over `l ++ p.tail`,
dropping the duplicated junction state. -/
theorem chain_glue {succs : State → Array State} (l p : List State)
    (hne : l ≠ []) (hpne : p ≠ [])
    (hlchain : ∀ i, (hi : i + 1 < l.length) → l[i + 1] ∈ succs l[i])
    (hpchain : ∀ i, (hi : i + 1 < p.length) → p[i + 1] ∈ succs p[i])
    (hjunc : p.head hpne = l.getLast hne) :
    ∃ hne' : (l ++ p.tail) ≠ [], (l ++ p.tail).getLast hne' = p.getLast hpne ∧
      ∀ i, (hi : i + 1 < (l ++ p.tail).length) → (l ++ p.tail)[i + 1] ∈ succs (l ++ p.tail)[i] := by
  cases p with
  | nil => exact absurd rfl hpne
  | cons a rest =>
    have ha : a = l.getLast hne := by simpa using hjunc
    subst ha
    cases rest with
    | nil => exact ⟨by simpa using hne, by simp, by simpa using hlchain⟩
    | cons b rest' =>
      have hedge : b ∈ succs (l.getLast hne) := by simpa using hpchain 0 (by simp)
      have hrestchain : ∀ i, (hi : i + 1 < (b :: rest').length) →
          (b :: rest')[i + 1] ∈ succs (b :: rest')[i] := fun i hi => by
        have h := hpchain (i + 1) (by simpa using hi)
        simpa using h
      exact ⟨by simp, by simp [List.getLast_cons],
        chain_append l (b :: rest') hlchain hrestchain hne (by simp) hedge⟩

/-- What an SCC enumeration has to deliver. Every listed set is reachable and internally connected, and every
reachable internally connected set sits inside one of them, which is maximality in the form the prune needs. -/
def SCCEnumerationSound (initialStates : List State) (succs : State → Array State)
    (sccs : List (Std.HashSet State)) : Prop :=
  (∀ C ∈ sccs, ∀ s ∈ C, Reachable initialStates succs s) ∧
  (∀ C ∈ sccs, InternallyConnected succs C) ∧
  ∀ D : Std.HashSet State, (∃ s, s ∈ D) → InternallyConnected succs D →
    (∀ s ∈ D, Reachable initialStates succs s) → ∃ C ∈ sccs, ∀ s ∈ D, s ∈ C

omit [LawfulBEq State] in
/-- An enumeration stays sound when the initial list is replaced by one with the same members. -/
theorem SCCEnumerationSound.congr_init {l l' : List State} {succs : State → Array State}
    {sccs : List (Std.HashSet State)} (hmem : ∀ x, x ∈ l ↔ x ∈ l') (h : SCCEnumerationSound l succs sccs) :
    SCCEnumerationSound l' succs sccs :=
  ⟨fun C hC s hs => (h.1 C hC s hs).mono_init fun x hx => (hmem x).mp hx, h.2.1,
    fun D hD hconn hreach => h.2.2 D hD hconn fun s hs => (hreach s hs).mono_init fun x hx => (hmem x).mpr hx⟩

/-! ## SCC to cycle -/

omit [LawfulBEq State] in
private theorem build_tour {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {scc : Std.HashSet State}
    (hconn : InternallyConnected succs scc) : ∀ (ms : List Nat),
    (∀ m ∈ ms, ∃ s ∈ scc, ∃ t ∈ scc, t ∈ succs s ∧ m ∈ edgeMarks s t) →
    ∀ {l : List State} (hne : l ≠ []), l.getLast hne ∈ scc →
      (∀ i, (hi : i + 1 < l.length) → l[i + 1] ∈ sccSuccs succs scc (l[i])) →
      ∃ l' : List State, ∃ hne' : l' ≠ [], l'.head hne' = l.head hne ∧ l'.getLast hne' ∈ scc ∧
        l.length ≤ l'.length ∧
        (∀ i, (hi : i + 1 < l'.length) → l'[i + 1] ∈ sccSuccs succs scc (l'[i])) ∧
        ∀ m ∈ ms, ∃ (i : Nat) (hi : i + 1 < l'.length), m ∈ edgeMarks (l'[i]) (l'[i + 1]) := by
  intro ms
  induction ms with
  | nil => intro _ l hne hlast hchain; exact ⟨l, hne, rfl, hlast, le_refl _, hchain, by simp⟩
  | cons m rest ih =>
    intro hms l hne hlast hchain
    obtain ⟨l1, hne1, hhead1, hlast1, hlen1, hchain1, hcov1⟩ :=
      ih (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')) hne hlast hchain
    obtain ⟨sm, hsm, tm, htm, hedget, hmark⟩ := hms m List.mem_cons_self
    obtain ⟨p, hpne, hphead, hplast, hpchain⟩ :=
      connect_toChain (hconn (l1.getLast hne1) hlast1 sm hsm)
    obtain ⟨hne2, hlast2, hchain2⟩ := chain_glue l1 p hne1 hpne hchain1 hpchain hphead
    have hlast2' : (l1 ++ p.tail).getLast hne2 = sm := hlast2.trans hplast
    have hlen2pos : (l1 ++ p.tail).length ≥ 1 := List.length_pos_iff.mpr hne2
    have htm_edge : tm ∈ sccSuccs succs scc ((l1 ++ p.tail).getLast hne2) := by
      rw [hlast2']; exact Array.mem_filter.mpr ⟨hedget, htm⟩
    have hchain3 := chain_append_singleton (l1 ++ p.tail) tm hchain2 hne2 htm_edge
    have hlen3 : ((l1 ++ p.tail) ++ [tm]).length = (l1 ++ p.tail).length + 1 := by simp; omega
    have hlen4 : (l1 ++ p.tail).length ≥ l1.length := by simp
    refine ⟨(l1 ++ p.tail) ++ [tm], by simp, ?_, by simpa using htm, by omega, hchain3, ?_⟩
    · simp only [List.append_assoc, List.head_append_of_ne_nil hne1]; exact hhead1
    · intro m' hm'
      rcases List.mem_cons.mp hm' with rfl | hm''
      · refine ⟨(l1 ++ p.tail).length - 1, by omega, ?_⟩
        have e1 : ((l1 ++ p.tail) ++ [tm])[(l1 ++ p.tail).length - 1]'(by omega) =
            (l1 ++ p.tail).getLast hne2 := by
          rw [List.getElem_append_left (by omega), List.getLast_eq_getElem]
        have e2 : ((l1 ++ p.tail) ++ [tm])[(l1 ++ p.tail).length - 1 + 1]'(by omega) = tm := by
          have hlen : (l1 ++ p.tail).length - 1 + 1 = (l1 ++ p.tail).length := by omega
          exact List.getElem_concat_length hlen _
        rw [e1, e2, hlast2']
        exact hmark
      · obtain ⟨i, hi, hcov⟩ := hcov1 m' hm''
        obtain ⟨i', hi', hcov'⟩ := chain_covers_persist l1 (p.tail ++ [tm]) ⟨i, hi, hcov⟩
        have heq3 : (l1 ++ p.tail) ++ [tm] = l1 ++ (p.tail ++ [tm]) := List.append_assoc l1 p.tail [tm]
        have hi'' : i' + 1 < ((l1 ++ p.tail) ++ [tm]).length := by rw [heq3]; exact hi'
        have hcov'' : m' ∈ edgeMarks (((l1 ++ p.tail) ++ [tm])[i']) (((l1 ++ p.tail) ++ [tm])[i' + 1]) := by
          simp only [heq3]; exact hcov'
        exact ⟨i', hi'', hcov''⟩

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- A mark-covering position in a prefix `l1` of `l2 := l1 ++ suffix` transfers to `cycle := l2.dropLast`,
matching `TAcceptingCycle`'s modular wraparound indexing. -/
theorem mark_pos_dropLast {edgeMarks : State → State → Std.HashSet Nat}
    (l1 suffix : List State) (hl1ne : l1 ≠ []) {m : Nat} {i : Nat} (hi : i + 1 < l1.length)
    (hm : m ∈ edgeMarks (l1[i]) (l1[i + 1]))
    (hl2ne : (l1 ++ suffix) ≠ [])
    (hloop : (l1 ++ suffix).getLast hl2ne = (l1 ++ suffix).head hl2ne) :
    ∃ (i : Nat) (hi : i < (l1 ++ suffix).dropLast.length),
      m ∈ edgeMarks ((l1 ++ suffix).dropLast[i])
        ((l1 ++ suffix).dropLast[(i + 1) % (l1 ++ suffix).dropLast.length]'(Nat.mod_lt _ (by
          simp only [List.length_dropLast, List.length_append]; omega))) := by
  have hl2len : (l1 ++ suffix).length = l1.length + suffix.length := List.length_append
  have hdlen : (l1 ++ suffix).dropLast.length = (l1 ++ suffix).length - 1 :=
    List.length_dropLast (xs := l1 ++ suffix)
  have hipos : i < (l1 ++ suffix).dropLast.length := by omega
  refine ⟨i, hipos, ?_⟩
  have hei : (l1 ++ suffix).dropLast[i] = l1[i] := by
    rw [List.getElem_dropLast]
    exact List.getElem_append_left (by omega)
  by_cases hwrap : i + 1 < (l1 ++ suffix).dropLast.length
  · have hidx : (i + 1) % (l1 ++ suffix).dropLast.length = i + 1 := Nat.mod_eq_of_lt hwrap
    have hei1 : (l1 ++ suffix).dropLast[(i + 1) % (l1 ++ suffix).dropLast.length] = l1[i + 1] := by
      simp only [hidx, List.getElem_dropLast]
      exact List.getElem_append_left (by omega)
    rw [hei, hei1]; exact hm
  · have hsuffixnil : suffix = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hdlen1 : (l1 ++ suffix).dropLast.length = l1.dropLast.length := by simp [hsuffixnil]
    have hidx : (i + 1) % (l1 ++ suffix).dropLast.length = 0 := by
      rw [hdlen1]
      have heq2 : i + 1 = l1.dropLast.length := by
        have := List.length_dropLast (xs := l1); omega
      rw [heq2]; simp
    have hne'' : (l1 ++ suffix).dropLast ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hcyclehead : (l1 ++ suffix).dropLast[(i + 1) % (l1 ++ suffix).dropLast.length] =
        (l1 ++ suffix).head hl2ne := by
      simp only [hidx]
      rw [← List.head_eq_getElem hne'']
      exact head_dropLast_eq (l1 ++ suffix) hl2ne hne''
    have hlasteq : (l1 ++ suffix).getLast hl2ne = l1.getLast hl1ne := by simp [hsuffixnil]
    have hei1 : l1[i + 1] = l1.getLast hl1ne := by
      rw [List.getLast_eq_getElem]; congr 1; omega
    have hei2 : (l1 ++ suffix).dropLast[(i + 1) % (l1 ++ suffix).dropLast.length] = l1[i + 1] := by
      rw [hcyclehead, ← hloop, hlasteq, ← hei1]
    rw [hei, hei2]; exact hm

omit [LawfulBEq State] in
/-- Soundness: a reachable accepting SCC gives a `TAcceptingCycle` witness. -/
theorem AcceptingSCC.exists_acceptingCycle {initialStates : List State} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat}
    (A : AcceptingSCC initialStates succs edgeMarks numMarks) :
    ∃ _ac : TAcceptingCycle initialStates succs edgeMarks numMarks, True := by
  obtain ⟨anchor, hanchor⟩ := A.nonempty
  obtain ⟨⟨s0, hs0, t0, ht0, hedge0⟩, hcovers⟩ := A.covers
  obtain ⟨stemL, hstemne, hstemhead, hstemlast, hstemchain⟩ :=
    (A.reachable anchor hanchor).toChain
  obtain ⟨p1, hp1ne, hp1head, hp1last, hp1chain⟩ := connect_toChain (A.connected anchor hanchor s0 hs0)
  have ht0mem : t0 ∈ sccSuccs succs A.scc (p1.getLast hp1ne) := by
    rw [hp1last]; exact Array.mem_filter.mpr ⟨hedge0, ht0⟩
  have hl0chain := chain_append_singleton p1 t0 hp1chain hp1ne ht0mem
  have hl0ne : p1 ++ [t0] ≠ [] := by simp
  have hl0head : (p1 ++ [t0]).head hl0ne = anchor := by
    rw [List.head_append_of_ne_nil hp1ne]; exact hp1head
  have hl0last : (p1 ++ [t0]).getLast hl0ne ∈ A.scc := by simpa using ht0
  have hmarkscov : ∀ m ∈ List.range numMarks, ∃ s ∈ A.scc, ∃ t ∈ A.scc, t ∈ succs s ∧ m ∈ edgeMarks s t :=
    fun m hm => hcovers m (List.mem_range.mp hm)
  obtain ⟨l1, hl1ne, hl1head, hl1last, hl1len, hl1chain, hl1cov⟩ :=
    build_tour A.connected (List.range numMarks) hmarkscov hl0ne hl0last hl0chain
  have hl1head' : l1.head hl1ne = anchor := hl1head.trans hl0head
  have hl1len2 : (p1 ++ [t0]).length ≥ 2 := by
    have : p1.length ≥ 1 := List.length_pos_iff.mpr hp1ne
    simp; omega
  obtain ⟨p2, hp2ne, hp2head, hp2last, hp2chain⟩ :=
    connect_toChain (A.connected (l1.getLast hl1ne) hl1last anchor hanchor)
  obtain ⟨hl2ne, hl2last, hl2chain⟩ := chain_glue l1 p2 hl1ne hp2ne hl1chain hp2chain hp2head
  have hl2last' : (l1 ++ p2.tail).getLast hl2ne = anchor := hl2last.trans hp2last
  have hl2head' : (l1 ++ p2.tail).head hl2ne = anchor := by
    rw [List.head_append_of_ne_nil hl1ne]; exact hl1head'
  have hloop : (l1 ++ p2.tail).getLast hl2ne = (l1 ++ p2.tail).head hl2ne := by
    rw [hl2last', hl2head']
  have hl2chain' : ∀ i, (hi : i + 1 < (l1 ++ p2.tail).length) →
      (l1 ++ p2.tail)[i + 1] ∈ succs ((l1 ++ p2.tail)[i]) := fun i hi =>
    (Array.mem_filter.mp (hl2chain i hi)).1
  have hl2len2 : (l1 ++ p2.tail).length ≥ 2 := by
    have : (l1 ++ p2.tail).length ≥ l1.length := by simp
    omega
  have hcyclene : (l1 ++ p2.tail).dropLast ≠ [] :=
    List.ne_nil_of_length_pos (by rw [List.length_dropLast]; omega)
  have hcyclehead : (l1 ++ p2.tail).dropLast.head hcyclene = anchor :=
    (head_dropLast_eq (l1 ++ p2.tail) hl2ne hcyclene).trans hl2head'
  have hcycleback : (l1 ++ p2.tail).dropLast.head hcyclene ∈
      succs ((l1 ++ p2.tail).dropLast.getLast hcyclene) := by
    rw [hcyclehead, ← hl2last']
    exact chain_getLast_edge (l1 ++ p2.tail) hl2ne hcyclene hl2chain'
  have hcyclechain : ∀ i, (hi : i + 1 < (l1 ++ p2.tail).dropLast.length) →
      (l1 ++ p2.tail).dropLast[i + 1] ∈ succs ((l1 ++ p2.tail).dropLast[i]) := fun i hi =>
    chain_dropLast (l1 ++ p2.tail) hl2chain' i hi
  refine ⟨{
    stem := stemL
    cycle := (l1 ++ p2.tail).dropLast
    stem_nonempty := List.length_pos_iff.mpr hstemne
    cycle_nonempty := List.length_pos_iff.mpr hcyclene
    stem_head_initial := hstemhead
    stem_chain := hstemchain
    overlap := hstemlast.trans hcyclehead.symm
    cycle_chain := hcyclechain
    cycle_back := hcycleback
    cycle_covers_marks := fun m hm => by
      obtain ⟨i, hi, hcov⟩ := hl1cov m (List.mem_range.mpr hm)
      exact mark_pos_dropLast l1 p2.tail hl1ne hi hcov hl2ne hloop
  }, trivial⟩

/-! ## Cycle to SCC -/

omit [BEq State] [Hashable State] [LawfulBEq State] in
private theorem reachable_of_chain {initialStates : List State} {succs : State → Array State}
    (l : List State) (hchain : ∀ i, (hi : i + 1 < l.length) → l[i + 1] ∈ succs l[i]) :
    ∀ {i0 : State}, Reachable initialStates succs i0 → (hne : l ≠ []) → l.head hne = i0 →
      ∀ x ∈ l, Reachable initialStates succs x := by
  induction l with
  | nil => intro i0 hr0 hne; exact absurd rfl hne
  | cons a t ih =>
    intro i0 hr0 hne hheadeq x hx
    have ha : a = i0 := hheadeq
    cases t with
    | nil =>
      simp only [List.mem_singleton] at hx
      rwa [hx, ha]
    | cons b t' =>
      have hab : b ∈ succs a := by simpa using hchain 0 (by simp)
      have hab' : b ∈ succs i0 := ha ▸ hab
      have hrb : Reachable initialStates succs b := Reachable.step hr0 hab'
      rcases List.mem_cons.mp hx with rfl | hx'
      · rwa [ha]
      · have hchain_tail : ∀ i, (hi : i + 1 < (b :: t').length) →
            (b :: t')[i + 1] ∈ succs (b :: t')[i] := by
          intro i hi; have h1 := hchain (i + 1) (by simpa using hi); simpa using h1
        exact ih hchain_tail hrb (by simp) rfl x hx'

variable {succs : State → Array State} {scc : Std.HashSet State}

omit [LawfulBEq State] in
private theorem chain_reaches_restricted (l : List State)
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i + 1] ∈ succs l[i]) (hmem : ∀ x ∈ l, x ∈ scc) :
    ∀ (hne : l ≠ []), l.head hne = l.getLast hne ∨
      PathTo (sccSuccs succs scc) (fun _ => False) (l.head hne) (l.getLast hne) := by
  induction l with
  | nil => intro hne; exact absurd rfl hne
  | cons a t ih =>
    intro _
    cases t with
    | nil => left; rfl
    | cons b t' =>
      right
      have hab : b ∈ sccSuccs succs scc a := by
        have h0 := hchain 0 (by simp)
        exact Array.mem_filter.mpr ⟨by simpa using h0, hmem b (by simp)⟩
      have hchain_tail : ∀ i, (hi : i + 1 < (b :: t').length) →
          (b :: t')[i + 1] ∈ succs (b :: t')[i] := by
        intro i hi
        have h1 := hchain (i + 1) (by simpa using hi)
        simpa using h1
      have hmem_tail : ∀ x ∈ (b :: t'), x ∈ scc := fun x hx => hmem x (by simp [hx])
      have hhead : (a :: b :: t').head (by simp) = a := rfl
      have hgetlast : (a :: b :: t').getLast (by simp) = (b :: t').getLast (by simp) :=
        List.getLast_cons (by simp)
      rw [hhead, hgetlast]
      rcases ih hchain_tail hmem_tail (by simp) with heq | hp
      · exact heq ▸ PathTo.direct hab
      · exact PathTo.trans (PathTo.direct hab) hp

variable [LawfulHashable State]

/-- Completeness: the states of any `TAcceptingCycle` form a reachable accepting SCC. -/
theorem TAcceptingCycle.exists_acceptingSCC {initialStates : List State} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat}
    (ac : TAcceptingCycle initialStates succs edgeMarks numMarks) :
    ∃ A : AcceptingSCC initialStates succs edgeMarks numMarks, ∀ s, s ∈ A.scc ↔ s ∈ ac.cycle := by
  have hcyclen : ac.cycle.length ≥ 1 := ac.cycle_nonempty
  have hstemlen : ac.stem.length ≥ 1 := ac.stem_nonempty
  have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos (by omega)
  set scc := Std.HashSet.ofList ac.cycle with hsccdef
  have hmemscc : ∀ x, x ∈ scc ↔ x ∈ ac.cycle := fun x => by
    rw [hsccdef, Std.HashSet.mem_ofList, List.contains_iff_mem]
  -- Every state in the cycle can reach, and be reached from, the cycle's head.
  have hheadreaches : ∀ t ∈ ac.cycle, ac.cycle.head hne = t ∨
      PathTo (sccSuccs succs scc) (fun _ => False) (ac.cycle.head hne) t := by
    intro t ht
    obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem ht
    have hpre : ∀ i, (hi : i + 1 < (ac.cycle.take (j + 1)).length) →
        (ac.cycle.take (j + 1))[i + 1] ∈ succs ((ac.cycle.take (j + 1))[i]) :=
      chain_take ac.cycle (j + 1) ac.cycle_chain
    have hpremem : ∀ x ∈ ac.cycle.take (j + 1), x ∈ scc := fun x hx =>
      (hmemscc x).mpr (List.mem_of_mem_take hx)
    have hpne : ac.cycle.take (j + 1) ≠ [] := by simp; omega
    have hpheadeq : (ac.cycle.take (j + 1)).head hpne = ac.cycle.head hne := List.head_take hpne
    have hplasteq : (ac.cycle.take (j + 1)).getLast hpne = t := by
      rw [List.getLast_take hpne]
      simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem hj]
      simpa using hjeq
    rcases chain_reaches_restricted (ac.cycle.take (j + 1)) hpre hpremem hpne with heq | hp
    · left; rw [← hpheadeq, ← hplasteq]; exact heq
    · right; rwa [hpheadeq, hplasteq] at hp
  have hreacheshead : ∀ s ∈ ac.cycle, s = ac.cycle.head hne ∨
      PathTo (sccSuccs succs scc) (fun _ => False) s (ac.cycle.head hne) := by
    intro s hs
    obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hs
    have hsuf : ∀ i, (hi : i + 1 < (ac.cycle.drop k).length) →
        (ac.cycle.drop k)[i + 1] ∈ succs ((ac.cycle.drop k)[i]) :=
      chain_drop ac.cycle k ac.cycle_chain
    have hsufmem : ∀ x ∈ ac.cycle.drop k, x ∈ scc := fun x hx =>
      (hmemscc x).mpr (List.mem_of_mem_drop hx)
    have hsne : ac.cycle.drop k ≠ [] := by simp; omega
    have hsheadeq : (ac.cycle.drop k).head hsne = s := by
      rw [List.head_eq_getElem, List.getElem_drop]
      simpa using hkeq
    have hslasteq : (ac.cycle.drop k).getLast hsne = ac.cycle.getLast hne := by
      simp [List.getLast_drop]
    have hclosing : ac.cycle.head hne ∈ sccSuccs succs scc (ac.cycle.getLast hne) :=
      Array.mem_filter.mpr ⟨ac.cycle_back, (hmemscc _).mpr (List.head_mem hne)⟩
    rcases chain_reaches_restricted (ac.cycle.drop k) hsuf hsufmem hsne with heq | hp
    · right; rw [hsheadeq, hslasteq] at heq; exact heq ▸ PathTo.direct hclosing
    · right
      rw [hsheadeq, hslasteq] at hp
      exact PathTo.trans hp (PathTo.direct hclosing)
  have hconnected : InternallyConnected succs scc := by
    intro s hs t ht
    have hs' : s ∈ ac.cycle := (hmemscc s).mp hs
    have ht' : t ∈ ac.cycle := (hmemscc t).mp ht
    rcases hreacheshead s hs' with hsh | hsh
    · rcases hheadreaches t ht' with hht | hht
      · left; rw [hsh, hht]
      · right; rw [hsh]; exact hht
    · rcases hheadreaches t ht' with hht | hht
      · right; rw [← hht]; exact hsh
      · right; exact PathTo.trans hsh hht
  have hcovers : AcceptingMarks succs edgeMarks numMarks scc := by
    refine ⟨⟨ac.cycle.getLast hne, (hmemscc _).mpr (List.getLast_mem hne),
      ac.cycle.head hne, (hmemscc _).mpr (List.head_mem hne), ac.cycle_back⟩, ?_⟩
    intro m hm
    obtain ⟨i, hi, hcov⟩ := ac.cycle_covers_marks m hm
    refine ⟨ac.cycle[i], (hmemscc _).mpr (List.getElem_mem _),
      ac.cycle[(i + 1) % ac.cycle.length]'(Nat.mod_lt _ (by omega)),
      (hmemscc _).mpr (List.getElem_mem _), ?_, hcov⟩
    rcases Nat.lt_or_ge (i + 1) ac.cycle.length with hlt | hge
    · have hidx : (i + 1) % ac.cycle.length = i + 1 := Nat.mod_eq_of_lt hlt
      have heq : ac.cycle[(i + 1) % ac.cycle.length]'(Nat.mod_lt _ (by omega)) = ac.cycle[i + 1] := by
        simp only [hidx]
      rw [heq]; exact ac.cycle_chain i hlt
    · have hidx : (i + 1) % ac.cycle.length = 0 := by
        have heqlen : i + 1 = ac.cycle.length := by omega
        rw [heqlen]; simp
      have heq : ac.cycle[(i + 1) % ac.cycle.length]'(Nat.mod_lt _ (by omega)) =
          ac.cycle.head hne := by
        simp only [hidx]; exact (List.head_eq_getElem hne).symm
      rw [heq]
      have hilast : ac.cycle[i] = ac.cycle.getLast hne := by
        rw [List.getLast_eq_getElem]; congr 1; omega
      rw [hilast]
      exact ac.cycle_back
  have hreachable : ∀ s ∈ scc, Reachable initialStates succs s := by
    intro s hs
    have hs' : s ∈ ac.cycle := (hmemscc s).mp hs
    have hoverlap : ac.cycle.head (List.ne_nil_of_length_pos (by omega)) =
        ac.stem.getLast (List.ne_nil_of_length_pos (by omega)) := ac.overlap.symm
    have hr0 : Reachable initialStates succs (ac.cycle.head hne) := by
      rw [hoverlap]
      exact reachable_of_chain ac.stem ac.stem_chain
        (Reachable.base ac.stem_head_initial) (List.ne_nil_of_length_pos (by omega)) rfl
        (ac.stem.getLast (List.ne_nil_of_length_pos (by omega))) (List.getLast_mem _)
    exact reachable_of_chain ac.cycle ac.cycle_chain hr0 hne rfl s hs'
  exact ⟨⟨scc, ⟨ac.cycle.head hne, (hmemscc _).mpr (List.head_mem hne)⟩, hconnected, hcovers,
    hreachable⟩, hmemscc⟩

/-! ## Sufficiency -/

/-- A reachable accepting SCC exists iff a `TAcceptingCycle` does. -/
theorem acceptingSCC_iff_acceptingCycle {initialStates : List State} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} :
    (∃ _A : AcceptingSCC initialStates succs edgeMarks numMarks, True) ↔
    ∃ _ac : TAcceptingCycle initialStates succs edgeMarks numMarks, True := by
  constructor
  · rintro ⟨A, -⟩; exact A.exists_acceptingCycle
  · rintro ⟨ac, -⟩
    obtain ⟨A, -⟩ := ac.exists_acceptingSCC
    exact ⟨A, trivial⟩

end LTLLib
