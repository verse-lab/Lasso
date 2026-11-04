module

/-
  Streett acceptance on an SCC when the hoisted regions restrict steps rather than states.

  `StreettSCC.lean` reads a region `FG l` as a predicate on states, which is exact only while every step out of
  a state reads the same letter. A region here is instead a predicate on letters that selects a subgraph, and the
  marks are recomputed on what survives. A spec exposes the restricted graph and the restricted marks as operators
  indexed by the region, and both halves of availability are read off them, an option's mark `g` being witnessed is
  membership of the restricted graph at the conjoined predicate `region ∧ g`, so region and mark are answered on
  one realization.

  Availability does not compose across conjuncts: an edge may have a realization for each region separately and
  none satisfying both, so an `RFairSCC` carries its selection and is connected in the conjunction of the selected
  regions.

  Defines:
  - `RStreettSpec`: the region-indexed spec, and `RStreettSpec.Compat`, its laws against an ambient graph
  - `selRegion`: the conjunction of a selection's regions
  - `RStreettSpec.AvailableWith`, `RStreettSpec.Accepting`: availability of a selection on a set
  - `RFairSCC`: what an edge-aware prune reports
  - `RRun`: a run together with the letter and marks its chosen realization reads at each step

  Proves:
  - `selRegion_le`, `selRegion_and_le`: the conjunction is below each conjunct, and below itself conjoined with more
  - `RStreettSpec.Compat.succs_sub`, `marks_sub`: a restricted step is an ambient step
  - `RFairSCC.toAcceptingSCC`: the ambient `AcceptingSCC` underneath
  - `exists_RFairSCC_of_run`: a run meeting the property's marks and every conjunct settles into an
    `RFairSCC`, [LSFZ16, Theorem 2] with regions read on steps

  References:
  - [LSFZ16] Li, Song, Feng, Zhang. Verify LTL with Fairness Assumptions Efficiently. arXiv:1606.08116, 2016.

  Sections:
  - The region-indexed spec
  - Selections
  - Availability
  - Fair SCCs
  - The edge-indexed reading
  - Runs that carry their letters
  - From a fair run to a fair SCC
-/
public import LTLLib.AbstractSpec.Pumping
public import LTLLib.AbstractSpec.SCCTheory
public import LTLLib.AbstractSpec.StreettSCC
meta import LTLLib.Tactic.Set

public section

namespace LTLLib

variable {State : Type u} {L : Type w} [BEq State] [Hashable State] [LawfulBEq State]

/-! ## The region-indexed spec -/

/-- A hoisted fairness assumption whose regions restrict steps. `regionSuccs r` is the graph of steps whose
letter satisfies `r`, and `regionMarks r` the property automaton's marks carried by those same steps. -/
structure RStreettSpec (State : Type u) (L : Type w) where
  numMarks : Nat
  regionSuccs : (L → Bool) → State → Array State
  regionMarks : (L → Bool) → State → State → Std.HashSet Nat
  conjuncts : Array (Array (StreettOption L))
  -- A region's graph and marks from one pass over the source. A spec that can share its per-source work should
  -- say so here, the default pairs `regionSuccs` with `regionMarks` naively.
  regionExpand : (L → Bool) → State → Array State × Array (Std.HashSet Nat) × Array Nat :=
    fun r => derivedExpand (regionSuccs r) (regionMarks r)
  -- `regionExpand` computes what `regionSuccs` and `regionMarks` say it does.
  regionExpand_coherent : ∀ r, ExpandCoherent (regionSuccs r) (regionMarks r) (regionExpand r)

/-- A predicate entailing another, pointwise. -/
@[expose] def LePred (r' r : L → Bool) : Prop := ∀ l, r' l = true → r l = true

theorem LePred.refl (r : L → Bool) : LePred r r := fun _ h => h

theorem LePred.trans {r₁ r₂ r₃ : L → Bool} (h₁ : LePred r₁ r₂) (h₂ : LePred r₂ r₃) :
    LePred r₁ r₃ := fun l h => h₂ l (h₁ l h)

/-- The laws tying a spec's restricted operators to the ambient graph it lives over: antitone in the region,
and the identity at the top region. -/
structure RStreettSpec.Compat (spec : RStreettSpec State L) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) : Prop where
  succs_mono : ∀ {r' r : L → Bool}, LePred r' r →
    ∀ s t, t ∈ spec.regionSuccs r' s → t ∈ spec.regionSuccs r s
  marks_mono : ∀ {r' r : L → Bool}, LePred r' r →
    ∀ s t m, m ∈ spec.regionMarks r' s t → m ∈ spec.regionMarks r s t
  succs_top : ∀ s, spec.regionSuccs (fun _ => true) s = succs s
  -- pointwise, not an equality of `Std.HashSet Nat`, an implementation may answer from a shared, grouped table
  -- whose bucket layout differs from a per-realization fold.
  marks_top : ∀ s t m, m ∈ spec.regionMarks (fun _ => true) s t ↔ m ∈ edgeMarks s t

/-- The antitone halves of `Compat` on their own, saying nothing about any ambient graph. -/
structure RStreettSpec.Mono (spec : RStreettSpec State L) : Prop where
  succs_mono : ∀ {r' r : L → Bool}, LePred r' r →
    ∀ s t, t ∈ spec.regionSuccs r' s → t ∈ spec.regionSuccs r s
  marks_mono : ∀ {r' r : L → Bool}, LePred r' r →
    ∀ s t m, m ∈ spec.regionMarks r' s t → m ∈ spec.regionMarks r s t

variable {spec : RStreettSpec State L} {succs : State → Array State}
  {edgeMarks : State → State → Std.HashSet Nat}

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- A restricted step is an ambient step. -/
theorem RStreettSpec.Compat.succs_sub (h : spec.Compat succs edgeMarks) (r : L → Bool) (s t : State)
    (hst : t ∈ spec.regionSuccs r s) : t ∈ succs s := by
  rw [← h.succs_top s]
  exact h.succs_mono (fun _ _ => rfl) s t hst

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- A restricted mark is an ambient mark. -/
theorem RStreettSpec.Compat.marks_sub (h : spec.Compat succs edgeMarks) (r : L → Bool) (s t : State)
    (m : Nat) (hm : m ∈ spec.regionMarks r s t) : m ∈ edgeMarks s t :=
  (h.marks_top s t m).mp (h.marks_mono (fun _ _ => rfl) s t m hm)

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- The graph-free half of a compatibility proof. -/
theorem RStreettSpec.Compat.toMono (h : spec.Compat succs edgeMarks) : spec.Mono :=
  ⟨h.succs_mono, h.marks_mono⟩

/-! ## Selections -/

/-- The conjunction of the regions of one option per conjunct. A cycle witnessing a selection must satisfy
every selected region at every step, so this, not the individual regions, is what restricts its graph. -/
@[expose] def selRegion (sel : List (StreettOption L)) : L → Bool :=
  fun l => sel.all fun opt => opt.region l

/-- A selection's region entails the region of every option in it. -/
theorem selRegion_le {sel : List (StreettOption L)} {opt : StreettOption L} (h : opt ∈ sel) :
    LePred (selRegion sel) opt.region :=
  fun _ hl => List.all_eq_true.mp hl opt h

theorem selRegion_and_le {sel : List (StreettOption L)} (g : L → Bool) :
    LePred (fun l => selRegion sel l && g l) (selRegion sel) :=
  fun _ hl => (Bool.and_eq_true _ _ |>.mp hl).1

/-! ## Availability -/

/-- A selection is available on `B`: `B` is internally connected and covers the property's marks in the
graph the selection restricts to, and each selected option's marks are witnessed by an internal edge that
is itself in-region. -/
structure RStreettSpec.AvailableWith (spec : RStreettSpec State L) (sel : List (StreettOption L))
    (B : Std.HashSet State) : Prop where
  connected : InternallyConnected (spec.regionSuccs (selRegion sel)) B
  covers : AcceptingMarks (spec.regionSuccs (selRegion sel))
    (spec.regionMarks (selRegion sel)) spec.numMarks B
  optMarks : ∀ opt ∈ sel, ∀ g ∈ opt.marks, ∃ s ∈ B, ∃ t ∈ B,
    t ∈ spec.regionSuccs (fun l => selRegion sel l && g l) s

/-- Some selection picking one option per conjunct is available on `B`. -/
@[expose] def RStreettSpec.Accepting (spec : RStreettSpec State L) (B : Std.HashSet State) : Prop :=
  ∃ sel : List (StreettOption L),
    (∀ c ∈ spec.conjuncts, ∃ opt ∈ sel, opt ∈ c) ∧ spec.AvailableWith sel B

/-! ## Fair SCCs -/

/-- What an edge-aware prune reports: a reachable set that is an SCC of, and covers its marks in, the
subgraph its own selection restricts to. -/
structure RFairSCC (initialStates : List State) (succs : State → Array State)
    (spec : RStreettSpec State L) where
  scc : Std.HashSet State
  nonempty : ∃ s, s ∈ scc
  reachable : ∀ s ∈ scc, Reachable initialStates succs s
  fair : spec.Accepting scc

/-- The ambient `AcceptingSCC` underneath, obtained by relaxing the restricted graph and marks to the ambient ones. -/
@[expose] noncomputable def RFairSCC.toAcceptingSCC {initialStates : List State}
    (hcompat : spec.Compat succs edgeMarks) (A : RFairSCC initialStates succs spec) :
    AcceptingSCC initialStates succs edgeMarks spec.numMarks :=
  let sel := A.fair.choose
  let hav := A.fair.choose_spec.2
  { scc := A.scc
    nonempty := A.nonempty
    connected := hav.connected.mono_graph
      (fun s t hst => hcompat.succs_sub (selRegion sel) s t hst)
    covers := by
      obtain ⟨⟨s, hs, t, ht, he⟩, hcov⟩ := hav.covers
      refine ⟨⟨s, hs, t, ht, hcompat.succs_sub _ s t he⟩, fun m hm => ?_⟩
      obtain ⟨u, hu, v, hv, huv, hmm⟩ := hcov m hm
      exact ⟨u, hu, v, hv, hcompat.succs_sub _ u v huv, hcompat.marks_sub _ u v m hmm⟩
    reachable := A.reachable }

/-! ## The edge-indexed reading

The prune scans the SCC's internal edges, so each option is re-read as a predicate on edges: its region admits an
edge that has an in-region realization, and its mark `g` is witnessed by an edge with a realization satisfying the
region and `g`. The mark predicate conjoins the region, so the two are answered on one realization. -/

/-- An option read on edges. -/
@[expose] def StreettOption.onEdges (spec : RStreettSpec State L) (opt : StreettOption L) :
    StreettOption (State × State) where
  region := fun e => (spec.regionSuccs opt.region e.1).contains e.2
  marks := opt.marks.map fun g e =>
    (spec.regionSuccs (fun l => opt.region l && g l) e.1).contains e.2

/-- An option read on edges inside a letter restriction `r`: its region admits an edge that has a realization
satisfying `r` and the region, and its mark `g` is witnessed by an edge with a realization satisfying `r`, the
region and `g`, all three at once. `r` is the candidate's own region, the conjunction of the options already
committed to it, and reading the option at `r ∧ opt.region` is what makes the scan's verdict joint with those
commitments. `onEdges` is the case `r = ⊤`. -/
@[expose] def StreettOption.onEdgesIn (spec : RStreettSpec State L) (r : L → Bool) (opt : StreettOption L) :
    StreettOption (State × State) where
  region := fun e => (spec.regionSuccs (fun l => r l && opt.region l) e.1).contains e.2
  marks := opt.marks.map fun g e =>
    (spec.regionSuccs (fun l => r l && opt.region l && g l) e.1).contains e.2

omit [Hashable State] [LawfulBEq State] in
/-- At the top region an option's edge reading is the unrestricted one. -/
@[simp] theorem StreettOption.onEdgesIn_top (spec : RStreettSpec State L) (opt : StreettOption L) :
    opt.onEdgesIn spec (fun _ => true) = opt.onEdges spec := rfl

omit [Hashable State] in
@[simp] theorem StreettOption.onEdgesIn_marks_size (spec : RStreettSpec State L) (r : L → Bool)
    (opt : StreettOption L) : (opt.onEdgesIn spec r).marks.size = opt.marks.size := by
  simp [StreettOption.onEdgesIn]

/-- The spec the prune compiles: the same conjuncts, read on edges. Its `label` is never consulted, the
edge scan is pointed at an explicit edge list, so it is pinned to the diagonal. -/
@[expose] def RStreettSpec.edgeSpec (spec : RStreettSpec State L) : StreettSpec State (State × State) where
  numMarks := spec.numMarks
  label := fun s => (s, s)
  conjuncts := spec.conjuncts.map fun c => c.map fun opt => opt.onEdges spec

omit [Hashable State] [LawfulBEq State] in
@[simp] theorem RStreettSpec.edgeSpec_numMarks (spec : RStreettSpec State L) :
    spec.edgeSpec.numMarks = spec.numMarks := rfl

omit [Hashable State] [LawfulBEq State] in
theorem RStreettSpec.edgeSpec_conjuncts_size (spec : RStreettSpec State L) :
    spec.edgeSpec.conjuncts.size = spec.conjuncts.size := by simp [RStreettSpec.edgeSpec]

omit [Hashable State] [LawfulBEq State] in
theorem RStreettSpec.edgeSpec_conjunct_size (spec : RStreettSpec State L) {i : Nat}
    (hi : i < spec.conjuncts.size) :
    (spec.edgeSpec.conjuncts[i]!).size = (spec.conjuncts[i]!).size := by
  rw [RStreettSpec.edgeSpec]
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos _ i hi]
  simp

omit [Hashable State] [LawfulBEq State] in
/-- Option `k` of conjunct `i` of the edge spec is the edge reading of the same option. -/
theorem RStreettSpec.edgeSpec_getElem (spec : RStreettSpec State L) {i : Nat}
    (hi : i < spec.conjuncts.size) {k : Nat} (hk : k < (spec.conjuncts[i]!).size) :
    (spec.edgeSpec.conjuncts[i]!)[k]! = ((spec.conjuncts[i]!)[k]!).onEdges spec := by
  have h1 : spec.edgeSpec.conjuncts[i]! = (spec.conjuncts[i]!).map fun opt => opt.onEdges spec := by
    rw [RStreettSpec.edgeSpec]
    rw [getElem!_pos _ i (by simpa using hi), getElem!_pos _ i hi]
    simp
  rw [h1, getElem!_pos _ k (by simpa using hk), getElem!_pos _ k hk]
  simp

/-! ## Runs that carry their letters

The abstract layer cannot see realizations, so a run carries, at each step, the letter its chosen realization reads
and the marks that realization carries. The two laws say that a step whose letter satisfies `r` survives the
`r`-restriction, with its marks. -/

/-- A run of `succs` together with the letter and marks its chosen realization reads at each step. -/
structure RRun (spec : RStreettSpec State L) (initialStates : List State) where
  st : Nat → State
  lets : Nat → L
  rmarks : Nat → Std.HashSet Nat
  init : st 0 ∈ initialStates
  step : ∀ (n : Nat) (r : L → Bool), r (lets n) = true → st (n + 1) ∈ spec.regionSuccs r (st n)
  mark : ∀ (n : Nat) (r : L → Bool), r (lets n) = true →
    ∀ m ∈ rmarks n, m ∈ spec.regionMarks r (st n) (st (n + 1))

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- The ambient step relation the run walks. -/
theorem RRun.trans (hcompat : spec.Compat succs edgeMarks) {initialStates : List State}
    (ρ : RRun spec initialStates) (n : Nat) : ρ.st (n + 1) ∈ succs (ρ.st n) :=
  hcompat.succs_sub _ _ _ (ρ.step n (fun _ => true) rfl)

/-! ## From a fair run to a fair SCC -/

private theorem exists_selection' {α : Type u₁} {β : Type u₂} (mem : α → β → Prop) (P : β → Prop) :
    ∀ l : List α, (∀ a ∈ l, ∃ b, mem a b ∧ P b) →
      ∃ sel : List β, (∀ a ∈ l, ∃ b ∈ sel, mem a b) ∧ ∀ b ∈ sel, P b
  | [], _ => ⟨[], by simp, by simp⟩
  | a :: l, h => by
    obtain ⟨b, hb, hPb⟩ := h a (by simp)
    obtain ⟨sel, hsel, hall⟩ := exists_selection' mem P l fun x hx => h x (by simp [hx])
    refine ⟨b :: sel, fun x hx => ?_, fun c hc => ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b, by simp, hb⟩
      · obtain ⟨c, hc, hmem⟩ := hsel x hx
        exact ⟨c, by simp [hc], hmem⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact hPb
      · exact hall c hc

private theorem exists_common_threshold' {β : Type u₂} (f : β → Nat → Prop) :
    ∀ l : List β, (∀ b ∈ l, ∃ N, ∀ n, N ≤ n → f b n) → ∃ N, ∀ b ∈ l, ∀ n, N ≤ n → f b n
  | [], _ => ⟨0, by simp⟩
  | b :: l, h => by
    obtain ⟨N₁, hN₁⟩ := h b (by simp)
    obtain ⟨N₂, hN₂⟩ := exists_common_threshold' f l fun x hx => h x (by simp [hx])
    refine ⟨max N₁ N₂, fun x hx n hn => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hN₁ n (Nat.le_trans (Nat.le_max_left _ _) hn)
    · exact hN₂ x hx n (Nat.le_trans (Nat.le_max_right _ _) hn)

/-- The conjunction of a selection holds at a letter exactly when every member's region does. -/
theorem selRegion_eq_true {sel : List (StreettOption L)} {l : L}
    (h : ∀ opt ∈ sel, opt.region l = true) : selRegion sel l = true :=
  List.all_eq_true.mpr h

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- Every state the run visits is reachable in the ambient graph. -/
theorem RRun.reachable (hcompat : spec.Compat succs edgeMarks) {initialStates : List State}
    (ρ : RRun spec initialStates) : ∀ n, Reachable initialStates succs (ρ.st n)
  | 0 => .base ρ.init
  | n + 1 => (ρ.reachable hcompat n).step (ρ.trans hcompat n)

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- The restricted graph reaches no further than the ambient one, so finiteness transfers. -/
theorem finiteReach_of_sub {initialStates : List State} {g : State → Array State} {s₀ : State}
    (hg : ∀ a b, b ∈ g a → b ∈ succs a) (fr : FiniteReach initialStates succs)
    (h₀ : Reachable initialStates succs s₀) : FiniteReach [s₀] g := by
  refine fr.subset fun x hx => ?_
  show Reachable initialStates succs x
  induction hx with
  | base hi => rw [List.mem_singleton.mp hi]; exact h₀
  | step _ ht ih => exact Reachable.step ih (hg _ _ ht)

set_option maxHeartbeats 1000000 in
/-- A run that covers the property's marks and satisfies every conjunct settles into an `RFairSCC`,
[LSFZ16, Theorem 2] with the regions read on steps rather than on states.

The marks the cycle has to cover are the property's own plus one per selected option mark, the extra one sitting on
an edge exactly when that edge has a realization satisfying the selection's region and the option mark. -/
theorem exists_RFairSCC_of_run (hcompat : spec.Compat succs edgeMarks)
    {initialStates : List State} (fr : FiniteReach initialStates succs)
    (ρ : RRun spec initialStates)
    (hacc : ∀ m, m < spec.numMarks → ∀ K, ∃ n ≥ K, m ∈ ρ.rmarks n)
    (hfair : ∀ c ∈ spec.conjuncts, ∃ opt ∈ c,
      (∃ N, ∀ n, N ≤ n → opt.region (ρ.lets n) = true) ∧
      ∀ g ∈ opt.marks, ∀ K, ∃ n ≥ K, g (ρ.lets n) = true) :
    Nonempty (RFairSCC initialStates succs spec) := by
  classical
  -- one option per conjunct, then a threshold past which every selected region holds
  obtain ⟨sel, hsel, hselP⟩ :=
    exists_selection' (fun (c : Array (StreettOption L)) opt => opt ∈ c) _ spec.conjuncts.toList
      fun c hc => by simpa using hfair c (by simpa using hc)
  obtain ⟨N, hN⟩ := exists_common_threshold' (fun opt n => opt.region (ρ.lets n) = true) sel
    fun opt h => (hselP opt h).1
  set R : L → Bool := selRegion sel with hR
  have hRtrue : ∀ n, N ≤ n → R (ρ.lets n) = true :=
    fun n hn => selRegion_eq_true fun opt hopt => hN opt hopt n hn
  set g : State → Array State := spec.regionSuccs R with hg
  have hgsub : ∀ a b, b ∈ g a → b ∈ succs a := fun a b h => hcompat.succs_sub R a b h
  -- the option marks, flattened and indexed
  set gs : List (L → Bool) := sel.flatMap fun opt => opt.marks.toList with hgs
  have hgsP : ∀ gj ∈ gs, ∀ K, ∃ n ≥ K, gj (ρ.lets n) = true := by
    intro gj hgj K
    obtain ⟨opt, hopt, hmem⟩ := List.mem_flatMap.mp hgj
    exact (hselP opt hopt).2 gj (by simpa using hmem) K
  -- the augmented edge marks: the property's, plus one per option mark, region-gated
  set em : State → State → Std.HashSet Nat := fun s t =>
    Std.HashSet.ofList ((spec.regionMarks R s t).toList.filter (· < spec.numMarks) ++
      (List.range gs.length).filterMap fun j =>
        if (spec.regionSuccs (fun l => R l && (gs.getD j (fun _ => false)) l) s).contains t
        then some (spec.numMarks + j) else none) with hem
  have hgetD : ∀ (j : Nat) (h : j < gs.length), gs.getD j (fun _ => false) = gs[j] := by
    intro j h; simp [List.getD, h]
  have hmem : ∀ s t m, m ∈ em s t ↔ (m ∈ spec.regionMarks R s t ∧ m < spec.numMarks) ∨
      ∃ j, j < gs.length ∧ m = spec.numMarks + j ∧
        (spec.regionSuccs (fun l => R l && (gs.getD j (fun _ => false)) l) s).contains t = true := by
    intro s t m
    rw [hem]
    rw [show (fun s t => Std.HashSet.ofList _ : State → State → Std.HashSet Nat) s t = _ from rfl,
      Std.HashSet.mem_ofList, List.contains_iff_mem, List.mem_append, List.mem_filter,
      Std.HashSet.mem_toList, List.mem_filterMap]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨j, hj, hje⟩)
      · exact Or.inl ⟨h1, by simpa using h2⟩
      · refine Or.inr ⟨j, List.mem_range.mp hj, ?_⟩
        by_cases hp : (spec.regionSuccs (fun l => R l && (gs.getD j (fun _ => false)) l) s).contains t = true
        · rw [if_pos hp] at hje
          exact ⟨(Option.some.inj hje).symm, hp⟩
        · rw [if_neg hp] at hje
          exact absurd hje (by simp)
    · rintro (⟨h1, h2⟩ | ⟨j, hj, rfl, hp⟩)
      · exact Or.inl ⟨h1, by simpa using h2⟩
      · exact Or.inr ⟨j, List.mem_range.mpr hj, by rw [if_pos hp]⟩
  -- shift the run past the threshold, where every step is a restricted step
  set σ : Nat → State := fun n => ρ.st (N + n) with hσ
  have htrans : ∀ n, σ (n + 1) ∈ g (σ n) := by
    intro n
    show ρ.st (N + n + 1) ∈ spec.regionSuccs R (ρ.st (N + n))
    exact ρ.step (N + n) R (hRtrue _ (by omega))
  have hacc' : ∀ m, m < spec.numMarks + gs.length → ∀ K, ∃ n ≥ K, m ∈ em (σ n) (σ (n + 1)) := by
    intro m hm K
    rcases Nat.lt_or_ge m spec.numMarks with hlt | hge
    · obtain ⟨n, hn, hmn⟩ := hacc m hlt (N + K)
      refine ⟨n - N, by omega, (hmem _ _ m).mpr (Or.inl ⟨?_, hlt⟩)⟩
      have e1 : σ (n - N) = ρ.st n := by simp only [hσ]; congr 1; omega
      have e2 : σ (n - N + 1) = ρ.st (n + 1) := by simp only [hσ]; congr 1; omega
      rw [e1, e2]
      exact ρ.mark n R (hRtrue n (by omega)) m hmn
    · set j := m - spec.numMarks with hj
      have hjlt : j < gs.length := by omega
      have hgj : gs.getD j (fun _ => false) ∈ gs := by
        rw [hgetD j hjlt]; exact List.getElem_mem hjlt
      obtain ⟨n, hn, hgn⟩ := hgsP _ hgj (N + K)
      refine ⟨n - N, by omega, (hmem _ _ m).mpr (Or.inr ⟨j, hjlt, by omega, ?_⟩)⟩
      have e1 : σ (n - N) = ρ.st n := by simp only [hσ]; congr 1; omega
      have e2 : σ (n - N + 1) = ρ.st (n + 1) := by simp only [hσ]; congr 1; omega
      rw [e1, e2]
      exact Array.contains_iff_mem.mpr
        (ρ.step n _ (by rw [Bool.and_eq_true]; exact ⟨hRtrue n (by omega), hgn⟩))
  -- pump the shifted run into an accepting cycle of the restricted graph
  obtain ⟨ac, htail, -⟩ := exists_TAcceptingCycle_of_run_marks
    (finiteReach_of_sub hgsub fr (ρ.reachable hcompat N)) (σ := σ)
    (by simp only [hσ]; exact List.mem_singleton.mpr (by congr 1)) htrans hacc' 0 [] (by simp)
  obtain ⟨A, hA⟩ := ac.exists_acceptingSCC
  have hcov := A.covers.2
  refine ⟨⟨A.scc, A.nonempty, fun s hs => ?_, sel, fun c hc => hsel c (by simpa using hc), ?_, ?_, ?_⟩⟩
  · obtain ⟨n, -, rfl⟩ := htail s ((hA s).mp hs)
    exact ρ.reachable hcompat (N + n)
  · exact A.connected
  · refine ⟨A.covers.1, fun m hmlt => ?_⟩
    obtain ⟨u, hu, v, hv, huv, hmm⟩ := hcov m (by omega)
    rcases (hmem u v m).mp hmm with ⟨h1, -⟩ | ⟨j, -, rfl, -⟩
    · exact ⟨u, hu, v, hv, huv, h1⟩
    · omega
  · intro opt hopt gj hgj
    obtain ⟨j, hjlt, hjeq⟩ := List.mem_iff_getElem.mp
      (List.mem_flatMap.mpr ⟨opt, hopt, by simpa using hgj⟩ : gj ∈ gs)
    obtain ⟨u, hu, v, hv, huv, hmm⟩ := hcov (spec.numMarks + j) (Nat.add_lt_add_left hjlt _)
    rcases (hmem u v _).mp hmm with ⟨-, h2⟩ | ⟨j', -, hje, hct⟩
    · omega
    · have hjj : j' = j := by omega
      refine ⟨u, hu, v, hv, ?_⟩
      rw [hjj, hgetD j hjlt, hjeq] at hct
      exact Array.contains_iff_mem.mp hct

end LTLLib
