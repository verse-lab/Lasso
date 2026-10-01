/-
  What it means for an SCC to satisfy a hoisted fairness assumption, which is Streett acceptance stated on a strongly
  connected set rather than on a run. A hoisted conjunct arrives as a list of options, an option being a region `FG l`
  and a list of marks `GF g`, and an SCC satisfies the conjunct when one of its options is available there, [LSFZ16]'s
  Definition 3 read one conjunct at a time. Regions are downward closed and the presence of a mark is upward closed,
  which is what makes the prune terminate and stay complete.

  Defines:
  - `StreettOption`, `StreettSpec`: the option data the search is handed
  - `StreettSpec.flatten`: the spec's options in walk order, with where each conjunct begins
  - `StreettOption.regionHolds`, `StreettOption.marksPresent`, `StreettOption.availableIn`
  - `StreettSpec.accepting`: every conjunct has an available option
  - `StreettOption.availableOn`, `StreettSpec.fairCycle`: the same test decided on a reported cycle
  - `FairSCC`: an `AcceptingSCC` that is also `accepting`, which is what the prune reports
  - `StreettOption.prune`: the candidate one prune step recurses on
  - `FairSCC.restrict`: the same fair SCC read inside a larger candidate

  Proves:
  - `marksPresent_mono`: a mark present in a subset is present in the whole, so a dead option stays dead
  - `regionHolds_anti`: a region holding on a set holds on every subset
  - `marksPresent_of_availableIn_subset`: an option available in a subset has its marks present in the whole set
  - `exists_option_of_fairCycle`, `fairCycle_of_options`: a cycle passes the check exactly when every conjunct
    has an option available on it
  - `exists_FairSCC_of_run`: a run covering the marks and satisfying every conjunct settles into a `FairSCC`
  - `StreettSpec.flatten_spec`: the conjuncts sit contiguously in the flattened array

  References:
  - [LSFZ16] Li, Song, Feng, Zhang. Verify LTL with Fairness Assumptions Efficiently. arXiv:1606.08116, 2016.
  - [SLDP09] Sun, Liu, Dong, Pang. PAT: Towards Flexible Verification under Fairness. CAV 2009.

  Sections:
  - The option structure
  - Availability
  - Flattening
  - Monotonicity
  - Deciding availability on a reported cycle
  - Fair SCCs
  - Pruning a candidate
  - From a fair run to a fair SCC
-/
import LTLLib.TGBABased.AbstractSpec.Pumping
import LTLLib.TGBABased.AbstractSpec.SCCTheory

namespace LTLLib

variable {State : Type u} {L : Type w} [BEq State] [Hashable State] [LawfulBEq State]

/-! ## The option structure -/

/-- One option of one hoisted conjunct, a region that has to hold everywhere in the SCC and marks that each
have to hold somewhere in it. -/
structure StreettOption (L : Type w) where
  region : L → Bool
  marks : Array (L → Bool)
deriving Inhabited

/-- A hoisted fairness assumption as the SCC test sees it, one entry per conjunct of the negated property. -/
structure StreettSpec (State : Type u) (L : Type w) where
  numMarks : Nat  -- the property automaton's own generalized Büchi marks, which the SCC also has to cover
  label : State → L
  conjuncts : Array (Array (StreettOption L))

/-! ## Availability -/

/-- The option's region holds at every state of `B`, which is `FG l` on a cycle that stays inside `B`. -/
def StreettOption.regionHolds (opt : StreettOption L) (label : State → L) (B : Std.HashSet State) : Prop :=
  ∀ s ∈ B, opt.region (label s) = true

/-- Every one of the option's marks holds somewhere in `B`, which is `GF g` on a cycle covering `B`. -/
def StreettOption.marksPresent (opt : StreettOption L) (label : State → L) (B : Std.HashSet State) : Prop :=
  ∀ g ∈ opt.marks, ∃ s ∈ B, g (label s) = true

/-- [LSFZ16, Definition 3] for one option. -/
def StreettOption.availableIn (opt : StreettOption L) (label : State → L) (B : Std.HashSet State) : Prop :=
  opt.regionHolds label B ∧ opt.marksPresent label B

/-- Every conjunct is satisfied by one of its options, which is the decomposed form of "some crossed disjunct
is accepting for `B`". -/
def StreettSpec.accepting (spec : StreettSpec State L) (B : Std.HashSet State) : Prop :=
  ∀ c ∈ spec.conjuncts, ∃ opt ∈ c, opt.availableIn spec.label B

/-! ## Flattening

The compiled form of a spec indexes options by position, so the conjuncts are concatenated once and the position each
one begins at is recorded alongside. -/

section Flatten
omit [BEq State] [Hashable State] [LawfulBEq State]

-- concatenate the conjuncts from `i` on, recording in `starts` where each one begins
private def flattenAux (cs : Array (Array (StreettOption L))) (i : Nat)
    (out : Array (StreettOption L)) (starts : Array Nat) : Array (StreettOption L) × Array Nat :=
  if h : i < cs.size then
    flattenAux cs (i + 1) (out ++ cs[i]) (starts.push (out.size + cs[i].size))
  else (out, starts)
termination_by cs.size - i

/-- Conjuncts concatenated in walk order, with the position each one begins at. -/
def flattenOpts (cs : Array (Array (StreettOption L))) : Array (StreettOption L) × Array Nat :=
  flattenAux cs 0 #[] #[0]

/-- The spec's options in walk order, paired with the position each conjunct begins at. -/
def StreettSpec.flatten (spec : StreettSpec State L) : Array (StreettOption L) × Array Nat :=
  flattenOpts spec.conjuncts

private theorem flattenAux_spec (cs : Array (Array (StreettOption L))) :
    ∀ i out starts, i ≤ cs.size → starts.size = i + 1 → starts[i]! = out.size →
      (flattenAux cs i out starts).2.size = cs.size + 1 ∧
      (∀ j < i + 1, (flattenAux cs i out starts).2[j]! = starts[j]!) ∧
      (∀ j < out.size, (flattenAux cs i out starts).1[j]! = out[j]!) ∧
      (flattenAux cs i out starts).1.size = (flattenAux cs i out starts).2[cs.size]! ∧
      (∀ p, i ≤ p → p < cs.size →
        (flattenAux cs i out starts).2[p + 1]! =
            (flattenAux cs i out starts).2[p]! + (cs[p]!).size ∧
          ∀ k < (cs[p]!).size,
            (flattenAux cs i out starts).1[(flattenAux cs i out starts).2[p]! + k]! =
              (cs[p]!)[k]!) := by
  intro i out starts
  induction i, out, starts using flattenAux.induct (cs := cs) with
  | case1 i out starts hi ih =>
    intro hle hsize hstart
    have hgetA : ∀ (a : Array (StreettOption L)) (j : Nat) (h : j < a.size), a[j]! = a[j]'h :=
      fun a j h => getElem!_pos a j h
    have hcs : cs[i]! = cs[i] := getElem!_pos cs i hi
    -- the push leaves the earlier starts alone and records where the appended block ends
    have hpush : ∀ j < i + 1, (starts.push (out.size + cs[i].size))[j]! = starts[j]! := by
      intro j hj
      rw [getElem!_pos _ _ (by simp [hsize]; omega), getElem!_pos starts j (by omega),
        Array.getElem_push_lt (by omega)]
    have hpushTop : (starts.push (out.size + cs[i].size))[i + 1]! = (out ++ cs[i]).size := by
      rw [getElem!_pos _ _ (by simp [hsize])]
      simp [Array.getElem_push, hsize]
    have happ : ∀ j < out.size, (out ++ cs[i])[j]! = out[j]! := by
      intro j hj
      rw [getElem!_pos _ _ (by simp; omega), getElem!_pos out j hj, Array.getElem_append_left hj]
    have hs' : (starts.push (out.size + cs[i].size)).size = i + 1 + 1 := by simp [hsize]
    obtain ⟨q1, q2, q3, q4, q5⟩ := ih (by omega) hs' hpushTop
    rw [flattenAux]
    simp only [hi, dif_pos]
    refine ⟨q1, fun j hj => ?_, fun j hj => ?_, q4, fun p hip hp => ?_⟩
    · rw [q2 j (by omega), hpush j hj]
    · rw [q3 j (by simp; omega), happ j hj]
    · rcases Nat.eq_or_lt_of_le hip with rfl | hlt
      · have hstartP : (flattenAux cs (i + 1) (out ++ cs[i])
            (starts.push (out.size + cs[i].size))).2[i]! = out.size := by
          rw [q2 i (by omega), hpush i (by omega), hstart]
        refine ⟨?_, fun k hk => ?_⟩
        · rw [q2 (i + 1) (by omega), hpushTop, hstartP, hcs]
          simp
        · have hk' : k < cs[i].size := by rwa [hcs] at hk
          have hgk := hgetA cs[i] k hk'
          have hidx : out.size + k < (out ++ cs[i]).size := by simp; omega
          rw [hstartP, q3 (out.size + k) hidx, hgetA _ _ hidx, hcs, hgk,
            Array.getElem_append_right (by omega)]
          simp
      · exact q5 p hlt hp
  | case2 i out starts hi =>
    intro hle hsize hstart
    have hieq : i = cs.size := by omega
    subst hieq
    rw [flattenAux]
    simp only [hi, dif_neg, not_false_iff]
    refine ⟨hsize, ?_, ?_, hstart.symm, fun p hip hp => absurd hp (by omega)⟩ <;>
      intros <;> trivial

/-- The conjuncts sit contiguously in `flattenOpts _ |>.1`, conjunct `i` occupying
`flattenOpts.2[i] ..< flattenOpts.2[i+1]`. -/
theorem flattenOpts_spec (cs : Array (Array (StreettOption L))) :
    (flattenOpts cs).2.size = cs.size + 1 ∧
    (flattenOpts cs).2[0]! = 0 ∧
    (flattenOpts cs).1.size = (flattenOpts cs).2[cs.size]! ∧
    ∀ i < cs.size,
      (flattenOpts cs).2[i + 1]! = (flattenOpts cs).2[i]! + (cs[i]!).size ∧
      ∀ k < (cs[i]!).size,
        (flattenOpts cs).1[(flattenOpts cs).2[i]! + k]! = (cs[i]!)[k]! := by
  obtain ⟨q1, q2, q3, q4, q5⟩ :=
    flattenAux_spec cs 0 #[] #[0] (Nat.zero_le _) (by simp) (by simp)
  have hz : (flattenOpts cs).2[0]! = 0 := by
    show (flattenAux cs 0 #[] #[0]).2[0]! = 0
    rw [q2 0 (by omega)]; simp
  exact ⟨q1, hz, q4, fun i hi => q5 i (Nat.zero_le _) hi⟩

/-- The conjuncts sit contiguously in `flatten.1`, conjunct `i` occupying `flatten.2[i] ..< flatten.2[i+1]`. -/
theorem StreettSpec.flatten_spec (spec : StreettSpec State L) :
    spec.flatten.2.size = spec.conjuncts.size + 1 ∧
    spec.flatten.2[0]! = 0 ∧
    spec.flatten.1.size = spec.flatten.2[spec.conjuncts.size]! ∧
    ∀ i < spec.conjuncts.size,
      spec.flatten.2[i + 1]! = spec.flatten.2[i]! + (spec.conjuncts[i]!).size ∧
      ∀ k < (spec.conjuncts[i]!).size,
        spec.flatten.1[spec.flatten.2[i]! + k]! = (spec.conjuncts[i]!)[k]! :=
  flattenOpts_spec spec.conjuncts

end Flatten

/-! ## Monotonicity -/

omit [LawfulBEq State] in
/-- Marks are upward closed, so an option whose marks are missing from `B` is dead in every subgraph of `B`. -/
theorem marksPresent_mono {opt : StreettOption L} {label : State → L} {B B' : Std.HashSet State}
    (hsub : ∀ s ∈ B', s ∈ B) (h : opt.marksPresent label B') : opt.marksPresent label B := by
  intro g hg
  obtain ⟨s, hs, hgs⟩ := h g hg
  exact ⟨s, hsub s hs, hgs⟩

omit [LawfulBEq State] in
/-- Regions are downward closed, so pruning can only ever make more of them hold. -/
theorem regionHolds_anti {opt : StreettOption L} {label : State → L} {B B' : Std.HashSet State}
    (hsub : ∀ s ∈ B', s ∈ B) (h : opt.regionHolds label B) : opt.regionHolds label B' :=
  fun s hs => h s (hsub s hs)

omit [LawfulBEq State] in
/-- An option available anywhere below `B` has its marks present in `B`. -/
theorem marksPresent_of_availableIn_subset {opt : StreettOption L} {label : State → L}
    {B B' : Std.HashSet State} (hsub : ∀ s ∈ B', s ∈ B) (h : opt.availableIn label B') :
    opt.marksPresent label B :=
  marksPresent_mono hsub h.2

/-! ## Deciding availability on a reported cycle -/

/-- `availableIn` on the list a reported witness comes in, decided. -/
def StreettOption.availableOn (opt : StreettOption L) (label : State → L) (cycle : List State) : Bool :=
  cycle.all (fun s => opt.region (label s)) && opt.marks.all fun g => cycle.any fun s => g (label s)

/-- Every conjunct has an option available on the cycle, which is `accepting` decided on the states of one
lasso rather than on an SCC. -/
def StreettSpec.fairCycle (spec : StreettSpec State L) (cycle : List State) : Bool :=
  spec.conjuncts.all fun c => c.any fun opt => opt.availableOn spec.label cycle

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- What a passing check gives back: one option per conjunct, its region holding at every cycle state and each
of its marks at some cycle state. -/
theorem exists_option_of_fairCycle {spec : StreettSpec State L} {cycle : List State}
    (h : spec.fairCycle cycle = true) {c : Array (StreettOption L)} (hc : c ∈ spec.conjuncts) :
    ∃ opt ∈ c, (∀ s ∈ cycle, opt.region (spec.label s) = true) ∧
      ∀ g ∈ opt.marks, ∃ s ∈ cycle, g (spec.label s) = true := by
  obtain ⟨opt, hopt, hav⟩ := Array.any_eq_true'.mp (Array.all_eq_true'.mp h c hc)
  rw [StreettOption.availableOn, Bool.and_eq_true] at hav
  refine ⟨opt, hopt, fun s hs => List.all_eq_true.mp hav.1 s hs, fun g hg => ?_⟩
  obtain ⟨s, hs, hgs⟩ := List.any_eq_true.mp (Array.all_eq_true'.mp hav.2 g hg)
  exact ⟨s, hs, hgs⟩

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- One option per conjunct available on the cycle passes the check. -/
theorem fairCycle_of_options {spec : StreettSpec State L} {cycle : List State}
    (h : ∀ c ∈ spec.conjuncts, ∃ opt ∈ c, (∀ s ∈ cycle, opt.region (spec.label s) = true) ∧
      ∀ g ∈ opt.marks, ∃ s ∈ cycle, g (spec.label s) = true) :
    spec.fairCycle cycle = true := by
  refine Array.all_eq_true'.mpr fun c hc => ?_
  obtain ⟨opt, hopt, hreg, hmarks⟩ := h c hc
  refine Array.any_eq_true'.mpr ⟨opt, hopt, ?_⟩
  rw [StreettOption.availableOn, Bool.and_eq_true]
  refine ⟨List.all_eq_true.mpr hreg, Array.all_eq_true'.mpr fun g hg => ?_⟩
  obtain ⟨s, hs, hgs⟩ := hmarks g hg
  exact List.any_eq_true.mpr ⟨s, hs, hgs⟩

/-! ## Fair SCCs -/

/-- What the prune reports: a reachable, internally connected set that covers the property's own marks and
satisfies every hoisted conjunct. -/
structure FairSCC (initialStates : List State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (spec : StreettSpec State L) where
  scc : Std.HashSet State
  nonempty : ∃ s, s ∈ scc
  connected : InternallyConnected succs scc
  covers : AcceptingMarks succs edgeMarks spec.numMarks scc
  reachable : ∀ s ∈ scc, Reachable initialStates succs s
  fair : spec.accepting scc

/-- The underlying `AcceptingSCC`. -/
def FairSCC.toAcceptingSCC {initialStates : List State} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {spec : StreettSpec State L}
    (A : FairSCC initialStates succs edgeMarks spec) :
    AcceptingSCC initialStates succs edgeMarks spec.numMarks :=
  ⟨A.scc, A.nonempty, A.connected, A.covers, A.reachable⟩

/-! ## Pruning a candidate -/

/-- The part of a candidate the option's region admits, which is what a prune step recurses on. -/
def StreettOption.prune [LawfulHashable State] (opt : StreettOption L) (label : State → L)
    (C : Std.HashSet State) : Std.HashSet State :=
  C.filter fun s => opt.region (label s)

omit [LawfulBEq State] in
theorem StreettOption.mem_prune [LawfulBEq State] [LawfulHashable State] {opt : StreettOption L}
    {label : State → L} {C : Std.HashSet State} {s : State} :
    s ∈ opt.prune label C ↔ s ∈ C ∧ opt.region (label s) = true := by
  rw [StreettOption.prune, Std.HashSet.mem_filter]
  constructor
  · rintro ⟨h, hf⟩
    rw [Std.HashSet.get_eq h] at hf
    exact ⟨h, hf⟩
  · rintro ⟨h, hf⟩
    exact ⟨h, by rw [Std.HashSet.get_eq h]; exact hf⟩

/-- A fair SCC is a fair SCC of any candidate that contains it, the graph being restricted to that candidate.
`g` is the graph it was found in, which only has to admit ambient edges. -/
def FairSCC.restrict {initialStates : List State} {g succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {spec : StreettSpec State L}
    (A : FairSCC initialStates g edgeMarks spec) (hg : ∀ a b, b ∈ g a → b ∈ succs a)
    {D : Std.HashSet State} (hsub : ∀ s ∈ A.scc, s ∈ D) :
    FairSCC D.toList (sccSuccs succs D) edgeMarks spec where
  scc := A.scc
  nonempty := A.nonempty
  connected := A.connected.restrict hg hsub
  covers := A.covers.restrict hg hsub
  reachable := fun s hs => .base (by simpa using hsub s hs)
  fair := A.fair

/-! ## From a fair run to a fair SCC -/

private theorem exists_selection {α : Type u₁} {β : Type u₂} (mem : α → β → Prop) (P : β → Prop) :
    ∀ l : List α, (∀ a ∈ l, ∃ b, mem a b ∧ P b) →
      ∃ sel : List β, (∀ a ∈ l, ∃ b ∈ sel, mem a b) ∧ ∀ b ∈ sel, P b
  | [], _ => ⟨[], by simp, by simp⟩
  | a :: l, h => by
    obtain ⟨b, hb, hPb⟩ := h a (by simp)
    obtain ⟨sel, hsel, hall⟩ := exists_selection mem P l fun x hx => h x (by simp [hx])
    refine ⟨b :: sel, fun x hx => ?_, fun c hc => ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b, by simp, hb⟩
      · obtain ⟨c, hc, hmem⟩ := hsel x hx
        exact ⟨c, by simp [hc], hmem⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact hPb
      · exact hall c hc

private theorem exists_common_threshold {β : Type u₂} (f : β → Nat → Prop) :
    ∀ l : List β, (∀ b ∈ l, ∃ N, ∀ n, N ≤ n → f b n) → ∃ N, ∀ b ∈ l, ∀ n, N ≤ n → f b n
  | [], _ => ⟨0, by simp⟩
  | b :: l, h => by
    obtain ⟨N₁, hN₁⟩ := h b (by simp)
    obtain ⟨N₂, hN₂⟩ := exists_common_threshold f l fun x hx => h x (by simp [hx])
    refine ⟨max N₁ N₂, fun x hx n hn => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hN₁ n (Nat.le_trans (Nat.le_max_left _ _) hn)
    · exact hN₂ x hx n (Nat.le_trans (Nat.le_max_right _ _) hn)

/-- A run that covers the property marks and satisfies every conjunct settles into a `FairSCC`, [LSFZ16, Theorem 2]
read one conjunct at a time. -/
theorem exists_FairSCC_of_run {spec : StreettSpec State L} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {initialStates : List State}
    (fr : FiniteReach initialStates succs) {σ : Nat → State} (hinit : σ 0 ∈ initialStates)
    (htrans : ∀ n, σ (n + 1) ∈ succs (σ n))
    (hacc : ∀ m, m < spec.numMarks → ∀ K, ∃ n ≥ K, m ∈ edgeMarks (σ n) (σ (n + 1)))
    (hfair : ∀ c ∈ spec.conjuncts, ∃ opt ∈ c,
      (∃ N, ∀ n, N ≤ n → opt.region (spec.label (σ n)) = true) ∧
      ∀ g ∈ opt.marks, ∀ K, ∃ n ≥ K, g (spec.label (σ n)) = true) :
    Nonempty (FairSCC initialStates succs edgeMarks spec) := by
  -- one option per conjunct, then one threshold past which every chosen region holds
  obtain ⟨sel, hsel, hselP⟩ :=
    exists_selection (fun (c : Array (StreettOption L)) opt => opt ∈ c) _ spec.conjuncts.toList
      fun c hc => by simpa using hfair c (by simpa using hc)
  obtain ⟨N, hN⟩ := exists_common_threshold (fun opt n => opt.region (spec.label (σ n)) = true) sel
    fun opt h => (hselP opt h).1
  let ps : List (State → Bool) :=
    sel.flatMap fun opt => opt.marks.toList.map fun g => fun s => g (spec.label s)
  have hps : ∀ p ∈ ps, ∀ K, ∃ n ≥ K, p (σ n) = true := by
    intro p hp K
    obtain ⟨opt, hopt, hmem⟩ := List.mem_flatMap.mp hp
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hmem
    exact (hselP opt hopt).2 g (by simpa using hg) K
  obtain ⟨ac, htail, hmeets⟩ := exists_TAcceptingCycle_of_run_marks fr hinit htrans hacc N ps hps
  obtain ⟨A, hA⟩ := ac.exists_acceptingSCC
  refine ⟨⟨A.scc, A.nonempty, A.connected, A.covers, A.reachable, fun c hc => ?_⟩⟩
  obtain ⟨opt, hoptsel, hoptc⟩ := hsel c (by simpa using hc)
  refine ⟨opt, hoptc, fun s hs => ?_, fun g hg => ?_⟩
  · obtain ⟨n, hn, rfl⟩ := htail s ((hA s).mp hs)
    exact hN opt hoptsel n hn
  · obtain ⟨s, hs, hgs⟩ := hmeets (fun s => g (spec.label s))
      (List.mem_flatMap.mpr ⟨opt, hoptsel, List.mem_map.mpr ⟨g, by simpa using hg, rfl⟩⟩)
    exact ⟨s, (hA s).mpr hs, hgs⟩

end LTLLib
