module

/-
  The region latch: checking a static `FG l` restriction with one call to an unmodified emptiness checker. `FG l`
  constrains only the tail of a run, so the accepting cycle must lie inside the `l`-region while the stem need not, and
  restricting `succs` globally would be incomplete. The latch doubles the graph with a Bool, `(s, false)` for the stem
  and `(s, true)` for the part committed to the region, with edges `false → false`, `false → true` into the region and
  `true → true` inside it. One extra mark carried only by `true → true` edges forces the accepting cycle into the
  region, and the witness projects back by dropping the Bool.

  Defines:
  - `latchSuccs`, `latchInit`, `latchMarks`: the doubled graph
  - `TRegionCycle`: a `TAcceptingCycle` whose cycle lies entirely inside the region

  Proves:
  - `TAcceptingCycle.cycle_forall_of_step`: a step-closed property holding at one cycle position holds at all
  - `latch_sound`: a latched `TAcceptingCycle` projects to a `TRegionCycle` on the original graph
  - `latch_complete`: a run whose tail stays in the region and covers every mark yields a latched one
  - `latch_complete_total`: the same for an everywhere-true region, starting committed so the stem copy is never entered

  Sections:
  - Cyclic propagation
  - The latched graph
  - Finite reachability
  - Region cycles
  - Soundness
  - Completeness
-/
public import LTLLib.TGBABased.AbstractSpec.Lasso
public import LTLLib.TGBABased.AbstractSpec.Pumping

public section

namespace LTLLib

variable {State : Type u}

/-! ## Cyclic propagation -/

/-- A property closed under `succs`-steps and holding at one cycle position holds at every cycle position. -/
theorem TAcceptingCycle.cycle_forall_of_step {initialStates : List State}
    {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat}
    {P : State → Prop} (ac : TAcceptingCycle initialStates succs edgeMarks numMarks)
    (hstep : ∀ s t, t ∈ succs s → P s → P t)
    {i : Nat} (hi : i < ac.cycle.length) (hP : P (ac.cycle[i]'hi)) :
    ∀ j, (hj : j < ac.cycle.length) → P (ac.cycle[j]'hj) := by
  have hL : 0 < ac.cycle.length := by have := ac.cycle_nonempty; omega
  have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos hL
  -- Transport along index equality.
  have key : ∀ a b, (ha : a < ac.cycle.length) → (hb : b < ac.cycle.length) → a = b →
      P (ac.cycle[a]'ha) → P (ac.cycle[b]'hb) := by
    intro a b ha hb hab h; subst hab; exact h
  have hwalk : ∀ k, P (ac.cycle[(i + k) % ac.cycle.length]'(Nat.mod_lt _ hL)) := by
    intro k
    induction k with
    | zero => exact key i _ hi (Nat.mod_lt _ hL) (by rw [Nat.add_zero, Nat.mod_eq_of_lt hi]) hP
    | succ k ih =>
      have hmem := ac.cycle_succ_mem hne ((i + k) % ac.cycle.length) (Nat.mod_lt _ hL)
      exact key _ _ (Nat.mod_lt _ hL) (Nat.mod_lt _ hL)
        (by rw [Nat.mod_add_mod, Nat.add_assoc]) (hstep _ _ hmem ih)
  intro j hj
  by_cases hij : i ≤ j
  · exact key _ _ (Nat.mod_lt _ hL) hj
      (by rw [show i + (j - i) = j from by omega, Nat.mod_eq_of_lt hj]) (hwalk (j - i))
  · exact key _ _ (Nat.mod_lt _ hL) hj
      (by rw [show i + (ac.cycle.length + j - i) = ac.cycle.length + j from by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt hj]) (hwalk (ac.cycle.length + j - i))

/-! ## The latched graph

The `FG` part arrives as a *restriction of the graph*, `succsR`, not as a predicate on states. With a
propositional `FG l` over state atoms the two coincide — `succsR = (succs ·).filter (l.eval ∘ label)` — but
once a letter belongs to the step (`TGBABased/LabelledSys.lean`), `◇□ l` restricts which *edges* the
accepting cycle may traverse, and two parallel steps out of one state can differ on it. See
`EdgeLabels.md` §6.4. -/

/-- Successors of the doubled graph. The stem copy moves freely along `succs` and may commit at any step;
the committed copy moves only along `succsR` and never returns. -/
@[expose] def latchSuccs (succs succsR : State → Array State) :
    State × Bool → Array (State × Bool) :=
  fun p =>
    let committed := (succsR p.1).map (·, true)
    if p.2 then committed else ((succs p.1).map (·, false)) ++ committed

theorem mem_latchSuccs_iff (succs succsR : State → Array State) (p q : State × Bool) :
    q ∈ latchSuccs succs succsR p ↔
      (q.2 = true ∧ q.1 ∈ succsR p.1) ∨ (p.2 = false ∧ q.2 = false ∧ q.1 ∈ succs p.1) := by
  obtain ⟨s, b⟩ := p
  obtain ⟨t, c⟩ := q
  cases b <;> simp [latchSuccs, Array.mem_map, Array.mem_append] <;> grind

/-- A latched step projects to a step of the ambient graph, given that the restriction is one. -/
theorem latchSuccs_fst {succs succsR : State → Array State}
    (hsub : ∀ s t, t ∈ succsR s → t ∈ succs s) {p q : State × Bool}
    (h : q ∈ latchSuccs succs succsR p) : q.1 ∈ succs p.1 := by
  rcases (mem_latchSuccs_iff succs succsR p q).mp h with ⟨-, hr⟩ | ⟨-, -, hs⟩
  · exact hsub _ _ hr
  · exact hs

/-- Initial states of the doubled graph: in the stem copy, or already committed. Unlike the state-region
form this needs no filter — commitment constrains the *outgoing* step, which `succsR` already governs, so a
state with no restricted step out of it is simply a dead end in the committed copy. Under `total` every run
starts committed, sound exactly when the restriction is the whole graph. -/
@[expose] def latchInit (initialStates : List State) (total : Bool) : List (State × Bool) :=
  if total then initialStates.map (·, true)
  else initialStates.map (·, false) ++ initialStates.map (·, true)

theorem mem_latchInit_iff (initialStates : List State) (p : State × Bool) :
    p ∈ latchInit initialStates false ↔ p.1 ∈ initialStates := by
  obtain ⟨s, b⟩ := p
  cases b <;> simp [latchInit]

theorem mem_latchInit_total_iff (initialStates : List State) (p : State × Bool) :
    p ∈ latchInit initialStates true ↔ p.1 ∈ initialStates ∧ p.2 = true := by
  obtain ⟨s, b⟩ := p
  cases b <;> simp [latchInit]

theorem latchInit_fst_mem {initialStates : List State} {total : Bool} {p : State × Bool}
    (h : p ∈ latchInit initialStates total) : p.1 ∈ initialStates := by
  cases total
  · exact (mem_latchInit_iff _ _).mp h
  · exact ((mem_latchInit_total_iff _ _).mp h).1

/-- Marks of the doubled graph. Every edge *into* the committed copy reads `edgeMarksR`, because a mark
there has to be realizable by a restricted step; `numMarks` is added when the source is committed too, which
is what forces the accepting cycle inside. Keying on `p.2 && q.2`, as the state-region form did, would give
the commit edge ambient marks — harmless while the two mark functions agree, wrong once they differ. -/
@[expose] def latchMarks (edgeMarks edgeMarksR : State → State → Std.HashSet Nat) (numMarks : Nat) :
    State × Bool → State × Bool → Std.HashSet Nat :=
  fun p q =>
    if q.2 then (if p.2 then (edgeMarksR p.1 q.1).insert numMarks else edgeMarksR p.1 q.1)
    else edgeMarks p.1 q.1

theorem mem_latchMarks_iff (edgeMarks edgeMarksR : State → State → Std.HashSet Nat) (numMarks : Nat)
    (p q : State × Bool) (m : Nat) :
    m ∈ latchMarks edgeMarks edgeMarksR numMarks p q ↔
      (q.2 = false ∧ m ∈ edgeMarks p.1 q.1) ∨
      (q.2 = true ∧ (m ∈ edgeMarksR p.1 q.1 ∨ (p.2 = true ∧ m = numMarks))) := by
  obtain ⟨s, b⟩ := p
  obtain ⟨t, c⟩ := q
  cases b <;> cases c <;> simp [latchMarks] <;> grind

theorem latchMarks_lt {edgeMarks edgeMarksR : State → State → Std.HashSet Nat} {numMarks : Nat}
    (hbound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (hboundR : ∀ s t, ∀ m ∈ edgeMarksR s t, m < numMarks) (p q : State × Bool) (m : Nat)
    (hm : m ∈ latchMarks edgeMarks edgeMarksR numMarks p q) : m < numMarks + 1 := by
  rcases (mem_latchMarks_iff edgeMarks edgeMarksR numMarks p q m).mp hm with ⟨-, h⟩ | ⟨-, h | ⟨-, rfl⟩⟩
  · have := hbound p.1 q.1 m h; omega
  · have := hboundR p.1 q.1 m h; omega
  · omega

/-! ## Finite reachability -/

theorem latch_reachable_fst {initialStates : List State} {succs succsR : State → Array State}
    (hsub : ∀ s t, t ∈ succsR s → t ∈ succs s) {total : Bool} {p : State × Bool}
    (h : Reachable (latchInit initialStates total) (latchSuccs succs succsR) p) :
    Reachable initialStates succs p.1 := by
  induction h with
  | base hi => exact .base (latchInit_fst_mem hi)
  | step _ hmem ih => exact .step ih (latchSuccs_fst hsub hmem)

/-- The latched graph's reachable set sits inside a product with `Bool`, so it stays finite. -/
theorem latch_finiteReach {initialStates : List State} {succs succsR : State → Array State}
    (hsub : ∀ s t, t ∈ succsR s → t ∈ succs s) (total : Bool)
    (fr : FiniteReach initialStates succs) :
    FiniteReach (latchInit initialStates total) (latchSuccs succs succsR) :=
  (fr.prod (FinitePred.of_forall_mem (p := fun _ : Bool => True) [false, true] fun b => by cases b <;> simp)).subset
    fun _ hp => ⟨latch_reachable_fst hsub hp, trivial⟩

/-- The fused expansion for the doubled graph: one call to each side's `expand` per latched state. -/
@[expose] def latchExpand (expand expandR : State → Array State × Array (Std.HashSet Nat) × Array Nat) (numMarks : Nat) :
    State × Bool → Array (State × Bool) × Array (Std.HashSet Nat) × Array Nat :=
  fun p =>
    let r := expandR p.1
    if p.2 then (r.1.map (·, true), r.2.1.map (·.insert numMarks), r.2.2)
    else
      let e := expand p.1
      -- The payload is *empty or parallel to the successors*, and a bare `++` only preserves that when
      -- both sides agree on emptiness. They do on every route today — the latch is the crossing route,
      -- which has no options — but a mixed pair would silently misalign the bits against an appended
      -- successor array, so the empty side is padded rather than skipped. §13.17
      (e.1.map (·, false) ++ r.1.map (·, true), e.2.1 ++ r.2.1,
        if e.2.2.isEmpty && r.2.2.isEmpty then #[]
        else (if e.2.2.isEmpty then Array.replicate e.1.size 0 else e.2.2)
          ++ (if r.2.2.isEmpty then Array.replicate r.1.size 0 else r.2.2))

theorem latchExpand_coherent {succs succsR : State → Array State}
    {edgeMarks edgeMarksR : State → State → Std.HashSet Nat}
    {expand expandR : State → Array State × Array (Std.HashSet Nat) × Array Nat}
    (hexp : ExpandCoherent succs edgeMarks expand)
    (hexpR : ExpandCoherent succsR edgeMarksR expandR) (numMarks : Nat) :
    ExpandCoherent (latchSuccs succs succsR) (latchMarks edgeMarks edgeMarksR numMarks)
      (latchExpand expand expandR numMarks) := by
  intro p
  obtain ⟨s, b⟩ := p
  cases b
  · simp [latchExpand, latchSuccs, latchMarks, hexp.fst s, hexp.snd s, hexpR.fst s, hexpR.snd s,
      Array.map_map, Function.comp_def]
  · simp [latchExpand, latchSuccs, latchMarks, hexpR.fst s, hexpR.snd s,
      Array.map_map, Function.comp_def]

/-! ## Soundness -/

/-- A latched accepting cycle lies entirely inside the committed copy. -/
theorem latch_cycle_committed {initialStates : List State} {succs succsR : State → Array State}
    {edgeMarks edgeMarksR : State → State → Std.HashSet Nat} {numMarks : Nat} {total : Bool}
    (hbound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (hboundR : ∀ s t, ∀ m ∈ edgeMarksR s t, m < numMarks)
    (ac : TAcceptingCycle (latchInit initialStates total) (latchSuccs succs succsR)
      (latchMarks edgeMarks edgeMarksR numMarks) (numMarks + 1)) :
    ∀ j, (hj : j < ac.cycle.length) → (ac.cycle[j]'hj).2 = true := by
  have hL : 0 < ac.cycle.length := by have := ac.cycle_nonempty; omega
  obtain ⟨i, hi, hmark⟩ := ac.cycle_covers_marks numMarks (by omega)
  have hsrc : (ac.cycle[i]'hi).2 = true := by
    rcases (mem_latchMarks_iff edgeMarks edgeMarksR numMarks _ _ numMarks).mp hmark with
      ⟨-, h⟩ | ⟨-, h | ⟨h, -⟩⟩
    · exact absurd (hbound _ _ numMarks h) (by omega)
    · exact absurd (hboundR _ _ numMarks h) (by omega)
    · exact h
  refine ac.cycle_forall_of_step (P := fun p => p.2 = true) ?_ hi hsrc
  intro p q hq hp
  rcases (mem_latchSuccs_iff succs succsR p q).mp hq with ⟨h, -⟩ | ⟨h, -, -⟩
  · exact h
  · exact absurd h (by rw [hp]; simp)

/-- A latched accepting cycle projects to a region cycle, by dropping the Bool: the stem walks `succs`, and
the cycle — being entirely committed — walks `succsR` and carries `edgeMarksR`'s marks. -/
@[expose] def latch_sound {initialStates : List State} {succs succsR : State → Array State}
    {edgeMarks edgeMarksR : State → State → Std.HashSet Nat} {numMarks : Nat} {total : Bool}
    (hsub : ∀ s t, t ∈ succsR s → t ∈ succs s)
    (hbound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (hboundR : ∀ s t, ∀ m ∈ edgeMarksR s t, m < numMarks)
    (ac : TAcceptingCycle (latchInit initialStates total) (latchSuccs succs succsR)
      (latchMarks edgeMarks edgeMarksR numMarks) (numMarks + 1)) :
    TRegionCycle initialStates succs succsR edgeMarks edgeMarksR numMarks := by
  have hcommitted := latch_cycle_committed hbound hboundR ac
  refine
    { stem := ac.stem.map Prod.fst
      cycle := ac.cycle.map Prod.fst
      stem_nonempty := by simpa using ac.stem_nonempty
      cycle_nonempty := by simpa using ac.cycle_nonempty
      stem_head_initial := ?_
      stem_chain := ?_
      overlap := ?_
      cycle_chain := ?_
      cycle_back := ?_
      cycle_covers_marks := ?_ }
  · rw [List.head_map]
    exact latchInit_fst_mem ac.stem_head_initial
  · intro i hi
    simp only [List.length_map] at hi
    simp only [List.getElem_map]
    exact latchSuccs_fst hsub (ac.stem_chain i hi)
  · rw [List.getLast_map, List.head_map]
    exact congrArg Prod.fst ac.overlap
  · intro i hi
    simp only [List.length_map] at hi
    simp only [List.getElem_map]
    rcases (mem_latchSuccs_iff _ _ _ _).mp (ac.cycle_chain i hi) with ⟨-, h⟩ | ⟨-, h, -⟩
    · exact h
    · exact absurd h (by rw [hcommitted (i + 1) hi]; simp)
  · rw [List.head_map, List.getLast_map]
    have hL : 0 < ac.cycle.length := by have := ac.cycle_nonempty; omega
    have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos hL
    rcases (mem_latchSuccs_iff _ _ _ _).mp ac.cycle_back with ⟨-, h⟩ | ⟨-, h, -⟩
    · exact h
    · exact absurd h (by
        rw [show (ac.cycle.head hne).2 = true from by
          rw [List.head_eq_getElem hne]; exact hcommitted 0 hL]; simp)
  · intro m hm
    obtain ⟨i, hi, hmark⟩ := ac.cycle_covers_marks m (by omega)
    simp only [List.length_map, List.getElem_map]
    refine ⟨i, hi, ?_⟩
    rcases (mem_latchMarks_iff edgeMarks edgeMarksR numMarks _ _ m).mp hmark with
      ⟨h, -⟩ | ⟨-, h | ⟨-, rfl⟩⟩
    · exact absurd h (by rw [hcommitted _ (Nat.mod_lt _ (by omega))]; simp)
    · exact h
    · omega

/-! ## Completeness -/

/-- A run whose tail steps inside the restricted graph and which covers every mark infinitely often there
yields a latched accepting cycle. -/
theorem latch_complete {initialStates : List State} {succs succsR : State → Array State}
    {edgeMarks edgeMarksR : State → State → Std.HashSet Nat} {numMarks : Nat}
    (flr : FiniteReach (latchInit initialStates false) (latchSuccs succs succsR))
    {σ : Nat → State} (hinit : σ 0 ∈ initialStates) (htrans : ∀ n, σ (n + 1) ∈ succs (σ n))
    {N : Nat} (hregion : ∀ n, N ≤ n → σ (n + 1) ∈ succsR (σ n))
    (hmarks : ∀ m, m < numMarks → ∀ K, ∃ n ≥ K, N ≤ n ∧ m ∈ edgeMarksR (σ n) (σ (n + 1))) :
    ∃ _ac : TAcceptingCycle (latchInit initialStates false) (latchSuccs succs succsR)
      (latchMarks edgeMarks edgeMarksR numMarks) (numMarks + 1), True := by
  refine exists_TAcceptingCycle_of_run flr (σ := fun n => (σ n, decide (N < n))) ?_ ?_ ?_
  · exact (mem_latchInit_iff _ _).mpr hinit
  · intro n
    refine (mem_latchSuccs_iff _ _ _ _).mpr ?_
    by_cases h : N ≤ n
    · exact Or.inl ⟨by simp; omega, hregion n h⟩
    · exact Or.inr ⟨by simp; omega, by simp; omega, htrans n⟩
  · intro m hm K
    by_cases hlt : m < numMarks
    · obtain ⟨n, hn, hNn, hmark⟩ := hmarks m hlt (max K (N + 1))
      exact ⟨n, by omega, (mem_latchMarks_iff _ _ _ _ _ _).mpr
        (Or.inr ⟨by simp; omega, Or.inl hmark⟩)⟩
    · exact ⟨max K (N + 1), by omega, (mem_latchMarks_iff _ _ _ _ _ _).mpr
        (Or.inr ⟨by simp; omega, Or.inr ⟨by simp; omega, by omega⟩⟩)⟩

/-- The same when the restriction is the whole graph, with the run starting committed. -/
theorem latch_complete_total {initialStates : List State} {succs succsR : State → Array State}
    {edgeMarks edgeMarksR : State → State → Std.HashSet Nat} {numMarks : Nat}
    (flr : FiniteReach (latchInit initialStates true) (latchSuccs succs succsR))
    {σ : Nat → State} (hinit : σ 0 ∈ initialStates)
    (hregion : ∀ n, σ (n + 1) ∈ succsR (σ n))
    (hmarks : ∀ m, m < numMarks → ∀ K, ∃ n ≥ K, m ∈ edgeMarksR (σ n) (σ (n + 1))) :
    ∃ _ac : TAcceptingCycle (latchInit initialStates true) (latchSuccs succs succsR)
      (latchMarks edgeMarks edgeMarksR numMarks) (numMarks + 1), True := by
  refine exists_TAcceptingCycle_of_run flr (σ := fun n => (σ n, true)) ?_ ?_ ?_
  · exact (mem_latchInit_total_iff _ _).mpr ⟨hinit, rfl⟩
  · exact fun n => (mem_latchSuccs_iff _ _ _ _).mpr (Or.inl ⟨rfl, hregion n⟩)
  · intro m hm K
    by_cases hlt : m < numMarks
    · obtain ⟨n, hn, hmark⟩ := hmarks m hlt K
      exact ⟨n, hn, (mem_latchMarks_iff _ _ _ _ _ _).mpr (Or.inr ⟨rfl, Or.inl hmark⟩)⟩
    · exact ⟨K, Nat.le_refl _, (mem_latchMarks_iff _ _ _ _ _ _).mpr
        (Or.inr ⟨rfl, Or.inr ⟨rfl, by omega⟩⟩)⟩

end LTLLib
