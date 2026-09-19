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
import Mathlib.Data.Finite.Prod
import LTLLib.TGBABased.AbstractSpec.Lasso
import LTLLib.TGBABased.AbstractSpec.Pumping

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

/-! ## The latched graph -/

/-- Successors of the doubled graph. The stem copy moves freely and may commit to the region at any step, the
committed copy stays inside the region and never returns. -/
def latchSuccs (succs : State → Array State) (region : State → Bool) :
    State × Bool → Array (State × Bool) :=
  fun p =>
    let committed := ((succs p.1).filter region).map (·, true)
    if p.2 then committed else ((succs p.1).map (·, false)) ++ committed

theorem mem_latchSuccs_iff (succs : State → Array State) (region : State → Bool)
    (p q : State × Bool) :
    q ∈ latchSuccs succs region p ↔
      q.1 ∈ succs p.1 ∧ ((q.2 = true ∧ region q.1 = true) ∨ (p.2 = false ∧ q.2 = false)) := by
  obtain ⟨s, b⟩ := p
  obtain ⟨t, c⟩ := q
  cases b <;> simp [latchSuccs, Array.mem_map, Array.mem_filter, Array.mem_append] <;> grind

/-- Initial states of the doubled graph, in the stem copy, or already committed when the state is in the region.
Under `total` every run starts committed instead, which is sound exactly when the region holds everywhere. -/
def latchInit (initialStates : List State) (region : State → Bool) (total : Bool) :
    List (State × Bool) :=
  if total then initialStates.map (·, true)
  else initialStates.map (·, false) ++ (initialStates.filter region).map (·, true)

theorem mem_latchInit_iff (initialStates : List State) (region : State → Bool) (p : State × Bool) :
    p ∈ latchInit initialStates region false ↔
      p.1 ∈ initialStates ∧ (p.2 = false ∨ region p.1 = true) := by
  obtain ⟨s, b⟩ := p
  cases b <;> simp [latchInit, List.mem_filter]

theorem mem_latchInit_total_iff (initialStates : List State) (region : State → Bool)
    (p : State × Bool) :
    p ∈ latchInit initialStates region true ↔ p.1 ∈ initialStates ∧ p.2 = true := by
  obtain ⟨s, b⟩ := p
  cases b <;> simp [latchInit]

/-- Whatever the flag, a latched initial state projects to an initial state. -/
theorem latchInit_fst_mem {initialStates : List State} {region : State → Bool} {total : Bool}
    {p : State × Bool} (h : p ∈ latchInit initialStates region total) : p.1 ∈ initialStates := by
  cases total
  · exact ((mem_latchInit_iff _ _ _).mp h).1
  · exact ((mem_latchInit_total_iff _ _ _).mp h).1

/-- Marks of the doubled graph: the original ones, plus `numMarks` on the edges internal to the committed copy. -/
def latchMarks (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat) :
    State × Bool → State × Bool → Std.HashSet Nat :=
  fun p q => if p.2 && q.2 then (edgeMarks p.1 q.1).insert numMarks else edgeMarks p.1 q.1

theorem mem_latchMarks_iff (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat)
    (p q : State × Bool) (m : Nat) :
    m ∈ latchMarks edgeMarks numMarks p q ↔
      m ∈ edgeMarks p.1 q.1 ∨ (m = numMarks ∧ p.2 = true ∧ q.2 = true) := by
  obtain ⟨s, b⟩ := p
  obtain ⟨t, c⟩ := q
  cases b <;> cases c <;> simp [latchMarks]
  grind

/-- Every latched mark stays below `numMarks + 1`. -/
theorem latchMarks_lt {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat}
    (hbound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks) (p q : State × Bool) (m : Nat)
    (hm : m ∈ latchMarks edgeMarks numMarks p q) : m < numMarks + 1 := by
  rcases (mem_latchMarks_iff edgeMarks numMarks p q m).mp hm with h | ⟨rfl, -, -⟩
  · have := hbound p.1 q.1 m h; omega
  · omega

/-! ## Finite reachability -/

theorem latch_reachable_fst {initialStates : List State} {succs : State → Array State}
    {region : State → Bool} {total : Bool} {p : State × Bool}
    (h : Reachable (latchInit initialStates region total) (latchSuccs succs region) p) :
    Reachable initialStates succs p.1 := by
  induction h with
  | base hi => exact .base (latchInit_fst_mem hi)
  | step _ hmem ih => exact .step ih ((mem_latchSuccs_iff _ _ _ _).mp hmem).1

/-- The latched graph's reachable set sits inside a product with `Bool`, so it stays finite. -/
theorem latch_finiteReach {initialStates : List State} {succs : State → Array State}
    (region : State → Bool) (total : Bool) (fr : FiniteReach initialStates succs) :
    FiniteReach (latchInit initialStates region total) (latchSuccs succs region) :=
  (Set.Finite.prod fr (Set.finite_univ (α := Bool))).subset
    fun _ hp => ⟨latch_reachable_fst hp, trivial⟩

/-! ## Region cycles -/

/-- A `TAcceptingCycle` whose cycle lies entirely inside `region`, which is what a static `FG` restriction asks
for: the cycle is confined, the stem is not. -/
structure TRegionCycle (initialStates : List State) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat) (region : State → Bool)
    extends TAcceptingCycle initialStates succs edgeMarks numMarks where
  cycle_region : ∀ s ∈ cycle, region s = true

/-! ## Soundness -/

/-- A latched accepting cycle lies entirely inside the committed copy, and so inside the region. -/
theorem latch_cycle_committed {initialStates : List State} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} {region : State → Bool}
    {total : Bool} (hbound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (ac : TAcceptingCycle (latchInit initialStates region total) (latchSuccs succs region)
      (latchMarks edgeMarks numMarks) (numMarks + 1)) :
    ∀ j, (hj : j < ac.cycle.length) → (ac.cycle[j]'hj).2 = true ∧ region (ac.cycle[j]'hj).1 = true := by
  have hL : 0 < ac.cycle.length := by have := ac.cycle_nonempty; omega
  have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos hL
  obtain ⟨i, hi, hmark⟩ := ac.cycle_covers_marks numMarks (by omega)
  -- The extra mark can only sit on an edge internal to the committed copy.
  have hsrc : (ac.cycle[i]'hi).2 = true := by
    rcases (mem_latchMarks_iff edgeMarks numMarks _ _ numMarks).mp hmark with h | ⟨-, h, -⟩
    · exact absurd (hbound _ _ numMarks h) (by omega)
    · exact h
  -- Start the walk one step on, where the edge into the state also gives the region.
  have hedge := ac.cycle_succ_mem hne i hi
  obtain ⟨-, hcases⟩ := (mem_latchSuccs_iff succs region _ _).mp hedge
  have hstart : (ac.cycle[(i + 1) % ac.cycle.length]'(Nat.mod_lt _ hL)).2 = true ∧
      region (ac.cycle[(i + 1) % ac.cycle.length]'(Nat.mod_lt _ hL)).1 = true := by
    rcases hcases with h | ⟨h, -⟩
    · exact h
    · exact absurd h (by rw [hsrc]; simp)
  refine ac.cycle_forall_of_step (P := fun p => p.2 = true ∧ region p.1 = true) ?_
    (Nat.mod_lt _ hL) hstart
  intro p q hq hp
  rcases ((mem_latchSuccs_iff succs region p q).mp hq).2 with h | ⟨h, -⟩
  · exact h
  · exact absurd h (by rw [hp.1]; simp)

/-- A latched accepting cycle projects to a region cycle on the original graph, by dropping the Bool. -/
def latch_sound {initialStates : List State} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} {region : State → Bool}
    {total : Bool} (hbound : ∀ s t, ∀ m ∈ edgeMarks s t, m < numMarks)
    (ac : TAcceptingCycle (latchInit initialStates region total) (latchSuccs succs region)
      (latchMarks edgeMarks numMarks) (numMarks + 1)) :
    TRegionCycle initialStates succs edgeMarks numMarks region := by
  have hcommitted := latch_cycle_committed hbound ac
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
      cycle_covers_marks := ?_
      cycle_region := ?_ }
  · rw [List.head_map]
    exact latchInit_fst_mem ac.stem_head_initial
  · intro i hi
    simp only [List.length_map] at hi
    simp only [List.getElem_map]
    exact ((mem_latchSuccs_iff _ _ _ _).mp (ac.stem_chain i hi)).1
  · rw [List.getLast_map, List.head_map]
    exact congrArg Prod.fst ac.overlap
  · intro i hi
    simp only [List.length_map] at hi
    simp only [List.getElem_map]
    exact ((mem_latchSuccs_iff _ _ _ _).mp (ac.cycle_chain i hi)).1
  · rw [List.head_map, List.getLast_map]
    exact ((mem_latchSuccs_iff _ _ _ _).mp ac.cycle_back).1
  · intro m hm
    obtain ⟨i, hi, hmark⟩ := ac.cycle_covers_marks m (by omega)
    simp only [List.length_map, List.getElem_map]
    refine ⟨i, hi, ?_⟩
    rcases (mem_latchMarks_iff edgeMarks numMarks _ _ m).mp hmark with h | ⟨rfl, -, -⟩
    · exact h
    · omega
  · intro s hs
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    exact (hcommitted j hj).2

/-! ## Completeness -/

/-- A run whose tail stays inside the region and which covers every mark infinitely often yields a latched
accepting cycle. -/
theorem latch_complete {initialStates : List State} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} {region : State → Bool}
    (flr : FiniteReach (latchInit initialStates region false) (latchSuccs succs region))
    {σ : Nat → State} (hinit : σ 0 ∈ initialStates) (htrans : ∀ n, σ (n + 1) ∈ succs (σ n))
    {N : Nat} (hregion : ∀ n, N ≤ n → region (σ n) = true)
    (hmarks : ∀ m, m < numMarks → ∀ K, ∃ n ≥ K, m ∈ edgeMarks (σ n) (σ (n + 1))) :
    ∃ _ac : TAcceptingCycle (latchInit initialStates region false) (latchSuccs succs region)
      (latchMarks edgeMarks numMarks) (numMarks + 1), True := by
  refine exists_TAcceptingCycle_of_run flr (σ := fun n => (σ n, decide (N ≤ n))) ?_ ?_ ?_
  · refine (mem_latchInit_iff _ _ _).mpr ⟨hinit, ?_⟩
    by_cases h : N ≤ 0
    · exact Or.inr (hregion 0 h)
    · exact Or.inl (by simp [h])
  · intro n
    refine (mem_latchSuccs_iff _ _ _ _).mpr ⟨htrans n, ?_⟩
    by_cases h : N ≤ n + 1
    · exact Or.inl ⟨by simp [h], hregion _ h⟩
    · exact Or.inr ⟨by simp; omega, by simp [h]⟩
  · intro m hm K
    by_cases hlt : m < numMarks
    · obtain ⟨n, hn, hmark⟩ := hmarks m hlt K
      exact ⟨n, hn, (mem_latchMarks_iff _ _ _ _ _).mpr (Or.inl hmark)⟩
    · refine ⟨max K N, Nat.le_max_left _ _, (mem_latchMarks_iff _ _ _ _ _).mpr (Or.inr ⟨by omega, ?_, ?_⟩)⟩
      · simp
      · simp; omega

/-- The same when the region holds everywhere, with the whole run starting committed. -/
theorem latch_complete_total {initialStates : List State} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} {region : State → Bool}
    (flr : FiniteReach (latchInit initialStates region true) (latchSuccs succs region))
    {σ : Nat → State} (hinit : σ 0 ∈ initialStates) (htrans : ∀ n, σ (n + 1) ∈ succs (σ n))
    (hregion : ∀ s, region s = true)
    (hmarks : ∀ m, m < numMarks → ∀ K, ∃ n ≥ K, m ∈ edgeMarks (σ n) (σ (n + 1))) :
    ∃ _ac : TAcceptingCycle (latchInit initialStates region true) (latchSuccs succs region)
      (latchMarks edgeMarks numMarks) (numMarks + 1), True := by
  refine exists_TAcceptingCycle_of_run flr (σ := fun n => (σ n, true)) ?_ ?_ ?_
  · exact (mem_latchInit_total_iff _ _ _).mpr ⟨hinit, rfl⟩
  · exact fun n => (mem_latchSuccs_iff _ _ _ _).mpr ⟨htrans n, Or.inl ⟨rfl, hregion _⟩⟩
  · intro m hm K
    by_cases hlt : m < numMarks
    · obtain ⟨n, hn, hmark⟩ := hmarks m hlt K
      exact ⟨n, hn, (mem_latchMarks_iff _ _ _ _ _).mpr (Or.inl hmark)⟩
    · exact ⟨K, Nat.le_refl _, (mem_latchMarks_iff _ _ _ _ _).mpr (Or.inr ⟨by omega, rfl, rfl⟩)⟩

end LTLLib
