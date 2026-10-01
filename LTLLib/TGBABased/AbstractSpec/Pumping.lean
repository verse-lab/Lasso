/-
  From an accepting run to a `TAcceptingCycle` lasso witness. Pigeonholing on marked positions is not enough, a cycle
  spanning two marked positions need not carry every mark. The run is instead cut into rounds, each containing an
  occurrence of every mark, and the pigeonhole is applied to the round boundaries, so any repeat delimits a cycle that
  has seen every mark. This is the round-robin counting of the standard degeneralization [Cho74], applied to the run.

  Proves:
  - `exists_TAcceptingCycle_of_run`: a run hitting every mark infinitely often yields a `TAcceptingCycle`
  - `exists_TAcceptingCycle_of_run_tail`: the same with the cycle past a given position
  - `exists_TAcceptingCycle_of_run_marks`: the same again, the cycle also meeting each of a list of state predicates the
    run satisfies infinitely often

  References:
  - [Cho74] Choueka. Theories of Automata on ω-Tapes: A Simplified Approach. JCSS 8(2), 1974.

  Sections:
  - Round boundaries
  - The pumping lemma
-/
import LTLLib.TGBABased.AbstractSpec.EmptinessCheck
import LTLLib.Tactic.Set

namespace LTLLib

/-! ## Round boundaries

`coverFrom k` walks marks `0 .. k-1` one at a time from a given start, and `roundEnd` iterates full sweeps of all
`numMarks` of them. The extra `+ 1` at each level keeps the boundaries strictly increasing even when `numMarks = 0`. -/

section RoundBoundaries

variable {State : Type u} {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} {σ : Nat → State}

/-- Marks recur forever along `σ`. -/
private abbrev MarksRecur (edgeMarks : State → State → Std.HashSet Nat) (numMarks : Nat) (σ : Nat → State) :=
  ∀ m, m < numMarks → ∀ N, ∃ n ≥ N, m ∈ edgeMarks (σ n) (σ (n + 1))

/-- Some index at or after `N` whose outgoing edge carries mark `m`, `N` itself for an out-of-range `m`. -/
private noncomputable def nextMark (hacc : MarksRecur edgeMarks numMarks σ) (m N : Nat) : Nat :=
  if h : m < numMarks then (hacc m h N).choose else N

private theorem nextMark_ge (hacc : MarksRecur edgeMarks numMarks σ) (m N : Nat) :
    N ≤ nextMark hacc m N := by
  rw [nextMark]
  split
  · next h => exact (hacc m h N).choose_spec.1
  · exact Nat.le_refl N

private theorem nextMark_spec (hacc : MarksRecur edgeMarks numMarks σ) {m : Nat} (hm : m < numMarks)
    (N : Nat) : m ∈ edgeMarks (σ (nextMark hacc m N)) (σ (nextMark hacc m N + 1)) := by
  rw [nextMark, dif_pos hm]
  exact (hacc m hm N).choose_spec.2

/-- One index past the point where marks `0 .. k-1` have each occurred at or after `N`. -/
private noncomputable def coverFrom (hacc : MarksRecur edgeMarks numMarks σ) : Nat → Nat → Nat
  | 0, N => N
  | k + 1, N => nextMark hacc k (coverFrom hacc k N) + 1

private theorem coverFrom_ge (hacc : MarksRecur edgeMarks numMarks σ) (k N : Nat) :
    N ≤ coverFrom hacc k N := by
  induction k with
  | zero => exact Nat.le_refl N
  | succ k ih =>
    show N ≤ nextMark hacc k (coverFrom hacc k N) + 1
    have := nextMark_ge hacc k (coverFrom hacc k N)
    omega

private theorem coverFrom_lt_succ (hacc : MarksRecur edgeMarks numMarks σ) (k N : Nat) :
    coverFrom hacc k N < coverFrom hacc (k + 1) N := by
  show coverFrom hacc k N < nextMark hacc k (coverFrom hacc k N) + 1
  have := nextMark_ge hacc k (coverFrom hacc k N)
  omega

private theorem coverFrom_le_of_le (hacc : MarksRecur edgeMarks numMarks σ) {k k' : Nat} (h : k ≤ k')
    (N : Nat) : coverFrom hacc k N ≤ coverFrom hacc k' N := by
  induction k' with
  | zero => rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with hlt | hge
    · exact Nat.le_trans (ih (by omega)) (Nat.le_of_lt (coverFrom_lt_succ hacc k' N))
    · rw [Nat.le_antisymm h hge]; exact Nat.le_refl _

/-- Every mark below `k` occurs on an edge inside `[N, coverFrom k N)`. -/
private theorem coverFrom_covers (hacc : MarksRecur edgeMarks numMarks σ) {m k : Nat} (hm : m < numMarks)
    (hmk : m < k) (N : Nat) :
    ∃ n, N ≤ n ∧ n + 1 ≤ coverFrom hacc k N ∧ m ∈ edgeMarks (σ n) (σ (n + 1)) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge m k with hlt | hge
    · obtain ⟨n, h1, h2, h3⟩ := ih hlt
      exact ⟨n, h1, Nat.le_trans h2 (Nat.le_of_lt (coverFrom_lt_succ hacc k N)), h3⟩
    · -- `m = k`, so this sweep's own pick is the witness and the window ends exactly one past it
      have hmk' : m = k := by omega
      subst hmk'
      exact ⟨nextMark hacc m (coverFrom hacc m N),
        Nat.le_trans (coverFrom_ge hacc m N) (nextMark_ge hacc m _), Nat.le_refl _, nextMark_spec hacc hm _⟩

/-- Boundary of the `k`-th round counted from `N`, every mark occurring on an edge strictly inside
`[roundEnd N k, roundEnd N (k+1))`. -/
private noncomputable def roundEnd (hacc : MarksRecur edgeMarks numMarks σ) (N : Nat) : Nat → Nat
  | 0 => N
  | k + 1 => coverFrom hacc numMarks (roundEnd hacc N k) + 1

private theorem roundEnd_lt_succ (hacc : MarksRecur edgeMarks numMarks σ) (N k : Nat) :
    roundEnd hacc N k < roundEnd hacc N (k + 1) := by
  show roundEnd hacc N k < coverFrom hacc numMarks (roundEnd hacc N k) + 1
  have := coverFrom_ge hacc numMarks (roundEnd hacc N k)
  omega

private theorem roundEnd_lt_of_lt (hacc : MarksRecur edgeMarks numMarks σ) (N : Nat) {i j : Nat}
    (h : i < j) : roundEnd hacc N i < roundEnd hacc N j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact Nat.lt_trans (ih hlt) (roundEnd_lt_succ hacc N j)
    · have : i = j := by omega
      rw [this]
      exact roundEnd_lt_succ hacc N j

private theorem roundEnd_le_of_le (hacc : MarksRecur edgeMarks numMarks σ) (N : Nat) {i j : Nat}
    (h : i ≤ j) : roundEnd hacc N i ≤ roundEnd hacc N j := by
  rcases Nat.lt_or_ge i j with hlt | hge
  · exact Nat.le_of_lt (roundEnd_lt_of_lt hacc N hlt)
  · rw [Nat.le_antisymm h hge]; exact Nat.le_refl _

private theorem roundEnd_covers (hacc : MarksRecur edgeMarks numMarks σ) {m : Nat} (hm : m < numMarks)
    (N k : Nat) :
    ∃ n, roundEnd hacc N k ≤ n ∧ n + 1 ≤ roundEnd hacc N (k + 1) ∧
      m ∈ edgeMarks (σ n) (σ (n + 1)) := by
  obtain ⟨n, h1, h2, h3⟩ := coverFrom_covers hacc hm hm (roundEnd hacc N k)
  exact ⟨n, h1, by show n + 1 ≤ coverFrom hacc numMarks (roundEnd hacc N k) + 1; omega, h3⟩

end RoundBoundaries

/-! ## The pumping lemma -/

section Pumping

variable {State : Type u}

/-- A run hitting every mark infinitely often yields a `TAcceptingCycle` whose cycle lies entirely at or past `N`. -/
theorem exists_TAcceptingCycle_of_run_tail {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} {initialStates : List State}
    (fr : FiniteReach initialStates succs) {σ : Nat → State} (hinit : σ 0 ∈ initialStates)
    (htrans : ∀ n, σ (n + 1) ∈ succs (σ n))
    (hacc : ∀ m, m < numMarks → ∀ N, ∃ n ≥ N, m ∈ edgeMarks (σ n) (σ (n + 1))) (N : Nat) :
    ∃ ac : TAcceptingCycle initialStates succs edgeMarks numMarks,
      ∀ s ∈ ac.cycle, ∃ n, N ≤ n ∧ s = σ n := by
  obtain ⟨i, j, hij, heq⟩ :=
    fr.exists_lt_sample_eq (Reachable.of_run hinit htrans) (roundEnd hacc N)
  have hpq : roundEnd hacc N i < roundEnd hacc N j := roundEnd_lt_of_lt hacc N hij
  have hNp : N ≤ roundEnd hacc N i := roundEnd_le_of_le hacc N (Nat.zero_le i)
  set p := roundEnd hacc N i with hp
  set q := roundEnd hacc N j with hq
  have hstem_get : ∀ i, (hi : i < p + 1) →
      ((List.range (p + 1)).map σ)[i]'(by simpa using hi) = σ i := by
    intro i hi; simp
  have hcycle_get : ∀ i, (hi : i < q - p) →
      ((List.range (q - p)).map (fun k => σ (p + k)))[i]'(by simpa using hi) = σ (p + i) := by
    intro i hi; simp
  -- the successor index wraps at the end of the cycle, where `heq` identifies `σ p` with `σ q`
  have hwrap : ∀ i, i < q - p → σ (p + (i + 1) % (q - p)) = σ (p + i + 1) := by
    intro i hi
    rcases Nat.lt_or_ge (i + 1) (q - p) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt, Nat.add_assoc]
    · have h1 : i + 1 = q - p := by omega
      rw [h1, Nat.mod_self, Nat.add_zero]
      have h2 : p + i + 1 = q := by omega
      rw [h2]
      exact heq
  refine ⟨{
    stem := (List.range (p + 1)).map σ
    cycle := (List.range (q - p)).map (fun k => σ (p + k))
    stem_nonempty := by simp
    cycle_nonempty := by simp; omega
    stem_head_initial := by
      rw [List.head_eq_getElem, hstem_get 0 (by omega)]
      exact hinit
    stem_chain := by
      intro i hi
      simp only [List.length_map, List.length_range] at hi
      rw [hstem_get i (by omega), hstem_get (i + 1) (by omega)]
      exact htrans i
    overlap := by
      rw [List.getLast_eq_getElem, List.head_eq_getElem]
      simp only [List.length_map, List.length_range, Nat.add_sub_cancel]
      rw [hstem_get p (by omega), hcycle_get 0 (by omega)]
      rfl
    cycle_chain := by
      intro i hi
      simp only [List.length_map, List.length_range] at hi
      rw [hcycle_get i (by omega), hcycle_get (i + 1) (by omega)]
      simpa [Nat.add_assoc] using htrans (p + i)
    cycle_back := by
      rw [List.head_eq_getElem, List.getLast_eq_getElem]
      simp only [List.length_map, List.length_range]
      rw [hcycle_get 0 (by omega), hcycle_get (q - p - 1) (by omega)]
      have ht := htrans (p + (q - p - 1))
      have heq2 : p + (q - p - 1) + 1 = q := by omega
      rw [heq2] at ht
      rwa [← heq] at ht
    cycle_covers_marks := by
      intro m hm
      obtain ⟨n, hn1, hn2, hn3⟩ := roundEnd_covers hacc hm N i
      have hnq : n + 1 ≤ q := Nat.le_trans hn2 (roundEnd_le_of_le hacc N (by omega))
      refine ⟨n - p, by simpa using (by omega : n - p < q - p), ?_⟩
      simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
      rw [hwrap (n - p) (by omega)]
      have hnp : p + (n - p) = n := by omega
      rw [hnp]
      exact hn3
  }, fun s hs => ?_⟩
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hs
  exact ⟨p + k, by omega, rfl⟩

/-- A run hitting every mark infinitely often yields a `TAcceptingCycle`. -/
theorem exists_TAcceptingCycle_of_run {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} {initialStates : List State}
    (fr : FiniteReach initialStates succs) {σ : Nat → State} (hinit : σ 0 ∈ initialStates)
    (htrans : ∀ n, σ (n + 1) ∈ succs (σ n))
    (hacc : ∀ m, m < numMarks → ∀ N, ∃ n ≥ N, m ∈ edgeMarks (σ n) (σ (n + 1))) :
    ∃ _ac : TAcceptingCycle initialStates succs edgeMarks numMarks, True :=
  ⟨(exists_TAcceptingCycle_of_run_tail fr hinit htrans hacc 0).choose, trivial⟩

/-- The same with extra state predicates the run satisfies infinitely often, the cycle visiting a state satisfying
each of them. -/
theorem exists_TAcceptingCycle_of_run_marks {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} {initialStates : List State}
    (fr : FiniteReach initialStates succs) {σ : Nat → State} (hinit : σ 0 ∈ initialStates)
    (htrans : ∀ n, σ (n + 1) ∈ succs (σ n))
    (hacc : ∀ m, m < numMarks → ∀ N, ∃ n ≥ N, m ∈ edgeMarks (σ n) (σ (n + 1)))
    (N : Nat) (ps : List (State → Bool))
    (hps : ∀ p ∈ ps, ∀ K, ∃ n ≥ K, p (σ n) = true) :
    ∃ ac : TAcceptingCycle initialStates succs edgeMarks numMarks,
      (∀ s ∈ ac.cycle, ∃ n, N ≤ n ∧ s = σ n) ∧ ∀ p ∈ ps, ∃ s ∈ ac.cycle, p s = true := by
  let em' : State → State → Std.HashSet Nat := fun s t =>
    Std.HashSet.ofList ((edgeMarks s t).toList.filter (· < numMarks) ++
      (List.range ps.length).filterMap fun j =>
        if ps.getD j (fun _ => false) s then some (numMarks + j) else none)
  have hmem : ∀ s t m, m ∈ em' s t ↔ (m ∈ edgeMarks s t ∧ m < numMarks) ∨
      ∃ j, j < ps.length ∧ m = numMarks + j ∧ ps.getD j (fun _ => false) s = true := by
    intro s t m
    rw [show em' s t = _ from rfl, Std.HashSet.mem_ofList, List.contains_iff_mem, List.mem_append,
      List.mem_filter, Std.HashSet.mem_toList, List.mem_filterMap]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨j, hj, hje⟩)
      · exact Or.inl ⟨h1, by simpa using h2⟩
      · refine Or.inr ⟨j, List.mem_range.mp hj, ?_⟩
        by_cases hp : ps.getD j (fun _ => false) s = true
        · rw [if_pos hp] at hje
          exact ⟨(Option.some.inj hje).symm, hp⟩
        · rw [if_neg hp] at hje
          exact absurd hje (by simp)
    · rintro (⟨h1, h2⟩ | ⟨j, hj, rfl, hp⟩)
      · exact Or.inl ⟨h1, by simpa using h2⟩
      · exact Or.inr ⟨j, List.mem_range.mpr hj, by rw [if_pos hp]⟩
  have hacc' : ∀ m, m < numMarks + ps.length → ∀ K, ∃ n ≥ K, m ∈ em' (σ n) (σ (n + 1)) := by
    intro m hm K
    rcases Nat.lt_or_ge m numMarks with hlt | hge
    · obtain ⟨n, hn, hmn⟩ := hacc m hlt K
      exact ⟨n, hn, (hmem _ _ m).mpr (Or.inl ⟨hmn, hlt⟩)⟩
    · have hj : m - numMarks < ps.length := by omega
      have hget : ps.getD (m - numMarks) (fun _ => false) = ps[m - numMarks] :=
        (List.getElem_eq_getD _).symm
      obtain ⟨n, hn, hpn⟩ := hps ps[m - numMarks] (List.getElem_mem hj) K
      exact ⟨n, hn, (hmem _ _ m).mpr (Or.inr ⟨m - numMarks, hj, by omega, by rw [hget]; exact hpn⟩)⟩
  obtain ⟨ac, htail⟩ := exists_TAcceptingCycle_of_run_tail fr hinit htrans hacc' N
  refine ⟨{
    stem := ac.stem
    cycle := ac.cycle
    stem_nonempty := ac.stem_nonempty
    cycle_nonempty := ac.cycle_nonempty
    stem_head_initial := ac.stem_head_initial
    stem_chain := ac.stem_chain
    overlap := ac.overlap
    cycle_chain := ac.cycle_chain
    cycle_back := ac.cycle_back
    cycle_covers_marks := fun m hm => ?_ }, htail, fun p hp => ?_⟩
  · obtain ⟨i, hi, hm'⟩ := ac.cycle_covers_marks m (by omega)
    exact ⟨i, hi, (((hmem _ _ m).mp hm').resolve_right (by rintro ⟨j, -, rfl, -⟩; omega)).1⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨i, hi, hm'⟩ := ac.cycle_covers_marks (numMarks + j) (by omega)
    rcases (hmem _ _ _).mp hm' with ⟨-, hlt⟩ | ⟨j', hj', heq, hpj⟩
    · omega
    · have hjj : j' = j := by omega
      subst hjj
      rw [List.getElem_eq_getD (fallback := fun _ => false)]
      exact ⟨ac.cycle[i], List.getElem_mem hi, hpj⟩

end Pumping

end LTLLib
