/-
  From an accepting run to a `TAcceptingCycle` lasso witness.

  Pigeonholing on the run's marked positions is not enough per-transition, a cycle spanning two marked
  positions need not carry every mark. The run is instead cut into rounds, each long enough to contain an
  occurrence of every mark, and the pigeonhole is applied to the round boundaries, so any repeat delimits a
  cycle that has already seen all of `F`. Round-robin counting as in the standard degeneralization (Choueka,
  "Theories of Automata on ω-Tapes: A Simplified Approach", JCSS 8(2), 1974), applied to the run rather than
  to the automaton.

  Key theorems:
  - `exists_TAcceptingCycle_of_run`: a run hitting every mark infinitely often yields a `TAcceptingCycle`

  Sections:
  - Round boundaries
  - The pumping lemma
-/
import LTLLib.TGBABased.AbstractSpec.EmptinessCheck

namespace LTLLib

/-! ## Round boundaries

`coverFrom k` walks marks `0 .. k-1` one at a time from a given start, and `roundEnd` iterates a full sweep of
all `numMarks` of them. The extra `+ 1` at each level keeps the sequence strictly increasing even when
`numMarks = 0`, where a window would otherwise be empty and the pigeonhole would find only `i = j`.
-/

section RoundBoundaries

variable {State : Type u} {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} {σ : Nat → State}

/-- Marks recur forever along `σ`, what every definition in this section is indexed by. -/
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
  | zero => rw [Nat.le_zero.mp h]
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with hlt | hge
    · exact le_trans (ih (by omega)) (le_of_lt (coverFrom_lt_succ hacc k' N))
    · rw [Nat.le_antisymm h hge]

/-- Every mark below `k` occurs on an edge inside `[N, coverFrom k N)`. -/
private theorem coverFrom_covers (hacc : MarksRecur edgeMarks numMarks σ) {m k : Nat} (hm : m < numMarks)
    (hmk : m < k) (N : Nat) :
    ∃ n, N ≤ n ∧ n + 1 ≤ coverFrom hacc k N ∧ m ∈ edgeMarks (σ n) (σ (n + 1)) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge m k with hlt | hge
    · obtain ⟨n, h1, h2, h3⟩ := ih hlt
      exact ⟨n, h1, le_trans h2 (le_of_lt (coverFrom_lt_succ hacc k N)), h3⟩
    · -- `m = k`, so this sweep's own pick is the witness and the window ends exactly one past it
      have hmk' : m = k := by omega
      subst hmk'
      exact ⟨nextMark hacc m (coverFrom hacc m N),
        le_trans (coverFrom_ge hacc m N) (nextMark_ge hacc m _), Nat.le_refl _, nextMark_spec hacc hm _⟩

/-- Boundary of the `k`-th round, every mark occurs on an edge strictly inside `[roundEnd k, roundEnd (k+1))`. -/
private noncomputable def roundEnd (hacc : MarksRecur edgeMarks numMarks σ) : Nat → Nat
  | 0 => 0
  | k + 1 => coverFrom hacc numMarks (roundEnd hacc k) + 1

private theorem roundEnd_lt_succ (hacc : MarksRecur edgeMarks numMarks σ) (k : Nat) :
    roundEnd hacc k < roundEnd hacc (k + 1) := by
  show roundEnd hacc k < coverFrom hacc numMarks (roundEnd hacc k) + 1
  have := coverFrom_ge hacc numMarks (roundEnd hacc k)
  omega

private theorem roundEnd_lt_of_lt (hacc : MarksRecur edgeMarks numMarks σ) {i j : Nat} (h : i < j) :
    roundEnd hacc i < roundEnd hacc j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact Nat.lt_trans (ih hlt) (roundEnd_lt_succ hacc j)
    · have : i = j := by omega
      rw [this]
      exact roundEnd_lt_succ hacc j

private theorem roundEnd_le_of_le (hacc : MarksRecur edgeMarks numMarks σ) {i j : Nat} (h : i ≤ j) :
    roundEnd hacc i ≤ roundEnd hacc j := by
  rcases Nat.lt_or_ge i j with hlt | hge
  · exact le_of_lt (roundEnd_lt_of_lt hacc hlt)
  · rw [Nat.le_antisymm h hge]

private theorem roundEnd_covers (hacc : MarksRecur edgeMarks numMarks σ) {m : Nat} (hm : m < numMarks)
    (k : Nat) :
    ∃ n, roundEnd hacc k ≤ n ∧ n + 1 ≤ roundEnd hacc (k + 1) ∧ m ∈ edgeMarks (σ n) (σ (n + 1)) := by
  obtain ⟨n, h1, h2, h3⟩ := coverFrom_covers hacc hm hm (roundEnd hacc k)
  exact ⟨n, h1, by show n + 1 ≤ coverFrom hacc numMarks (roundEnd hacc k) + 1; omega, h3⟩

end RoundBoundaries

/-! ## The pumping lemma -/

section Pumping

variable {State : Type u}

/-- A run hitting every mark infinitely often yields a `TAcceptingCycle`. Round boundaries repeat by
finiteness, and the window between two equal ones is a cycle that has already seen every mark. -/
theorem exists_TAcceptingCycle_of_run {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {numMarks : Nat} {initialStates : List State}
    (fr : FiniteReach initialStates succs) {σ : Nat → State} (hinit : σ 0 ∈ initialStates)
    (htrans : ∀ n, σ (n + 1) ∈ succs (σ n))
    (hacc : ∀ m, m < numMarks → ∀ N, ∃ n ≥ N, m ∈ edgeMarks (σ n) (σ (n + 1))) :
    ∃ _ac : TAcceptingCycle initialStates succs edgeMarks numMarks, True := by
  obtain ⟨i, j, hij, heq⟩ :=
    fr.exists_lt_sample_eq (Reachable.of_run hinit htrans) (roundEnd hacc)
  have hpq : roundEnd hacc i < roundEnd hacc j := roundEnd_lt_of_lt hacc hij
  set p := roundEnd hacc i with hp
  set q := roundEnd hacc j with hq
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
      simpa using htrans (p + i)
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
      obtain ⟨n, hn1, hn2, hn3⟩ := roundEnd_covers hacc hm i
      have hnq : n + 1 ≤ q := le_trans hn2 (roundEnd_le_of_le hacc (by omega))
      refine ⟨n - p, by simpa using (by omega : n - p < q - p), ?_⟩
      simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
      rw [hwrap (n - p) (by omega)]
      have hnp : p + (n - p) = n := by omega
      rw [hnp]
      exact hn3
  }, trivial⟩

end Pumping

end LTLLib
