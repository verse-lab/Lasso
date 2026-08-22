/-
  Abstract lasso theory: a valid lasso (stem + cycle) witnesses non-emptiness
  of a Büchi automaton.

  Given:
  - `stem = [s₀, ..., q]`       : Path from initial state to accepting state q
  - `cycle = [q, c₁, ..., cₙ]`  : Cycle starting and ending at q

  The infinite run `lassoRun stem cycle` is:
    s₀, s₁, ..., s_{m-2}, q, c₁, ..., cₙ, q, c₁, ..., cₙ, ...

  Overlap handling: `stem.getLast = cycle.head`, and the run transitions
  from `stem[m-2]` directly to `cycle[0] = q` without stuttering.

  This file is independent of any specific automaton implementation.
  It works with `OASpec` (abstract automaton specification).
-/
import LTLLib.AbstractSpec.Acceptance

namespace LTLLib

open TLA

private theorem List.ne_nil_of_length_ge_one {l : List α} (h : l.length ≥ 1) : l ≠ [] :=
  List.ne_nil_of_length_pos (by omega)

/-! ## Lasso run construction -/

/-- Construct an infinite run from a stem and a cycle.
    The stem and cycle overlap at one state: `stem.getLast = cycle.head`.
    Positions `0` to `stem.length - 2` come from the stem.
    Position `stem.length - 1` onwards cycles through `cycle`. -/
noncomputable def lassoRun {State : Type u}
    (stem cycle : List State) (default : State) : Nat → State :=
  fun i =>
    if h : i + 1 < stem.length then
      stem[i]
    else if h2 : cycle.length > 0 then
      cycle[(i - (stem.length - 1)) % cycle.length]'(Nat.mod_lt _ h2)
    else
      default

/-! ## lassoRun lemmas -/

theorem lassoRun_stem {State : Type u} (stem cycle : List State) (d : State)
    (i : Nat) (hi : i + 1 < stem.length) :
    lassoRun stem cycle d i = stem[i]'(by omega) := by
  simp [lassoRun, hi]

theorem lassoRun_cycle {State : Type u} (stem cycle : List State) (d : State)
    (hcycle : cycle.length ≥ 1)
    (i : Nat) (hi : ¬ (i + 1 < stem.length)) :
    lassoRun stem cycle d i =
    cycle[(i - (stem.length - 1)) % cycle.length]'(Nat.mod_lt _ (by omega)) := by
  simp [lassoRun, hi, show cycle.length > 0 by omega]

/-- At a general position in the cycle region with mod = 0, the run equals `cycle.head`. -/
theorem lassoRun_cycle_head {State : Type u} (stem cycle : List State) (d : State)
    (hcycle : cycle.length ≥ 1)
    (p : Nat) (hp : ¬ (p + 1 < stem.length))
    (hmod : (p - (stem.length - 1)) % cycle.length = 0) :
    lassoRun stem cycle d p =
    cycle.head (List.ne_nil_of_length_ge_one hcycle) := by
  simp only [lassoRun, hp, ↓reduceDIte, show cycle.length > 0 by omega, hmod]
  simp [List.head_eq_getElem]

/-! ## Validity conditions for a lasso -/

/-- A lasso (stem + cycle) is valid for an `OASpec` automaton with 1 acceptance set. -/
structure ValidLasso {State : Type u} {α : Type v}
    (A : OASpec State α 1) (stem cycle : List State) : Prop where
  stem_nonempty : stem.length ≥ 1
  cycle_nonempty : cycle.length ≥ 1
  stem_initial : A.initial (stem.head (List.ne_nil_of_length_ge_one stem_nonempty))
  stem_chain : ∀ (i : Nat), (hi : i + 1 < stem.length) →
    A.trans (stem[i]'(by omega)) (stem[i + 1]'(by omega))
  overlap : stem.getLast (List.ne_nil_of_length_ge_one stem_nonempty) =
            cycle.head (List.ne_nil_of_length_ge_one cycle_nonempty)
  cycle_chain : ∀ (i : Nat), (hi : i + 1 < cycle.length) →
    A.trans (cycle[i]'(by omega)) (cycle[i + 1]'(by omega))
  cycle_back : A.trans (cycle.getLast (List.ne_nil_of_length_ge_one cycle_nonempty))
                       (cycle.head (List.ne_nil_of_length_ge_one cycle_nonempty))
  cycle_accepting : A.acceptSet ⟨0, by omega⟩
                                (cycle.head (List.ne_nil_of_length_ge_one cycle_nonempty))

namespace ValidLasso

variable {State : Type u} {α : Type v} {A : OASpec State α 1}
  {stem cycle : List State}
  (hv : ValidLasso A stem cycle)

/-- The constructed run (uses `cycle.head` as default, which is always valid). -/
noncomputable def run : Nat → State :=
  lassoRun stem cycle (cycle.head (List.ne_nil_of_length_ge_one hv.cycle_nonempty))

/-! ## The run is valid (initial + transitions) -/

/-- The run starts at an initial state. -/
theorem run_initial : A.initial (hv.run 0) := by
  simp only [run]
  by_cases h : stem.length ≥ 2
  · rw [lassoRun_stem _ _ _ 0 (by omega)]
    convert hv.stem_initial using 1
    simp [List.head_eq_getElem]
  · have hslen : stem.length = 1 := by have := hv.stem_nonempty; omega
    rw [lassoRun_cycle_head _ _ _ hv.cycle_nonempty 0 (by omega) (by simp [hslen])]
    convert hv.stem_initial using 1
    rw [← hv.overlap]
    simp [List.getLast_eq_getElem, List.head_eq_getElem, hslen]

/-- Transition from one cycle position to the next (mod wrapping). -/
private theorem cycle_trans (j : Nat) :
    A.trans (cycle[j % cycle.length]'(Nat.mod_lt _ (by have := hv.cycle_nonempty; omega)))
           (cycle[(j + 1) % cycle.length]'(Nat.mod_lt _ (by have := hv.cycle_nonempty; omega))) := by
  by_cases hwrap : j % cycle.length + 1 < cycle.length
  · -- Non-wrapping case: (j+1) % len = j % len + 1
    have hmod_succ : (j + 1) % cycle.length = j % cycle.length + 1 := by
      have key := Nat.div_add_mod j cycle.length
      calc (j + 1) % cycle.length
          = (cycle.length * (j / cycle.length) + (j % cycle.length + 1)) % cycle.length := by
            congr 1; omega
        _ = (j % cycle.length + 1) % cycle.length := by rw [Nat.mul_add_mod]
        _ = j % cycle.length + 1 := Nat.mod_eq_of_lt hwrap
    simp only [hmod_succ]
    exact hv.cycle_chain (j % cycle.length) hwrap
  · -- Wrapping case: j % len = len - 1, (j+1) % len = 0
    have hclen := hv.cycle_nonempty
    have hjmod : j % cycle.length = cycle.length - 1 := by
      have := Nat.mod_lt j (show cycle.length > 0 by omega); omega
    have hmod_succ : (j + 1) % cycle.length = 0 := by
      have key := Nat.div_add_mod j cycle.length
      calc (j + 1) % cycle.length
          = (cycle.length * (j / cycle.length) + (j % cycle.length + 1)) % cycle.length := by
            congr 1; omega
        _ = (j % cycle.length + 1) % cycle.length := by rw [Nat.mul_add_mod]
        _ = (cycle.length - 1 + 1) % cycle.length := by rw [hjmod]
        _ = cycle.length % cycle.length := by congr 1; omega
        _ = 0 := Nat.mod_self cycle.length
    have hback := hv.cycle_back
    simp only [List.getLast_eq_getElem, List.head_eq_getElem] at hback
    have hcpos : cycle.length > 0 := by have := hv.cycle_nonempty; omega
    have h1 : cycle[j % cycle.length]'(Nat.mod_lt _ hcpos) =
              cycle[cycle.length - 1]'(by omega) := by congr 1
    have h2 : cycle[(j + 1) % cycle.length]'(Nat.mod_lt _ hcpos) =
              cycle[0]'(by omega) := by congr 1
    rw [h1, h2]; exact hback

/-- The run has valid transitions at every step. -/
theorem run_trans (n : Nat) : A.trans (hv.run n) (hv.run (n + 1)) := by
  simp only [run]
  by_cases h1 : n + 1 + 1 < stem.length
  · -- Both n and n+1 in stem region
    rw [lassoRun_stem _ _ _ n (by omega), lassoRun_stem _ _ _ (n + 1) h1]
    exact hv.stem_chain n (by omega)
  · by_cases h2 : n + 1 < stem.length
    · -- n in stem, n+1 at boundary
      have hneq : n + 1 = stem.length - 1 := by omega
      rw [lassoRun_stem _ _ _ n (by omega),
          lassoRun_cycle _ _ _ hv.cycle_nonempty (n + 1) (by omega)]
      rw [hneq]; simp
      have hstem_trans := hv.stem_chain (stem.length - 2) (by omega)
      have hne_stem : stem ≠ [] := List.ne_nil_of_length_ge_one (by omega)
      have h1 : stem[stem.length - 2 + 1]'(by omega) = stem.getLast hne_stem := by
        simp [List.getLast_eq_getElem]; congr; omega
      rw [h1, hv.overlap] at hstem_trans
      convert hstem_trans using 1
      · congr; omega
      · simp [List.head_eq_getElem]
    · -- Both in cycle region
      rw [lassoRun_cycle _ _ _ hv.cycle_nonempty n (by omega),
          lassoRun_cycle _ _ _ hv.cycle_nonempty (n + 1) (by omega)]
      have hoff : n + 1 - (stem.length - 1) = (n - (stem.length - 1)) + 1 := by omega
      rw [hoff]
      exact cycle_trans hv (n - (stem.length - 1))

theorem run_isRun : A.isRun hv.run :=
  ⟨hv.run_initial, hv.run_trans⟩

/-! ## The run is accepting -/

/-- The cycle head appears at position `n + j` for some `j`, for any `n`. -/
private theorem find_cycle_position (n : Nat) :
    ∃ j, hv.run (n + j) = cycle.head
      (List.ne_nil_of_length_ge_one hv.cycle_nonempty) := by
  have hcpos : cycle.length > 0 := by have := hv.cycle_nonempty; omega
  -- Find m such that stem.length - 1 + m * cycle.length ≥ n
  have hle : n ≤ stem.length - 1 + n * cycle.length :=
    le_trans (Nat.le_mul_of_pos_right n hcpos) (Nat.le_add_left ..)
  -- j = stem.length - 1 + n * cycle.length - n
  have hsum : n + (stem.length - 1 + n * cycle.length - n) =
      stem.length - 1 + n * cycle.length := by omega
  refine ⟨stem.length - 1 + n * cycle.length - n, ?_⟩
  simp only [run]
  apply lassoRun_cycle_head _ _ _ hv.cycle_nonempty
  · rw [hsum]; omega
  · rw [hsum]
    show (stem.length - 1 + n * cycle.length - (stem.length - 1)) % cycle.length = 0
    rw [show stem.length - 1 + n * cycle.length - (stem.length - 1) =
        n * cycle.length from by omega, Nat.mul_comm, Nat.mul_mod_right]

theorem run_isAccepting : A.isAcceptingRun hv.run := by
  intro i n
  obtain ⟨j, hj⟩ := find_cycle_position hv n
  refine ⟨j, ?_⟩
  rw [hj]
  have : i = ⟨0, by omega⟩ := Fin.ext (by omega)
  subst this
  exact hv.cycle_accepting

/-- A valid lasso with compatible labeling implies the automaton accepts. -/
theorem accepts_of_validLasso
    (hcompat : ∀ n, A.labelCompat (hv.run n) (ξ n)) :
    A.accepts ξ :=
  ⟨hv.run, hv.run_isRun, hcompat, hv.run_isAccepting⟩

end ValidLasso

/-! ## Connecting lasso to non-emptiness -/

/-- If a valid lasso exists with compatible labeling, the automaton's language is non-empty. -/
theorem lasso_implies_nonempty {State : Type u} {α : Type v}
    (A : OASpec State α 1) (stem cycle : List State)
    (hv : ValidLasso A stem cycle)
    (ξ : OmegaWord α)
    (hcompat : ∀ n, A.labelCompat (hv.run n) (ξ n)) :
    A.accepts ξ :=
  hv.accepts_of_validLasso hcompat

end LTLLib
