/-
  Abstract automata acceptance definitions.

  Defines `OASpec`, a unified abstract specification for both Generalized
  Büchi Automata (GBA, with `k` acceptance sets) and standard Büchi Automata
  (BA, with `k = 1`), their acceptance conditions, and the degeneralization
  construction with its correctness proof.

  Key definitions:
  - `OASpec`: Proof-level automaton with `k` acceptance sets (parameter)
  - `OASpec.degeneralize`: Abstract degeneralization construction (k → 1)

  Key theorems:
  - `degeneralize_correct`: Degeneralized BA accepts the same ω-words as the GBA

  Sections:
  - Proof-level automaton specification
  - Abstract degeneralization
  - Degeneralization correctness
  - Canonical labeling
-/
import Lentil
import LTLLib.LTL.Semantics
import Mathlib.Order.Nat

namespace LTLLib

open TLA Classical

/-! ## Proof-level automaton specification -/

/-- Abstract specification of an ω-automaton with `k` acceptance sets.
    When `k = 1`, this is a standard Büchi Automaton (BA).
    When `k > 1`, this is a Generalized Büchi Automaton (GBA).
    When `k = 0`, every run is vacuously accepting. -/
structure OASpec (State : Type u) (α : Type v) (k : Nat) where
  -- Transition relation.
  trans : State → State → Prop
  -- Initial state predicate.
  initial : State → Prop
  -- Label compatibility: state is compatible with a valuation.
  labelCompat : State → (α → Prop) → Prop
  -- Acceptance set predicate, indexed by `Fin k`.
  acceptSet : Fin k → State → Prop

namespace OASpec

variable {State : Type u} {α : Type v} {k : Nat} (A : OASpec State α k)

/-- An infinite run: initial state and valid transitions. -/
def isRun (σ : exec State) : Prop :=
  A.initial (σ 0) ∧ ∀ n, A.trans (σ n) (σ (n + 1))

/-- A run is compatible with an ω-word if each state is label-compatible
    with the corresponding position. -/
def runCompatible (σ : exec State) (ξ : OmegaWord α) : Prop :=
  ∀ n, A.labelCompat (σ n) (ξ n)

/-- A run is accepting if it visits each acceptance set infinitely often. -/
def isAcceptingRun (σ : exec State) : Prop :=
  ∀ i : Fin k, ∀ n, ∃ j, A.acceptSet i (σ (n + j))

/-- The automaton accepts an ω-word if there exists a run that is valid,
    compatible, and accepting. -/
def accepts (ξ : OmegaWord α) : Prop :=
  ∃ σ : exec State, A.isRun σ ∧ A.runCompatible σ ξ ∧ A.isAcceptingRun σ

end OASpec

/-! ## Abstract degeneralization -/

/-- One-step counter update for degeneralization.
    Advances the counter when the current acceptance set is visited. -/
noncomputable def OASpec.counterStep {State : Type u} {α : Type v} {k : Nat}
    (A : OASpec State α k) (hk : k > 0) (q : State) (c : Fin k) :
    Fin k :=
  if A.acceptSet c q
  then ⟨(c.val + 1) % k, Nat.mod_lt _ hk⟩
  else c

/-- Counter sequence for the degeneralized run, starting at 0. -/
noncomputable def OASpec.mkCounter {State : Type u} {α : Type v} {k : Nat}
    (A : OASpec State α k) (hk : k > 0) (σ : exec State) : Nat → Fin k
  | 0 => ⟨0, hk⟩
  | n + 1 => A.counterStep hk (σ n) (A.mkCounter hk σ n)

/-- Degeneralize an automaton with `k` acceptance sets into one with 1. States of the output
    are pairs `(q, c)` where `q` is the original state and `c : Fin k` is a counter that advances
    (mod k) when the current acceptance set is visited. The single acceptance set requires
    counter = 0 and the state in acceptance set 0. -/
noncomputable def OASpec.degeneralize {State : Type u} {α : Type v} {k : Nat}
    (A : OASpec State α k) (hk : k > 0) :
    OASpec (State × Fin k) α 1 where
  trans := fun (q, c) (q', c') =>
    A.trans q q' ∧ c' = A.counterStep hk q c
  initial := fun (q, c) => A.initial q ∧ c = ⟨0, hk⟩
  labelCompat := fun (q, _) v => A.labelCompat q v
  acceptSet := fun _ (q, c) =>
    c = ⟨0, hk⟩ ∧ A.acceptSet ⟨0, hk⟩ q

/-! ## Degeneralization correctness -/

section DegeneralizationCorrectness

variable {State : Type u} {α : Type v} {k : Nat} (A : OASpec State α k) (hk : k > 0)

/-- When F_c is NOT visited, counter stays at c. -/
private theorem counterStep_not_accept (q : State)
    (c : Fin k) (hna : ¬ A.acceptSet c q) :
    A.counterStep hk q c = c := by
  unfold OASpec.counterStep; exact if_neg hna

/-- When F_c IS visited, counter advances to (c+1) % k. -/
private theorem counterStep_accept (q : State)
    (c : Fin k) (ha : A.acceptSet c q) :
    A.counterStep hk q c = ⟨(c.val + 1) % k, Nat.mod_lt _ hk⟩ := by
  unfold OASpec.counterStep; exact if_pos ha

/-- Counter stays at value c as long as F_c is not visited. -/
private theorem counter_stays_at (σ : exec State) (n m : Nat)
    (c : Fin k) (hc : A.mkCounter hk σ n = c)
    (hna : ∀ p, n ≤ p → p < n + m → ¬ A.acceptSet c (σ p)) :
    A.mkCounter hk σ (n + m) = c := by
  induction m with
  | zero => simpa using hc
  | succ m ih =>
    have ih' : A.mkCounter hk σ (n + m) = c := by
      apply ih; intro p hp1 hp2; exact hna p hp1 (by omega)
    show A.mkCounter hk σ (n + m + 1) = _
    simp [OASpec.mkCounter, ih']
    exact counterStep_not_accept A hk (σ (n + m)) c (hna (n + m) (by omega) (by omega))

/-- Counter eventually advances from c to (c+1) % k. -/
private theorem counter_advances_from (σ : exec State) (n : Nat)
    (c : Fin k) (hc : A.mkCounter hk σ n = c)
    (hvisit : ∃ j, A.acceptSet c (σ (n + j))) :
    ∃ m, n < m ∧
      A.mkCounter hk σ m = ⟨(c.val + 1) % k, Nat.mod_lt _ hk⟩ := by
  let j := Nat.find hvisit
  have hj_spec : A.acceptSet c (σ (n + j)) := Nat.find_spec hvisit
  have hj_min : ∀ m, m < j → ¬ A.acceptSet c (σ (n + m)) :=
    fun m hm => Nat.find_min hvisit hm
  have hstay : A.mkCounter hk σ (n + j) = c :=
    counter_stays_at A hk σ n j c hc (fun p hp1 hp2 => by
      have : p - n < j := by omega
      have := hj_min (p - n) this
      rwa [show n + (p - n) = p from by omega] at this)
  refine ⟨n + j + 1, by omega, ?_⟩
  simp [OASpec.mkCounter, hstay]
  exact counterStep_accept A hk (σ (n + j)) c hj_spec

/-- Counter eventually reaches 0 from any value, given all acceptance sets are visited infinitely often. -/
private theorem counter_reaches_zero (σ : exec State) (n : Nat)
    (hacc : ∀ i : Fin k, ∀ n, ∃ j, A.acceptSet i (σ (n + j))) :
    ∃ m, n ≤ m ∧ (A.mkCounter hk σ m).val = 0 := by
  suffices h : ∀ (d : Nat) (n : Nat) (c : Fin k),
      A.mkCounter hk σ n = c → k - c.val ≤ d →
      ∃ m, n ≤ m ∧ (A.mkCounter hk σ m).val = 0 from
    h k n _ rfl (by omega)
  intro d
  induction d with
  | zero =>
    intro n c hc hd
    exact absurd hd (by have := c.isLt; omega)
  | succ d ih =>
    intro n c hc hd
    by_cases h0 : c.val = 0
    · exact ⟨n, le_refl n, by rw [hc]; exact h0⟩
    · obtain ⟨m, hnm, hm⟩ := counter_advances_from A hk σ n c hc (hacc c n)
      let c' : Fin k := ⟨(c.val + 1) % k, Nat.mod_lt _ hk⟩
      by_cases h0' : c'.val = 0
      · exact ⟨m, by omega, by rw [hm]; exact h0'⟩
      · have hc'lt : c.val + 1 < k := by
          by_contra hge
          push_neg at hge
          have hceq : c.val + 1 = k := by have := c.isLt; omega
          exact h0' (by simp only [c']; rw [hceq, Nat.mod_self])
        have hc'eq : c'.val = c.val + 1 := by
          simp only [c']; exact Nat.mod_eq_of_lt hc'lt
        have hdist : k - c'.val ≤ d := by rw [hc'eq]; omega
        obtain ⟨m', hm'le, hm'zero⟩ := ih m c' hm hdist
        exact ⟨m', by omega, hm'zero⟩

/-- If counter is at v > 0 at position c, and counter reaches 0 at position d ≥ c,
    then acceptSet v is visited somewhere in [c, d), and the counter advances there. -/
private theorem counter_advance_to_next (σ : exec State) (c d : Nat)
    (v : Fin k) (hv : v.val > 0)
    (hc : A.mkCounter hk σ c = v)
    (hd : (A.mkCounter hk σ d).val = 0)
    (hcd : c ≤ d) :
    ∃ p, c ≤ p ∧ p < d ∧
      A.acceptSet v (σ p) ∧
      A.mkCounter hk σ (p + 1) = ⟨(v.val + 1) % k, Nat.mod_lt _ hk⟩ := by
  have hexists : ∃ j, A.acceptSet v (σ (c + j)) := by
    by_contra h
    push_neg at h
    have hstay := counter_stays_at A hk σ c (d - c) v hc (fun p hp1 hp2 => by
      have := h (p - c); rwa [show c + (p - c) = p by omega] at this)
    rw [show c + (d - c) = d by omega] at hstay
    have : v.val = 0 := by rw [← congrArg Fin.val hstay]; exact hd
    omega
  let j₀ := Nat.find hexists
  have hj0_spec := Nat.find_spec hexists
  have hj0_min : ∀ q, q < j₀ → ¬ A.acceptSet v (σ (c + q)) :=
    fun q hq => Nat.find_min hexists hq
  have hstay : A.mkCounter hk σ (c + j₀) = v :=
    counter_stays_at A hk σ c j₀ v hc (fun p hp1 hp2 => by
      have := hj0_min (p - c) (by omega)
      rwa [show c + (p - c) = p by omega] at this)
  have hj0_bound : c + j₀ < d := by
    by_contra h
    push_neg at h
    have hstay_d := counter_stays_at A hk σ c (d - c) v hc (fun p hp1 hp2 => by
      have : p - c < j₀ := by omega
      have := hj0_min (p - c) this
      rwa [show c + (p - c) = p by omega] at this)
    rw [show c + (d - c) = d by omega] at hstay_d
    have : v.val = 0 := by rw [← congrArg Fin.val hstay_d]; exact hd
    omega
  refine ⟨c + j₀, by omega, hj0_bound, hj0_spec, ?_⟩
  simp [OASpec.mkCounter, hstay]
  exact counterStep_accept A hk (σ (c + j₀)) v hj0_spec

/-- Forward direction: if the degeneralized BA accepts, so does the GBA. -/
private theorem degeneralize_forward {ξ : OmegaWord α}
    (h : (A.degeneralize hk).accepts ξ) : A.accepts ξ := by
  obtain ⟨σ_ba, hrun, hcompat, hacc⟩ := h
  let σ_gba : exec State := fun n => (σ_ba n).1
  refine ⟨σ_gba, ?_, ?_, ?_⟩
  · constructor
    · exact (hrun.1).1
    · intro n; exact (hrun.2 n).1
  · intro n; exact hcompat n
  · intro i
    have hcounter : ∀ n, (σ_ba n).2 = A.mkCounter hk σ_gba n := by
      intro n; induction n with
      | zero => exact (hrun.1).2 ▸ (by simp [OASpec.mkCounter])
      | succ n ih =>
        have htrans := (hrun.2 n).2
        simp [OASpec.mkCounter, σ_gba, ← ih]; exact htrans
    have hacc_ba := hacc ⟨0, by omega⟩
    have hacc' : ∀ n, ∃ j,
        (A.mkCounter hk σ_gba (n + j)).val = 0 ∧
        A.acceptSet ⟨0, hk⟩ (σ_gba (n + j)) := by
      intro n
      obtain ⟨j, hj⟩ := hacc_ba n
      refine ⟨j, ?_, ?_⟩
      · have h1 := hj.1
        simp at h1
        rw [hcounter] at h1
        exact congrArg Fin.val h1
      · exact hj.2
    intro n
    by_cases hi0 : i.val = 0
    · obtain ⟨j, _, hf0⟩ := hacc' n
      exact ⟨j, by rwa [show i = ⟨0, hk⟩ from Fin.ext hi0]⟩
    · have hk2 : k ≥ 2 := by have := i.isLt; omega
      obtain ⟨j₁, hm1_c0, hm1_f0⟩ := hacc' n
      let m₁ := n + j₁
      have hm1_eq : A.mkCounter hk σ_gba m₁ = ⟨0, hk⟩ := Fin.ext hm1_c0
      have hm1_next : A.mkCounter hk σ_gba (m₁ + 1) = ⟨1, by omega⟩ := by
        show A.counterStep hk (σ_gba m₁) (A.mkCounter hk σ_gba m₁) = _
        rw [hm1_eq]; unfold OASpec.counterStep
        have hf0 : A.acceptSet ⟨0, hk⟩ (σ_gba m₁) := hm1_f0
        rw [if_pos hf0]
        have h1k : 1 < k := by omega
        exact Fin.ext (Nat.mod_eq_of_lt h1k)
      obtain ⟨j₂, hm2_c0, _⟩ := hacc' (m₁ + 1)
      let m₂ := m₁ + 1 + j₂
      suffices hsuff : ∀ w : Nat, (hw1 : 1 ≤ w) → (hwi : w ≤ i.val) →
          (hwk : w < k) →
          ∃ p, m₁ + 1 ≤ p ∧ p < m₂ ∧
            A.acceptSet ⟨w, by omega⟩ (σ_gba p) ∧
            A.mkCounter hk σ_gba (p + 1) =
              ⟨(w + 1) % k, Nat.mod_lt _ hk⟩ by
        obtain ⟨p, hp1, _, hpacc, _⟩ := hsuff i.val (by omega) le_rfl i.isLt
        exact ⟨p - n, by rw [show n + (p - n) = p by omega]; exact hpacc⟩
      intro w
      induction w with
      | zero => intro h; omega
      | succ w ih =>
        intro hw1 hwi hwk
        by_cases hw_eq : w = 0
        · subst hw_eq
          obtain ⟨p, hlo, hhi, hacc_p, hnext_p⟩ :=
            counter_advance_to_next A hk σ_gba (m₁ + 1) m₂
              ⟨1, by omega⟩ (by simp) hm1_next hm2_c0 (by omega)
          exact ⟨p, hlo, hhi, hacc_p, hnext_p⟩
        · obtain ⟨p₁, hp1_lo, hp1_hi, _, hp1_next⟩ :=
            ih (by omega) (by omega) (by omega)
          have hw1_mod : (w + 1) % k = w + 1 :=
            Nat.mod_eq_of_lt (by omega)
          have hc_p1 : A.mkCounter hk σ_gba (p₁ + 1) = ⟨w + 1, by omega⟩ := by
            rw [hp1_next]; exact Fin.ext hw1_mod
          obtain ⟨p₂, hp2_lo, hp2_hi, hp2_acc, hp2_next⟩ :=
            counter_advance_to_next A hk σ_gba (p₁ + 1) m₂
              ⟨w + 1, by omega⟩ (Nat.succ_pos w) hc_p1 hm2_c0 (by omega)
          exact ⟨p₂, by omega, hp2_hi, hp2_acc, hp2_next⟩

/-- Backward direction: if the GBA accepts, so does the degeneralized BA. -/
private theorem degeneralize_backward {ξ : OmegaWord α}
    (h : A.accepts ξ) : (A.degeneralize hk).accepts ξ := by
  obtain ⟨σ_gba, hrun, hcompat, hacc⟩ := h
  let σ_ba : exec (State × Fin k) :=
    fun n => (σ_gba n, A.mkCounter hk σ_gba n)
  refine ⟨σ_ba, ?_, ?_, ?_⟩
  · constructor
    · exact ⟨hrun.1, rfl⟩
    · intro n; exact ⟨hrun.2 n, rfl⟩
  · intro n; exact hcompat n
  · intro i n
    obtain ⟨m, hnm, hm0⟩ := counter_reaches_zero A hk σ_gba n hacc
    have hvisit0 : ∃ j, A.acceptSet ⟨0, hk⟩ (σ_gba (m + j)) := hacc ⟨0, hk⟩ m
    let j₀ := Nat.find hvisit0
    have hj0_spec : A.acceptSet ⟨0, hk⟩ (σ_gba (m + j₀)) := Nat.find_spec hvisit0
    have hstay : A.mkCounter hk σ_gba (m + j₀) = ⟨0, hk⟩ :=
      counter_stays_at A hk σ_gba m j₀ ⟨0, hk⟩ (Fin.ext hm0) (fun p hp1 hp2 => by
        have := Nat.find_min hvisit0 (show p - m < j₀ by omega)
        rwa [show m + (p - m) = p by omega] at this)
    refine ⟨m + j₀ - n, ?_⟩
    rw [show n + (m + j₀ - n) = m + j₀ by omega]
    show (A.degeneralize hk).acceptSet i (σ_ba (m + j₀))
    simp only [OASpec.degeneralize, σ_ba]
    exact ⟨hstay, hj0_spec⟩

/-- The degeneralized BA accepts exactly the same ω-words as the GBA. -/
theorem degeneralize_correct (ξ : OmegaWord α) :
    (A.degeneralize hk).accepts ξ ↔ A.accepts ξ :=
  ⟨degeneralize_forward A hk, degeneralize_backward A hk⟩

end DegeneralizationCorrectness

/-! ## Canonical labeling

`labelCompat` is a relation. A state may be compatible with many valuations
(it only constrains atoms actually mentioned in `pos`/`neg`).
-/

/-- The canonical valuation at state `q`: true exactly on `q`'s positive
atoms (per `labeling`), `False` everywhere if `q` isn't in `labeling`'s domain. -/
def canonicalLabel {α : Type u} [BEq α] [Hashable α]
    (labeling : Std.HashMap Nat (Std.HashSet α × Std.HashSet α)) (q : Nat) :
    α → Prop :=
  fun a => (labeling[q]?).elim False (fun p => p.1.contains a)

/-- `canonicalLabel` satisfies a state's label-compatibility constraint,
given the state's positive/negative atom sets are disjoint. -/
theorem canonicalLabel_compat {α : Type u} [BEq α] [Hashable α]
    {labeling : Std.HashMap Nat (Std.HashSet α × Std.HashSet α)}
    {q : Nat} {pos neg : Std.HashSet α} (hlab : labeling[q]? = some (pos, neg))
    (hdisjoint : ∀ a, pos.contains a → neg.contains a → False) :
    (∀ a, pos.contains a → canonicalLabel labeling q a) ∧
    (∀ a, neg.contains a → ¬ canonicalLabel labeling q a) := by
  refine ⟨fun a ha => by simp only [canonicalLabel, hlab, Option.elim]; exact ha,
    fun a ha hpos => ?_⟩
  simp only [canonicalLabel, hlab, Option.elim] at hpos
  exact hdisjoint a hpos ha

end LTLLib
