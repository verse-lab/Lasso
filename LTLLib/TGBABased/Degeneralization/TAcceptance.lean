module

/-
  Abstract degeneralization of edge-indexed automata, the transition-based analogue of `OASpec.degeneralize`.
  The `k` acceptance marks of a `TOASpec` collapse into one by pairing states and edges with a counter `c : Fin k`,
  which advances when the edge taken carries the awaited mark.

  Defines:
  - `TOASpec.degeneralize`: the degeneralized single-mark automaton

  Proves:
  - `TOASpec.degeneralize_correct`: the degeneralized automaton accepts the same words as the original

  References:
  - Baier, Katoen. Principles of Model Checking, Section 4.3.3, the state-based proof followed here.

  Sections:
  - Abstract degeneralization
  - Degeneralization correctness
-/
public import LTLLib.TGBABased.AbstractSpec.Acceptance

public section

namespace LTLLib

open Lentil Classical

/-! ## Abstract degeneralization -/

/-- One-step counter update, advances when the edge taken carries the currently awaited mark. -/
@[expose] noncomputable def TOASpec.counterStep {State : Type u} {Edge : Type u'} {α : Type v} {k : Nat}
    (A : TOASpec State Edge α k) (hk : k > 0) (e : Edge) (c : Fin k) : Fin k :=
  if A.acceptMark c e then ⟨(c.val + 1) % k, Nat.mod_lt _ hk⟩ else c

/-- Counter sequence along an edge-run, starting at 0. -/
@[expose] noncomputable def TOASpec.mkCounter {State : Type u} {Edge : Type u'} {α : Type v} {k : Nat}
    (A : TOASpec State Edge α k) (hk : k > 0) (σ : exec Edge) : Nat → Fin k
  | 0 => ⟨0, hk⟩
  | n + 1 => A.counterStep hk (σ n) (A.mkCounter hk σ n)

/-- Degeneralize a `k`-mark edge-indexed automaton into a single-mark one by pairing states and edges with a counter.
The single mark requires counter 0 and the edge carrying mark 0. -/
@[expose] noncomputable def TOASpec.degeneralize {State : Type u} {Edge : Type u'} {α : Type v} {k : Nat}
    (A : TOASpec State Edge α k) (hk : k > 0) :
    TOASpec (State × Fin k) (Edge × Fin k) α 1 where
  src := fun (e, c) => (A.src e, c)
  dst := fun (e, c) => (A.dst e, A.counterStep hk e c)
  valid := fun (e, _) => A.valid e
  initial := fun (q, c) => A.initial q ∧ c = ⟨0, hk⟩
  labelCompat := fun (e, _) v => A.labelCompat e v
  acceptMark := fun _ (e, c) => c = ⟨0, hk⟩ ∧ A.acceptMark ⟨0, hk⟩ e

/-! ## Degeneralization correctness -/

section DegeneralizationCorrectness

variable {State : Type u} {Edge : Type u'} {α : Type v} {k : Nat} (A : TOASpec State Edge α k) (hk : k > 0)

private theorem counterStep_not_accept (e : Edge) (c : Fin k) (hna : ¬ A.acceptMark c e) :
    A.counterStep hk e c = c := by
  unfold TOASpec.counterStep; exact if_neg hna

private theorem counterStep_accept (e : Edge) (c : Fin k) (ha : A.acceptMark c e) :
    A.counterStep hk e c = ⟨(c.val + 1) % k, Nat.mod_lt _ hk⟩ := by
  unfold TOASpec.counterStep; exact if_pos ha

/-- Counter stays at value c as long as mark c is not carried. -/
private theorem counter_stays_at (σ : exec Edge) (n m : Nat) (c : Fin k) (hc : A.mkCounter hk σ n = c)
    (hna : ∀ p, n ≤ p → p < n + m → ¬ A.acceptMark c (σ p)) :
    A.mkCounter hk σ (n + m) = c := by
  induction m with
  | zero => simpa using hc
  | succ m ih =>
    have ih' : A.mkCounter hk σ (n + m) = c := by
      apply ih; intro p hp1 hp2; exact hna p hp1 (by omega)
    show A.mkCounter hk σ (n + m + 1) = _
    simp [TOASpec.mkCounter, ih']
    exact counterStep_not_accept A hk (σ (n + m)) c (hna (n + m) (by omega) (by omega))

/-- Counter eventually advances from c to (c+1) % k. -/
private theorem counter_advances_from (σ : exec Edge) (n : Nat) (c : Fin k) (hc : A.mkCounter hk σ n = c)
    (hvisit : ∃ j, A.acceptMark c (σ (n + j))) :
    ∃ m, n < m ∧ A.mkCounter hk σ m = ⟨(c.val + 1) % k, Nat.mod_lt _ hk⟩ := by
  obtain ⟨j, -, hj_spec, hj_min⟩ :=
    LentilLib.Nat.find_min (p := fun j => A.acceptMark c (σ (n + j))) _ hvisit.choose_spec
  have hstay : A.mkCounter hk σ (n + j) = c :=
    counter_stays_at A hk σ n j c hc (fun p hp1 hp2 => by
      have : p - n < j := by omega
      have := hj_min (p - n) this
      rwa [show n + (p - n) = p from by omega] at this)
  refine ⟨n + j + 1, by omega, ?_⟩
  simp [TOASpec.mkCounter, hstay]
  exact counterStep_accept A hk (σ (n + j)) c hj_spec

/-- Counter eventually reaches 0 from any value, given every mark is carried infinitely often. -/
private theorem counter_reaches_zero (σ : exec Edge) (n : Nat)
    (hacc : ∀ i : Fin k, ∀ n, ∃ j, A.acceptMark i (σ (n + j))) :
    ∃ m, n ≤ m ∧ (A.mkCounter hk σ m).val = 0 := by
  suffices h : ∀ (d : Nat) (n : Nat) (c : Fin k), A.mkCounter hk σ n = c → k - c.val ≤ d →
      ∃ m, n ≤ m ∧ (A.mkCounter hk σ m).val = 0 from h k n _ rfl (by omega)
  intro d
  induction d with
  | zero =>
    intro n c hc hd
    exact absurd hd (by have := c.isLt; omega)
  | succ d ih =>
    intro n c hc hd
    by_cases h0 : c.val = 0
    · exact ⟨n, Nat.le_refl n, by rw [hc]; exact h0⟩
    · obtain ⟨m, hnm, hm⟩ := counter_advances_from A hk σ n c hc (hacc c n)
      let c' : Fin k := ⟨(c.val + 1) % k, Nat.mod_lt _ hk⟩
      by_cases h0' : c'.val = 0
      · exact ⟨m, by omega, by rw [hm]; exact h0'⟩
      · have hc'lt : c.val + 1 < k := by
          by_contra hge
          have hceq : c.val + 1 = k := by have := c.isLt; omega
          exact h0' (by simp only [c']; rw [hceq, Nat.mod_self])
        have hc'eq : c'.val = c.val + 1 := by simp only [c']; exact Nat.mod_eq_of_lt hc'lt
        have hdist : k - c'.val ≤ d := by rw [hc'eq]; omega
        obtain ⟨m', hm'le, hm'zero⟩ := ih m c' hm hdist
        exact ⟨m', by omega, hm'zero⟩

/-- A counter at `v > 0` at position `c` that reaches 0 at `d ≥ c` advances past `v` somewhere in `[c, d)`. -/
private theorem counter_advance_to_next (σ : exec Edge) (c d : Nat) (v : Fin k) (hv : v.val > 0)
    (hc : A.mkCounter hk σ c = v) (hd : (A.mkCounter hk σ d).val = 0) (hcd : c ≤ d) :
    ∃ p, c ≤ p ∧ p < d ∧ A.acceptMark v (σ p) ∧
      A.mkCounter hk σ (p + 1) = ⟨(v.val + 1) % k, Nat.mod_lt _ hk⟩ := by
  have hexists : ∃ j, A.acceptMark v (σ (c + j)) := by
    by_contra h
    simp only [_root_.not_exists] at h
    have hstay := counter_stays_at A hk σ c (d - c) v hc (fun p hp1 hp2 => by
      have := h (p - c); rwa [show c + (p - c) = p by omega] at this)
    rw [show c + (d - c) = d by omega] at hstay
    have : v.val = 0 := by rw [← congrArg Fin.val hstay]; exact hd
    omega
  obtain ⟨j₀, -, hj0_spec, hj0_min⟩ :=
    LentilLib.Nat.find_min (p := fun j => A.acceptMark v (σ (c + j))) _ hexists.choose_spec
  have hstay : A.mkCounter hk σ (c + j₀) = v :=
    counter_stays_at A hk σ c j₀ v hc (fun p hp1 hp2 => by
      have := hj0_min (p - c) (by omega)
      rwa [show c + (p - c) = p by omega] at this)
  have hj0_bound : c + j₀ < d := by
    by_contra h
    rw [Nat.not_lt] at h
    have hstay_d := counter_stays_at A hk σ c (d - c) v hc (fun p hp1 hp2 => by
      have : p - c < j₀ := by omega
      have := hj0_min (p - c) this
      rwa [show c + (p - c) = p by omega] at this)
    rw [show c + (d - c) = d by omega] at hstay_d
    have : v.val = 0 := by rw [← congrArg Fin.val hstay_d]; exact hd
    omega
  refine ⟨c + j₀, by omega, hj0_bound, hj0_spec, ?_⟩
  simp [TOASpec.mkCounter, hstay]
  exact counterStep_accept A hk (σ (c + j₀)) v hj0_spec

/-- Forward direction: if the degeneralized automaton accepts, so does the original. -/
private theorem degeneralize_forward {ξ : OmegaWord α} (h : (A.degeneralize hk).accepts ξ) : A.accepts ξ := by
  obtain ⟨σ_deg, hrun, hcompat, hacc⟩ := h
  let σ_edge : exec Edge := fun n => (σ_deg n).1
  refine ⟨σ_edge, ?_, ?_, ?_⟩
  · exact ⟨(hrun.1).1, fun n => ⟨(hrun.2 n).1, congrArg Prod.fst (hrun.2 n).2⟩⟩
  · intro n; exact hcompat n
  · have hcounter : ∀ n, (σ_deg n).2 = A.mkCounter hk σ_edge n := by
      intro n; induction n with
      | zero =>
        show (σ_deg 0).2 = A.mkCounter hk σ_edge 0
        rw [TOASpec.mkCounter]; exact (hrun.1).2
      | succ n ih =>
        have hcnt := congrArg Prod.snd (hrun.2 n).2
        show (σ_deg (n + 1)).2 = A.mkCounter hk σ_edge (n + 1)
        rw [TOASpec.mkCounter, ← ih]
        exact hcnt.symm
    have hacc_ba := hacc ⟨0, by omega⟩
    have hacc' : ∀ n, ∃ j,
        (A.mkCounter hk σ_edge (n + j)).val = 0 ∧
        A.acceptMark ⟨0, hk⟩ (σ_edge (n + j)) := by
      intro n
      obtain ⟨j, hj⟩ := hacc_ba n
      refine ⟨j, ?_, ?_⟩
      · have h1 := hj.1
        rw [hcounter] at h1
        exact congrArg Fin.val h1
      · exact hj.2
    intro i n
    by_cases hi0 : i.val = 0
    · obtain ⟨j, _, hf0⟩ := hacc' n
      exact ⟨j, by rwa [show i = ⟨0, hk⟩ from Fin.ext hi0]⟩
    · have hk2 : k ≥ 2 := by have := i.isLt; omega
      obtain ⟨j₁, hm1_c0, hm1_f0⟩ := hacc' n
      let m₁ := n + j₁
      have hm1_eq : A.mkCounter hk σ_edge m₁ = ⟨0, hk⟩ := Fin.ext hm1_c0
      have hm1_next : A.mkCounter hk σ_edge (m₁ + 1) = ⟨1, by omega⟩ := by
        show A.counterStep hk (σ_edge m₁) (A.mkCounter hk σ_edge m₁) = _
        rw [hm1_eq]; unfold TOASpec.counterStep
        have hf0 : A.acceptMark ⟨0, hk⟩ (σ_edge m₁) := hm1_f0
        rw [if_pos hf0]
        have h1k : 1 < k := by omega
        exact Fin.ext (Nat.mod_eq_of_lt h1k)
      obtain ⟨j₂, hm2_c0, _⟩ := hacc' (m₁ + 1)
      let m₂ := m₁ + 1 + j₂
      suffices hsuff : ∀ w : Nat, 1 ≤ w → w ≤ i.val →
          (hwk : w < k) →
          ∃ p, m₁ + 1 ≤ p ∧ p < m₂ ∧
            A.acceptMark ⟨w, hwk⟩ (σ_edge p) ∧
            A.mkCounter hk σ_edge (p + 1) =
              ⟨(w + 1) % k, Nat.mod_lt _ hk⟩ by
        obtain ⟨p, hp1, _, hpacc, _⟩ := hsuff i.val (by omega) (Nat.le_refl _) i.isLt
        exact ⟨p - n, by rw [show n + (p - n) = p by omega]; exact hpacc⟩
      intro w
      induction w with
      | zero => intro h; omega
      | succ w ih =>
        intro hw1 hwi hwk
        by_cases hw_eq : w = 0
        · subst hw_eq
          obtain ⟨p, hlo, hhi, hacc_p, hnext_p⟩ :=
            counter_advance_to_next A hk σ_edge (m₁ + 1) m₂
              ⟨1, by omega⟩ (by simp) hm1_next hm2_c0 (by omega)
          exact ⟨p, hlo, hhi, hacc_p, hnext_p⟩
        · obtain ⟨p₁, hp1_lo, hp1_hi, _, hp1_next⟩ :=
            ih (by omega) (by omega) (by omega)
          have hw1_mod : (w + 1) % k = w + 1 :=
            Nat.mod_eq_of_lt (by omega)
          have hc_p1 : A.mkCounter hk σ_edge (p₁ + 1) = ⟨w + 1, by omega⟩ := by
            rw [hp1_next]; exact Fin.ext hw1_mod
          obtain ⟨p₂, hp2_lo, hp2_hi, hp2_acc, hp2_next⟩ :=
            counter_advance_to_next A hk σ_edge (p₁ + 1) m₂
              ⟨w + 1, by omega⟩ (Nat.succ_pos w) hc_p1 hm2_c0 (by omega)
          exact ⟨p₂, by omega, hp2_hi, hp2_acc, hp2_next⟩

/-- Backward direction: if the original automaton accepts, so does the degeneralized one. -/
private theorem degeneralize_backward {ξ : OmegaWord α} (h : A.accepts ξ) : (A.degeneralize hk).accepts ξ := by
  obtain ⟨σ_edge, hrun, hcompat, hacc⟩ := h
  let σ_deg : exec (Edge × Fin k) := fun n => (σ_edge n, A.mkCounter hk σ_edge n)
  refine ⟨σ_deg, ?_, ?_, ?_⟩
  · refine ⟨⟨hrun.1, rfl⟩, fun n => ⟨(hrun.2 n).1, ?_⟩⟩
    show (A.dst (σ_edge n), A.counterStep hk (σ_edge n) (A.mkCounter hk σ_edge n)) =
      (A.src (σ_edge (n + 1)), A.mkCounter hk σ_edge (n + 1))
    rw [(hrun.2 n).2, TOASpec.mkCounter]
  · intro n; exact hcompat n
  · intro i n
    obtain ⟨m, hnm, hm0⟩ := counter_reaches_zero A hk σ_edge n hacc
    have hvisit0 : ∃ j, A.acceptMark ⟨0, hk⟩ (σ_edge (m + j)) := hacc ⟨0, hk⟩ m
    obtain ⟨j₀, -, hj0_spec, hj0_min⟩ :=
      LentilLib.Nat.find_min (p := fun j => A.acceptMark ⟨0, hk⟩ (σ_edge (m + j))) _ hvisit0.choose_spec
    have hstay : A.mkCounter hk σ_edge (m + j₀) = ⟨0, hk⟩ :=
      counter_stays_at A hk σ_edge m j₀ ⟨0, hk⟩ (Fin.ext hm0) (fun p hp1 hp2 => by
        have := hj0_min (p - m) (show p - m < j₀ by omega)
        rwa [show m + (p - m) = p by omega] at this)
    refine ⟨m + j₀ - n, ?_⟩
    rw [show n + (m + j₀ - n) = m + j₀ by omega]
    exact ⟨hstay, hj0_spec⟩

/-- The degeneralized automaton accepts exactly the same ω-words as the original. -/
theorem TOASpec.degeneralize_correct (ξ : OmegaWord α) :
    (A.degeneralize hk).accepts ξ ↔ A.accepts ξ :=
  ⟨degeneralize_forward A hk, degeneralize_backward A hk⟩

end DegeneralizationCorrectness

end LTLLib
