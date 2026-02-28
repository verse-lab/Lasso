/-
  Proof-level automata acceptance definitions.

  Defines abstract specifications for Generalized Büchi Automata (GBA) and
  standard Büchi Automata (BA), their acceptance conditions, and the
  degeneralization construction with its correctness proof.

  Key definitions:
  - `GBASpec`: Proof-level GBA with multiple acceptance sets
  - `BASpec`: Proof-level BA with single acceptance set
  - `GBASpec.degeneralize`: Abstract degeneralization construction
  - `GBA.toSpec`: Bridge from computational `GBA` to `GBASpec`

  Key theorems:
  - `degeneralize_correct`: Degeneralized BA accepts the same ω-words as the GBA
-/
import Lentil
import LTLLib.GBA
import LTLLib.BA
import LTLLib.LTL.Semantics
import Mathlib.Order.Nat

namespace LTLLib

open TLA Classical

/-! ## Proof-level GBA specification -/

/-- Abstract specification of a Generalized Büchi Automaton.
    Parametrized by state type `State` and atomic proposition type `α`. -/
structure GBASpec (State : Type) (α : Type) where
  /-- Transition relation. -/
  trans : State → State → Prop
  /-- Initial state predicate. -/
  initial : State → Prop
  /-- Label compatibility: state is compatible with a valuation. -/
  labelCompat : State → (α → Prop) → Prop
  /-- Number of acceptance sets. -/
  numAcceptSets : Nat
  /-- Acceptance set predicate, indexed by `Fin numAcceptSets`. -/
  acceptSet : Fin numAcceptSets → State → Prop

namespace GBASpec

variable {State : Type} {α : Type} (A : GBASpec State α)

/-- An infinite run of the GBA: initial state and valid transitions. -/
def IsRun (σ : exec State) : Prop :=
  A.initial (σ 0) ∧ ∀ k, A.trans (σ k) (σ (k + 1))

/-- A run is compatible with an ω-word if each state is label-compatible
    with the corresponding position. -/
def RunCompatible (σ : exec State) (ξ : OmegaWord α) : Prop :=
  ∀ k, A.labelCompat (σ k) (ξ k)

/-- A run is GBA-accepting if it visits each acceptance set infinitely often. -/
def IsAccepting (σ : exec State) : Prop :=
  ∀ i : Fin A.numAcceptSets, ∀ k, ∃ j, A.acceptSet i (σ (k + j))

/-- The GBA accepts an ω-word if there exists a run that is valid,
    compatible, and accepting. -/
def Accepts (ξ : OmegaWord α) : Prop :=
  ∃ σ : exec State, A.IsRun σ ∧ A.RunCompatible σ ξ ∧ A.IsAccepting σ

end GBASpec

/-! ## Proof-level BA specification -/

/-- Abstract specification of a (standard) Büchi Automaton.
    Has a single set of accepting states instead of multiple acceptance sets. -/
structure BASpec (State : Type) (α : Type) where
  /-- Transition relation. -/
  trans : State → State → Prop
  /-- Initial state predicate. -/
  initial : State → Prop
  /-- Label compatibility. -/
  labelCompat : State → (α → Prop) → Prop
  /-- Accepting state predicate. -/
  accepting : State → Prop

namespace BASpec

variable {State : Type} {α : Type} (A : BASpec State α)

/-- An infinite run of the BA. -/
def IsRun (σ : exec State) : Prop :=
  A.initial (σ 0) ∧ ∀ k, A.trans (σ k) (σ (k + 1))

/-- A run is compatible with an ω-word. -/
def RunCompatible (σ : exec State) (ξ : OmegaWord α) : Prop :=
  ∀ k, A.labelCompat (σ k) (ξ k)

/-- A run is BA-accepting if it visits an accepting state infinitely often. -/
def IsAccepting (σ : exec State) : Prop :=
  ∀ k, ∃ j, A.accepting (σ (k + j))

/-- The BA accepts an ω-word if there exists a valid, compatible,
    accepting run. -/
def Accepts (ξ : OmegaWord α) : Prop :=
  ∃ σ : exec State, A.IsRun σ ∧ A.RunCompatible σ ξ ∧ A.IsAccepting σ

end BASpec

/-! ## Abstract degeneralization -/

/-- One-step counter update for degeneralization.
    Advances the counter when the current acceptance set is visited. -/
noncomputable def GBASpec.counterStep {State : Type} {α : Type}
    (A : GBASpec State α) (q : State) (c : Fin (max 1 A.numAcceptSets)) :
    Fin (max 1 A.numAcceptSets) :=
  if h : A.numAcceptSets = 0 then c
  else
    let k := A.numAcceptSets
    have hk : k > 0 := Nat.pos_of_ne_zero h
    if A.acceptSet ⟨c.val % k, Nat.mod_lt _ hk⟩ q
    then ⟨(c.val + 1) % (max 1 k), Nat.mod_lt _ (by omega)⟩
    else c

/-- Counter sequence for the degeneralized run, starting at 0. -/
noncomputable def GBASpec.mkCounter {State : Type} {α : Type}
    (A : GBASpec State α) (σ : exec State) : Nat → Fin (max 1 A.numAcceptSets)
  | 0 => ⟨0, by omega⟩
  | n + 1 => A.counterStep (σ n) (A.mkCounter σ n)

/-- Degeneralize a GBA spec into a BA spec.

    States of the BA are pairs `(q, c)` where `q` is a GBA state and
    `c : Fin (max 1 numAcceptSets)` is the acceptance counter.

    The counter advances (mod k) when the current acceptance set is visited.
    Accepting states have counter = 0 AND (when k > 0) the state is in
    acceptance set 0. This prevents trivial acceptance when the counter
    never advances. -/
noncomputable def GBASpec.degeneralize {State : Type} {α : Type}
    (A : GBASpec State α) :
    BASpec (State × Fin (max 1 A.numAcceptSets)) α where
  trans := fun (q, c) (q', c') =>
    A.trans q q' ∧ c' = A.counterStep q c
  initial := fun (q, c) => A.initial q ∧ c = ⟨0, by omega⟩
  labelCompat := fun (q, _) v => A.labelCompat q v
  accepting := fun (q, c) =>
    c = ⟨0, by omega⟩ ∧
    if h : A.numAcceptSets = 0 then True
    else A.acceptSet ⟨0, Nat.pos_of_ne_zero h⟩ q

/-! ## Degeneralization correctness -/

section DegeneralizationCorrectness

variable {State : Type} {α : Type} (A : GBASpec State α)

/-- When counter is at 0 and F_0 is not visited, counter stays at 0. -/
private theorem counterStep_zero_not_accept (q : State) (hk : A.numAcceptSets > 0)
    (hna : ¬ A.acceptSet ⟨0, hk⟩ q) :
    A.counterStep q ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  unfold GBASpec.counterStep
  have hne : A.numAcceptSets ≠ 0 := by omega
  simp [dif_neg hne]
  intro h
  exact absurd h (by simpa using hna)

/-- When counter is at 0 and F_0 IS visited, counter advances to 1 (mod max 1 k). -/
private theorem counterStep_zero_accept (q : State) (hk : A.numAcceptSets > 0)
    (ha : A.acceptSet ⟨0, hk⟩ q) :
    A.counterStep q ⟨0, by omega⟩ = ⟨1 % (max 1 A.numAcceptSets), Nat.mod_lt _ (by omega)⟩ := by
  unfold GBASpec.counterStep
  have hne : A.numAcceptSets ≠ 0 := by omega
  simp [dif_neg hne]
  intro h
  exact absurd (by simpa using ha) h

/-- Counter stays at 0 as long as F_0 is not visited. -/
private theorem counter_stays_zero (σ : exec State) (n m : Nat)
    (hk : A.numAcceptSets > 0)
    (hc : A.mkCounter σ n = ⟨0, by omega⟩)
    (hna : ∀ p, n ≤ p → p < n + m → ¬ A.acceptSet ⟨0, hk⟩ (σ p)) :
    A.mkCounter σ (n + m) = ⟨0, by omega⟩ := by
  induction m with
  | zero => simpa using hc
  | succ m ih =>
    have ih' : A.mkCounter σ (n + m) = ⟨0, by omega⟩ := by
      apply ih; intro p hp1 hp2; exact hna p hp1 (by omega)
    show A.mkCounter σ (n + m + 1) = _
    simp [GBASpec.mkCounter, ih']
    exact counterStep_zero_not_accept A (σ (n + m)) hk (hna (n + m) (by omega) (by omega))

/-- Generalized: when F_c is NOT visited, counter stays at c. -/
private theorem counterStep_not_accept_gen (q : State)
    (c : Fin (max 1 A.numAcceptSets))
    (hk : A.numAcceptSets > 0)
    (hna : ¬ A.acceptSet ⟨c.val, by have := c.isLt; omega⟩ q) :
    A.counterStep q c = c := by
  unfold GBASpec.counterStep
  have hne : A.numAcceptSets ≠ 0 := by omega
  rw [dif_neg hne]
  have hmod : c.val % A.numAcceptSets = c.val :=
    Nat.mod_eq_of_lt (by have := c.isLt; omega)
  have : ¬ A.acceptSet ⟨c.val % A.numAcceptSets, Nat.mod_lt _ (by omega)⟩ q := by
    rwa [show (⟨c.val % A.numAcceptSets, Nat.mod_lt _ (by omega)⟩ : Fin A.numAcceptSets) =
      ⟨c.val, by have := c.isLt; omega⟩ from Fin.ext hmod]
  simp [if_neg this]

/-- Generalized: when F_c IS visited, counter advances. -/
private theorem counterStep_accept_gen (q : State)
    (c : Fin (max 1 A.numAcceptSets))
    (hk : A.numAcceptSets > 0)
    (ha : A.acceptSet ⟨c.val, by have := c.isLt; omega⟩ q) :
    A.counterStep q c = ⟨(c.val + 1) % (max 1 A.numAcceptSets),
      Nat.mod_lt _ (by omega)⟩ := by
  unfold GBASpec.counterStep
  have hne : A.numAcceptSets ≠ 0 := by omega
  rw [dif_neg hne]
  have hmod : c.val % A.numAcceptSets = c.val :=
    Nat.mod_eq_of_lt (by have := c.isLt; omega)
  have : A.acceptSet ⟨c.val % A.numAcceptSets, Nat.mod_lt _ (by omega)⟩ q := by
    rwa [show (⟨c.val % A.numAcceptSets, Nat.mod_lt _ (by omega)⟩ : Fin A.numAcceptSets) =
      ⟨c.val, by have := c.isLt; omega⟩ from Fin.ext hmod]
  simp [if_pos this]

/-- Counter stays at value c as long as F_c is not visited (generalization of counter_stays_zero). -/
private theorem counter_stays_at (σ : exec State) (n m : Nat)
    (c : Fin (max 1 A.numAcceptSets))
    (hk : A.numAcceptSets > 0)
    (hc : A.mkCounter σ n = c)
    (hna : ∀ p, n ≤ p → p < n + m → ¬ A.acceptSet ⟨c.val, by have := c.isLt; omega⟩ (σ p)) :
    A.mkCounter σ (n + m) = c := by
  induction m with
  | zero => simpa using hc
  | succ m ih =>
    have ih' : A.mkCounter σ (n + m) = c := by
      apply ih; intro p hp1 hp2; exact hna p hp1 (by omega)
    show A.mkCounter σ (n + m + 1) = _
    simp [GBASpec.mkCounter, ih']
    exact counterStep_not_accept_gen A (σ (n + m)) c hk (hna (n + m) (by omega) (by omega))

/-- Counter eventually advances from c to (c+1) % max 1 k.
    Uses Nat.find to locate the first visit to F_c, then counter_stays_at
    to show counter is still at c at that point. -/
private theorem counter_advances_from (σ : exec State) (n : Nat)
    (c : Fin (max 1 A.numAcceptSets))
    (hk : A.numAcceptSets > 0)
    (hc : A.mkCounter σ n = c)
    (hvisit : ∃ j, A.acceptSet ⟨c.val, by have := c.isLt; omega⟩ (σ (n + j))) :
    ∃ m, n < m ∧
      A.mkCounter σ m = ⟨(c.val + 1) % (max 1 A.numAcceptSets),
        Nat.mod_lt _ (by omega)⟩ := by
  -- Find the first j such that F_c is visited at σ (n + j)
  let j := Nat.find hvisit
  have hj_spec : A.acceptSet ⟨c.val, _⟩ (σ (n + j)) := Nat.find_spec hvisit
  have hj_min : ∀ m, m < j → ¬ A.acceptSet ⟨c.val, _⟩ (σ (n + m)) :=
    fun m hm => Nat.find_min hvisit hm
  -- Counter stays at c until position n + j
  have hstay : A.mkCounter σ (n + j) = c :=
    counter_stays_at A σ n j c hk hc (fun p hp1 hp2 => by
      have : p - n < j := by omega
      have := hj_min (p - n) this
      rwa [show n + (p - n) = p from by omega] at this)
  -- At n + j, F_c is visited, so counter advances
  refine ⟨n + j + 1, by omega, ?_⟩
  simp [GBASpec.mkCounter, hstay]
  exact counterStep_accept_gen A (σ (n + j)) c hk hj_spec

/-- Counter eventually reaches 0 from any value, given all acceptance sets
    are visited infinitely often. -/
private theorem counter_reaches_zero (σ : exec State) (n : Nat)
    (hk : A.numAcceptSets > 0)
    (hacc : ∀ i : Fin A.numAcceptSets, ∀ k, ∃ j, A.acceptSet i (σ (k + j))) :
    ∃ m, n ≤ m ∧ (A.mkCounter σ m).val = 0 := by
  -- Induction on fuel = max 1 k, using distance k - c.val as decreasing measure
  suffices h : ∀ (d : Nat) (n : Nat) (c : Fin (max 1 A.numAcceptSets)),
      A.mkCounter σ n = c → max 1 A.numAcceptSets - c.val ≤ d →
      ∃ m, n ≤ m ∧ (A.mkCounter σ m).val = 0 from
    h (max 1 A.numAcceptSets) n _ rfl (by omega)
  intro d
  induction d with
  | zero =>
    intro n c hc hd
    exact absurd hd (by have := c.isLt; omega)
  | succ d ih =>
    intro n c hc hd
    by_cases h0 : c.val = 0
    · exact ⟨n, le_refl n, by rw [hc]; exact h0⟩
    · -- Counter at c > 0; advance to (c+1) % max 1 k
      have hcv : c.val < A.numAcceptSets := by have := c.isLt; omega
      obtain ⟨m, hnm, hm⟩ := counter_advances_from A σ n c hk hc
        (hacc ⟨c.val, hcv⟩ n)
      let c' : Fin (max 1 A.numAcceptSets) :=
        ⟨(c.val + 1) % (max 1 A.numAcceptSets), Nat.mod_lt _ (by omega)⟩
      by_cases h0' : c'.val = 0
      · -- Counter reached 0 after one advance
        exact ⟨m, by omega, by rw [hm]; exact h0'⟩
      · -- Counter still not 0; c+1 < max 1 k so c'.val = c.val + 1
        have hc'lt : c.val + 1 < max 1 A.numAcceptSets := by
          by_contra hge
          push_neg at hge
          have hceq : c.val + 1 = max 1 A.numAcceptSets := by
            have := c.isLt; omega
          have : (c.val + 1) % max 1 A.numAcceptSets = 0 := by
            rw [hceq, Nat.mod_self]
          exact h0' this
        have hc'eq : c'.val = c.val + 1 := by
          simp only [c']
          exact Nat.mod_eq_of_lt hc'lt
        have hdist : max 1 A.numAcceptSets - c'.val ≤ d := by
          rw [hc'eq]; omega
        obtain ⟨m', hm'le, hm'zero⟩ := ih m c' hm hdist
        exact ⟨m', by omega, hm'zero⟩

/-- If counter is at v > 0 at position c, and counter reaches 0 at position d ≥ c,
    then acceptSet v is visited somewhere in [c, d), and the counter advances there. -/
private theorem counter_advance_to_next (σ : exec State) (c d : Nat)
    (v : Fin (max 1 A.numAcceptSets))
    (hk : A.numAcceptSets > 0)
    (hv : v.val > 0)
    (hc : A.mkCounter σ c = v)
    (hd : (A.mkCounter σ d).val = 0)
    (hcd : c ≤ d) :
    ∃ p, c ≤ p ∧ p < d ∧
      A.acceptSet ⟨v.val, by have := v.isLt; omega⟩ (σ p) ∧
      A.mkCounter σ (p + 1) = ⟨(v.val + 1) % max 1 A.numAcceptSets,
        Nat.mod_lt _ (by omega)⟩ := by
  -- Find the first visit to F_v after c
  have hexists : ∃ j, A.acceptSet ⟨v.val, by have := v.isLt; omega⟩ (σ (c + j)) := by
    -- If F_v is never visited in [c, d), counter stays at v, contradicting counter(d) = 0
    by_contra h
    push_neg at h
    have hstay := counter_stays_at A σ c (d - c) v hk hc (fun p hp1 hp2 => by
      have := h (p - c); rwa [show c + (p - c) = p by omega] at this)
    rw [show c + (d - c) = d by omega] at hstay
    have : v.val = 0 := by rw [← congrArg Fin.val hstay]; exact hd
    omega
  let j₀ := Nat.find hexists
  have hj0_spec := Nat.find_spec hexists
  have hj0_min : ∀ q, q < j₀ → ¬ A.acceptSet ⟨v.val, _⟩ (σ (c + q)) :=
    fun q hq => Nat.find_min hexists hq
  -- Counter stays at v from c to c + j₀
  have hstay : A.mkCounter σ (c + j₀) = v :=
    counter_stays_at A σ c j₀ v hk hc (fun p hp1 hp2 => by
      have := hj0_min (p - c) (by omega)
      rwa [show c + (p - c) = p by omega] at this)
  -- j₀ < d - c (otherwise counter(d) would be v ≠ 0)
  have hj0_bound : c + j₀ < d := by
    by_contra h
    push_neg at h
    have hstay_d := counter_stays_at A σ c (d - c) v hk hc (fun p hp1 hp2 => by
      have : p - c < j₀ := by omega
      have := hj0_min (p - c) this
      rwa [show c + (p - c) = p by omega] at this)
    rw [show c + (d - c) = d by omega] at hstay_d
    have : v.val = 0 := by rw [← congrArg Fin.val hstay_d]; exact hd
    omega
  refine ⟨c + j₀, by omega, hj0_bound, hj0_spec, ?_⟩
  simp [GBASpec.mkCounter, hstay]
  exact counterStep_accept_gen A (σ (c + j₀)) v hk hj0_spec

/-- Forward direction: if the degeneralized BA accepts, so does the GBA.
    Project the BA run onto its state component to get a GBA run. -/
private theorem degeneralize_forward {ξ : OmegaWord α}
    (h : A.degeneralize.Accepts ξ) : A.Accepts ξ := by
  obtain ⟨σ_ba, hrun, hcompat, hacc⟩ := h
  let σ_gba : exec State := fun k => (σ_ba k).1
  refine ⟨σ_gba, ?_, ?_, ?_⟩
  · -- IsRun
    constructor
    · exact (hrun.1).1
    · intro k; exact (hrun.2 k).1
  · -- RunCompatible
    intro k; exact hcompat k
  · -- IsAccepting
    intro i
    by_cases h0 : A.numAcceptSets = 0
    · have := i.isLt; omega
    · have hk : A.numAcceptSets > 0 := Nat.pos_of_ne_zero h0
      -- Establish: (σ_ba n).2 = A.mkCounter σ_gba n
      have hcounter : ∀ n, (σ_ba n).2 = A.mkCounter σ_gba n := by
        intro n; induction n with
        | zero => exact (hrun.1).2 ▸ (by simp [GBASpec.mkCounter])
        | succ n ih =>
          have htrans := (hrun.2 n).2
          simp [GBASpec.mkCounter, σ_gba, ← ih]; exact htrans
      -- Extract BA acceptance info using counter correspondence
      have hacc' : ∀ n, ∃ j,
          (A.mkCounter σ_gba (n + j)).val = 0 ∧
          A.acceptSet ⟨0, hk⟩ (σ_gba (n + j)) := by
        intro n
        obtain ⟨j, hj⟩ := hacc n
        refine ⟨j, ?_, ?_⟩
        · have h1 := hj.1
          simp at h1
          rw [hcounter] at h1
          exact congrArg Fin.val h1
        · have h2 := hj.2
          simp [dif_neg h0] at h2
          exact h2
      intro n
      -- Case i = 0: directly from BA acceptance
      by_cases hi0 : i.val = 0
      · obtain ⟨j, _, hf0⟩ := hacc' n
        exact ⟨j, by rwa [show i = ⟨0, hk⟩ from Fin.ext hi0]⟩
      · -- Case i > 0: chain counter advances between two accepting positions
        have hi_pos : i.val ≥ 1 := by omega
        have hk2 : A.numAcceptSets ≥ 2 := by have := i.isLt; omega
        -- Step 1: find m₁ ≥ n with counter = 0 ∧ F_0
        obtain ⟨j₁, hm1_c0, hm1_f0⟩ := hacc' n
        let m₁ := n + j₁
        -- counter(m₁) = ⟨0, _⟩
        have hm1_eq : A.mkCounter σ_gba m₁ = ⟨0, by omega⟩ := Fin.ext hm1_c0
        -- counter(m₁+1) advances to ⟨1, _⟩ (since k ≥ 2, 1 % k = 1)
        have hm1_next : A.mkCounter σ_gba (m₁ + 1) = ⟨1, by omega⟩ := by
          unfold GBASpec.mkCounter
          rw [hm1_eq, counterStep_zero_accept A (σ_gba m₁) hk hm1_f0]
          exact Fin.ext (Nat.mod_eq_of_lt (by omega))
        -- Step 2: find m₂ > m₁ with counter = 0
        obtain ⟨j₂, hm2_c0, _⟩ := hacc' (m₁ + 1)
        let m₂ := m₁ + 1 + j₂
        -- Step 3: chain counter_advance_to_next from value 1 up to value i
        -- Key claim: ∀ w with 1 ≤ w ≤ i.val, ∃ position in [m₁+1, m₂)
        --   where acceptSet w is visited and counter advances
        suffices hsuff : ∀ w : Nat, (hw1 : 1 ≤ w) → (hwi : w ≤ i.val) →
            (hwk : w < A.numAcceptSets) →
            ∃ p, m₁ + 1 ≤ p ∧ p < m₂ ∧
              A.acceptSet ⟨w, by omega⟩ (σ_gba p) ∧
              A.mkCounter σ_gba (p + 1) =
                ⟨(w + 1) % max 1 A.numAcceptSets, Nat.mod_lt _ (by omega)⟩ by
          obtain ⟨p, hp1, _, hpacc, _⟩ := hsuff i.val (by omega) le_rfl i.isLt
          exact ⟨p - n, by rw [show n + (p - n) = p by omega]; exact hpacc⟩
        intro w
        induction w with
        | zero => intro h; omega
        | succ w ih =>
          intro hw1 hwi hwk
          by_cases hw_eq : w = 0
          · -- w+1 = 1: use counter_advance_to_next from m₁+1 (counter = 1)
            subst hw_eq
            have hone : (⟨1, by omega⟩ : Fin (max 1 A.numAcceptSets)).val > 0 := by
              simp
            obtain ⟨p, hlo, hhi, hacc_p, hnext_p⟩ :=
              counter_advance_to_next A σ_gba (m₁ + 1) m₂
                ⟨1, by omega⟩ hk hone hm1_next hm2_c0 (by omega)
            exact ⟨p, hlo, hhi, hacc_p, hnext_p⟩
          · -- w+1 > 1: use IH for w, then counter_advance_to_next
            obtain ⟨p₁, hp1_lo, hp1_hi, _, hp1_next⟩ :=
              ih (by omega) (by omega) (by omega)
            -- counter(p₁+1) = (w+1) % max 1 k. Since w+1 < k, this is w+1.
            have hw1_mod : (w + 1) % max 1 A.numAcceptSets = w + 1 :=
              Nat.mod_eq_of_lt (by omega)
            have hc_p1 : A.mkCounter σ_gba (p₁ + 1) = ⟨w + 1, by omega⟩ := by
              rw [hp1_next]; exact Fin.ext hw1_mod
            have hw1_pos : (⟨w + 1, by omega⟩ :
                Fin (max 1 A.numAcceptSets)).val > 0 := Nat.succ_pos w
            obtain ⟨p₂, hp2_lo, hp2_hi, hp2_acc, hp2_next⟩ :=
              counter_advance_to_next A σ_gba (p₁ + 1) m₂
                ⟨w + 1, by omega⟩ hk hw1_pos hc_p1 hm2_c0 (by omega)
            exact ⟨p₂, by omega, hp2_hi, hp2_acc, hp2_next⟩

/-- Backward direction: if the GBA accepts, so does the degeneralized BA.
    Construct the acceptance counter from the GBA run. -/
private theorem degeneralize_backward {ξ : OmegaWord α}
    (h : A.Accepts ξ) : A.degeneralize.Accepts ξ := by
  obtain ⟨σ_gba, hrun, hcompat, hacc⟩ := h
  -- The BA run pairs each GBA state with its counter value
  let σ_ba : exec (State × Fin (max 1 A.numAcceptSets)) :=
    fun n => (σ_gba n, A.mkCounter σ_gba n)
  refine ⟨σ_ba, ?_, ?_, ?_⟩
  · -- IsRun
    constructor
    · -- Initial: σ_gba 0 is initial and counter starts at 0
      exact ⟨hrun.1, rfl⟩
    · -- Transitions
      intro n
      exact ⟨hrun.2 n, rfl⟩
  · -- RunCompatible
    intro k; exact hcompat k
  · -- IsAccepting
    intro n
    by_cases h0 : A.numAcceptSets = 0
    · -- No acceptance sets: counter is always 0, and acceptance is trivially true
      refine ⟨0, ?_⟩
      simp [GBASpec.degeneralize]
      constructor
      · -- counter = ⟨0, _⟩
        have : ∀ m, (A.mkCounter σ_gba m).val = 0 := by
          intro m; induction m with
          | zero => simp [GBASpec.mkCounter]
          | succ m ih =>
            simp [GBASpec.mkCounter, GBASpec.counterStep, h0]
            exact ih
        exact Fin.ext (this (n + 0))
      · simp [h0]
    · -- k > 0: need counter = 0 ∧ acceptSet 0
      have hk : A.numAcceptSets > 0 := Nat.pos_of_ne_zero h0
      -- Step 1: Find m ≥ n where counter reaches 0
      obtain ⟨m, hnm, hm0⟩ := counter_reaches_zero A σ_gba n hk hacc
      -- Step 2: F_0 is visited i.o.; find first visit after m
      have hvisit0 : ∃ j, A.acceptSet ⟨0, hk⟩ (σ_gba (m + j)) := hacc ⟨0, hk⟩ m
      let j₀ := Nat.find hvisit0
      have hj0_spec : A.acceptSet ⟨0, hk⟩ (σ_gba (m + j₀)) := Nat.find_spec hvisit0
      -- Step 3: Counter stays at 0 from m to m + j₀
      have hstay : A.mkCounter σ_gba (m + j₀) = ⟨0, by omega⟩ :=
        counter_stays_zero A σ_gba m j₀ hk (Fin.ext hm0) (fun p hp1 hp2 => by
          have := Nat.find_min hvisit0 (show p - m < j₀ by omega)
          rwa [show m + (p - m) = p by omega] at this)
      -- Witness: position m + j₀
      refine ⟨m + j₀ - n, ?_⟩
      rw [show n + (m + j₀ - n) = m + j₀ by omega]
      show A.degeneralize.accepting (σ_ba (m + j₀))
      simp only [GBASpec.degeneralize, σ_ba]
      refine ⟨hstay, ?_⟩
      simp [dif_neg h0]
      exact hj0_spec

/-- The degeneralized BA accepts exactly the same ω-words as the GBA. -/
theorem degeneralize_correct (ξ : OmegaWord α) :
    A.degeneralize.Accepts ξ ↔ A.Accepts ξ :=
  ⟨degeneralize_forward A, degeneralize_backward A⟩

end DegeneralizationCorrectness

/-! ## Bridge from computational GBA to proof-level spec -/

/-- Convert a computational `GBA` to a proof-level `GBASpec`. -/
def GBA.toSpec [BEq α] [Hashable α] (gba : GBA α) : GBASpec Nat α where
  trans q q' := q' ∈ gba.getSuccessors q
  initial q := gba.isInitial q
  labelCompat q v :=
    match gba.labeling[q]? with
    | some (pos, neg) =>
      (∀ a, pos.contains a → v a) ∧ (∀ a, neg.contains a → ¬ v a)
    | none => True
  numAcceptSets := gba.numAcceptSets
  acceptSet i q := gba.isAccepting i.val q

end LTLLib
