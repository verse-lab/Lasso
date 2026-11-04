module

/-
  Syntactic recognisers for the fairness class, and the classifier that routes a conjunct of a fairness
  assumption to a mechanism.

  [LSFZ16, Definition 1] defines a fairness as a formula whose language is closed under suffixes and under
  prepending finite prefixes. Those two closures are exactly Etessami and Holzmann's purely universal and pure
  eventuality classes, so `isFairness` is their conjunction and needs no further argument. The published
  CONCUR'00 pure eventuality grammar has a typo, `ψ₁ U γ` where it should be `γ U ψ₁`, corrected here.

  Deviation from [EH00]. Two rules are generalised, both by dropping a condition on a binary operator's left
  operand. [EH00]'s pure eventuality grammar has `e R e` and this file has `f R e`, and its purely universal
  grammar has `u U u` and this file has `f U u`. The soundness proofs below use only the right operand's closure,
  so strictly more formulas are recognised, for instance `a R F b` and `a U G b`, at no cost.

  Key definitions:
  - `isPureEventuality`, `isPurelyUniversal`, `isFairness`: the two grammars and their conjunction
  - `isLTLFG`, `isLTLUX`: the `F`/`G`-only and `U`/`X`-only fragments
  - `isFastFair`: [LSFZ16, Definition 4]'s class, on which `fnf` stays linear rather than exponential
  - `classify`: which route a conjunct takes

  Key theorems:
  - `isPureEventuality_sound`: a pure eventuality holding at a suffix holds at the whole word
  - `isPurelyUniversal_sound`: a purely universal formula holding at a word holds at every suffix
  - `eventually_of_isPureEventuality`, `always_of_isPurelyUniversal`: `F e ≡ e` and `G u ≡ u`
  - `isFairness_alwaysEventually`: `φ ≡ GF φ` for a fairness, the precondition `fnf` needs

  References:
  - [LSFZ16] Li, Song, Feng, Zhang. Verify LTL with Fairness Assumptions Efficiently. arXiv:1606.08116, 2016.
    Definition 1 and Lemma 1 for the class, Definition 4 for the no-blowup fragment.
  - [EH00] Etessami, Holzmann. Optimizing Büchi Automata. CONCUR'00. The two grammars.

  Sections:
  - Shape helpers
  - The two grammars
  - Fragments
  - Soundness of the pure eventuality grammar
  - Soundness of the purely universal grammar
  - Fairness
  - Routing
-/
public import Lasso.LTL.Semantics

public section

namespace Lasso

open Lentil

namespace NNF

variable {α : Type u}

/-! ## Shape helpers

`F` and `G` are `⊤ U ψ` and `⊥ R ψ` in `NNF`, so the grammars need to see those two shapes apart from a
general `U` or `R`.
-/

/-- Is this `⊤`, the left operand that makes `φ U ψ` an `F`? -/
@[expose] def isTop : NNF α → Bool
  | .tt => true
  | _ => false

/-- Is this `⊥`, the left operand that makes `φ R ψ` a `G`? -/
@[expose] def isBot : NNF α → Bool
  | .ff => true
  | _ => false

theorem eq_tt_of_isTop {φ : NNF α} (h : φ.isTop = true) : φ = .tt := by
  cases φ <;> simp_all [isTop]

theorem eq_ff_of_isBot {φ : NNF α} (h : φ.isBot = true) : φ = .ff := by
  cases φ <;> simp_all [isBot]

/-! ## The two grammars -/

/-- A pure eventuality, whose language is closed under prepending a finite prefix, so `F e ≡ e`.
Grammar: `e ::= ⊤ | ⊥ | X e | F f | e ∧ e | e ∨ e | f U e | f R e`, where `G e = ⊥ R e` is the last rule at
`f = ⊥`. The last rule generalises [EH00]'s `e R e`, see the deviation note in the file header. -/
@[expose] def isPureEventuality : NNF α → Bool
  | .tt | .ff => true
  | .prop _ | .nprop _ => false
  | .and φ ψ | .or φ ψ => isPureEventuality φ && isPureEventuality ψ
  | .next φ => isPureEventuality φ
  | .until φ ψ => φ.isTop || isPureEventuality ψ
  | .release _ ψ => isPureEventuality ψ

/-- A purely universal formula, whose language is closed under suffixes, so `G u ≡ u`.
Grammar: `u ::= ⊤ | ⊥ | X u | G f | u ∧ u | u ∨ u | f U u | f R u`, where `F u = ⊤ U u` is the `f U u` rule at
`f = ⊤`. That rule generalises [EH00]'s `u U u`, see the deviation note in the file header. -/
@[expose] def isPurelyUniversal : NNF α → Bool
  | .tt | .ff => true
  | .prop _ | .nprop _ => false
  | .and φ ψ | .or φ ψ => isPurelyUniversal φ && isPurelyUniversal ψ
  | .next φ => isPurelyUniversal φ
  | .until _ ψ => isPurelyUniversal ψ
  | .release φ ψ => φ.isBot || isPurelyUniversal ψ

/-- A fairness in the sense of [LSFZ16, Definition 1], both closures at once. -/
@[expose] def isFairness (φ : NNF α) : Bool := φ.isPureEventuality && φ.isPurelyUniversal

/-! ## Fragments -/

/-- The `LTL(F, G)` fragment, where the only modalities are `F` and `G`. -/
def isLTLFG : NNF α → Bool
  | .tt | .ff | .prop _ | .nprop _ => true
  | .and φ ψ | .or φ ψ => isLTLFG φ && isLTLFG ψ
  | .next _ => false
  | .until φ ψ => φ.isTop && isLTLFG ψ
  | .release φ ψ => φ.isBot && isLTLFG ψ

/-- The `LTL(U, X)` fragment, the co-safety formulas [LSFZ16] leaves innermost in the temporal normal form. -/
def isLTLUX : NNF α → Bool
  | .tt | .ff | .prop _ | .nprop _ => true
  | .and φ ψ | .or φ ψ => isLTLUX φ && isLTLUX ψ
  | .next φ => isLTLUX φ
  | .until φ ψ => isLTLUX φ && isLTLUX ψ
  | .release _ _ => false

/-- [LSFZ16, Definition 4]'s `φ₀ ::= φ₁ | F φ₀ | G φ₀ | φ₀ ∧ φ₀`, with `φ₁` co-safety. -/
def isFastConj : NNF α → Bool
  | .and φ ψ => isFastConj φ && isFastConj ψ
  | .until φ ψ => (φ.isTop && isFastConj ψ) || (isLTLUX φ && isLTLUX ψ)
  | .release φ ψ => φ.isBot && isFastConj ψ
  | φ => isLTLUX φ

/-- [LSFZ16, Definition 4]'s `φ_f ::= φ₀ | φ_f ∨ φ_f`, on which the flattening stays linear in `|φ|`. -/
@[expose] def isFastFair : NNF α → Bool
  | .or φ ψ => isFastFair φ && isFastFair ψ
  | φ => isFastConj φ

/-! ## Soundness of the pure eventuality grammar -/

/-- [LSFZ16, Definition 1, clause 2]. Holding at a suffix implies holding at the whole word, which is closure
under prepending a finite prefix stated without having to build the prefix. -/
theorem isPureEventuality_sound : ∀ (φ : NNF α), φ.isPureEventuality = true →
    ∀ (ξ : OmegaWord α) (k : Nat), φ.satisfies (ξ.drop k) → φ.satisfies ξ := by
  intro φ
  induction φ with
  | tt => intro _ ξ _ _; exact (satisfies_tt ξ).mpr trivial
  | ff => intro _ _ _ hs; exact hs
  | prop a => intro h; simp [isPureEventuality] at h
  | nprop a => intro h; simp [isPureEventuality] at h
  | and φ ψ ihφ ihψ =>
    intro h ξ k hs
    simp only [isPureEventuality, Bool.and_eq_true] at h
    rw [satisfies_and] at hs ⊢
    exact ⟨ihφ h.1 ξ k hs.1, ihψ h.2 ξ k hs.2⟩
  | or φ ψ ihφ ihψ =>
    intro h ξ k hs
    simp only [isPureEventuality, Bool.and_eq_true] at h
    rw [satisfies_or] at hs ⊢
    exact hs.imp (ihφ h.1 ξ k) (ihψ h.2 ξ k)
  | next φ ih =>
    intro h ξ k hs
    rw [satisfies_next] at hs ⊢
    refine ih h (ξ.drop 1) k ?_
    rwa [exec.drop_drop, Nat.add_comm, ← exec.drop_drop]
  | «until» φ ψ _ ihψ =>
    intro h ξ k hs
    obtain ⟨i, hψ, hφ⟩ := (satisfies_until _ _ _).mp hs
    rw [exec.drop_drop] at hψ
    by_cases htop : φ.isTop = true
    -- `F ψ`, the witness index simply shifts by `k`
    · refine (satisfies_until _ _ _).mpr ⟨k + i, hψ, fun j _ => ?_⟩
      rw [eq_tt_of_isTop htop]
      exact (satisfies_tt _).mpr trivial
    -- `f U e`, the right operand already holds at the whole word so index `0` witnesses it
    · simp only [isPureEventuality, htop, Bool.false_or] at h
      exact (satisfies_until _ _ _).mpr
        ⟨0, by rw [exec_drop_zero]; exact ihψ h ξ (k + i) hψ, fun j hj => absurd hj (by omega)⟩
  | release φ ψ _ ihψ =>
    intro h ξ k hs
    simp only [isPureEventuality] at h
    -- The right operand holds at `ξ.drop k`, the `j = 0` instance having no earlier witness available.
    have hψk : ψ.satisfies (ξ.drop k) := by
      rcases (satisfies_release _ _ _).mp hs 0 with hψ | ⟨i, hi, -⟩
      · rwa [exec_drop_zero] at hψ
      · omega
    refine (satisfies_release _ _ _).mpr fun j => ?_
    by_cases hjk : j ≤ k
    -- Before the shift, the right operand still holds, being a pure eventuality
    · refine Or.inl (ihψ h (ξ.drop j) (k - j) ?_)
      rwa [exec.drop_drop, show j + (k - j) = k from by omega]
    -- After the shift, the original disjunction at index `j - k` transfers
    · rcases (satisfies_release _ _ _).mp hs (j - k) with hψ | ⟨i, hi, hφ⟩
      · rw [exec.drop_drop, show k + (j - k) = j from by omega] at hψ
        exact Or.inl hψ
      · rw [exec.drop_drop] at hφ
        exact Or.inr ⟨k + i, by omega, hφ⟩

/-- `F e ≡ e` for a pure eventuality. -/
theorem eventually_of_isPureEventuality {φ : NNF α} (h : φ.isPureEventuality = true)
    (ξ : OmegaWord α) : (NNF.eventually φ).satisfies ξ ↔ φ.satisfies ξ := by
  rw [satisfies_eventually]
  exact ⟨fun ⟨k, hk⟩ => isPureEventuality_sound φ h ξ k hk,
    fun hs => ⟨0, by rwa [exec_drop_zero]⟩⟩

/-! ## Soundness of the purely universal grammar -/

/-- [LSFZ16, Definition 1, clause 1]. Holding at a word implies holding at every suffix. -/
theorem isPurelyUniversal_sound : ∀ (φ : NNF α), φ.isPurelyUniversal = true →
    ∀ (ξ : OmegaWord α) (k : Nat), φ.satisfies ξ → φ.satisfies (ξ.drop k) := by
  intro φ
  induction φ with
  | tt => intro _ ξ k _; exact (satisfies_tt _).mpr trivial
  | ff => intro _ _ _ hs; exact hs.elim
  | prop a => intro h; simp [isPurelyUniversal] at h
  | nprop a => intro h; simp [isPurelyUniversal] at h
  | and φ ψ ihφ ihψ =>
    intro h ξ k hs
    simp only [isPurelyUniversal, Bool.and_eq_true] at h
    rw [satisfies_and] at hs ⊢
    exact ⟨ihφ h.1 ξ k hs.1, ihψ h.2 ξ k hs.2⟩
  | or φ ψ ihφ ihψ =>
    intro h ξ k hs
    simp only [isPurelyUniversal, Bool.and_eq_true] at h
    rw [satisfies_or] at hs ⊢
    exact hs.imp (ihφ h.1 ξ k) (ihψ h.2 ξ k)
  | next φ ih =>
    intro h ξ k hs
    rw [satisfies_next] at hs ⊢
    rw [exec.drop_drop, Nat.add_comm, ← exec.drop_drop]
    exact ih h (ξ.drop 1) k hs
  | «until» φ ψ _ ihψ =>
    intro h ξ k hs
    simp only [isPurelyUniversal] at h
    obtain ⟨i, hψ, hφ⟩ := (satisfies_until _ _ _).mp hs
    by_cases hki : k ≤ i
    -- The witness is still ahead, so it just shifts back by `k`
    · refine (satisfies_until _ _ _).mpr ⟨i - k, ?_, fun j hj => ?_⟩
      · rwa [exec.drop_drop, show k + (i - k) = i from by omega]
      · rw [exec.drop_drop]; exact hφ (k + j) (by omega)
    -- The witness is behind, and the right operand carries forward, being purely universal
    · refine (satisfies_until _ _ _).mpr ⟨0, ?_, fun j hj => absurd hj (by omega)⟩
      rw [exec_drop_zero]
      have hstep := ihψ h (ξ.drop i) (k - i) hψ
      rwa [exec.drop_drop, show i + (k - i) = k from by omega] at hstep
  | release φ ψ _ ihψ =>
    intro h ξ k hs
    by_cases hbot : φ.isBot = true
    -- `G ψ`, every index of the shifted word is an index of the original
    · refine (satisfies_release _ _ _).mpr fun j => Or.inl ?_
      rcases (satisfies_release _ _ _).mp hs (k + j) with hψ | ⟨i, -, hφ⟩
      · rwa [exec.drop_drop]
      · rw [eq_ff_of_isBot hbot] at hφ; exact hφ.elim
    -- `f R u`, the right operand holds at index `0` and, being purely universal, then everywhere
    · simp only [isPurelyUniversal, hbot, Bool.false_or] at h
      have hψ0 : ψ.satisfies ξ := by
        rcases (satisfies_release _ _ _).mp hs 0 with hψ | ⟨i, hi, -⟩
        · rwa [exec_drop_zero] at hψ
        · omega
      refine (satisfies_release _ _ _).mpr fun j => Or.inl ?_
      rw [exec.drop_drop]
      exact ihψ h ξ (k + j) hψ0

/-- `G u ≡ u` for a purely universal formula. -/
theorem always_of_isPurelyUniversal {φ : NNF α} (h : φ.isPurelyUniversal = true)
    (ξ : OmegaWord α) : (NNF.always φ).satisfies ξ ↔ φ.satisfies ξ := by
  rw [satisfies_always]
  exact ⟨fun hk => by have := hk 0; rwa [exec_drop_zero] at this,
    fun hs k => isPurelyUniversal_sound φ h ξ k hs⟩

/-! ## Fairness -/

/-- [LSFZ16, Lemma 1]. A fairness is unchanged by prefixing `GF`, which is what lets `fnf` start by adding it. -/
theorem isFairness_alwaysEventually {φ : NNF α} (h : φ.isFairness = true) (ξ : OmegaWord α) :
    (NNF.always (NNF.eventually φ)).satisfies ξ ↔ φ.satisfies ξ := by
  simp only [isFairness, Bool.and_eq_true] at h
  rw [satisfies_always]
  constructor
  · intro hk
    have := hk 0
    rw [exec_drop_zero, eventually_of_isPureEventuality h.1] at this
    exact this
  · intro hs k
    rw [eventually_of_isPureEventuality h.1]
    exact isPurelyUniversal_sound φ h.2 ξ k hs

/-! ## Routing -/

/-- Which mechanism a conjunct of a fairness assumption is routed to. -/
inductive FairRoute where
  -- Not a fairness at all, so it stays in the property and goes through the translator.
  | notFairness
  -- A fairness in `LTL(F, G)`, which `fnf` flattens into `FG`/`GF` disjuncts.
  | fgFragment
  -- A fairness with `U` or `X` inside, which needs the temporal route.
  | temporal
deriving Repr, DecidableEq, BEq, Hashable, Inhabited

/-- Classify a conjunct, first by whether it is a fairness at all, then by which fragment it falls in. -/
@[expose] def classify (φ : NNF α) : FairRoute :=
  if φ.isFairness then (if φ.isLTLFG then .fgFragment else .temporal) else .notFairness

theorem classify_eq_notFairness {φ : NNF α} (h : φ.isFairness = false) :
    φ.classify = .notFairness := by simp [classify, h]

theorem isFairness_of_classify_ne {φ : NNF α} (h : φ.classify ≠ .notFairness) :
    φ.isFairness = true := by
  by_contra hc
  exact h (classify_eq_notFairness (by simpa using hc))

end NNF

end Lasso
