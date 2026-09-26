/-
  LTL semantics: denotation of NNF and Formula types into propositions
  over ω-words, built on Lentil's TLA temporal logic foundations.

  Key definitions:
  - `tla_release`: Release operator (dual of Until), missing from Lentil
  - `NNF.toPred`: Denotation from NNF syntax to Lentil `Lentil.pred`
  - `NNF.satisfies`: ω-word satisfies an NNF formula
  - `Formula.directSatisfies`: Independent semantics on user-facing Formula type
  - `Formula.satisfies`: Defined via NNF

  Key theorems:
  - `NNF.neg_correct`: Negation correctness for NNF
  - `toNNF_correct`: `Formula.directSatisfies` ↔ `NNF.satisfies ∘ toNNF`
  - `NNF.satisfies_splitConj`: splitting at the top-level conjunctions preserves meaning

  Sections:
  - ω-words
  - Release operator
  - NNF denotation
  - Unfolding lemmas for NNF.satisfies
  - Negation correctness
  - Formula-level semantics
  - toNNF correctness
-/
import Lentil
import LTLLib.LTL.Syntax

namespace LTLLib

open Lentil

/-! ## ω-words

An ω-word over atomic propositions of type `α` is an infinite sequence
where each position maps atoms to truth values. We use Lentil's `exec`
type instantiated at `α → Prop`. -/

/-- An ω-word over atomic propositions `α`. Each time step is a valuation
    `α → Prop` assigning truth values to atoms. -/
abbrev OmegaWord (α : Type u) := exec (α → Prop)

/-! ## Release operator

Lentil provides `tl_until` but not its dual `release`.
We define it here and prove the key properties. -/

/-- Release operator: `p R q` holds iff for every `j`, `q` holds at suffix `j` or `p` held at some `i < j`.
    Dual of Until: `p R q ≡ ¬(¬p U ¬q)`. -/
def tla_release {α : Type u} (p q : pred α) : pred α :=
  fun σ n => ∀ j, q σ (n + j) ∨ ∃ i, i < j ∧ p σ (n + i)

syntax:25 tlfml:26 " 𝑅 " tlfml:25 : tlfml

macro_rules
  | `([tlfml| $f1:tlfml 𝑅 $f2:tlfml ]) => `(LTLLib.tla_release [tlfml| $f1 ] [tlfml| $f2 ])

/-- Release is the dual of Until: `p R q ↔ ¬(¬p U ¬q)`. -/
theorem release_iff_not_until_neg {α : Type u} (p q : pred α) :
  ((p 𝑅 q)) =tl= (¬ (¬ p 𝑈 ¬ q)) := by
  funext e n ; unfold tla_release ; tunfold_simp ; grind

/-- Until is the dual of release: `p U q ↔ ¬(¬p R ¬q)`. -/
theorem until_iff_not_release_neg {α : Type u} (p q : pred α) :
  ((p 𝑈 q)) =tl= (¬ (¬ p 𝑅 ¬ q)) := by
  funext e n ; unfold tla_release ; tunfold_simp

/-- □ p = ⊥ R p. -/
theorem always_eq_release_false {α : Type u} (p : pred α) :
  (□ p) =tl= (⊥ 𝑅 p) := by
  funext e n ; unfold tla_release ; tunfold_simp

/-! ## NNF denotation -/

/-- Denotational semantics: map an NNF formula to a Lentil predicate over ω-words.
    Each ω-word position is a valuation `α → Prop`. -/
def NNF.toPred {α} : NNF α → pred (α → Prop)
  | .tt        => tl_true
  | .ff        => tl_false
  | .prop a    => state_pred (fun v => v a)
  | .nprop a   => state_pred (fun v => ¬ v a)
  | .and φ ψ   => tl_and φ.toPred ψ.toPred
  | .or φ ψ    => tl_or φ.toPred ψ.toPred
  | .next φ    => later φ.toPred
  | .until φ ψ => tl_until φ.toPred ψ.toPred
  | .release φ ψ => tla_release φ.toPred ψ.toPred

private theorem NNF.toPred_drop (φ : NNF α) (ξ : OmegaWord α) (k n : Nat) :
    φ.toPred (ξ.drop k) n = φ.toPred ξ (n + k) := by
  induction φ generalizing n with
  | _ => simp [toPred, tl_true, tl_false, pure_pred, state_pred, tl_and, tl_or,
      later, tl_until, tla_release, exec.drop, *, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

/-- An ω-word `ξ` satisfies an NNF formula `φ`. -/
def NNF.satisfies {α} (ξ : OmegaWord α) (φ : NNF α) : Prop :=
  φ.toPred ξ 0

/-! ## Unfolding lemmas for NNF.satisfies -/

/-- Suffix compatibility: satisfying at a suffix composes properly. -/
theorem NNF.satisfies_drop_drop (ξ : OmegaWord α) (k l : Nat) (φ : NNF α) :
  φ.satisfies ((ξ.drop k).drop l) ↔ φ.satisfies (ξ.drop (k + l)) := by
  simp only [NNF.satisfies, exec.drop_drop]

theorem exec_drop_zero {β : Type u} (σ : exec β) : σ.drop 0 = σ := by
  funext n; simp [exec.drop]

theorem NNF.satisfies_tt (ξ : OmegaWord α) : (NNF.tt : NNF α).satisfies ξ ↔ True := Iff.rfl

theorem NNF.satisfies_ff (ξ : OmegaWord α) : (NNF.ff : NNF α).satisfies ξ ↔ False := Iff.rfl

theorem NNF.satisfies_prop (ξ : OmegaWord α) (a : α) : (NNF.prop a).satisfies ξ ↔ ξ 0 a := Iff.rfl

theorem NNF.satisfies_nprop (ξ : OmegaWord α) (a : α) : (NNF.nprop a).satisfies ξ ↔ ¬ ξ 0 a := Iff.rfl

theorem NNF.satisfies_and (ξ : OmegaWord α) (φ ψ : NNF α) :
    (NNF.and φ ψ).satisfies ξ ↔ φ.satisfies ξ ∧ ψ.satisfies ξ := Iff.rfl

theorem NNF.satisfies_or (ξ : OmegaWord α) (φ ψ : NNF α) :
    (NNF.or φ ψ).satisfies ξ ↔ φ.satisfies ξ ∨ ψ.satisfies ξ := Iff.rfl

theorem NNF.satisfies_next (ξ : OmegaWord α) (φ : NNF α) :
    (NNF.next φ).satisfies ξ ↔ φ.satisfies (ξ.drop 1) := by
  simp [satisfies, toPred, later, toPred_drop]

theorem NNF.satisfies_until (ξ : OmegaWord α) (φ ψ : NNF α) :
    (NNF.until φ ψ).satisfies ξ ↔
      ∃ i, ψ.satisfies (ξ.drop i) ∧ ∀ j, j < i → φ.satisfies (ξ.drop j) := by
  simp [satisfies, toPred, tl_until, toPred_drop]

theorem NNF.satisfies_release (ξ : OmegaWord α) (φ ψ : NNF α) :
    (NNF.release φ ψ).satisfies ξ ↔
      ∀ j, ψ.satisfies (ξ.drop j) ∨ ∃ i, i < j ∧ φ.satisfies (ξ.drop i) := by
  simp [satisfies, toPred, tla_release, toPred_drop]

/-- `□φ` holds at every suffix, the `⊥ R φ` encoding's left disjunct being unreachable. -/
theorem NNF.satisfies_always (ξ : OmegaWord α) (φ : NNF α) :
    (NNF.always φ).satisfies ξ ↔ ∀ k, φ.satisfies (ξ.drop k) := by
  simp [NNF.always, satisfies_release, satisfies_ff]

/-- `◇φ` holds at some suffix, the `⊤ U φ` encoding's guard being vacuous. -/
theorem NNF.satisfies_eventually (ξ : OmegaWord α) (φ : NNF α) :
    (NNF.eventually φ).satisfies ξ ↔ ∃ k, φ.satisfies (ξ.drop k) := by
  simp [NNF.eventually, satisfies_until, satisfies_tt]

/-! ## Negation correctness -/

/-- Negating an NNF formula flips satisfaction. -/
theorem NNF.neg_correct (ξ : OmegaWord α) (φ : NNF α) :
  φ.neg.satisfies ξ ↔ ¬ φ.satisfies ξ := by
  induction φ generalizing ξ <;>
    simp only [NNF.neg, satisfies_tt, satisfies_ff, satisfies_prop, satisfies_nprop,
      satisfies_and, satisfies_or, satisfies_next, satisfies_until, satisfies_release] <;>
    grind

/-! ## Formula-level semantics

`directSatisfies` is defined with plain `Prop` operations rather than Lentil combinators, keeping it
independent of the TLA layer so `toNNF_correct` is a genuine cross-check between two independent
semantics. -/

/-- Direct semantics on the user-facing Formula type, independent of NNF. -/
def Formula.directSatisfies {α} (ξ : OmegaWord α) : Formula α → Prop
  | .tt => True
  | .ff => False
  | .atom a => ξ 0 a
  | .not φ => ¬ φ.directSatisfies ξ
  | .and φ ψ => φ.directSatisfies ξ ∧ ψ.directSatisfies ξ
  | .or φ ψ => φ.directSatisfies ξ ∨ ψ.directSatisfies ξ
  | .implies φ ψ => φ.directSatisfies ξ → ψ.directSatisfies ξ
  | .iff φ ψ => φ.directSatisfies ξ ↔ ψ.directSatisfies ξ
  | .next φ => φ.directSatisfies (ξ.drop 1)
  | .until φ ψ =>
    ∃ j, ψ.directSatisfies (ξ.drop j) ∧ ∀ i, i < j → φ.directSatisfies (ξ.drop i)
  | .release φ ψ =>
    ∀ j, ψ.directSatisfies (ξ.drop j) ∨ ∃ i, i < j ∧ φ.directSatisfies (ξ.drop i)
  | .eventually φ => ∃ j, φ.directSatisfies (ξ.drop j)
  | .always φ => ∀ j, φ.directSatisfies (ξ.drop j)

/-- NNF-based satisfaction on the user-facing Formula type. -/
def Formula.satisfies {α} (ξ : OmegaWord α) (φ : Formula α) : Prop :=
  (φ.toNNF true).satisfies ξ

/-- Splitting at the top-level conjunctions preserves meaning. -/
theorem NNF.satisfies_splitConj {α} (ξ : OmegaWord α) (φ : NNF α) :
    φ.satisfies ξ ↔ ∀ c ∈ φ.splitConj, c.satisfies ξ := by
  induction φ with
  | and φ ψ ihφ ihψ =>
    simp only [NNF.splitConj, NNF.satisfies_and, List.mem_append, ihφ, ihψ]
    grind
  | _ => simp [NNF.splitConj]

/-- `conj` is the conjunction of its list. -/
theorem Formula.directSatisfies_conj {α} (ξ : OmegaWord α) (φs : List (Formula α)) :
    (conj φs).directSatisfies ξ ↔ ∀ c ∈ φs, c.directSatisfies ξ := by
  induction φs with
  | nil => simp [conj, directSatisfies]
  | cons φ φs ih =>
    cases φs with
    | nil => simp [conj]
    | cons ψ ψs => simpa [conj, directSatisfies] using and_congr_right (fun _ => ih)

/-- `assuming` discharges its list of assumptions. -/
theorem Formula.directSatisfies_assuming {α} (ξ : OmegaWord α) (ψs : List (Formula α))
    (φ : Formula α) :
    (assuming ψs φ).directSatisfies ξ ↔ ((∀ c ∈ ψs, c.directSatisfies ξ) → φ.directSatisfies ξ) := by
  cases ψs with
  | nil => simp [assuming]
  | cons ψ ψs => simp only [assuming, directSatisfies, directSatisfies_conj]

/-! ## toNNF correctness -/

/-- `toNNF` preserves satisfaction at positive polarity and negates it at negative polarity. -/
private theorem Formula.toNNF_correct_aux {α} (ξ : OmegaWord α) (φ : Formula α) :
    (φ.directSatisfies ξ ↔ (φ.toNNF true).satisfies ξ) ∧
    (¬ φ.directSatisfies ξ ↔ (φ.toNNF false).satisfies ξ) := by
  induction φ generalizing ξ <;>
    dsimp [toNNF, directSatisfies] <;>
    simp [NNF.satisfies_tt, NNF.satisfies_ff,
      NNF.satisfies_prop, NNF.satisfies_nprop, NNF.satisfies_and, NNF.satisfies_or,
      NNF.satisfies_next, NNF.satisfies_until, NNF.satisfies_release, *] <;>
    grind

/-- Converting to NNF preserves satisfaction. -/
theorem Formula.toNNF_correct {α} (ξ : OmegaWord α) (φ : Formula α) :
    φ.directSatisfies ξ ↔ (φ.toNNF true).satisfies ξ :=
  (toNNF_correct_aux ξ φ).1

/-- Negative-polarity half of `toNNF_correct`: converting to NNF at negative polarity captures negated satisfaction. -/
theorem Formula.toNNF_correct_neg {α} (ξ : OmegaWord α) (φ : Formula α) :
    ¬ φ.directSatisfies ξ ↔ (φ.toNNF false).satisfies ξ :=
  (toNNF_correct_aux ξ φ).2

/-- The embedding back into the surface syntax preserves meaning. -/
theorem NNF.directSatisfies_toFormula {α} (ξ : OmegaWord α) (φ : NNF α) :
    φ.toFormula.directSatisfies ξ ↔ φ.satisfies ξ := by
  rw [Formula.toNNF_correct, NNF.toNNF_toFormula]

/-- The two satisfaction notions for Formula agree. -/
theorem Formula.directSatisfies_eq_satisfies {α} (ξ : OmegaWord α) (φ : Formula α) :
    φ.directSatisfies ξ ↔ φ.satisfies ξ :=
  toNNF_correct ξ φ

end LTLLib
