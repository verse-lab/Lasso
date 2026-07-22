/-
  LTL semantics: denotation of NNF and Formula types into propositions
  over ω-words, built on Lentil's TLA temporal logic foundations.

  Key definitions:
  - `tla_release`: Release operator (dual of Until), missing from Lentil
  - `NNF.toPred`: Denotation from NNF syntax to Lentil `TLA.pred`
  - `NNF.satisfies`: ω-word satisfies an NNF formula
  - `Formula.directSatisfies`: Independent semantics on user-facing Formula type
  - `Formula.satisfies`: Defined via NNF

  Key theorems:
  - `NNF.neg_correct`: Negation correctness for NNF
  - `toNNF_correct`: `Formula.directSatisfies` ↔ `NNF.satisfies ∘ toNNF`
-/
import Lentil
import LTLLib.LTL.Syntax

namespace LTLLib

open TLA

/-! ## ω-words

An ω-word over atomic propositions of type `α` is an infinite sequence
where each position maps atoms to truth values. We use Lentil's `exec`
type instantiated at `α → Prop`. -/

/-- An ω-word over atomic propositions `α`. Each time step is a valuation
    `α → Prop` assigning truth values to atoms. -/
abbrev OmegaWord (α : Type u) := exec (α → Prop)

/-! ## Release operator

Lentil provides `tla_until` but not its dual `release`.
We define it here and prove the key properties. -/

/-- Release operator: `p R q` holds iff for every `j`, either `q` holds at suffix `j`,
    or there exists some `i < j` where `p` holds.
    This is the dual of Until: `p R q ≡ ¬(¬p U ¬q)`. -/
def tla_release {α : Type u} (p q : pred α) : pred α :=
  fun σ => ∀ j, (q <| σ.drop j) ∨ ∃ i, i < j ∧ (p <| σ.drop i)

syntax:25 tlafml:26 " 𝑅 " tlafml:25 : tlafml

macro_rules
  | `([tlafml| $f1:tlafml 𝑅 $f2:tlafml ]) => `(LTLLib.tla_release [tlafml| $f1 ] [tlafml| $f2 ])

/-- Release is the dual of Until: `p R q ↔ ¬(¬p U ¬q)`. -/
theorem release_iff_not_until_neg {α : Type u} (p q : pred α) :
  ((p 𝑅 q)) =tla= (¬ (¬ p 𝑈 ¬ q)) := by
  funext e ; unfold tla_release ; tunfold_simp ; grind

/-- Until is the dual of release: `p U q ↔ ¬(¬p R ¬q)`. -/
theorem until_iff_not_release_neg {α : Type u} (p q : pred α) :
  ((p 𝑈 q)) =tla= (¬ (¬ p 𝑅 ¬ q)) := by
  funext e ; unfold tla_release ; tunfold_simp

/-- □ p = ⊥ R p. -/
theorem always_eq_release_false {α : Type u} (p : pred α) :
  (□ p) =tla= (⊥ 𝑅 p) := by
  funext e ; unfold tla_release ; tunfold_simp

/-! ## NNF denotation -/

/-- Denotational semantics: map an NNF formula to a Lentil predicate over ω-words.
    Each ω-word position is a valuation `α → Prop`. -/
def NNF.toPred : NNF α → pred (α → Prop)
  | .tt        => tla_true
  | .ff        => tla_false
  | .prop a    => state_pred (fun v => v a)
  | .nprop a   => state_pred (fun v => ¬ v a)
  | .and φ ψ   => tla_and φ.toPred ψ.toPred
  | .or φ ψ    => tla_or φ.toPred ψ.toPred
  | .next φ    => later φ.toPred
  | .until φ ψ => tla_until φ.toPred ψ.toPred
  | .release φ ψ => tla_release φ.toPred ψ.toPred

/-- An ω-word `ξ` satisfies an NNF formula `φ`. -/
def NNF.satisfies (ξ : OmegaWord α) (φ : NNF α) : Prop :=
  φ.toPred ξ

/-! ## Unfolding lemmas for NNF.satisfies -/

/-- Suffix compatibility: satisfying at a suffix composes properly. -/
theorem NNF.satisfies_drop_drop (ξ : OmegaWord α) (k l : Nat) (φ : NNF α) :
  φ.satisfies ((ξ.drop k).drop l) ↔ φ.satisfies (ξ.drop (k + l)) := by
  simp only [NNF.satisfies, exec.drop_drop]

/-! ## Negation correctness -/

/-- Negating an NNF formula flips satisfaction. -/
theorem NNF.neg_correct (ξ : OmegaWord α) (φ : NNF α) :
  φ.neg.satisfies ξ ↔ ¬ φ.satisfies ξ := by
  induction φ generalizing ξ <;> dsimp [satisfies, NNF.neg, NNF.toPred, tla_release] at * <;> tunfold_simp <;> try grind

/-! ## Formula-level semantics

`directSatisfies` is intentionally defined using plain Prop operations rather
than Lentil combinators. This keeps it independent of the TLA layer so that
`toNNF_correct` (which proves `directSatisfies ↔ NNF.satisfies ∘ toNNF`)
serves as a genuine cross-check between two independent semantics. -/

/-- Direct semantics on the user-facing Formula type, independent of NNF. -/
def Formula.directSatisfies (ξ : OmegaWord α) : Formula α → Prop
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
def Formula.satisfies (ξ : OmegaWord α) (φ : Formula α) : Prop :=
  (φ.toNNF true).satisfies ξ

/-! ## toNNF correctness

The main difficulty is handling polarity: `toNNF` takes a `Bool` parameter
tracking whether we are in a positive or negative context. We prove the
positive and negative cases simultaneously by induction on the formula.

We use `show` to explicitly state the goal after unfolding `toNNF`,
which avoids issues with `simp` not fully reducing Bool if-then-else. -/

/-- The key generalized statement: toNNF preserves/negates satisfaction
    depending on polarity. -/
private theorem Formula.toNNF_correct_aux (ξ : OmegaWord α) (φ : Formula α) :
    (φ.directSatisfies ξ ↔ (φ.toNNF true).satisfies ξ) ∧
    (¬ φ.directSatisfies ξ ↔ (φ.toNNF false).satisfies ξ) := by
  induction φ generalizing ξ <;> dsimp [toNNF, directSatisfies, NNF.satisfies, NNF.toPred, state_pred, tla_release] at * <;> tunfold_simp' <;> try grind

/-- Converting to NNF preserves satisfaction. -/
theorem Formula.toNNF_correct (ξ : OmegaWord α) (φ : Formula α) :
    φ.directSatisfies ξ ↔ (φ.toNNF true).satisfies ξ :=
  (toNNF_correct_aux ξ φ).1

/-- The two satisfaction notions for Formula agree. -/
theorem Formula.directSatisfies_eq_satisfies (ξ : OmegaWord α) (φ : Formula α) :
    φ.directSatisfies ξ ↔ φ.satisfies ξ :=
  toNNF_correct ξ φ

end LTLLib
