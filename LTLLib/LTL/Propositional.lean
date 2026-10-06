module

/-
  Propositional formulas over atoms, the fragment fairness assumptions are checked in.

  Fairness routing evaluates a formula at a single state rather than over a word, so the propositional
  fragment gets its own total, decidable type instead of a partial evaluator on `NNF`. `BoolFormula` embeds
  into `NNF` and `NNF.asBool?` recognises the image, so the two views can be exchanged freely.

  Key definitions:
  - `BoolFormula`: propositional formulas in negation normal form
  - `BoolFormula.holds`: denotation against a valuation `α → Prop`
  - `BoolFormula.eval`: executable denotation against a `Std.HashSet α` under the closed-world reading
  - `BoolFormula.simplify`, `BoolFormula.isTrue`, `BoolFormula.isFalse`: folding, and the tests a folded
    constant answers
  - `BoolFormula.conjuncts`: the conjuncts of a formula, so implication between folded formulas is an inclusion
  - `BoolFormula.toNNF`/`NNF.asBool?`: the embedding into `NNF` and its partial inverse

  Key theorems:
  - `BoolFormula.eval_iff_holds`: `eval` agrees with `holds` read against set membership
  - `BoolFormula.satisfies_toNNF`: the embedding is denotationally the valuation at position 0
  - `BoolFormula.eval_iff_satisfies`: the composite used by the product, `eval` against a state's label
    agrees with `NNF.satisfies` on any word whose first position carries that label

  Sections:
  - Propositional syntax
  - Semantics
  - Executable evaluation
  - NNF embedding
  - Recognising the propositional fragment
-/
public import LTLLib.LTL.Semantics

public section

namespace LTLLib

open Lentil

/-! ## Propositional syntax -/

/-- A propositional formula in negation normal form, negation only at atoms. -/
inductive BoolFormula (α : Type u) where
  | tt : BoolFormula α
  | ff : BoolFormula α
  | prop (a : α) : BoolFormula α
  | nprop (a : α) : BoolFormula α
  | and (φ ψ : BoolFormula α) : BoolFormula α
  | or (φ ψ : BoolFormula α) : BoolFormula α
deriving Repr, Inhabited, DecidableEq, BEq, Hashable

namespace BoolFormula

/-- Negate, pushing the negation to the atoms so the result stays in the fragment. -/
@[expose] def neg {α} : BoolFormula α → BoolFormula α
  | .tt => .ff
  | .ff => .tt
  | .prop a => .nprop a
  | .nprop a => .prop a
  | .and φ ψ => .or φ.neg ψ.neg
  | .or φ ψ => .and φ.neg ψ.neg

/-- Conjunction of a list, `⊤` when empty. -/
@[expose] def conj {α} : List (BoolFormula α) → BoolFormula α
  | [] => .tt
  | [b] => b
  | b :: bs => .and b (conj bs)

/-- Constant folding with idempotence and the complementary-literal identities, applied bottom-up so a nest
of `⊤` collapses and so a region crossed with its own negation folds to `⊥`. -/
@[expose] def simplify {α} [DecidableEq α] : BoolFormula α → BoolFormula α
  | .and φ ψ =>
    match simplify φ, simplify ψ with
    | .ff, _ | _, .ff => .ff
    | .tt, b | b, .tt => b
    | a, b => if a = b then a else if a = b.neg then .ff else .and a b
  | .or φ ψ =>
    match simplify φ, simplify ψ with
    | .tt, _ | _, .tt => .tt
    | .ff, b | b, .ff => b
    | a, b => if a = b then a else if a = b.neg then .tt else .or a b
  | φ => φ

/-- Is this literally `⊤`? After folding, a disjunct with no real `FG` content answers yes. -/
@[expose] def isTrue {α} : BoolFormula α → Bool
  | .tt => true
  | _ => false

/-- Is this literally `⊥`? After folding, a region no state can satisfy answers yes. -/
@[expose] def isFalse {α} : BoolFormula α → Bool
  | .ff => true
  | _ => false

/-- The conjuncts of a formula, split at `∧`, so that `⊤` has none and an implication between two folded
formulas can be read off as an inclusion of conjunct lists. -/
@[expose] def conjuncts {α} : BoolFormula α → List (BoolFormula α)
  | .tt => []
  | .and φ ψ => φ.conjuncts ++ ψ.conjuncts
  | b => [b]

/-- Pretty-print a propositional formula. -/
@[expose] def toString {α} [ToString α] : BoolFormula α → String
  | .tt => "⊤"
  | .ff => "⊥"
  | .prop a => s!"{a}"
  | .nprop a => s!"¬{a}"
  | .and φ ψ => s!"({φ.toString} ∧ {ψ.toString})"
  | .or φ ψ => s!"({φ.toString} ∨ {ψ.toString})"

instance {α} [ToString α] : ToString (BoolFormula α) := ⟨BoolFormula.toString⟩

/-! ## Semantics -/

/-- Denotation against a valuation. -/
@[expose] def holds {α} (v : α → Prop) : BoolFormula α → Prop
  | .tt => True
  | .ff => False
  | .prop a => v a
  | .nprop a => ¬ v a
  | .and φ ψ => holds v φ ∧ holds v ψ
  | .or φ ψ => holds v φ ∨ holds v ψ

theorem holds_neg {α} (v : α → Prop) (b : BoolFormula α) : holds v b.neg ↔ ¬ holds v b := by
  induction b <;> simp [neg, holds, *]
  grind

theorem holds_simplify {α} [DecidableEq α] (v : α → Prop) (b : BoolFormula α) :
    holds v (simplify b) ↔ holds v b := by
  induction b with
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    rw [simplify]
    simp only [holds]
    rw [← ihφ, ← ihψ]
    split <;> try split
    all_goals try split
    all_goals simp_all [holds, holds_neg]
    all_goals grind
  | _ => rfl

/-- A formula is the conjunction of its conjuncts, which is what makes an inclusion of conjunct lists an
implication. -/
theorem holds_conjuncts {α} (v : α → Prop) (b : BoolFormula α) :
    holds v b ↔ ∀ c ∈ b.conjuncts, holds v c := by
  induction b with
  | and φ ψ ihφ ihψ => simp only [conjuncts, holds, List.mem_append, ihφ, ihψ]; grind
  | _ => simp [conjuncts, holds]

/-- Every conjunct of `b` being one of `a`'s makes `a` the stronger formula. -/
theorem holds_of_conjuncts_subset {α} {a b : BoolFormula α} (h : ∀ c ∈ b.conjuncts, c ∈ a.conjuncts)
    {v : α → Prop} (ha : holds v a) : holds v b :=
  (holds_conjuncts v b).mpr fun c hc => (holds_conjuncts v a).mp ha c (h c hc)

theorem holds_of_isTrue {α} (v : α → Prop) {b : BoolFormula α} (h : b.isTrue = true) : holds v b := by
  cases b <;> simp_all [isTrue, holds]

/-- `holds` only reads the valuation through its atoms, so pointwise-equivalent valuations agree. -/
theorem holds_congr {α} {v w : α → Prop} (h : ∀ a, v a ↔ w a) (b : BoolFormula α) :
    holds v b ↔ holds w b := by
  induction b <;> simp [holds, *]

theorem holds_conj {α} (v : α → Prop) (bs : List (BoolFormula α)) :
    holds v (conj bs) ↔ ∀ b ∈ bs, holds v b := by
  induction bs with
  | nil => simp [conj, holds]
  | cons b bs ih =>
    cases bs with
    | nil => simp [conj]
    | cons c cs => simpa [conj, holds] using and_congr_right (fun _ => ih)

/-! ## Executable evaluation -/

variable {α : Type u} [BEq α] [Hashable α]

/-- Executable denotation against a state label, under the closed-world reading that an atom holds exactly
when it is in the label. -/
@[expose] def eval : BoolFormula α → Std.HashSet α → Bool
  | .tt, _ => true
  | .ff, _ => false
  | .prop a, l => l.contains a
  | .nprop a, l => !l.contains a
  | .and φ ψ, l => φ.eval l && ψ.eval l
  | .or φ ψ, l => φ.eval l || ψ.eval l

/-- The atoms the formula actually inspects. Used to decide, syntactically, that a formula cannot tell two
letters apart — which is how a caller discharges `LSys.StateOnly` without reasoning semantically. -/
@[expose] def atoms : BoolFormula α → List α
  | .tt | .ff => []
  | .prop a | .nprop a => [a]
  | .and φ ψ | .or φ ψ => φ.atoms ++ ψ.atoms

/-- Two letters agreeing on every atom the formula looks at score the same. -/
theorem eval_congr {b : BoolFormula α} {l m : Std.HashSet α}
    (h : ∀ a ∈ b.atoms, l.contains a = m.contains a) : b.eval l = b.eval m := by
  induction b with
  | tt | ff => rfl
  | prop a => exact h a (by simp [atoms])
  | nprop a => rw [eval, eval, h a (by simp [atoms])]
  | and φ ψ ihφ ihψ =>
    rw [eval, eval, ihφ (fun a ha => h a (by simp [atoms, ha])),
      ihψ (fun a ha => h a (by simp [atoms, ha]))]
  | or φ ψ ihφ ihψ =>
    rw [eval, eval, ihφ (fun a ha => h a (by simp [atoms, ha])),
      ihψ (fun a ha => h a (by simp [atoms, ha]))]

/-- `eval` is `holds` read against set membership. -/
theorem eval_iff_holds (b : BoolFormula α) (l : Std.HashSet α) :
    b.eval l = true ↔ holds (fun a => a ∈ l) b := by
  induction b <;> simp [eval, holds, *]

theorem eval_simplify [DecidableEq α] (b : BoolFormula α) (l : Std.HashSet α) :
    (simplify b).eval l = b.eval l := by
  rw [Bool.eq_iff_iff, eval_iff_holds, eval_iff_holds, holds_simplify]

/-- A folded `⊤` evaluates to `true` at every label, which is what lets the region restriction be skipped. -/
theorem eval_of_isTrue {b : BoolFormula α} (h : b.isTrue = true) (l : Std.HashSet α) :
    b.eval l = true := by
  cases b <;> simp_all [isTrue, eval]

/-! ## NNF embedding -/

/-- Embed into `NNF`, the fragment is exactly the temporal-operator-free part. -/
@[expose] def toNNF {α} : BoolFormula α → NNF α
  | .tt => .tt
  | .ff => .ff
  | .prop a => .prop a
  | .nprop a => .nprop a
  | .and φ ψ => .and φ.toNNF ψ.toNNF
  | .or φ ψ => .or φ.toNNF ψ.toNNF

theorem toNNF_neg {α} (b : BoolFormula α) : b.neg.toNNF = b.toNNF.neg := by
  induction b <;> simp [neg, toNNF, NNF.neg, *]

/-- The embedding reads the word's first position and nothing else. -/
theorem satisfies_toNNF {α} (ξ : OmegaWord α) (b : BoolFormula α) :
    b.toNNF.satisfies ξ ↔ holds (ξ 0) b := by
  induction b <;>
    dsimp [toNNF, holds, NNF.satisfies, NNF.toPred, state_pred] at * <;> tunfold_simp <;> try grind

theorem satisfies_toNNF_drop {α} (ξ : OmegaWord α) (b : BoolFormula α) (k : Nat) :
    b.toNNF.satisfies (ξ.drop k) ↔ holds (ξ k) b := by
  rw [satisfies_toNNF]; simp [exec.drop]

/-- `□◇b`, the shape a propositional fairness conjunct takes. -/
@[expose] def alwaysEventually {α} (b : BoolFormula α) : NNF α := .always (.eventually b.toNNF)

/-- `□◇b` holds exactly when `b` holds at infinitely many positions. -/
theorem satisfies_alwaysEventually {α} (ξ : OmegaWord α) (b : BoolFormula α) :
    (alwaysEventually b).satisfies ξ ↔ ∀ n, ∃ j, holds (ξ (n + j)) b := by
  simp only [alwaysEventually, NNF.satisfies_always, NNF.satisfies_eventually, exec.drop_drop,
    satisfies_toNNF_drop]

/-- `◇□b`, the enabling half of a weak fairness assumption. -/
@[expose] def eventuallyAlways {α} (b : BoolFormula α) : NNF α := .eventually (.always b.toNNF)

/-- `◇□b` holds exactly when `b` holds from some position onwards. -/
theorem satisfies_eventuallyAlways {α} (ξ : OmegaWord α) (b : BoolFormula α) :
    (eventuallyAlways b).satisfies ξ ↔ ∃ n, ∀ k, holds (ξ (n + k)) b := by
  simp only [eventuallyAlways, NNF.satisfies_eventually, NNF.satisfies_always, exec.drop_drop,
    satisfies_toNNF_drop]

/-- The composite the product needs, `eval` against a state's label decides the embedded formula on any word
whose first position carries that label. -/
theorem eval_iff_satisfies (b : BoolFormula α) (l : Std.HashSet α) (ξ : OmegaWord α)
    (hξ : ∀ a, ξ 0 a ↔ a ∈ l) : b.eval l = true ↔ b.toNNF.satisfies ξ := by
  rw [eval_iff_holds, satisfies_toNNF]
  exact (holds_congr hξ b).symm

end BoolFormula

/-! ## Recognising the propositional fragment -/

namespace NNF

/-- The partial inverse of `BoolFormula.toNNF`, `none` exactly when a temporal operator occurs. -/
@[expose] def asBool? {α} : NNF α → Option (BoolFormula α)
  | .tt => some .tt
  | .ff => some .ff
  | .prop a => some (.prop a)
  | .nprop a => some (.nprop a)
  | .and φ ψ => do return .and (← φ.asBool?) (← ψ.asBool?)
  | .or φ ψ => do return .or (← φ.asBool?) (← ψ.asBool?)
  | _ => none

theorem asBool?_toNNF {α} {φ : NNF α} {b : BoolFormula α} (h : φ.asBool? = some b) :
    b.toNNF = φ := by
  induction φ generalizing b <;> simp [asBool?, Option.bind_eq_some_iff] at h
  case and _ _ ihφ ihψ | or _ _ ihφ ihψ =>
    obtain ⟨c, hc, d, hd, rfl⟩ := h
    simp [BoolFormula.toNNF, ihφ hc, ihψ hd]
  all_goals simp [← h, BoolFormula.toNNF]

end NNF

end LTLLib
