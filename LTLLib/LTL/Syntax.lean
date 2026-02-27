/-
  LTL formula syntax: both the user-facing type and the internal NNF IR.

  Two representations:
  - `Formula α`: User-facing syntax with the full set of standard LTL operators
    (`not`, `implies`, `iff`, `eventually`, `always`, etc.).
    Corresponds to `'a ltln` in the CAVA LTL framework.

  - `NNF α`: Internal Negative Normal Form representation where
    negation only appears at the atomic level (`nprop`). This is the IR consumed
    by the GBA construction pipeline.
    Corresponds to `'a ltlr` / `'a frml` in the CAVA LTL framework.

  `Formula.toNNF` compiles the user-facing syntax to NNF.
  Corresponds to `ltln_to_ltlr` in the CAVA framework.
-/

namespace LTLLib

/-! ## User-facing syntax -/

/-- LTL formula with the standard set of operators.

This is the user-facing type. Use `toNNF` to compile to the internal
`NNF` representation before passing to the GBA pipeline.

Corresponds to `'a ltln` in the CAVA LTL framework. -/
inductive Formula (α : Type) where
  /-- Constant true. -/
  | tt : Formula α
  /-- Constant false. -/
  | ff : Formula α
  /-- Atomic proposition. -/
  | atom (a : α) : Formula α
  /-- Negation. -/
  | not (φ : Formula α) : Formula α
  /-- Conjunction. -/
  | and (φ ψ : Formula α) : Formula α
  /-- Disjunction. -/
  | or (φ ψ : Formula α) : Formula α
  /-- Implication. -/
  | implies (φ ψ : Formula α) : Formula α
  /-- Biconditional. -/
  | iff (φ ψ : Formula α) : Formula α
  /-- Next (X). -/
  | next (φ : Formula α) : Formula α
  /-- Until (U). -/
  | until (φ ψ : Formula α) : Formula α
  /-- Release (R), dual of Until: φ R ψ ≡ ¬(¬φ U ¬ψ). -/
  | release (φ ψ : Formula α) : Formula α
  /-- Eventually (◇φ) = true U φ. -/
  | eventually (φ : Formula α) : Formula α
  /-- Always (□φ) = false R φ. -/
  | always (φ : Formula α) : Formula α
deriving Repr, Inhabited, DecidableEq, BEq, Hashable

namespace Formula

/-- Pretty-print an LTL formula. -/
def toString [ToString α] : Formula α → String
  | .tt => "⊤"
  | .ff => "⊥"
  | .atom a => s!"{a}"
  | .not φ => s!"¬({φ.toString})"
  | .and φ ψ => s!"({φ.toString} ∧ {ψ.toString})"
  | .or φ ψ => s!"({φ.toString} ∨ {ψ.toString})"
  | .implies φ ψ => s!"({φ.toString} → {ψ.toString})"
  | .iff φ ψ => s!"({φ.toString} ↔ {ψ.toString})"
  | .next φ => s!"X({φ.toString})"
  | .until φ ψ => s!"({φ.toString} U {ψ.toString})"
  | .release φ ψ => s!"({φ.toString} R {ψ.toString})"
  | .eventually φ => s!"◇({φ.toString})"
  | .always φ => s!"□({φ.toString})"

instance [ToString α] : ToString (Formula α) := ⟨Formula.toString⟩

end Formula

/-! ## NNF (internal IR) -/

/-- LTL formula in Negative Normal Form (NNF).
Parametrized by the type of atomic propositions `α`.

This is the internal representation consumed by the GBA pipeline.
Negation only appears at the atomic level (`prop` vs `nprop`).

Corresponds to `'a ltlr` in the CAVA LTL framework, used as `'a frml`
in LTL_to_GBA.thy (line 98). -/
inductive NNF (α : Type) where
  /-- Constant true. Corresponds to `true_ltlr` / `True⁼`. -/
  | tt : NNF α
  /-- Constant false. Corresponds to `false_ltlr` / `False⁼`. -/
  | ff : NNF α
  /-- Positive atomic proposition. Corresponds to `prop_ltlr` / `prop⁼(q)`. -/
  | prop (a : α) : NNF α
  /-- Negated atomic proposition. Corresponds to `nprop_ltlr` / `nprop⁼(q)`. -/
  | nprop (a : α) : NNF α
  /-- Conjunction. Corresponds to `and_ltlr` / `ν and⁼ μ`. -/
  | and (φ ψ : NNF α) : NNF α
  /-- Disjunction. Corresponds to `or_ltlr` / `ν or⁼ μ`. -/
  | or (φ ψ : NNF α) : NNF α
  /-- Next (X). Corresponds to `next_ltlr` / `X⁼ ν`. -/
  | next (φ : NNF α) : NNF α
  /-- Until (U). Corresponds to `until_ltlr` / `μ U⁼ η`. -/
  | until (φ ψ : NNF α) : NNF α
  /-- Release (R), dual of Until. Corresponds to `release_ltlr` / `μ R⁼ η`. -/
  | release (φ ψ : NNF α) : NNF α
deriving Repr, Inhabited, DecidableEq, BEq, Hashable

namespace NNF

/-- Negate an LTL formula, pushing negation inward to maintain NNF.

Corresponds to `not⁼` / `not_ltlr` in the CAVA LTL framework.
Uses De Morgan laws and temporal duality:
  ¬(φ U ψ) = (¬φ) R (¬ψ)
  ¬(φ R ψ) = (¬φ) U (¬ψ)
  ¬(X φ)   = X (¬φ) -/
def neg : NNF α → NNF α
  | .tt => .ff
  | .ff => .tt
  | .prop a => .nprop a
  | .nprop a => .prop a
  | .and φ ψ => .or φ.neg ψ.neg
  | .or φ ψ => .and φ.neg ψ.neg
  | .next φ => .next φ.neg
  | .until φ ψ => .release φ.neg ψ.neg
  | .release φ ψ => .until φ.neg ψ.neg

/-- Eventually (◇φ) = true U φ. -/
def eventually (φ : NNF α) : NNF α := .until .tt φ

/-- Always (□φ) = false R φ. -/
def always (φ : NNF α) : NNF α := .release .ff φ

/-- Implication φ → ψ = ¬φ ∨ ψ (in NNF). -/
def implies (φ ψ : NNF α) : NNF α := .or φ.neg ψ

/-- Pretty-print an NNF formula. -/
def toString [ToString α] : NNF α → String
  | .tt => "⊤"
  | .ff => "⊥"
  | .prop a => s!"{a}"
  | .nprop a => s!"¬{a}"
  | .and φ ψ => s!"({φ.toString} ∧ {ψ.toString})"
  | .or φ ψ => s!"({φ.toString} ∨ {ψ.toString})"
  | .next φ => s!"X({φ.toString})"
  | .until φ ψ => s!"({φ.toString} U {ψ.toString})"
  | .release φ ψ => s!"({φ.toString} R {ψ.toString})"

instance [ToString α] : ToString (NNF α) := ⟨NNF.toString⟩

end NNF

/-! ## NNF normalization -/

namespace Formula

/-- Convert a surface LTL formula to Negative Normal Form.

Pushes negation inward to the atomic level using De Morgan laws and
temporal duality. Also desugars `implies`, `iff`, `eventually`, `always`.

The `pos` parameter tracks polarity: `true` = positive context,
`false` = negative context (under an odd number of negations).

Corresponds to `ltln_to_ltlr` in the CAVA LTL framework. -/
def toNNF (pos : Bool) : Formula α → NNF α
  | .tt => if pos then .tt else .ff
  | .ff => if pos then .ff else .tt
  | .atom a => if pos then .prop a else .nprop a
  | .not φ => toNNF (!pos) φ
  | .and φ ψ =>
    if pos then .and (toNNF true φ) (toNNF true ψ)
    else .or (toNNF false φ) (toNNF false ψ)
  | .or φ ψ =>
    if pos then .or (toNNF true φ) (toNNF true ψ)
    else .and (toNNF false φ) (toNNF false ψ)
  | .implies φ ψ =>
    if pos then .or (toNNF false φ) (toNNF true ψ)
    else .and (toNNF true φ) (toNNF false ψ)
  | .iff φ ψ =>
    if pos then .and (.or (toNNF false φ) (toNNF true ψ)) (.or (toNNF false ψ) (toNNF true φ))
    else .or (.and (toNNF true φ) (toNNF false ψ)) (.and (toNNF true ψ) (toNNF false φ))
  | .next φ => .next (toNNF pos φ)
  | .until φ ψ =>
    if pos then .until (toNNF true φ) (toNNF true ψ)
    else .release (toNNF false φ) (toNNF false ψ)
  | .release φ ψ =>
    if pos then .release (toNNF true φ) (toNNF true ψ)
    else .until (toNNF false φ) (toNNF false ψ)
  | .eventually φ =>
    if pos then .until .tt (toNNF true φ)
    else .release .ff (toNNF false φ)
  | .always φ =>
    if pos then .release .ff (toNNF true φ)
    else .until .tt (toNNF false φ)

end Formula

end LTLLib
