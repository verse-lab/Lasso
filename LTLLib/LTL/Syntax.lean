/-
  LTL formula syntax: both the user-facing type and the internal NNF IR.

  Two representations:
  - `Formula α`: User-facing syntax with the full set of standard LTL operators
    (`not`, `implies`, `iff`, `eventually`, `always`, etc.).

  - `NNF α`: Internal Negative Normal Form representation where
    negation only appears at the atomic level (`nprop`). This is the IR consumed
    by the GBA construction pipeline.

  `Formula.toNNF` compiles the user-facing syntax to NNF and `NNF.toFormula` embeds it back, `toNNF true`
  being a left inverse. `NNF.splitConj` splits at the top-level conjunctions, which fairness routing runs
  after `toNNF` so that a conjunction written under a negation splits too.

  Sections:
  - User-facing syntax
  - NNF (internal IR)
  - NNF normalization
-/

namespace LTLLib

/-! ## User-facing syntax -/

/-- LTL formula with the standard set of operators (the user-facing surface syntax). -/
inductive Formula (α : Type u) where
  | tt : Formula α
  | ff : Formula α
  | atom (a : α) : Formula α
  | not (φ : Formula α) : Formula α
  | and (φ ψ : Formula α) : Formula α
  | or (φ ψ : Formula α) : Formula α
  | implies (φ ψ : Formula α) : Formula α
  | iff (φ ψ : Formula α) : Formula α
  | next (φ : Formula α) : Formula α  -- X
  | until (φ ψ : Formula α) : Formula α  -- U
  | release (φ ψ : Formula α) : Formula α  -- R, dual of Until: φ R ψ ≡ ¬(¬φ U ¬ψ)
  | eventually (φ : Formula α) : Formula α  -- ◇φ = tt U φ
  | always (φ : Formula α) : Formula α  -- □φ = ff R φ
deriving Repr, Inhabited, DecidableEq, BEq, Hashable

namespace Formula

/-- Pretty-print an LTL formula. -/
def toString {α} [ToString α] : Formula α → String
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

instance {α} [ToString α] : ToString (Formula α) := ⟨Formula.toString⟩

/-- Conjunction of a list, `⊤` when empty. -/
def conj {α} : List (Formula α) → Formula α
  | [] => .tt
  | [φ] => φ
  | φ :: φs => .and φ (conj φs)

/-- `φ` under a list of assumptions, `φ` itself when there are none so an empty assumption costs nothing. -/
def assuming {α} (ψs : List (Formula α)) (φ : Formula α) : Formula α :=
  match ψs with
  | [] => φ
  | _ => .implies (conj ψs) φ

end Formula

/-! ## NNF (internal IR) -/

/-- LTL formula in Negative Normal Form: negation appears only at the atomic level (`prop`/`nprop`). -/
inductive NNF (α : Type u) where
  | tt : NNF α
  | ff : NNF α
  | prop (a : α) : NNF α
  | nprop (a : α) : NNF α
  | and (φ ψ : NNF α) : NNF α
  | or (φ ψ : NNF α) : NNF α
  | next (φ : NNF α) : NNF α  -- X
  | until (φ ψ : NNF α) : NNF α  -- U
  | release (φ ψ : NNF α) : NNF α  -- R, dual of Until
deriving Repr, Inhabited, DecidableEq, BEq, Hashable

instance {α} [BEq α] [LawfulBEq α] : LawfulBEq (NNF α) where
  rfl := by intro a ; induction a <;> simp [BEq.beq, instBEqNNF.beq] at * <;> grind
  eq_of_beq := by
    intro a ; induction a <;> intro b <;> cases b <;> try solve | simp [BEq.beq, instBEqNNF.beq]
    all_goals simp [BEq.beq, instBEqNNF.beq] at * ; try grind

instance {α} [BEq α] [Hashable α] [inst : LawfulHashable α] : LawfulHashable (NNF α) where
  hash_eq := by
    intro a ; induction a <;> intro b <;> cases b <;> try solve | simp [BEq.beq, instBEqNNF.beq]
    all_goals simp [BEq.beq, instBEqNNF.beq, hash, instHashableNNF.hash] at * ; try grind
    all_goals intro h ; have := inst.hash_eq _ _ h ; grind

namespace NNF

/-- Negate a formula, pushing negation inward to stay in NNF (De Morgan + temporal duality). -/
def neg {α} : NNF α → NNF α
  | .tt => .ff
  | .ff => .tt
  | .prop a => .nprop a
  | .nprop a => .prop a
  | .and φ ψ => .or φ.neg ψ.neg
  | .or φ ψ => .and φ.neg ψ.neg
  | .next φ => .next φ.neg
  | .until φ ψ => .release φ.neg ψ.neg  -- ¬(φ U ψ) = ¬φ R ¬ψ
  | .release φ ψ => .until φ.neg ψ.neg  -- ¬(φ R ψ) = ¬φ U ¬ψ

/-- Eventually (◇φ) = true U φ. -/
def eventually {α} (φ : NNF α) : NNF α := .until .tt φ

/-- Always (□φ) = false R φ. -/
def always {α} (φ : NNF α) : NNF α := .release .ff φ

/-- Implication φ → ψ = ¬φ ∨ ψ (in NNF). -/
def implies {α} (φ ψ : NNF α) : NNF α := .or φ.neg ψ

/-- Embed back into the surface syntax, so a formula recovered from NNF can re-enter the translator. -/
def toFormula {α} : NNF α → Formula α
  | .tt => .tt
  | .ff => .ff
  | .prop a => .atom a
  | .nprop a => .not (.atom a)
  | .and φ ψ => .and φ.toFormula ψ.toFormula
  | .or φ ψ => .or φ.toFormula ψ.toFormula
  | .next φ => .next φ.toFormula
  | .until φ ψ => .until φ.toFormula ψ.toFormula
  | .release φ ψ => .release φ.toFormula ψ.toFormula

/-- Split at the top-level conjunctions. Run on the NNF rather than the surface formula, so a conjunction
written as `¬(¬φ ∨ ¬ψ)` splits as well. -/
def splitConj {α} : NNF α → List (NNF α)
  | .and φ ψ => splitConj φ ++ splitConj ψ
  | φ => [φ]

/-- Pretty-print an NNF formula. -/
def toString {α} [ToString α] : NNF α → String
  | .tt => "⊤"
  | .ff => "⊥"
  | .prop a => s!"{a}"
  | .nprop a => s!"¬{a}"
  | .and φ ψ => s!"({φ.toString} ∧ {ψ.toString})"
  | .or φ ψ => s!"({φ.toString} ∨ {ψ.toString})"
  | .next φ => s!"X({φ.toString})"
  | .until φ ψ => s!"({φ.toString} U {ψ.toString})"
  | .release φ ψ => s!"({φ.toString} R {ψ.toString})"

instance {α} [ToString α] : ToString (NNF α) := ⟨NNF.toString⟩

end NNF

/-! ## NNF normalization -/

namespace Formula

/-- Convert a surface formula to NNF: pushes negations inward via De Morgan and temporal duality,
and desugars `implies`/`iff`/`eventually`/`always`. `pos` tracks polarity (`false` under an odd
number of negations). -/
def toNNF {α} (pos : Bool) : Formula α → NNF α
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

/-- `toNNF true` undoes the embedding, so a kept conjunct reaches the tableau exactly as it left it. -/
theorem NNF.toNNF_toFormula {α} (φ : NNF α) : φ.toFormula.toNNF true = φ := by
  induction φ <;> simp [NNF.toFormula, Formula.toNNF, *]

end LTLLib
