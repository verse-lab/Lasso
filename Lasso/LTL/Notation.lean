module

/-
  `[ltl| φ]`: an LTL formula written in Lentil's `tlfml` syntax, as a `Formula` syntax tree.
  It is the deep counterpart of Lentil's `[tlfml| φ]`, which gives a `Lentil.pred`.

  The connectives are macros onto the constructors of `Formula`, with `p ↝ q` and `p ⇒ q` unfolded to
  `□ (p → ◇ q)` and `□ (p → q)`. By default, `⌜ a ⌝` is the atom `a` and a plain term is a formula.
  A client can read the atoms differently with an elaborator of its own for `ltlFormula`,
  which, registered later, is tried first and can defer to the default with `throwUnsupportedSyntax`.

  Sections:
  - Connectives
  - Atoms
-/
public meta import Lean
public meta import Lentil.Basic
public import Lasso.LTL.Syntax
public import Lasso.LTL.Semantics

public meta section

namespace Lasso

open Lean Elab Term

/-- An LTL formula in Lentil's `tlfml` syntax, as a `Formula` syntax tree. -/
syntax (name := ltlFormula) "[ltl|" tlfml "]" : term

/-! ## Connectives -/

macro_rules
  | `([ltl| ( $f )]) => `([ltl| $f])
  | `([ltl| ⊤]) => `(Lasso.Formula.tt)
  | `([ltl| ⊥]) => `(Lasso.Formula.ff)
  | `([ltl| ¬ $f]) => `(Lasso.Formula.not [ltl| $f])
  | `([ltl| □ $f]) => `(Lasso.Formula.always [ltl| $f])
  | `([ltl| ◇ $f]) => `(Lasso.Formula.eventually [ltl| $f])
  | `([ltl| ◯ $f]) => `(Lasso.Formula.next [ltl| $f])
  | `([ltl| $f ∧ $g]) => `(Lasso.Formula.and [ltl| $f] [ltl| $g])
  | `([ltl| $f ∨ $g]) => `(Lasso.Formula.or [ltl| $f] [ltl| $g])
  | `([ltl| $f → $g]) => `(Lasso.Formula.implies [ltl| $f] [ltl| $g])
  | `([ltl| $f ↔ $g]) => `(Lasso.Formula.iff [ltl| $f] [ltl| $g])
  | `([ltl| $f 𝑈 $g]) => `(Lasso.Formula.until [ltl| $f] [ltl| $g])
  | `([ltl| $f 𝑅 $g]) => `(Lasso.Formula.release [ltl| $f] [ltl| $g])
  | `([ltl| $f ↝ $g]) => `([ltl| □ ($f → ◇ $g)])
  | `([ltl| $f ⇒ $g]) => `([ltl| □ ($f → $g)])

/-! ## Atoms -/

/-- The default reading of the atoms, `⌜ a ⌝` is the atom `a` and a plain term is a formula.
Other formulas of `tlfml`, such as `Enabled a` or `𝒲ℱ a`, have no counterpart. -/
@[term_elab ltlFormula] def elabLtlAtom : TermElab := fun stx expectedType? => do
  match stx with
  | `([ltl| ⌜ $a:term ⌝]) => elabTerm (← `(Lasso.Formula.atom $a)) expectedType?
  | `([ltl| $t:term]) => elabTerm t expectedType?
  | `([ltl| $f]) => throwErrorAt f "`[ltl| …]` has no counterpart for this formula"
  | _ => throwUnsupportedSyntax

end Lasso
