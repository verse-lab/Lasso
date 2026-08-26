/-
  Fairness combinators for LTL formulas: unconditional, weak (justice), and strong (compassion) fairness, plus
  helpers for combining and assuming multiple fairness constraints.

  These expand into standard LTL formulas and require no special handling in the GBA construction.
  Fairness-encoded formulas can however produce larger automata.
-/

import LTLLib.LTL.Syntax

namespace LTLLib

namespace Formula

/-- Unconditional fairness: □◇taken. `taken` happens infinitely often, unconditionally.
Equivalent to `weakFairness ⊤ taken`. -/
def unconditionalFairness (taken : Formula α) : Formula α :=
  .always (.eventually taken)

/-- Weak fairness (justice): □(◇¬enabled ∨ ◇taken).
If `enabled` is continuously true, then `taken` must eventually become true.
Equivalent to: □◇(¬enabled ∨ taken), or equivalently, ◇□enabled → □◇taken. -/
def weakFairness (enabled taken : Formula α) : Formula α :=
  .always (.or (.eventually enabled.not) (.eventually taken))

/-- Strong fairness (compassion): □◇enabled → □◇taken.
If `enabled` is true infinitely often, then `taken` must be true infinitely often. -/
def strongFairness (enabled taken : Formula α) : Formula α :=
  .implies (.always (.eventually enabled)) (.always (.eventually taken))

/-- Conjunction of multiple fairness constraints. -/
def fairnessConjunction (constraints : List (Formula α)) : Formula α :=
  match constraints with
  | [] => .tt
  | c :: cs => cs.foldl .and c

/-- Conjunction of weak fairness assumptions for every (enabled, taken) pair. -/
def allWeakFair (pairs : List (Formula α × Formula α)) : Formula α :=
  fairnessConjunction (pairs.map fun (e, t) => weakFairness e t)

/-- Conjunction of strong fairness assumptions for every (enabled, taken) pair. -/
def allStrongFair (pairs : List (Formula α × Formula α)) : Formula α :=
  fairnessConjunction (pairs.map fun (e, t) => strongFairness e t)

/-- `fairness₁ ∧ fairness₂ ∧ ... → property`: `property` need only hold under the given fairness assumptions. -/
def underFairness (fairnessAssumptions : List (Formula α)) (property : Formula α)
    : Formula α :=
  .implies (fairnessConjunction fairnessAssumptions) property

end Formula

end LTLLib
