/-
  Fairness combinators for LTL formulas.

  Provides standard fairness encodings in LTL:
  - Unconditional fairness: □◇taken
  - Weak fairness (justice): □(◇¬enabled ∨ ◇taken)
    i.e., if an action is continuously enabled, it is eventually taken
                  Equivalent to:  ◇□enabled → □◇taken
  - Strong fairness (compassion): □◇enabled → □◇taken
    i.e., if an action is infinitely often enabled, it is infinitely often taken

  These expand into standard LTL formulas and require no special handling
  in the GBA construction. Note that fairness-encoded LTL formulas can
  produce larger automata.
-/

import LTLLib.LTL.Syntax

namespace LTLLib

namespace Formula

/-- Unconditional Fairness: □◇taken.
Event taken will happen infinitely often.
Equivalent to: weakFairness(⊤, taken)-/
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

/-- Given a list of (enabled, taken) pairs, produce the conjunction of
weak fairness assumptions for all of them. -/
def allWeakFair (pairs : List (Formula α × Formula α)) : Formula α :=
  fairnessConjunction (pairs.map fun (e, t) => weakFairness e t)

/-- Given a list of (enabled, taken) pairs, produce the conjunction of
strong fairness assumptions for all of them. -/
def allStrongFair (pairs : List (Formula α × Formula α)) : Formula α :=
  fairnessConjunction (pairs.map fun (e, t) => strongFairness e t)

/-- Check a property under fairness assumptions:
  fairness₁ ∧ fairness₂ ∧ ... → property
Pass the result straight to `modelCheck` (`ModelCheck.lean`). -/
def underFairness (fairnessAssumptions : List (Formula α)) (property : Formula α)
    : Formula α :=
  .implies (fairnessConjunction fairnessAssumptions) property

end Formula

end LTLLib
