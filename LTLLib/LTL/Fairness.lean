/-
  Fairness combinators for LTL formulas.

  Provides standard fairness encodings in LTL:
  - Weak fairness (justice): □(◇¬enabled ∨ ◇taken)
    i.e., if an action is continuously enabled, it is eventually taken
  - Strong fairness (compassion): □(◇enabled → ◇taken)
    i.e., if an action is infinitely often enabled, it is infinitely often taken

  These expand into standard LTL formulas and require no special handling
  in the GBA construction. Note that fairness-encoded LTL formulas can
  produce larger automata.

  Operate on the surface `Formula α` (`LTL/Syntax.lean`), not the internal
  `NNF α` IR: `modelCheck` (`ModelCheck.lean`) is the client-facing entry
  point and takes `Formula α`, so a client builds their property, conjoins
  it with fairness assumptions via `underFairness`, and passes the result
  straight to `modelCheck` without ever touching `NNF`.

  No direct Isabelle correspondence — the Isabelle LTL_to_GBA formalization
  does not include fairness combinators (fairness is handled at a different
  level in the CAVA framework).
-/

import LTLLib.LTL.Syntax

namespace LTLLib

namespace Formula

/-- Weak fairness (justice): □(◇¬enabled ∨ ◇taken).
If `enabled` is continuously true, then `taken` must eventually become true.
Equivalent to: □◇¬enabled ∨ □◇taken, or equivalently, □◇(¬enabled ∨ taken). -/
def weakFairness (enabled taken : Formula α) : Formula α :=
  .always (.or (.eventually enabled.not) (.eventually taken))

/-- Strong fairness (compassion): □(◇enabled → ◇taken).
If `enabled` is true infinitely often, then `taken` must be true infinitely often. -/
def strongFairness (enabled taken : Formula α) : Formula α :=
  .always (.implies (.eventually enabled) (.eventually taken))

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
