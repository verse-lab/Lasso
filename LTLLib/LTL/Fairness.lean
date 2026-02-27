/-
  Fairness combinators for LTL formulas.

  Provides standard fairness encodings in LTL:
  - Weak fairness (justice): □(□◇¬enabled ∨ ◇taken)
    i.e., if an action is continuously enabled, it is eventually taken
  - Strong fairness (compassion): □(◇enabled → ◇taken)
    i.e., if an action is infinitely often enabled, it is infinitely often taken

  These expand into standard LTL formulas and require no special handling
  in the GBA construction. Note that fairness-encoded LTL formulas can
  produce larger automata.

  No direct Isabelle correspondence — the Isabelle LTL_to_GBA formalization
  does not include fairness combinators (fairness is handled at a different
  level in the CAVA framework).
-/

import LTLLib.LTL.Syntax

namespace LTLLib

namespace NNF

/-- Weak fairness (justice): □(□◇¬enabled ∨ ◇taken).
If `enabled` is continuously true, then `taken` must eventually become true.
Equivalent to: □(◇¬enabled) ∨ □◇taken, or equivalently, □◇(¬enabled ∨ taken). -/
def weakFairness (enabled taken : NNF α) : NNF α :=
  -- □(◇¬enabled ∨ ◇taken) which is equivalent to □◇(¬enabled ∨ taken)
  always (eventually (or enabled.neg taken))

/-- Strong fairness (compassion): □(◇enabled → ◇taken).
If `enabled` is true infinitely often, then `taken` must be true infinitely often.
Equivalent to: □◇¬enabled ∨ □◇taken. -/
def strongFairness (enabled taken : NNF α) : NNF α :=
  -- □(◇enabled → ◇taken) = □(□¬enabled ∨ ◇taken) -- no, let's expand properly
  -- ◇enabled → ◇taken = ¬◇enabled ∨ ◇taken = □¬enabled ∨ ◇taken
  -- □(□¬enabled ∨ ◇taken)
  always (or (always enabled.neg) (eventually taken))

/-- Conjunction of multiple fairness constraints. -/
def fairnessConjunction (constraints : List (NNF α)) : NNF α :=
  match constraints with
  | [] => .tt
  | c :: cs => cs.foldl .and c

/-- Given a list of (enabled, taken) pairs, produce the conjunction of
weak fairness assumptions for all of them. -/
def allWeakFair (pairs : List (NNF α × NNF α)) : NNF α :=
  fairnessConjunction (pairs.map fun (e, t) => weakFairness e t)

/-- Given a list of (enabled, taken) pairs, produce the conjunction of
strong fairness assumptions for all of them. -/
def allStrongFair (pairs : List (NNF α × NNF α)) : NNF α :=
  fairnessConjunction (pairs.map fun (e, t) => strongFairness e t)

/-- Check a property under fairness assumptions:
  fairness₁ ∧ fairness₂ ∧ ... → property
which in NNF is:
  ¬fairness₁ ∨ ¬fairness₂ ∨ ... ∨ property -/
def underFairness (fairnessAssumptions : List (NNF α)) (property : NNF α)
    : NNF α :=
  implies (fairnessConjunction fairnessAssumptions) property

end NNF

end LTLLib
