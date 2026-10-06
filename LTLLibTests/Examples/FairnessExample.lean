module

/-
  Slightly more complicated example that exercises a generalized Büchi
  acceptance condition with two acceptance sets.

  Formula: □◇a ∧ □◇b

  Each `always (eventually _)` contributes one Until-subformula
  (`⊤ U a` and `⊤ U b` respectively), and the GBA construction allocates one
  acceptance set per distinct Until-subformula (`GBA.lean`, `acceptSets`),
  so this formula produces exactly two acceptance sets, `F0` and `F1`.

  Therefore, the degeneralized Büchi automata will haver 2x the states of
  the GBA.
-/
import LTLLibTests.Examples.BuildPrint
meta import LTLLibTests.Examples.BuildPrint

namespace LTLLib.Tests.Examples

/-- Atomic propositions are plain strings for this example. -/
abbrev Prop' := String

/-- `□◇a ∧ □◇b`: `a` holds infinitely often, and `b` holds infinitely often. -/
def ψ : Formula Prop' :=
  .and (.always (.eventually (.atom "a"))) (.always (.eventually (.atom "b")))

#eval runExample ψ    /- GBA: 10 / BA: 20 -/

end LTLLib.Tests.Examples
