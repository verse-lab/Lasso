/-
  A slightly more complicated example that exercises a *generalized* Büchi
  acceptance condition with two acceptance sets.

  Formula: □◇a ∧ □◇b  ("`a` holds infinitely often, and `b` holds infinitely
  often") — the classic motivating example for GBAs: two independent
  fairness/liveness obligations that a single Büchi acceptance set cannot
  express without a state-space blowup (you'd need to track "which of a/b
  am I still waiting on" as part of the state, which is exactly what
  degeneralization does via `acceptIdx`).

  Each `always (eventually _)` contributes one Until-subformula
  (`⊤ U a` and `⊤ U b` respectively), and the GBA construction allocates one
  acceptance set per distinct Until-subformula (`GBA.lean`, `acceptSets`) —
  so this formula produces exactly two acceptance sets, `F0` and `F1`.
-/
import LTLLib.Examples.BuildPrint

namespace LTLLib.Examples

/-- Atomic propositions are plain strings for this example. -/
abbrev Prop' := String

/-- `□◇a ∧ □◇b`: `a` holds infinitely often, and `b` holds infinitely often. -/
def ψ : Formula Prop' :=
  .and (.always (.eventually (.atom "a"))) (.always (.eventually (.atom "b")))

#eval runExample ψ

end LTLLib.Examples
