/-
  A minimal end-to-end example: LTL formula → tableau → GBA → (degeneralized)
  Büchi automaton, printed via `#eval` using `BuildPrint.runExample`.

  Formula: □(a → ◇b)  ("whenever `a` holds, `b` eventually holds").
-/
import LTLLib.Examples.BuildPrint

namespace LTLLib.Examples

/-- Atomic propositions are plain strings for this example. -/
abbrev Prop' := String

/-- `□(a → ◇b)`: whenever `a` holds, `b` eventually holds. -/
def φ : Formula Prop' := .always (.implies (.atom "a") (.eventually (.atom "b")))

#eval runExample φ

end LTLLib.Examples
