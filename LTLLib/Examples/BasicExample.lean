/-
  Minimal end-to-end example: LTL formula → tableau → GBA → (degeneralized) BA

  Formula: □(a → ◇b)  ("whenever `a` holds, `b` eventually holds").
-/
import LTLLib.Examples.BuildPrint

namespace LTLLib.Examples

abbrev Prop' := String

/-- `□(a → ◇b)`: whenever `a` holds, `b` eventually holds. -/
def φ : Formula Prop' := .always (.implies (.atom "a") (.eventually (.atom "b")))

#eval runExample φ

end LTLLib.Examples
