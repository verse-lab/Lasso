module

/-
  Minimal end-to-end example: LTL formula → tableau → GBA → (degeneralized) BA

  Formula: □(a → ◇b)  ("whenever `a` holds, `b` eventually holds").
-/
import LTLLibTests.Examples.BuildPrint
meta import LTLLibTests.Examples.BuildPrint

namespace LTLLib.Tests.Examples

abbrev Prop' := String

/-- `□(a → ◇b)`: whenever `a` holds, `b` eventually holds. -/
def φ : Formula Prop' := .always (.implies (.atom "a") (.eventually (.atom "b")))

#eval runExample φ

end LTLLib.Tests.Examples
