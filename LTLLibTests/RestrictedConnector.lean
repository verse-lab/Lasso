module

/-
  Tests `checkWithWitness`'s connector search (`SCC/GenericDFS.lean`), where `stitchCycleAt`'s connectors are restricted
  to the accepting subset `ops.sccHint` returns. Dijkstra reports as soon as marks are covered, so the subset need not be
  maximal, and this graph leaves an ancestor state outside the merged range.

  Graph: `R → A → B → [D, C]`, with `B` exploring `D` before `C`. `D`'s marked back edge closes to the ancestor `B`,
  so `D` is not flushed as a trivial SCC, and `C`'s marked back edge closes to `A`, so the merge stops at `A` and
  leaves `R` outside the hint range.
-/
import LTLLib.SCC.DijkstraSCC
import LTLLibTests.TestUtil
meta import LTLLib.SCC.DijkstraSCC
meta import LTLLibTests.TestUtil

namespace LTLLib.Tests.RestrictedConnector

open LTLLib LTLLib.Tests

/-- `R = 0, A = 1, B = 2, D = 3, C = 4`. -/
def succs : Nat → Array Nat
  | 0 => #[1]     -- R -> A
  | 1 => #[2]     -- A -> B
  | 2 => #[3, 4]  -- B -> D, then C
  | 3 => #[2]     -- D -> B
  | 4 => #[1]     -- C -> A
  | _ => #[]

/-- `C → A` carries mark 0, `D → B` carries mark 1, every other edge is unmarked. -/
def marks (a b : Nat) : Std.HashSet Nat :=
  if a == 4 && b == 1 then {0}
  else if a == 3 && b == 2 then {1}
  else ∅

def report : IO Unit :=
  verdict "connectors stay inside a non-maximal hint range" do
    checkWitness succs marks 2 (dijkstraCheck succs [0] marks (derivedExpand succs marks) 2)

#eval report

end LTLLib.Tests.RestrictedConnector
