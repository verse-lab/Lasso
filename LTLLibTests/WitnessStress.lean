module

/-
  Tests `dijkstraCheck`'s witness extraction (`checkWithWitness` in `SCC/GenericDFS.lean`) on a graph where the marks of
  the accepting cycle are spread over a DFS branch abandoned before the back edge that closes the cycle.

  Graph: main cycle `A → B → C → A` with mark 0 on `C → A`, plus a side branch `B → D → B` with mark 1 on `D → B`, and
  `B` exploring `D` before `C`. When `C → A` closes the main cycle, `D` is off the DFS stack but still in `live`, so the
  witness cannot be read off `live` positionally.
-/
import LTLLib.SCC.DijkstraSCC
import LTLLibTests.TestUtil
meta import LTLLib.SCC.DijkstraSCC
meta import LTLLibTests.TestUtil

namespace LTLLib.Tests.WitnessStress

open LTLLib LTLLib.Tests

/-- `A = 0, B = 1, C = 2, D = 3`, with `D` explored and backtracked out of before the main cycle closes. -/
def succs : Nat → Array Nat
  | 0 => #[1]     -- A -> B
  | 1 => #[3, 2]  -- B -> D, then C
  | 2 => #[0]     -- C -> A
  | 3 => #[1]     -- D -> B
  | _ => #[]

/-- `C → A` carries mark 0, `D → B` carries mark 1, every other edge is unmarked. -/
def marks (a b : Nat) : Std.HashSet Nat :=
  if a == 2 && b == 0 then {0}
  else if a == 3 && b == 1 then {1}
  else ∅

def report : IO Unit :=
  verdict "witness extraction across an abandoned branch" do
    checkWitness succs marks 2 (dijkstraCheck succs [0] marks (derivedExpand succs marks) 2)

#eval report

end LTLLib.Tests.WitnessStress
