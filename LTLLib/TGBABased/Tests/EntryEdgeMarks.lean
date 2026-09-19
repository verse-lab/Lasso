/-
  Tests that `dijkstraUpdate`'s merge (`SCC/DijkstraSCC.lean`) does not count a mark on the tree edge entering an SCC's
  root as a mark of that SCC. The merge folds `dfs[roots.top().pos].acc` for each root it pops
  (Renault/Duret-Lutz/Kordon/Poitrenaud, §3.2 line 22), the root it leaves, never the one it settles on.

  All at `numMarks = 1`:
  - `PUSH`/`PUSH`/`PUSH`/`UPDATE` by hand on `A → B → C`, `C → B` with mark 0 only on `A → B`, `UPDATE` must report
    `found = false`.
  - The same graph searched whole must answer `.empty`.
  - The same plus the accepting SCC `A → D → E`, `E → D` with mark 0 on `E → D` must answer `.nonEmpty`, in either
    successor order of `A`.
  - `A → B`, `B → A` with mark 0 on the tree edge `A → B`, internal to `{A, B}`, must answer `.nonEmpty`.

  Sections:
  - The SCC whose only mark is on its entry edge
  - The same, with a real accepting SCC explored afterwards
  - A tree edge that genuinely is internal
  - Report
-/
import LTLLib.TGBABased.SCC.DijkstraSCC
import LTLLib.TGBABased.Tests.TestUtil

namespace LTLLib.Tests.EntryEdgeMarks

open LTLLib LTLLib.Tests

/-! ## The SCC whose only mark is on its entry edge -/

/-- `A = 0, B = 1, C = 2`. -/
def entrySuccs : Nat → Array Nat
  | 0 => #[1]   -- A -> B
  | 1 => #[2]   -- B -> C
  | 2 => #[1]   -- C -> B
  | _ => #[]

/-- Mark 0 on `A → B` only, which enters `{B, C}` rather than sitting inside it. -/
def entryMarks (a b : Nat) : Std.HashSet Nat :=
  if a == 0 && b == 1 then {0} else ∅

-- The three pushes the search makes before `C → B` closes the cycle, then that closing `UPDATE`.
def pushA := dijkstraPush (dijkstraInitAux (State := Nat)) 0 ∅
def pushB := dijkstraPush pushA.1 1 (entryMarks 0 1)
def pushC := dijkstraPush pushB.1 2 (entryMarks 1 2)
def closing := dijkstraUpdate 1 pushC.1 (entryMarks 2 1) 1

/-! ## The same, with a real accepting SCC explored afterwards -/

/-- `A` lists `B` before `D`, so the search reaches `{B, C}` first and `{D, E}` only after it backtracks. -/
def behindSuccs : Nat → Array Nat
  | 0 => #[1, 3]  -- A -> B, then D
  | 1 => #[2]     -- B -> C
  | 2 => #[1]     -- C -> B
  | 3 => #[4]     -- D -> E
  | 4 => #[3]     -- E -> D
  | _ => #[]

/-- The same successors with `D` explored first, to check the answer does not depend on the order. -/
def behindSuccsSwapped : Nat → Array Nat
  | 0 => #[3, 1]
  | n => behindSuccs n

/-- Mark 0 on `A → B` (entering `{B,C}`) and on `E → D` (internal to `{D,E}`). -/
def behindMarks (a b : Nat) : Std.HashSet Nat :=
  if (a == 0 && b == 1) || (a == 4 && b == 3) then {0} else ∅

/-! ## A tree edge that genuinely is internal -/

/-- `A = 0, B = 1`, a two-state cycle. -/
def loopSuccs : Nat → Array Nat
  | 0 => #[1]   -- A -> B
  | 1 => #[0]   -- B -> A
  | _ => #[]

/-- Mark 0 on the tree edge `A → B`, whose endpoints are both inside `{A, B}`. -/
def loopMarks (a b : Nat) : Std.HashSet Nat :=
  if a == 0 && b == 1 then {0} else ∅

/-! ## Report -/

def report : IO Unit :=
  verdict "entry-edge marks" do
    let a ← check "UPDATE reports no counterexample for a mark-free SCC" (closing.2 == false)
    let b ← check "the hint range is the SCC itself" ((dijkstraSccHint closing.1).toList.mergeSort (· < ·) == [1, 2])
    let c ← check "entry-edge mark alone is not accepting"
      (isEmptyResult (dijkstraCheck entrySuccs [0] entryMarks 1))
    let d ← check "real accepting SCC behind it is found"
      (!isEmptyResult (dijkstraCheck behindSuccs [0] behindMarks 1))
    let e ← check "same answer with successors reordered"
      (!isEmptyResult (dijkstraCheck behindSuccsSwapped [0] behindMarks 1))
    let f ← check "internal tree-edge mark still accepting"
      (!isEmptyResult (dijkstraCheck loopSuccs [0] loopMarks 1))
    return [a, b, c, d, e, f]

#eval report

end LTLLib.Tests.EntryEdgeMarks
