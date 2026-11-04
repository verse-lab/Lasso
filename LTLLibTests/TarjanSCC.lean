module

/-
  Differential test of `tarjanCheck` against `dijkstraCheck` on 240 generated graphs crossed with mark counts: the verdicts
  must agree, and every Tarjan witness must pass `checkWitness`. The graphs are deterministic pseudo-random digraphs over
  `Fin n` read as `Nat`, with marks placed by a second hash, so they mix trivial SCCs, nested SCCs and self-loops.

  `tarjanSCCs` is checked against a quadratic mutual-reachability computation and for partitioning the reachable states.
  The last checks are hand-built cases with obvious answers.

  Sections:
  - Generated graphs
  - Agreement and witnesses
  - SCC enumeration against brute force
  - Hand-built cases
-/
import LTLLib.SCC.DijkstraSCC
import LTLLib.SCC.TarjanSCC
import LTLLibTests.TestUtil
meta import LTLLib.SCC.DijkstraSCC
meta import LTLLib.SCC.TarjanSCC
meta import LTLLibTests.TestUtil

namespace LTLLib.Tests.TarjanSCC

open LTLLib LTLLib.Tests

/-! ## Generated graphs -/

private def mix (a b c : Nat) : Nat := (a * 1103515245 + b * 12345 + c * 2654435761) % 1000003

def genSucc (n seed s : Nat) : Array Nat :=
  #[mix s seed 1 % n, mix s seed 2 % n, mix s seed 3 % n]

def genMarks (seed k : Nat) (s t : Nat) : Std.HashSet Nat :=
  if k == 0 then ∅
  else if mix s t seed % 3 == 0 then {mix s t (seed + 5) % k} else ∅

/-! ## Agreement and witnesses -/

def agrees (n seed k : Nat) : Bool :=
  let succs := genSucc n seed
  let marks := genMarks seed k
  isEmptyResult (dijkstraCheck succs [0] marks (derivedExpand succs marks) k) ==
    isEmptyResult (tarjanCheck succs [0] marks (derivedExpand succs marks) k)

def sizes : List Nat := [3, 5, 8, 13, 21]
def seeds : List Nat := [1, 2, 3, 4, 5, 6, 7, 8]
def markCounts : List Nat := [0, 1, 2, 3, 5, 8]

def cases : List (Nat × Nat × Nat) :=
  sizes.flatMap fun n => seeds.flatMap fun seed => markCounts.map fun k => (n, seed, k)

/-- How many of the generated cases each side reports non-empty on, so an agreement of "all empty" cannot
pass by accident. -/
def nonEmptyCount : Nat :=
  (cases.filter fun (n, seed, k) =>
    ! isEmptyResult (tarjanCheck (genSucc n seed) [0] (genMarks seed k)
      (derivedExpand (genSucc n seed) (genMarks seed k)) k)).length

/-! ## SCC enumeration against brute force -/

/-- States reachable from `start` in zero or more steps, by saturation. -/
def reachFrom (succs : Nat → Array Nat) (fuel : Nat) (frontier acc : Std.HashSet Nat) : Std.HashSet Nat :=
  match fuel with
  | 0 => acc
  | f + 1 =>
    let next := frontier.toList.foldl (init := acc) fun a s => (succs s).foldl (·.insert ·) a
    let new := next.toList.filter fun t => ! acc.contains t
    if new.isEmpty then acc else reachFrom succs f (Std.HashSet.ofList new) next

def reachOf (succs : Nat → Array Nat) (n s : Nat) : Std.HashSet Nat :=
  reachFrom succs (n + 1) {s} {s}

/-- Maximal SCCs by mutual reachability, quadratic and obviously correct, for small graphs only. -/
def bruteSCCs (succs : Nat → Array Nat) (n start : Nat) : List (List Nat) :=
  let states := (reachOf succs n start).toList
  let equiv := fun a b => (reachOf succs n a).contains b && (reachOf succs n b).contains a
  let classes := states.foldl (init := ([] : List (List Nat))) fun cs s =>
    match cs.find? (fun c => match c with | r :: _ => equiv r s | [] => false) with
    | some _ => cs.map fun c => match c with
      | r :: _ => if equiv r s then s :: c else c
      | [] => c
    | none => [s] :: cs
  classes.map fun c => c.mergeSort (· < ·)

def normalise (sccs : List (Std.HashSet Nat)) : List (List Nat) :=
  (sccs.map fun c => c.toList.mergeSort (· < ·)).mergeSort (fun a b => a.headD 0 < b.headD 0)

def normaliseL (sccs : List (List Nat)) : List (List Nat) :=
  sccs.mergeSort (fun a b => a.headD 0 < b.headD 0)

def enumAgrees (n seed : Nat) : Bool :=
  normalise (tarjanSCCs (genSucc n seed) [0]) == normaliseL (bruteSCCs (genSucc n seed) n 0)

/-- Every reachable state lands in exactly one enumerated SCC. -/
def enumPartitions (n seed : Nat) : Bool :=
  let sccs := tarjanSCCs (genSucc n seed) [0]
  let all := sccs.flatMap (·.toList)
  let reach := (reachOf (genSucc n seed) n 0).toList
  all.length == reach.length && reach.all fun s => all.contains s

/-! ## Hand-built cases -/

-- 0 → 1 → 2 → 0, one mark on the closing edge, so the ring is the only accepting cycle
def ringSucc : Nat → Array Nat
  | 0 => #[1] | 1 => #[2] | _ => #[0]

def ringMarks (s _t : Nat) : Std.HashSet Nat := if s == 2 then {0} else ∅

-- 0 → 1, 1 → 1, with the mark only on the edge into the sink, never on the self-loop
def sinkSucc : Nat → Array Nat
  | 0 => #[1] | _ => #[1]

def sinkMarks (s t : Nat) : Std.HashSet Nat := if s == 0 && t == 1 then {0} else ∅

-- 0 → 1 → 0 with no marks at all, so any cycle is accepting at `numMarks = 0`
def pairSucc : Nat → Array Nat
  | 0 => #[1] | _ => #[0]

def report : IO Unit :=
  verdict "Tarjan agrees with Dijkstra and its witnesses re-validate" do
    IO.println s!"    {cases.length} generated cases, {nonEmptyCount} of them non-empty"
    let a ← check "every generated case gets the same verdict from both"
      (cases.all fun (n, seed, k) => agrees n seed k)
    let b ← check "the ring's single mark is found"
      (! isEmptyResult (tarjanCheck ringSucc [0] ringMarks (derivedExpand ringSucc ringMarks) 1))
    let c ← check "a mark reachable only outside every cycle is not accepting"
      (isEmptyResult (tarjanCheck sinkSucc [0] sinkMarks (derivedExpand sinkSucc sinkMarks) 1))
    let d ← check "at zero marks any cycle is accepting"
      (! isEmptyResult (tarjanCheck pairSucc [0] (fun _ _ => ∅) (derivedExpand pairSucc (fun _ _ => ∅)) 0))
    let e ← check "a mark index no edge carries leaves the ring empty"
      (isEmptyResult (tarjanCheck ringSucc [0] ringMarks (derivedExpand ringSucc ringMarks) 2))
    IO.println "  the ring witness, re-validated against the graph:"
    let ws ← checkWitness ringSucc ringMarks 1
      (tarjanCheck ringSucc [0] ringMarks (derivedExpand ringSucc ringMarks) 1)
      -- one generated non-empty case, re-validated the same way
    let ws2 ← match cases.find? (fun (n, seed, k) =>
        k > 1 && ! isEmptyResult (tarjanCheck (genSucc n seed) [0] (genMarks seed k)
          (derivedExpand (genSucc n seed) (genMarks seed k)) k)) with
      | none => check "a generated case is non-empty" false >>= (pure [·])
      | some (n, seed, k) => do
        IO.println s!"  a generated witness at n={n} seed={seed} marks={k}:"
        checkWitness (genSucc n seed) (genMarks seed k) k
          (tarjanCheck (genSucc n seed) [0] (genMarks seed k)
            (derivedExpand (genSucc n seed) (genMarks seed k)) k)
    let j ← check "the enumeration matches brute-force mutual reachability on every generated graph"
      ((sizes.flatMap fun n => seeds.map fun seed => (n, seed)).all fun (n, seed) => enumAgrees n seed)
    let k ← check "the enumeration partitions the reachable states"
      ((sizes.flatMap fun n => seeds.map fun seed => (n, seed)).all fun (n, seed) => enumPartitions n seed)
    let l ← check "the ring is one SCC of three, the restriction to two of its states splits it"
      (normalise (tarjanSCCs ringSucc [0]) == [[0, 1, 2]] &&
        normalise (tarjanSCCsWithin ringSucc (Std.HashSet.ofList [0, 1, 2]) (fun s => s != 2))
          == [[0], [1]])
    return [a, b, c, d, e, j, k, l] ++ ws ++ ws2

#eval report

end LTLLib.Tests.TarjanSCC
