module

/-
  Differential tests of `NNF.rtrans` against `Lasso.evalNNF`: the one-step expansion `φ.rtrans` encodes must agree with
  the evaluator at every lasso position, also after merging equal targets (`mergeByTarget`) or splitting away subsumed
  targets (`splitByTarget`).

  Sections:
  - One-step expansion
  - Reductions preserve meaning
  - Shape checks
-/
import LTLLib.LTL.Subformulas
import LTLLibTests.LTLtoTGBA.Eval
import LTLLibTests.LTLtoTGBA.Gen
import LTLLib.LTLtoTGBA.VWAA
import LTLLibTests.TestUtil
meta import LTLLib.LTL.Subformulas
meta import LTLLibTests.LTLtoTGBA.Eval
meta import LTLLibTests.LTLtoTGBA.Gen
meta import LTLLib.LTLtoTGBA.VWAA
meta import LTLLibTests.TestUtil

namespace LTLLib.LTLtoTGBA.Tests.VWAATests

open LTLLib LTLLib.Tests LTLLib.LTLtoTGBA.Tests

/-- Does some transition of `ts` fire at position `i` of `l`, with every target of `table` holding at `l.next i`? -/
def holdsVia (l : Lasso String) (table : SubformulaTable String) (ts : List (DNF String × Nat)) (i : Nat) : Bool :=
  ts.any fun (g, t) =>
    DNF.eval g (l.wordAt i) && (maskMembers t).all fun j =>
      (l.evalNNF (table.formulaOf j)).getD (l.next i) false

/-- `φ.rtrans` over `φ`'s own subformula table. -/
def rtransOf (φ : NNF String) : List (DNF String × Nat) := φ.rtrans (SubformulaTable.build φ).idOf

def transHolds (l : Lasso String) (φ : NNF String) (i : Nat) : Bool :=
  holdsVia l (SubformulaTable.build φ) (rtransOf φ) i

/-! ## One-step expansion -/

private def genCases (seed trials : Nat) : List (NNF String × Lasso String × Nat) :=
  go trials (mkStdGen seed)
where go : Nat → StdGen → List (NNF String × Lasso String × Nat)
  | 0, _ => []
  | n + 1, g =>
    let (φ, g1) := genFormula props 8 g
    let (l, g2) := genLasso props 6 5 g1
    let (i, g3) := randNat g2 0 (l.size - 1)
    (φ, l, i) :: go n g3

private def cases : List (NNF String × Lasso String × Nat) := genCases 314159 500

/-! ## Reductions preserve meaning -/

private def mergedHolds (l : Lasso String) (φ : NNF String) (i : Nat) : Bool :=
  holdsVia l (SubformulaTable.build φ) (mergeByTarget (rtransOf φ)) i

private def splitHolds (l : Lasso String) (φ : NNF String) (i : Nat) : Bool :=
  holdsVia l (SubformulaTable.build φ) (splitByTarget (rtransOf φ)) i

/-! ## Shape checks -/

private def targetsInTable (φ : NNF String) : Bool :=
  let n := (SubformulaTable.build φ).formulas.size
  (rtransOf φ).all fun (_, t) => t < 2 ^ n

private def isFinal : NNF String → Bool
  | .until _ _ => true
  | _ => false

def report : IO Unit :=
  verdict "NNF.rtrans against Lasso.evalNNF" do
    let a ← check "one-step expansion agrees with the evaluator at every position"
      (cases.all fun (φ, l, i) => (l.evalNNF φ).getD i false == transHolds l φ i)
    let b ← check "every target of φ.rtrans is a set of ids of φ's subformula table"
      (cases.all fun (φ, _, _) => targetsInTable φ)
    let c ← check "no transition of φ.rtrans has an unsatisfiable guard"
      (cases.all fun (φ, _, _) => (rtransOf φ).all fun (g, _) => !DNF.isEmpty g)
    let d ← check "mergeByTarget preserves the one-step expansion"
      (cases.all fun (φ, l, i) => transHolds l φ i == mergedHolds l φ i)
    let e ← check "splitByTarget preserves the one-step expansion"
      (cases.all fun (φ, l, i) => transHolds l φ i == splitHolds l φ i)
    let f ← check "φ.rtrans has no two transitions with the same target"
      (cases.all fun (φ, _, _) =>
        let m := rtransOf φ
        (List.range m.length).all fun i => (List.range m.length).all fun j => i == j || m[i]!.2 != m[j]!.2)
    let g ← check "U states are exactly the isFinal formulas among a sample"
      ((List.range 20).all fun n =>
        let (φ, _) := genFormula props n (mkStdGen (1000 + n))
        match φ with | .until _ _ => isFinal φ | _ => ! isFinal φ)
    return [a, b, c, d, e, f, g]

#eval report

end LTLLib.LTLtoTGBA.Tests.VWAATests
