/-
  Tests the shape of a mixed fairness assumption after the split. `hoistFairness` returns one list of options per
  conjunct of the negated property, an option being a region and a list of marks, and `crossAllDNF` multiplies them out.
  The checks pin what each kind of fairness contributes, and compare the total number of options, the cost of a
  prune-based check, against the number of crossed disjuncts, the cost of the router.

  The assumption is `strong ∧ weak ∧ nested`, the property `□¬bad → □◇served` contributes a hoisted fair half and a kept
  safety half.

  Sections:
  - The mixed assumption
  - What each kind contributes
-/
import LTLLib.LTL.FairNormalForm
import LTLLib.TGBABased.Fairness.FairRouter
import LTLLib.TGBABased.LTLtoTGBA.Pipeline
import LTLLib.TGBABased.Tests.TestUtil

namespace LTLLib.Tests.FairOptions

open LTLLib LTLLib.Tests

/-! ## The mixed assumption -/

def gf (a : Nat) : Formula Nat := .always (.eventually (.atom a))
def fgf (a : Nat) : Formula Nat := .eventually (.always (.atom a))

/-- `⋀ᵢ (GF aᵢ → GF bᵢ)`, the shape whose crossing costs `2ⁿ`. -/
def strong (s : Nat) : Formula Nat :=
  Formula.conj ((List.range s).map fun i => .implies (gf (10 + 2*i)) (gf (11 + 2*i)))

/-- `⋀ⱼ (FG cⱼ → GF dⱼ)`. -/
def weak (w : Nat) : Formula Nat :=
  Formula.conj ((List.range w).map fun j => .implies (fgf (50 + 2*j)) (gf (51 + 2*j)))

/-- `□◇(r ∧ ◇(w ∧ ◇e))`, the nested cycle fairness TLC has to build a tableau for. -/
def nested : Formula Nat :=
  .always (.eventually (.and (.atom 90) (.eventually (.and (.atom 91) (.eventually (.atom 92))))))

/-- `□¬bad → □◇served`, a safety half that stays and a fair half that is hoisted. -/
def property : Formula Nat := .implies (.always (.not (.atom 95))) (gf 96)

def whole (s w : Nat) : Formula Nat :=
  .implies (.and (strong s) (.and (weak w) nested)) property

def splitOf (s w : Nat) : List (List (NNF.FairDisjunct Nat)) × List (NNF Nat) :=
  hoistFairness ((whole s w).toNNF false).splitConj

def optionCount (s w : Nat) : Nat := ((splitOf s w).1.map (·.length)).foldl (· + ·) 0
def crossedCount (s w : Nat) : Nat := (NNF.crossAllDNF (splitOf s w).1).length

def keptStates (s w : Nat) : Nat :=
  let φ := keptProperty (splitOf s w).2
  match ltl3ba (φ.toNNF false) with
  | some t => t.states.size
  | none => 0

/-! ## What each kind contributes -/

def showOpt (d : NNF.FairDisjunct Nat) : String := s!"({d.1.toString} | {d.2.map BoolFormula.toString})"

/-- Region, and how many marks, for every option of every conjunct of one formula's negation. -/
def shapeOf (φ : Formula Nat) : List (List (String × Nat)) :=
  (hoistFairness (φ.toNNF false).splitConj).1.map fun ds => ds.map fun d => (d.1.toString, d.2.length)

def report : IO Unit :=
  verdict "a mixed fairness assumption splits into conjuncts of options" do
    for ds in (splitOf 2 1).1 do
      IO.println s!"    {ds.map showOpt}"
    IO.println s!"    kept {((splitOf 2 1).2).map NNF.toString}, automaton {keptStates 2 1} states"
    let a ← check "two strong, one weak, one nested and the property's fair half give five conjuncts"
      ((splitOf 2 1).1.length == 5)
    -- a strong pair offers a region with no marks, or no region with one mark, so it prunes deterministically
    let b ← check "a strong pair is two options, one region-only and one mark-only"
      (shapeOf (.implies (strong 1) (gf 96)) == [[("¬10", 0), ("⊤", 1)], [("¬96", 0)]])
    -- both weak options carry region ⊤, so an unsatisfied one kills the SCC rather than pruning it
    let c ← check "a weak pair is two options, both with region ⊤ and one mark"
      (shapeOf (.implies (weak 1) (gf 96)) == [[("⊤", 1), ("⊤", 1)], [("¬96", 0)]])
    -- the nested cycle fairness flattens to three marks and no region, so no tableau anywhere
    let d ← check "the nested cycle fairness is one option with three marks"
      (shapeOf (.implies nested (gf 96)) == [[("⊤", 3)], [("¬96", 0)]])
    let e ← check "the property's fair half is one option, a region with no marks"
      (shapeOf property == [[("¬96", 0)]])
    let f ← check "the property's safety half is kept and compiles to a one-state automaton"
      ((hoistFairness (property.toNNF false).splitConj).2.length == 1 &&
        keptStates 2 1 == 1)
    -- options against crossed disjuncts
    for (s, w) in [(1,1), (2,1), (2,2), (3,2), (4,3), (6,4)] do
      IO.println s!"    {s} strong, {w} weak: {(splitOf s w).1.length} conjuncts, \
{optionCount s w} options, {crossedCount s w} crossed disjuncts"
    -- options are `2s + 2w + 2`, the nested conjunct and the property's fair half adding one each
    let g ← check "options stay linear in the number of pairs"
      ([(1,1), (2,1), (2,2), (3,2), (4,3), (6,4)].all fun (s, w) => optionCount s w == 2*s + 2*w + 2)
    let h ← check "crossed disjuncts are exponential in the number of pairs"
      ([(1,1), (2,1), (2,2), (3,2), (4,3), (6,4)].all fun (s, w) => crossedCount s w == 2 ^ (s + w))
    let i ← check "at six strong and four weak the gap is 22 against 1024"
      (optionCount 6 4 == 22 && crossedCount 6 4 == 1024)
    return [a, b, c, d, e, f, g, h, i]

#eval report

end LTLLib.Tests.FairOptions
