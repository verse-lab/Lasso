module

/-
  Tests `TGBA.degeneralize` against the original `TGBA`: `dijkstraCheck` on the bare graphs, without a system product,
  must report the same emptiness for the `ltl3ba` automaton of each negated formula and its degeneralization.

  Covers zero marks (`◇p`), one mark (`□◇p`), two marks with a round-robin (`□◇p ∧ □◇q`), `p U q`, and `p ∧ ¬p`.
-/
import LTLLib.TGBABased.Degeneralization.DegeneralBridge
import LTLLib.TGBABased.LTLtoTGBA.Pipeline
import LTLLib.TGBABased.SCC.DijkstraSCC
import LTLLibTests.TGBABased.TestUtil
meta import LTLLib.TGBABased.Degeneralization.DegeneralBridge
meta import LTLLib.TGBABased.LTLtoTGBA.Pipeline
meta import LTLLib.TGBABased.SCC.DijkstraSCC
meta import LTLLibTests.TGBABased.TestUtil

namespace LTLLib.Tests.Degeneralization

open LTLLib LTLLib.Tests

def tgbaOf (φ : Formula String) : Option (TGBA String) := ltl3ba (φ.toNNF false)

def bareEmpty (tgba : TGBA String) : Bool :=
  isEmptyResult (dijkstraCheck tgba.succStates tgba.initialStates.toList tgba.edgeMarks tgba.numAcceptSets)

def degenEmpty (tgba : TGBA String) : Bool :=
  let tba := tgba.degeneralize
  isEmptyResult (dijkstraCheck tba.succStates tba.initialStates.toList tba.edgeMarks tba.numAcceptSets)

/-- The formula's automaton and its degeneralization agree on emptiness, and the degeneralization has a single mark. -/
def agrees (φ : Formula String) : Bool :=
  match tgbaOf φ with
  | some tgba => bareEmpty tgba == degenEmpty tgba && tgba.degeneralize.numAcceptSets == 1
  | none => false

def report : IO Unit :=
  verdict "TGBA.degeneralize agrees with the un-degeneralized TGBA on emptiness" do
    let a ← check "atom p" (agrees (.atom "p"))
    let b ← check "eventually p (zero marks)" (agrees (.eventually (.atom "p")))
    let c ← check "always eventually p (one mark)" (agrees (.always (.eventually (.atom "p"))))
    let d ← check "always eventually p and always eventually q (two marks, round-robin)"
      (agrees (.and (.always (.eventually (.atom "p"))) (.always (.eventually (.atom "q")))))
    let e ← check "p until q" (agrees (.until (.atom "p") (.atom "q")))
    let f ← check "p and not p" (agrees (.and (.atom "p") (.not (.atom "p"))))
    return [a, b, c, d, e, f]

#eval report

end LTLLib.Tests.Degeneralization
