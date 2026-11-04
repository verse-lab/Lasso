module

/-
  A ground-truth NNF evaluator on lasso words, independent of every translator in this folder, one `Bool` per lasso
  position for each subformula, bottom-up. `until` is the least fixpoint of `U[i] = ψ[i] ∨ (φ[i] ∧ U[next i])`, reached
  after `size + 1` relaxation steps since a witnessing path never revisits a position, and `release` is read off `φ R ψ ≡ ¬(¬φ U ¬ψ)`.

  Defines:
  - `leastFixpointUntil`: the least fixpoint behind `until` and `release`
  - `Lasso.evalNNF`, `Lasso.holdsNNF`: one Bool per position for every subformula, and truth at position 0

  Sections:
  - Least fixpoint until
  - Evaluation
-/
public import Lasso.LTL.Syntax
public import LassoTests.LTLtoTGBA.Lasso

public section

namespace Lasso.LTLtoTGBA.Tests

variable {α : Type u} [BEq α] [Hashable α]

/-! ## Least fixpoint until -/

private def untilStep (n : Nat) (next : Nat → Nat) (φarr ψarr u : Array Bool) : Array Bool :=
  (Array.range n).map fun i => ψarr.getD i false || (φarr.getD i false && u.getD (next i) false)

/-- The least fixpoint of `U[i] = ψ[i] ∨ (φ[i] ∧ U[next i])` on a finite state graph with successor `next`. -/
def leastFixpointUntil (n : Nat) (next : Nat → Nat) (φarr ψarr : Array Bool) : Array Bool :=
  (List.range (n + 1)).foldl (fun u _ => untilStep n next φarr ψarr u) (Array.replicate n false)

/-! ## Evaluation -/

/-- One `Bool` per lasso position for `φ`, bottom-up over its subformulas. -/
def Lasso.evalNNF (l : Lasso α) : NNF α → Array Bool
  | .tt => Array.replicate l.size true
  | .ff => Array.replicate l.size false
  | .prop a => (Array.range l.size).map fun i => (l.wordAt i).contains a
  | .nprop a => (Array.range l.size).map fun i => !(l.wordAt i).contains a
  | .and φ ψ => Array.zipWith (· && ·) (l.evalNNF φ) (l.evalNNF ψ)
  | .or φ ψ => Array.zipWith (· || ·) (l.evalNNF φ) (l.evalNNF ψ)
  | .next φ => let e := l.evalNNF φ; (Array.range l.size).map fun i => e.getD (l.next i) false
  | .until φ ψ => leastFixpointUntil l.size l.next (l.evalNNF φ) (l.evalNNF ψ)
  | .release φ ψ =>
    (leastFixpointUntil l.size l.next ((l.evalNNF φ).map Bool.not) ((l.evalNNF ψ).map Bool.not)).map Bool.not

/-- Does `l` satisfy `φ`, read at position `0`. -/
def Lasso.holdsNNF (l : Lasso α) (φ : NNF α) : Bool := (l.evalNNF φ).getD 0 false

end Lasso.LTLtoTGBA.Tests
