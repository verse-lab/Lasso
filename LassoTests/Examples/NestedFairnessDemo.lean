module

/-
  This file demonstrates a fairness assumption that our pipeline hoists but TLC's classifier does not.

  As a running example: a request-processing server

  A server sits idle until it accepts a request, processes it, and sends a reply.
  - idle  -- accept -->  recv  -- process -->  work  -- send -->  emit  -- finish -->  idle
  - From recv or work the server may instead abort, dropping the request and returning to idle.
  - It may also sit idle forever.

  Q: Is every request eventually served, i.e. does `□◇served` hold?
  - No: the server can sit idle forever, and it can accept-then-abort forever.

  What fairness fixes it:
  - `□◇recv` is not enough, the accept-then-abort loop satisfies it and still never serves.
  - `□◇(recv ∧ ◇(work ∧ ◇emit))`, "the whole receive-process-send cycle completes infinitely often",
    is enough, and is the natural way to write it.

  Why this formula is the interesting one:
  - TLC classifies a conjunct as `AEState` only when it is literally `[]<>P` for a state predicate `P`.
    Here the operand `recv ∧ ◇(work ∧ ◇emit)` is not a state predicate, so TLC builds a tableau for it.
  - [LSFZ16] Appendix A's rule `GF(φ ∧ ◇ψ) ≡ GF φ ∧ GF ψ` applies twice and flattens it to
    `□◇recv ∧ □◇work ∧ □◇emit`, three acceptance marks and no automaton at all.
-/
import Lasso
import Lasso.LTLtoTGBA.Pipeline
meta import Lasso.LTLtoTGBA.Pipeline
meta import Lasso.Fairness.FairRouter

namespace Lasso.Tests.Examples.NestedFairness

open Lasso

inductive Stage where
  | idle | recv | work | emit
deriving BEq, Hashable, Repr, Inhabited, DecidableEq

instance : LawfulBEq Stage where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

def succ : Stage → Array Stage
  | .idle => #[.idle, .recv]
  | .recv => #[.work, .idle]  -- the abort edge is what makes `□◇recv` too weak
  | .work => #[.emit, .idle]
  | .emit => #[.idle]

def label : Stage → Std.HashSet String
  | .idle => ∅
  | .recv => {"recv"}
  | .work => {"work"}
  | .emit => {"emit", "served"}

def init : List Stage := [.idle]

theorem fr : FiniteReach init succ :=
  .of_forall_mem [.idle, .recv, .work, .emit] fun s => by cases s <;> simp

def served : Formula String := .always (.eventually (.atom "served"))

/-- `□◇(recv ∧ ◇(work ∧ ◇emit))`, the whole cycle completing infinitely often. -/
def cycleFair : Formula String :=
  .always (.eventually (.and (.atom "recv")
    (.eventually (.and (.atom "work") (.eventually (.atom "emit"))))))

/-- `□◇recv`, which the accept-then-abort loop already satisfies. -/
def recvFair : Formula String := .always (.eventually (.atom "recv"))

def tgbaStatesOf (φ : Formula String) : Nat :=
  match ltl3ba (φ.toNNF false) with
  | some t => t.states.size
  | none => 0

def verdict {σ} : EmptinessResult σ → String
  | .empty _ => "holds"
  | .nonEmpty _ _ => "fails"

def exploredOf {σ} : EmptinessResult σ → Nat
  | .empty k => k
  | .nonEmpty stem loop => stem.length + loop.length

def report : IO Unit := do
  let n := cycleFair.toNNF true
  IO.println s!"is a fairness            : {n.isFairness}"
  IO.println s!"route                    : {repr n.classify}"
  match NNF.fnf n with
  | some ds =>
    IO.println s!"disjuncts after flattening: {ds.length}"
    for d in ds do
      IO.println s!"  FG({d.1}) with marks {d.2.map BoolFormula.toString}"
  | none => IO.println "does not flatten"
  IO.println ""
  IO.println s!"automaton for the property alone          : {tgbaStatesOf served} states"
  IO.println s!"automaton with the nested fairness compiled: {tgbaStatesOf (.implies cycleFair served)} states"
  IO.println s!"automaton with the flat fairness compiled  : {tgbaStatesOf (.implies recvFair served)} states"
  IO.println ""
  IO.println s!"□◇served, no assumption        : {verdict (modelCheckTGBA served init (LSys.unlabelled succ) label)}"
  IO.println s!"□◇served, under □◇recv          : {verdict (modelCheckUnderFairness (.implies recvFair served) init (LSys.unlabelled succ) label)}"
  IO.println s!"□◇served, under the cycle fairness: {verdict (modelCheckUnderFairness (.implies cycleFair served) init (LSys.unlabelled succ) label)}"
  IO.println ""
  IO.println s!"product states explored, hoisted : {exploredOf (modelCheckUnderFairness (.implies cycleFair served) init (LSys.unlabelled succ) label)}"
  IO.println s!"product states explored, compiled: {exploredOf (modelCheckTGBA (.implies cycleFair served) init (LSys.unlabelled succ) label)}"

#eval report

end Lasso.Tests.Examples.NestedFairness
