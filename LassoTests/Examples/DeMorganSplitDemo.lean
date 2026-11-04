module

/-
  This file demonstrates why the router splits after `toNNF` rather than on the surface syntax.

  As a running example: a request server that can break

  A server accepts a request, processes it, and emits a reply. From idle it may also slip into a broken
  mode, which it never leaves, and in which it still cycles through all three stages but never actually
  serves anything. From the receiving or working stage it may abort back to idle.

  Q: is every request eventually served, i.e. does `□◇served` hold?
  - No, for two independent reasons: the server can accept-then-abort forever, and it can break.

  The assumption that fixes it needs one conjunct for each reason:
  - `□◇(recv ∧ ◇(work ∧ ◇emit))` rules out the abort loop. It is a fairness and it flattens, so it is
    hoisted onto the product as three acceptance marks.
  - `□¬broken` rules out the broken mode. It is purely universal but not a pure eventuality, so it is not
    a fairness and it stays in the property.

  Where the splitting matters: those two conjuncts are only visible as conjuncts after negation normal
  form if the user writes them under a negation. `¬(¬□¬broken ∨ ¬cycleFair)` means exactly the same thing
  as `□¬broken ∧ cycleFair`, but its outermost node is a negation, not a conjunction.

  Splitting the surface syntax gives one conjunct there, whose negation normal form is a conjunction mixing
  a fairness with a non-fairness. `isFairness` says no to that conjunction as a whole, so nothing is
  hoisted and the entire assumption goes to the translator. Splitting after `toNNF` sees both conjuncts and
  hoists the one it can.

  Both answers are correct either way. What changes is the size of the automaton the translator builds, which
  the report measures. The split runs on the negated property, so `◇□¬served` joins the two conjuncts above and
  is hoisted with them, which is why two conjuncts are hoisted rather than one.
-/
import Lasso
import Lasso.LTLtoTGBA.Pipeline
meta import Lasso.LTLtoTGBA.Pipeline
meta import Lasso.Fairness.FairRouter

namespace Lasso.Tests.Examples.DeMorganSplit

open Lasso

inductive Stage where
  | idle | recv | work | emit
  | bidle | brecv | bwork | bemit
deriving BEq, Hashable, Repr, Inhabited, DecidableEq

instance : LawfulBEq Stage where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

def succ : Stage → Array Stage
  | .idle => #[.idle, .recv, .bidle]  -- may stall, work, or break
  | .recv => #[.work, .idle]          -- the abort edge
  | .work => #[.emit, .idle]
  | .emit => #[.idle]
  | .bidle => #[.brecv]               -- broken mode still cycles, but never serves
  | .brecv => #[.bwork]
  | .bwork => #[.bemit]
  | .bemit => #[.bidle]

def label : Stage → Std.HashSet String
  | .idle => ∅
  | .recv => {"recv"}
  | .work => {"work"}
  | .emit => {"emit", "served"}
  | .bidle => {"broken"}
  | .brecv => {"recv", "broken"}
  | .bwork => {"work", "broken"}
  | .bemit => {"emit", "broken"}

def init : List Stage := [.idle]

theorem fr : FiniteReach init succ :=
  .of_forall_mem [.idle, .recv, .work, .emit, .bidle, .brecv, .bwork, .bemit] fun s => by cases s <;> simp

def served : Formula String := .always (.eventually (.atom "served"))

/-- `□◇(recv ∧ ◇(work ∧ ◇emit))`, a fairness that flattens to three marks. -/
def cycleFair : Formula String :=
  .always (.eventually (.and (.atom "recv")
    (.eventually (.and (.atom "work") (.eventually (.atom "emit"))))))

/-- `□¬broken`, purely universal but not a pure eventuality, so not a fairness. -/
def notBroken : Formula String := .always (.not (.atom "broken"))

/-- The assumption with its conjunction visible on the surface. -/
def plainForm : Formula String := .and notBroken cycleFair

/-- The same assumption under a negation, where the conjunction only appears after `toNNF`. -/
def deMorganForm : Formula String :=
  .not (.or (.not notBroken) (.not cycleFair))

/-- Splitting the surface syntax instead of the negation normal form. Kept here only for the comparison. -/
def surfaceSplit : Formula String → List (Formula String)
  | .and φ ψ => surfaceSplit φ ++ surfaceSplit ψ
  | φ => [φ]

def tgbaStatesOf (φ : Formula String) : Nat :=
  match ltl3ba (φ.toNNF false) with
  | some t => t.states.size
  | none => 0

/-- Hoisted count, kept count, and the automaton the translator would then build. -/
def measure (conjuncts : List (NNF String)) : Nat × Nat × Nat :=
  let s := hoistFairness conjuncts
  (s.1.length, s.2.length, tgbaStatesOf (keptProperty s.2))

def report : IO Unit := do
  for (name, fair) in [("plain form   ", plainForm), ("de Morgan form", deMorganForm)] do
    let negated := (Formula.implies fair served).toNNF false
    let surface := measure ((surfaceSplit fair).map (·.toNNF true) ++ (served.toNNF false).splitConj)
    let nnf := measure negated.splitConj
    IO.println s!"{name}"
    IO.println s!"  surface split: {surface.1} hoisted, {surface.2.1} kept, \
automaton {surface.2.2} states"
    IO.println s!"  NNF split    : {nnf.1} hoisted, {nnf.2.1} kept, automaton {nnf.2.2} states"
  IO.println ""
  IO.println s!"□◇served, no assumption      : {isEmptyResult (modelCheckTGBA served init (LSys.unlabelled succ) label)}"
  IO.println s!"□◇served, cycle fairness only: {isEmptyResult (modelCheckUnderFairness (.implies cycleFair served) init (LSys.unlabelled succ) label)}"
  IO.println s!"□◇served, □¬broken only      : {isEmptyResult (modelCheckUnderFairness (.implies notBroken served) init (LSys.unlabelled succ) label)}"
  IO.println s!"□◇served, plain form         : {isEmptyResult (modelCheckUnderFairness (.implies plainForm served) init (LSys.unlabelled succ) label)}"
  IO.println s!"□◇served, de Morgan form     : {isEmptyResult (modelCheckUnderFairness (.implies deMorganForm served) init (LSys.unlabelled succ) label)}"
where
  isEmptyResult {σ} : EmptinessResult σ → String
    | .empty _ => "holds"
    | .nonEmpty _ _ => "fails"

#eval report

end Lasso.Tests.Examples.DeMorganSplit
