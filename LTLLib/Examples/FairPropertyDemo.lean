/-
  This file demonstrates a property that is itself a fairness, so the router hoists the property too and the
  translator is left with nothing to build.

  As a running example: a token ring

  A token circulates round four positions. The holder may keep the token for a while before passing it on.
  - park  -- grab -->  hold  -- pass -->  carry  -- deliver -->  drop  -- release -->  park
  - From park the ring may also idle, leaving the token where it is for another step.

  `p` marks `hold` and `q` marks `drop`, so `p` is "the token was picked up" and `q` is "it was delivered".

  Q: Is the token delivered infinitely often, i.e. does `□◇q` hold?
  - No: the ring can idle at `park` forever and never pick the token up at all.

  Q: Is it delivered infinitely often whenever it is picked up infinitely often, i.e. does `□◇p → □◇q` hold?
  - Yes: the only way back to `hold` runs through `drop`, so every fresh pickup is preceded by a delivery.

  Why this one is interesting:
  - Both halves are fairness formulas, so the whole implication is one, and so is its negation. The class is
    closed under negation, `isPureEventuality` and `isPurelyUniversal` being exact duals in negation normal form.
  - The router splits the negated property, so `□◇p` and `◇□¬q` are both hoisted, nothing is kept, and the
    translator receives `⊤`.
  - Splitting only the assumption, as the router used to, hoists `□◇p` and hands `□◇q` to the translator, which
    is a real automaton with a real acceptance mark that multiplies the product.

  `beforeSplit` reconstructs that older routing so the two can be measured side by side. With nothing kept, the
  system-level fail-fast decides the whole question on the system graph and the product is never built at all,
  and when a disjunct does survive the fail-fast the product it builds is the system against a one-state `⊤`.
-/
import LTLLib
import LTLLib.TGBABased.LTLtoTGBA.Pipeline
import Mathlib.Tactic.DeriveFintype

namespace LTLLib.Examples.FairProperty

open LTLLib

inductive Spot where
  | park | hold | carry | drop
deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Fintype

instance : LawfulBEq Spot where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

def succ : Spot → Array Spot
  | .park => #[.park, .hold]  -- the ring may idle here, which is what makes `□◇q` fail on its own
  | .hold => #[.carry]
  | .carry => #[.drop]
  | .drop => #[.park]

def label : Spot → Std.HashSet String
  | .hold => {"p"}
  | .drop => {"q"}
  | _ => ∅

def init : List Spot := [.park]

def fr : FiniteReach init succ := Set.toFinite _

/-- `□◇p`, the token is picked up infinitely often. -/
def pickup : Formula String := .always (.eventually (.atom "p"))

/-- `□◇q`, the token is delivered infinitely often. -/
def deliver : Formula String := .always (.eventually (.atom "q"))

/-- `□◇p → □◇q`, the property, itself a fairness. -/
def prop : Formula String := .implies pickup deliver

/-! ## What each routing hands to the translator -/

def keptOf (φ : Formula String) : List (NNF String) := (hoistFairness (φ.toNNF false).splitConj).2

def disjunctsOf (φ : Formula String) : List (NNF.FairDisjunct String) :=
  NNF.crossAllDNF (hoistFairness (φ.toNNF false).splitConj).1

def tgbaStatesOf (φ : Formula String) : Nat :=
  match ltl3ba (φ.toNNF false) with
  | some t => t.states.size
  | none => 0

def marksOf (φ : Formula String) : Nat :=
  match ltl3ba (φ.toNNF false) with
  | some t => t.numAcceptSets
  | none => 0

/-- The routing that split only the assumption, kept here so the two can be measured side by side. -/
def beforeSplit : EmptinessResult ((Spot × Nat) × Bool) :=
  let split := hoistFairness (pickup.toNNF true).splitConj
  checkDisjuncts
    (fun d => modelCheckTGBADisjunctFast
      (Formula.assuming (split.2.map NNF.toFormula) deliver) d.1 d.2 init succ label fr)
    (NNF.crossAllDNF split.1)

def verdict {α} : EmptinessResult α → String
  | .empty _ => "holds"
  | .nonEmpty _ _ => "fails"

def explored {α} : EmptinessResult α → String
  | .empty n => s!"{n} product states"
  | .nonEmpty stem loop => s!"counterexample {stem.length}+{loop.length}"

def report : IO Unit := do
  IO.println s!"□◇q on its own          : {verdict (modelCheckUnderFairness deliver init succ label fr)}, \
{explored (modelCheckUnderFairness deliver init succ label fr)}"
  IO.println s!"□◇p → □◇q               : {verdict (modelCheckUnderFairness prop init succ label fr)}, \
{explored (modelCheckUnderFairness prop init succ label fr)}"
  IO.println ""
  -- the assumption-only split leaves the property for the translator
  let beforeProp := Formula.assuming ((hoistFairness (pickup.toNNF true).splitConj).2.map NNF.toFormula) deliver
  IO.println s!"splitting the assumption only"
  IO.println s!"  translator receives  □◇q, {tgbaStatesOf beforeProp} TGBA states, {marksOf beforeProp} mark(s)"
  IO.println s!"  result               {verdict beforeSplit}, explored {explored beforeSplit}"
  IO.println ""
  -- the negated property splits into two fairness conjuncts, so nothing is kept
  IO.println s!"splitting the negated property"
  IO.println s!"  conjuncts            {(prop.toNNF false).splitConj.map NNF.toString}"
  IO.println s!"  kept                 {(keptOf prop).map NNF.toString}"
  IO.println s!"  hoisted              {(disjunctsOf prop).length} disjunct(s), \
{(disjunctsOf prop).foldl (fun n (d : NNF.FairDisjunct String) => n + d.2.length) 0} mark(s)"
  let afterProp := keptProperty (keptOf prop)
  IO.println s!"  translator receives  ⊤, {tgbaStatesOf afterProp} TGBA states, {marksOf afterProp} mark(s)"
  IO.println s!"  result               {verdict (modelCheckUnderFairness prop init succ label fr)}, \
explored {explored (modelCheckUnderFairness prop init succ label fr)}"

#eval report

end LTLLib.Examples.FairProperty
