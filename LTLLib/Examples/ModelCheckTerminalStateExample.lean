/-
  Illustrates a bug fixed by `Product.totalizeSucc` (`Product.lean`): a
  client system with a genuinely terminal state (no outgoing edges at all)
  used to make `modelCheck` silently miss real counterexamples whose
  violation only manifests by the system stalling forever in that state.

  LTL/Büchi-automaton semantics are defined over *infinite* words, so a
  Kripke structure is conventionally required to be total — every state has
  at least one successor. A "terminal" state is read as "the system stays
  here forever", exactly how NuSMV/SPIN treat deadlock states. Before this
  fix, `modelCheck` routed the client's `sysSucc` straight into the product
  graph: a state with no outgoing edges became a genuine dead end there too,
  so nested DFS could never close a lasso through it — a run that gets stuck
  looked like it simply *ended*, not like it violated a liveness property
  forever, and `modelCheck` reported `.empty` (no counterexample) even
  though the system does violate `ψ` below. `Product.getSuccessors` now
  routes `sysSucc` through `Product.totalizeSucc` first, which inserts the
  missing self-loop on any state with no outgoing edges, so this system is
  now correctly flagged as violating `ψ`.

  System: a light that switches on once, then off, then stops responding —
  `off` has no outgoing transitions at all (`breakableLightSucc .off = #[]`).

  Formula: `□◇on` ("the light turns on infinitely often") — false, since
  after the light turns `off` it never turns on again; it just stays `off`
  forever.
-/
import LTLLib
import Mathlib.Tactic.DeriveFintype

namespace LTLLib.Examples

/-- A light that switches on once, then off, then breaks — `off` is a
genuinely terminal state: `breakableLightSucc .off = #[]`. -/
inductive BreakableLight where
  | on | off
deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Fintype

private theorem BreakableLight.beq_def (x y : BreakableLight) :
    (x == y) = (match x, y with
      | .on, .on | .off, .off => true
      | _, _ => false) := by
  cases x <;> cases y <;> rfl

instance : LawfulBEq BreakableLight where
  eq_of_beq {x y} h := by cases x <;> cases y <;> first | rfl | (rw [BreakableLight.beq_def] at h; contradiction)
  rfl {x} := by cases x <;> rfl

instance : LawfulHashable BreakableLight where
  hash_eq {a b} h := by have := eq_of_beq h; subst this; rfl

instance : ToString BreakableLight where
  toString
    | .on => "on"
    | .off => "off"

/-- Atomic propositions labeling the light's states. -/
abbrev Prop' := String

/-- `on → off`, then stuck forever: `off` has no outgoing transitions,
unlike `ModelCheckExample.lean`/`ModelCheckCounterExample.lean`'s
`lightSucc`, which cycles and never hits a dead end. -/
def breakableLightSucc : BreakableLight → Array BreakableLight
  | .on => #[.off]
  | .off => #[]

/-- Only `on` is ever asserted; `off` holds no propositions. -/
def breakableLightLabel : BreakableLight → Std.HashSet Prop'
  | .on => {"on"}
  | .off => ∅

/-- The system starts at `on`. -/
def breakableLightInit : List BreakableLight := [.on]

/-- `BreakableLight` is a `Fintype`, so any `Set BreakableLight` is finite
for free. Note this is unaffected by `off` being terminal: `FiniteReach`
only asks that the *reachable* set is finite, not that the graph has no
dead ends — the bug this file demonstrates is not a `FiniteReach` failure,
it is `modelCheck` mishandling a dead end once one legitimately exists. -/
def breakableLightFR : FiniteReach breakableLightInit breakableLightSucc := Set.toFinite _

/-- `□◇on`: the light turns on infinitely often — false, since the light
only ever turns on once, then breaks and stays `off` forever. -/
def ψ : Formula Prop' := .always (.eventually (.atom "on"))

/-- `Std.HashSet (NNF Prop')`, the finite-set representation `modelCheck`
needs for its internal tableau construction. -/
abbrev S := Std.HashSet (NNF Prop')

/-- Render one system state together with the atoms holding there. -/
def showState (s : BreakableLight) : String :=
  let atoms := (breakableLightLabel s).toList.mergeSort (· < ·)
  s!"{s}\{{String.intercalate ", " atoms}}"

/-- Render a lasso path as an arrow chain. -/
def showPath (path : List BreakableLight) : String :=
  String.intercalate " → " (path.map showState)

/-- Render a `modelCheck` counterexample. See
`ModelCheckCounterExample.lean`'s `showCounterexample` for why
`loop.tail`, not `loop`, is the genuine cycle. Here `loop.tail` is
expected to be `[off]` — the self-loop `Product.totalizeSucc` inserted on
`off`, not a transition `breakableLightSucc` itself ever produces. -/
def showCounterexample (stem loop : List (BreakableLight × BAState)) : String :=
  s!"stem: {showPath (stem.map Prod.fst)}\n\
     loop: {showPath (loop.tail.map Prod.fst)} ⟲ (repeats forever)"

/-- `IO.println`, not a plain `String` result, so `#eval` doesn't
`Repr`-quote the output. -/
def report : IO Unit := do
  match modelCheck (S := S) ψ breakableLightInit breakableLightSucc breakableLightLabel
      breakableLightFR with
  | .empty n => IO.println s!"sys ⊨ ψ (no counterexample; explored {n} product states)"
  | .nonEmpty stem loop =>
    IO.println "sys ⊭ ψ"
    IO.println (showCounterexample stem loop)

#eval report

end LTLLib.Examples
