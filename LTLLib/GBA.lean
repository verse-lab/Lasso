module

/-
  Generalized Büchi Automaton (GBA) type definition.

  The GBA consists of:
  - States (node names)
  - Initial states
  - Transitions (based on incoming edges)
  - Labeling (positive/negative propositions from each node's `old` set)
  - Acceptance sets (one per Until-subformula)
-/

public import Std
public import LTLLib.AbstractSpec.Acceptance

public section

namespace LTLLib

/-- A Generalized Büchi Automaton. Parametrized by the type of atomic propositions.
  States are identified by Nat (node names). -/
structure GBA (α : Type u) [BEq α] [Hashable α] where
  states : Std.HashSet Nat
  initialStates : Std.HashSet Nat
  successors : Std.HashMap Nat (Array Nat)  -- state → successor states
  -- For each state, the sets of positive and negative propositions. A state q is
  -- compatible with a valuation L iff positiveProps(q) ⊆ L ∧ negativeProps(q) ∩ L = ∅.
  labeling : Std.HashMap Nat (Std.HashSet α × Std.HashSet α)
  -- One acceptance set per Until-subformula. State q is in F_{μ,η} iff
  -- (μ U η) ∉ old(q) ∨ η ∈ old(q), i.e. the obligation is absent or already satisfied.
  acceptSets : Array (Std.HashSet Nat)

namespace GBA

variable {α} [BEq α] [Hashable α]

/-- Number of states in the GBA. -/
@[expose] def numStates (gba : GBA α) : Nat := gba.states.size

/-- Number of acceptance sets (= number of distinct Until-subformulas). -/
@[expose] def numAcceptSets (gba : GBA α) : Nat := gba.acceptSets.size

/-- Get successors of a state. Returns empty array if state not found. -/
@[expose] def getSuccessors (gba : GBA α) (state : Nat) : Array Nat :=
  gba.successors[state]?.getD #[]

/-- Check if a state is initial. -/
@[expose] def isInitial (gba : GBA α) (state : Nat) : Bool :=
  gba.initialStates.contains state

/-- Check if a state is in a given acceptance set. -/
@[expose] def isAccepting (gba : GBA α) (setIdx : Nat) (state : Nat) : Bool :=
  match gba.acceptSets[setIdx]? with
  | some aset => aset.contains state
  | none => true  -- if no acceptance sets, all states accept

/-- Acceptance sets `q` belongs to. -/
@[expose] def acceptMarksOf (gba : GBA α) (q : Nat) : Std.HashSet Nat :=
  (List.range gba.acceptSets.size).foldl
    (init := Std.HashSet.emptyWithCapacity gba.acceptSets.size)
    fun acc i => if gba.isAccepting i q then acc.insert i else acc

/-- Well-formedness: initial and successor states are in the state set. -/
structure WellFormed (gba : GBA α) : Prop where
  initial_mem : ∀ q, gba.isInitial q → gba.states.contains q
  succ_mem : ∀ q q', gba.states.contains q → q' ∈ gba.getSuccessors q →
    gba.states.contains q'

/-- Convert a computational `GBA` to an abstract `OASpec`. -/
@[expose] def toSpec [BEq α] [Hashable α] (gba : GBA α) : OASpec Nat α gba.numAcceptSets where
  trans q q' := q' ∈ gba.getSuccessors q
  initial q := gba.isInitial q
  labelCompat q v :=
    match gba.labeling[q]? with
    | some (pos, neg) =>
      (∀ a, pos.contains a → v a) ∧ (∀ a, neg.contains a → ¬ v a)
    | none => True
  acceptSet i q := gba.isAccepting i.val q

end GBA

end LTLLib
