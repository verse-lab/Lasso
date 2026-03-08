/-
  Standard (non-generalized) Büchi Automaton and GBA degeneralization.

  The degeneralization converts a GBA (with multiple acceptance sets) into
  a standard BA (with a single set of accepting states) by introducing an
  acceptance counter that tracks which acceptance set to satisfy next.

  This is a standard construction (see e.g., Baier & Katoen, "Principles of
  Model Checking", Section 4.3.3). The Isabelle LTL_to_GBA formalization does
  not include degeneralization (it works with GBA/IGBA directly), but the
  CAVA framework's automata library supports it.

  State space: |BA| = |GBA| × max(1, k) where k = number of acceptance sets.
-/

import LTLLib.GBA

namespace LTLLib

/-- State in a standard Büchi Automaton after degeneralization.
Pairs the original GBA state with an acceptance counter. -/
structure BAState where
  /-- Original GBA state identifier. -/
  gbaState : Nat
  /-- Acceptance counter: which acceptance set we're waiting to visit next.
  Ranges from 0 to k-1 where k = number of GBA acceptance sets. -/
  acceptIdx : Nat
deriving BEq, Hashable, Repr, Inhabited

instance : ToString BAState where
  toString s := s!"({s.gbaState}, {s.acceptIdx})"

/-- A standard (non-generalized) Büchi Automaton.

States are `BAState` = (GBA state, acceptance counter).
A state is accepting iff its `acceptIdx = 0`.

This is produced by degeneralizing a GBA. -/
structure BA (α : Type u) [BEq α] [Hashable α] where
  /-- All states. -/
  states : Std.HashSet BAState

  /-- Initial states. -/
  initialStates : Std.HashSet BAState

  /-- Transition map: state → list of successor states. -/
  successors : Std.HashMap BAState (Array BAState)

  /-- Labeling inherited from GBA: maps GBA state to (positive, negative) propositions.
  The BAState's labeling is determined by its `gbaState` component. -/
  labeling : Std.HashMap Nat (Std.HashSet α × Std.HashSet α)

  /-- Number of acceptance sets in the original GBA (for reference). -/
  numAcceptSets : Nat

  /-- Accepting states: those with acceptIdx = 0.
  Precomputed for efficiency. -/
  acceptingStates : Std.HashSet BAState

namespace BA

variable [BEq α] [Hashable α]

/-- Check if a BA state is accepting (acceptIdx = 0). -/
def isAccepting (_ : BA α) (s : BAState) : Bool :=
  s.acceptIdx == 0

/-- Get successors of a BA state. -/
def getSuccessors (ba : BA α) (s : BAState) : Array BAState :=
  ba.successors[s]?.getD #[]

/-- Get the labeling of a BA state (determined by its GBA component). -/
def getLabeling (ba : BA α) (s : BAState) : Std.HashSet α × Std.HashSet α :=
  ba.labeling[s.gbaState]?.getD (Std.HashSet.emptyWithCapacity 0, Std.HashSet.emptyWithCapacity 0)

end BA

namespace GBA

variable [BEq α] [Hashable α]

/-- Degeneralize a GBA to a standard BA.

The standard construction (Baier & Katoen, Section 4.3.3):
- States: {(q, i) | q ∈ GBA.states, 0 ≤ i < k} where k = max(1, numAcceptSets)
- Initial: {(q, 0) | q ∈ GBA.initialStates}
- Transitions: (q, i) → (q', i') where q → q' in GBA, and
    i' = (i + 1) % k   if q ∈ acceptSets[i]
    i' = i              otherwise
- Accepting: {(q, 0) | q ∈ states}

When k = 0 (no Until-subformulas), we use k = 1 and all states are accepting
(since there are no fairness obligations to track). -/
def degeneralize (gba : GBA α) : BA α :=
  let k := if gba.acceptSets.size == 0 then 1 else gba.acceptSets.size
  let totalStates := gba.states.size * k

  -- Build all states
  let allStates := gba.states.fold
    (init := Std.HashSet.emptyWithCapacity totalStates) fun acc gbaState =>
      (List.range k).foldl (init := acc) fun acc i =>
        acc.insert { gbaState, acceptIdx := i }

  -- Build initial states: (q, 0) for each initial GBA state
  let initStates := gba.initialStates.fold
    (init := Std.HashSet.emptyWithCapacity gba.initialStates.size) fun acc gbaState =>
      acc.insert { gbaState, acceptIdx := 0 }

  -- Build transitions
  let succMap := gba.states.fold
    (init := Std.HashMap.emptyWithCapacity totalStates) fun succMap gbaState =>
      let gbaSuccs := gba.getSuccessors gbaState
      (List.range k).foldl (init := succMap) fun succMap i =>
        let baState : BAState := { gbaState, acceptIdx := i }
        -- Compute next acceptance index
        let nextIdx :=
          if gba.acceptSets.size == 0 then 0  -- no acceptance sets: stay at 0
          else if gba.isAccepting i gbaState then (i + 1) % k
          else i
        let baSuccs := gbaSuccs.map fun gbaSucc =>
          { gbaState := gbaSucc, acceptIdx := nextIdx : BAState }
        succMap.insert baState baSuccs

  -- Accepting states: (q, 0) for all q
  let acceptingStates := gba.states.fold
    (init := Std.HashSet.emptyWithCapacity gba.states.size) fun acc gbaState =>
      acc.insert { gbaState, acceptIdx := 0 }

  {
    states := allStates
    initialStates := initStates
    successors := succMap
    labeling := gba.labeling
    numAcceptSets := gba.acceptSets.size
    acceptingStates := acceptingStates
  }

end GBA

end LTLLib
