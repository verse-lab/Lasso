/-
  Standard (non-generalized) Büchi Automaton and GBA degeneralization.

  The degeneralization converts a GBA (with multiple acceptance sets) into
  a standard BA (with a single set of accepting states) by introducing an
  acceptance counter that tracks which acceptance set to satisfy next.

  This is a standard construction (see e.g., Baier & Katoen, "Principles of
  Model Checking", Section 4.3.3).

  State space: |BA| = |GBA| × max(1, k) where k = number of acceptance sets.
-/

import LTLLib.GBA
import LTLLib.AbstractSpec.Acceptance
import LTLLib.AbstractSpec.EmptinessCheck
import LTLLib.AbstractSpec.Lasso

namespace LTLLib

/-- State in a standard Büchi Automaton after degeneralization.
Pairs the original GBA state with an acceptance counter. -/
structure BAState where
  /-- Original GBA state identifier. -/
  gbaState : Nat
  /-- Acceptance counter: which acceptance set we're waiting to visit next.
  Ranges from 0 to k-1 where k = number of GBA acceptance sets. -/
  acceptIdx : Nat
deriving BEq, Hashable, Repr, Inhabited, DecidableEq

private theorem BAState.beq_def (x y : BAState) :
    (x == y) = (x.gbaState == y.gbaState && x.acceptIdx == y.acceptIdx) := rfl

instance : LawfulBEq BAState where
  eq_of_beq {x y} h := by
    rw [BAState.beq_def] at h
    simp [Bool.and_eq_true, beq_iff_eq] at h
    exact BAState.mk.injEq .. |>.mpr h
  rfl {a} := by rw [BAState.beq_def]; simp

instance : LawfulHashable BAState where
  hash_eq {a b} h := by have := eq_of_beq h; subst this; rfl

instance : ToString BAState where
  toString s := s!"({s.gbaState}, {s.acceptIdx})"

/-- A standard (non-generalized) Büchi Automaton.

States are `BAState` = (GBA state, acceptance counter).
A state is accepting iff `acceptIdx = 0` and the GBA state is in
acceptance set 0 (see `acceptingStates`).

This is produced by degeneralizing a GBA. -/
structure BA (α : Type u) [BEq α] [Hashable α] where
  /-- All states. -/
  states : Std.HashSet BAState

  /-- Initial states. -/
  initialStates : Std.HashSet BAState

  /-- Transition map: state → list of successor states. -/
  successors : Std.HashMap BAState (Array BAState)

  /-- Labeling inherited from GBA: maps GBA state to (positive, negative) propositions.
  The BAState's labeling is determined by its `gbaState` component only. -/
  labeling : Std.HashMap Nat (Std.HashSet α × Std.HashSet α)

  /-- Number of acceptance sets in the original GBA (for reference). -/
  numAcceptSets : Nat

  /-- Accepting states: `{(q, 0) | q ∈ F_0}` where `F_0` is the first GBA
  acceptance set. When there are no acceptance sets, all `(q, 0)` are accepting. -/
  acceptingStates : Std.HashSet BAState

namespace BA

variable {α} [BEq α] [Hashable α]

/-- Check if a BA state is accepting.
A state `(q, i)` is accepting iff `i = 0` and `q` is in the first GBA
acceptance set (or there are no acceptance sets). -/
def isAccepting (ba : BA α) (s : BAState) : Bool :=
  ba.acceptingStates.contains s

/-- Get successors of a BA state. -/
def getSuccessors (ba : BA α) (s : BAState) : Array BAState :=
  ba.successors[s]?.getD #[]

/-- Get the labeling of a BA state (determined by its GBA component only). -/
def getLabeling (ba : BA α) (s : BAState) : Std.HashSet α × Std.HashSet α :=
  ba.labeling[s.gbaState]?.getD (Std.HashSet.emptyWithCapacity 0, Std.HashSet.emptyWithCapacity 0)

/-- Label-compatibility check: does `valuation` satisfy `s`'s propositional
constraint? -/
def compatible (ba : BA α) (s : BAState) (valuation : Std.HashSet α) : Bool :=
  let (pos, neg) := ba.getLabeling s
  pos.all valuation.contains && !neg.any valuation.contains

/-- Well-formedness: initial and successor states are in the state set. -/
structure WellFormed (ba : BA α) : Prop where
  initial_mem : ∀ s, ba.initialStates.contains s → ba.states.contains s
  succ_mem : ∀ s s', ba.states.contains s → s' ∈ ba.getSuccessors s →
    ba.states.contains s'

/-- Convert a computational `BA` to an abstract `OASpec` with 1 acceptance set. -/
def toSpec [BEq α] [Hashable α] (ba : BA α) : OASpec BAState α 1 where
  trans s s' := s' ∈ ba.getSuccessors s
  initial s := ba.initialStates.contains s
  labelCompat s v :=
    match ba.labeling[s.gbaState]? with
    | some (pos, neg) =>
      (∀ a, pos.contains a → v a) ∧ (∀ a, neg.contains a → ¬ v a)
    | none => True
  acceptSet _ s := ba.isAccepting s

end BA

namespace GBA

variable {α} [BEq α] [Hashable α]

/-- Degeneralize a GBA to a standard BA.

The standard construction (Baier & Katoen, Section 4.3.3):
- States: {(q, i) | q ∈ GBA.states, 0 ≤ i < k} where k = max(1, numAcceptSets)
- Initial: {(q, 0) | q ∈ GBA.initialStates}
- Transitions: (q, i) → (q', i') where q → q' in GBA, and
    i' = (i + 1) % k   if q ∈ acceptSets[i]
    i' = i              otherwise
- Accepting: {(q, 0) | q ∈ states, q ∈ acceptSets[0]}
  (when k = 0, all (q, 0) are accepting since there are no fairness obligations)

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

  -- Accepting states: (q, 0) for q ∈ F_0 (or all q when no acceptance sets)
  let acceptingStates := gba.states.fold
    (init := Std.HashSet.emptyWithCapacity gba.states.size) fun acc gbaState =>
      if gba.isAccepting 0 gbaState then
        acc.insert { gbaState, acceptIdx := 0 }
      else acc

  {
    states := allStates
    initialStates := initStates
    successors := succMap
    labeling := gba.labeling
    numAcceptSets := gba.acceptSets.size
    acceptingStates := acceptingStates
  }

end GBA

/-- The `BA.toSpec` specialization of `toValidLassoOf`. -/
def AcceptingCycle.toValidLasso {α} [BEq α] [Hashable α] {ba : BA α}
    (ac : AcceptingCycle ba.initialStates.toList ba.getSuccessors ba.isAccepting) :
    ValidLasso ba.toSpec ac.stem ac.cycle :=
  ac.toValidLassoOf Iff.rfl (Std.HashSet.mem_toList.trans Std.HashSet.mem_iff_contains) Iff.rfl

/-! ## Every state on the cycle stays inside a well-formed `BA`'s state set -/

theorem AcceptingCycle.stem_states_mem {α} [BEq α] [Hashable α] {ba : BA α}
    (hwf : ba.WellFormed)
    (ac : AcceptingCycle ba.initialStates.toList ba.getSuccessors ba.isAccepting) :
    ∀ (i : Nat) (hi : i < ac.stem.length), ba.states.contains (ac.stem[i]'hi) = true := by
  intro i
  induction i with
  | zero =>
    intro hi
    have h0 : ac.stem[0]'hi = ac.stem.head (List.ne_nil_of_length_pos (by omega)) := by
      rw [List.head_eq_getElem]
    rw [h0]
    exact hwf.initial_mem _
      (Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp ac.stem_head_initial))
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    have hchain := ac.stem_chain i (by omega)
    exact hwf.succ_mem _ _ hprev hchain

theorem AcceptingCycle.cycle_states_mem {α} [BEq α] [Hashable α] {ba : BA α}
    (hwf : ba.WellFormed)
    (ac : AcceptingCycle ba.initialStates.toList ba.getSuccessors ba.isAccepting) :
    ∀ (i : Nat) (hi : i < ac.cycle.length), ba.states.contains (ac.cycle[i]'hi) = true := by
  have hsn := ac.stem_nonempty
  have hcn := ac.cycle_nonempty
  have hhead : ba.states.contains
      (ac.cycle.head (List.ne_nil_of_length_pos (by omega))) = true := by
    rw [← ac.overlap]
    have hlast : ac.stem[ac.stem.length - 1]'(by omega) =
        ac.stem.getLast (List.ne_nil_of_length_pos (by omega)) := by
      rw [List.getLast_eq_getElem]
    rw [← hlast]
    exact AcceptingCycle.stem_states_mem hwf ac (ac.stem.length - 1) (by omega)
  intro i
  induction i with
  | zero =>
    intro hi
    have h0 : ac.cycle[0]'hi = ac.cycle.head (List.ne_nil_of_length_pos (by omega)) := by
      rw [List.head_eq_getElem]
    rw [h0]; exact hhead
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    have hchain := ac.cycle_chain i (by omega)
    exact hwf.succ_mem _ _ hprev hchain

/-- Every position of the lasso-derived run stays inside a well-formed `BA`'s
state set. -/
theorem AcceptingCycle.run_states_mem {α} [BEq α] [Hashable α] {ba : BA α}
    (hwf : ba.WellFormed)
    (ac : AcceptingCycle ba.initialStates.toList ba.getSuccessors ba.isAccepting) (n : Nat) :
    ba.states.contains (ac.toValidLasso.run n) = true := by
  simp only [ValidLasso.run, lassoRun]
  split
  · next h => exact ac.stem_states_mem hwf n (by omega)
  · split
    · next h2 => exact ac.cycle_states_mem hwf _ (Nat.mod_lt _ h2)
    · next h h2 => exact absurd ac.cycle_nonempty (by omega)

end LTLLib
