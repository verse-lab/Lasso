/-
  Generalized Büchi Automaton (GBA) type definition.

  Corresponds to the GBA constructed by `create_gba_from_nodes` in
  LTL_to_GBA.thy. The GBA consists of:
  - States (node names)
  - Initial states (nodes reachable from expand_init)
  - Transitions (based on incoming edges)
  - Labeling (positive/negative propositions from each node's `old` set)
  - Acceptance sets (one per Until-subformula)

  The Isabelle definition of the GBA is:
    definition create_gba_from_nodes φ qs ≡ ⟨
      g_V = qs,
      g_E = {(q, q'). q∈qs ∧ q'∈qs ∧ name q ∈ incoming q'},
      g_V0 = {q∈qs. expand_init ∈ incoming q},
      gbg_F = {{q∈qs. μ U⁼ η ∈ old q → η ∈ old q} | μ η. μ U⁼ η ∈ subfrmlsr φ},
      gba_L = λq l. q∈qs ∧ {p. prop⁼(p)∈old q}⊆l ∧ {p. nprop⁼(p)∈old q} ∩ l = {}
    ⟩
-/

import Std

namespace LTLLib

/-- A Generalized Büchi Automaton.

Parametrized by `α`, the type of atomic propositions.

Corresponds to the GBA produced by `create_gba_from_nodes` in LTL_to_GBA.thy.
After the renaming phase (`gba_rename_ext`), states are identified by Nat (node names). -/
structure GBA (α : Type u) [BEq α] [Hashable α] where
  /-- All state identifiers.
  Corresponds to `g_V` in the GBA record. -/
  states : Std.HashSet Nat

  /-- Initial state identifiers.
  Corresponds to `g_V0 = {q∈qs. expand_init ∈ incoming q}`. -/
  initialStates : Std.HashSet Nat

  /-- Transition map: state → list of successor states.
  Corresponds to `g_E = {(q, q') | q∈qs ∧ q'∈qs ∧ name q ∈ incoming q'}`,
  organized as an adjacency list keyed by source state.
  Built by `build_succ` in LTL_to_GBA.thy. -/
  successors : Std.HashMap Nat (Array Nat)

  /-- Labeling: for each state, the sets of positive and negative propositions.
  Corresponds to `gba_L` and `pn_map` in LTL_to_GBA.thy:
    pn_map(q) = ({p | prop(p) ∈ old(q)}, {p | nprop(p) ∈ old(q)})
  A state q is compatible with a valuation L iff:
    positiveProps(q) ⊆ L ∧ negativeProps(q) ∩ L = ∅ -/
  labeling : Std.HashMap Nat (Std.HashSet α × Std.HashSet α)

  /-- Acceptance sets: one per Until-subformula.
  Corresponds to `gbg_F` in the GBA record:
    gbg_F = {{q∈qs. μ U⁼ η ∈ old q → η ∈ old q} | (μ,η). μ U⁼ η ∈ subfrmlsr φ}

  A state q is in acceptance set F_{μ,η} iff:
    (μ U η) ∉ old(q) ∨ η ∈ old(q)
  i.e., the Until obligation is either not present or already satisfied. -/
  acceptSets : Array (Std.HashSet Nat)

namespace GBA

variable [BEq α] [Hashable α]

/-- Number of states in the GBA. -/
def numStates (gba : GBA α) : Nat := gba.states.size

/-- Number of acceptance sets (= number of distinct Until-subformulas). -/
def numAcceptSets (gba : GBA α) : Nat := gba.acceptSets.size

/-- Get successors of a state. Returns empty array if state not found. -/
def getSuccessors (gba : GBA α) (state : Nat) : Array Nat :=
  gba.successors[state]?.getD #[]

/-- Check if a state is initial. -/
def isInitial (gba : GBA α) (state : Nat) : Bool :=
  gba.initialStates.contains state

/-- Check if a state is in a given acceptance set. -/
def isAccepting (gba : GBA α) (setIdx : Nat) (state : Nat) : Bool :=
  match gba.acceptSets[setIdx]? with
  | some aset => aset.contains state
  | none => true  -- if no acceptance sets, all states accept

end GBA

end LTLLib
