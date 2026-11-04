module

/-
  The state-indexed emptiness-check contract, acceptance being a predicate on states.

  Defines:
  - `AcceptingCycle`: the lasso witness of non-emptiness, its cycle passing through an accepting state
  - `EmptinessChecker`: the sound and complete contract a state-indexed check satisfies

  Sections:
  - Accepting cycle definition
  - Algorithm-agnostic emptiness-check contract
-/
public import LTLLib.AbstractSpec.Reachability

public section

namespace LTLLib

/-! ## Accepting cycle definition -/

/-- An accepting cycle: a stem from an initial state to an accepting state, plus a cycle from that
    state back to itself. This is the standard "lasso" witness for Büchi automaton non-emptiness
    (cf. CVWY §2, Schwoon & Esparza §2). -/
structure AcceptingCycle {State}
    (initialStates : List State) (succs : State → Array State)
    (isAccepting : State → Bool) where
  stem : List State
  cycle : List State
  stem_nonempty : stem.length ≥ 1
  cycle_nonempty : cycle.length ≥ 1
  stem_head_initial : stem.head (List.ne_nil_of_length_pos (by omega)) ∈ initialStates
  stem_chain : ∀ (i : Nat), (hi : i + 1 < stem.length) →
    stem[i + 1] ∈ succs (stem[i])
  overlap : stem.getLast (List.ne_nil_of_length_pos (by omega)) =
            cycle.head (List.ne_nil_of_length_pos (by omega))
  cycle_chain : ∀ (i : Nat), (hi : i + 1 < cycle.length) →
    cycle[i + 1] ∈ succs (cycle[i])
  cycle_back : cycle.head (List.ne_nil_of_length_pos (by omega)) ∈
    succs (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
  cycle_head_accepting : isAccepting (cycle.head (List.ne_nil_of_length_pos (by omega))) = true

/-! ## Algorithm-agnostic emptiness-check contract -/

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-- Contract any emptiness-check algorithm must satisfy. -/
structure EmptinessChecker (State : Type u) [BEq State] [Hashable State]
    [LawfulBEq State] where
  -- Runs the algorithm on a graph and reports whether an accepting cycle exists.
  check : (succs : State → Array State) → (initialStates : List State) →
    FiniteReach initialStates succs → (isAccepting : State → Bool) →
    EmptinessResult State
  -- Soundness of `.nonEmpty`: a returned `stem`/`loop` is a genuine `AcceptingCycle` witness.
  nonEmpty_valid : ∀ {succs : State → Array State} {initialStates : List State}
      {fr : FiniteReach initialStates succs} {isAccepting : State → Bool}
      {stem loop : List State},
    check succs initialStates fr isAccepting = .nonEmpty stem loop →
    ∃ ac : AcceptingCycle initialStates succs isAccepting,
      ac.stem = stem ∧ ac.cycle = loop.tail
  -- Completeness of `.empty`: no `AcceptingCycle` exists.
  empty_no_cycle : ∀ {succs : State → Array State} {initialStates : List State}
      {fr : FiniteReach initialStates succs} {isAccepting : State → Bool} {n : Nat},
    check succs initialStates fr isAccepting = .empty n →
    ¬∃ _ac : AcceptingCycle initialStates succs isAccepting, True

end LTLLib
