/-
  Algorithm-agnostic core of the emptiness-check story: the result type,
  the graph-reachability precondition, the pure graph-theoretic witness of
  non-emptiness, and the abstract contract any concrete emptiness-check
  algorithm must satisfy.

  Nothing in this file mentions `nestedDFS`/`innerDFS`/`outerDFSLoop` or any
  other concrete algorithm. `NestedDFS/NestedDFSRef.lean`/`NestedDFS/NestedDFSCorrectness.lean`/
  `NestedDFS/NestedDFSTermination.lean` are one particular *implementation* consuming
  these definitions — `nestedDFSChecker` (`NestedDFS/NestedDFSTermination.lean`) is
  the one existing instance of `EmptinessChecker` below. A future algorithm
  (e.g. an SCC-based checker) implements the same contract without touching
  this file, `NestedDFS*.lean`, or anything built on top of `EmptinessChecker`
  (`Pipeline.lean`/`ModelCheck.lean`).

  Corresponds to the algorithm-free half of CAVA's `CAVA_Automata`/
  `CAVA_Abstract` split: `AcceptingCycle` plays the role CAVA's
  `is_acc_run` plays, `EmptinessChecker` corresponds to `find_ce_spec`
  (`CAVA_Abstract.thy`) — see that structure's own docstring below for the
  full correspondence.
-/
import Std

namespace LTLLib

/-- Result of a graph emptiness check: does the graph reachable from
`initialStates` via `succs` contain a cycle through an `isAccepting`
state? -/
inductive EmptinessResult (State : Type u) where
  /-- No accepting cycle found — the automaton's language is empty
  (i.e., the checked property is satisfied). -/
  | empty (exploredStates : Nat)
  /-- An accepting cycle was found — the automaton's language is non-empty
  (i.e., the checked property is violated).
  - `stem`: path from an initial state to the accepting state (inclusive)
  - `loop`: cycle from the accepting state back to itself (inclusive on both ends) -/
  | nonEmpty (stem : List State) (loop : List State)
deriving Repr, Inhabited

/-! ## Accepting cycle definition -/

/-- An accepting cycle exists: there is a stem from an initial state to an
    accepting state, and a cycle from that state back to itself.

    This is the standard "lasso" witness for non-emptiness of a Büchi
    automaton (cf. CVWY §2, Schwoon & Esparza §2). Purely graph-theoretic —
    stated only over `initialStates`/`succs`/`isAccepting`, with no
    reference to how an algorithm might go about finding one. -/
structure AcceptingCycle
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

/-! ## Finite-reachability hypothesis

Lean analogue of CAVA's `fb_graph` locale assumption. Any concrete automaton
built by `constructGBA`/`GBA.degeneralize` satisfies this with `univ :=`
its own (finite, `Std.HashMap`-backed) state set.

No `initialStates` field here — that's only relevant at a concrete
checker's own top level (as a separate hypothesis
`∀ i ∈ initialStates, univ.contains i`), not here. -/
structure FiniteReach {State : Type u} [BEq State] [Hashable State]
    (succs : State → Array State) where
  univ : Std.HashSet State
  closed : ∀ s, univ.contains s → ∀ t ∈ succs s, univ.contains t

/-! ## Algorithm-agnostic emptiness-check contract

Corresponds to CAVA's `find_ce_spec` (`CAVA_Abstract.thy`): an abstract
specification of what it means for an emptiness-check result to be correct,
detached from any particular graph-search algorithm. CAVA proves its
top-level `abs_model_check_correct` once, entirely against `find_ce_spec`'s
contract; nested DFS (`find_ce_impl`) is then proven, as a separate
obligation, to *refine* that spec. Swapping in a different algorithm later
only requires a new refinement proof — `abs_model_check_correct` itself
never changes.

`AcceptingCycle` above is already the algorithm-free witness CAVA's
`is_acc_run` plays the role of — stated purely over
`initialStates`/`succs`/`isAccepting`, no mention of any specific search
strategy. `nestedDFSWF_nonEmpty_valid`/`nestedDFSWF_empty_no_cycle`
(`NestedDFS/NestedDFSTermination.lean`) are exactly `find_ce_spec`'s two cases, proven
for `nestedDFSWF` specifically. This structure packages that same contract
as an explicit interface so a future algorithm (e.g. an SCC-based checker)
can be swapped in by proving just these two obligations, without touching
any proof built on top of it (such as `Pipeline.lean`/`ModelCheck.lean`'s
correctness theorems, once they exist).

One honest divergence from CAVA: `find_ce_spec` allows a `Some None` case —
"confirmed nonempty, no witness computed" — which our two-case
`EmptinessResult` has no room for; every algorithm satisfying this
interface must produce a concrete `stem`/`loop` on `.nonEmpty`. That's a
strictly *stronger* contract than CAVA's abstract one, not a gap. -/

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-- Contract any emptiness-check algorithm must satisfy to be usable
wherever `nestedDFSWF` is used today, without requiring downstream proofs
to know which algorithm computed the result. -/
structure EmptinessChecker (State : Type u) [BEq State] [Hashable State]
    [LawfulBEq State] where
  /-- Compute the emptiness result for a graph given by its successor
  function, a finite-reachability witness, an accepting predicate, and its
  initial states — the same four pieces of data `nestedDFSWF` already takes. -/
  check : (succs : State → Array State) → FiniteReach succs →
    (isAccepting : State → Bool) → List State → EmptinessResult State
  /-- Soundness of `.nonEmpty`: a returned `stem`/`loop` is a genuine
  `AcceptingCycle` witness. -/
  nonEmpty_valid : ∀ {succs : State → Array State} {fr : FiniteReach succs}
      {isAccepting : State → Bool} {initialStates stem loop : List State},
    (∀ x ∈ initialStates, fr.univ.contains x) →
    check succs fr isAccepting initialStates = .nonEmpty stem loop →
    ∃ ac : AcceptingCycle initialStates succs isAccepting,
      ac.stem = stem ∧ ac.cycle = loop.tail
  /-- Completeness of `.empty`: no `AcceptingCycle` exists. -/
  empty_no_cycle : ∀ {succs : State → Array State} {fr : FiniteReach succs}
      {isAccepting : State → Bool} {initialStates : List State} {n : Nat},
    (∀ x ∈ initialStates, fr.univ.contains x) →
    check succs fr isAccepting initialStates = .empty n →
    ¬∃ _ac : AcceptingCycle initialStates succs isAccepting, True

end LTLLib
