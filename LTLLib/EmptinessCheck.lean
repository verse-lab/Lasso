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
import Mathlib.Data.Set.Card

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

Lean analogue of CAVA's `fb_graph` locale assumption — and, more precisely,
of the top-level `finite ((g_E sys)⇧* `` g_V0 sys)` assertion CAVA states
over the *canonical* reachability closure of a graph's own edge relation,
never over an arbitrary caller-named closed superset. `Reachable` below is
that canonical closure; `FiniteReach` is the bare existence certificate that
it's finite. Deliberately a `Prop` with no data fields at all: nothing here
is ever touched on an executable path, matching CAVA's `ASSERT`-once,
never-again discipline exactly (see `FiniteReachRedesign.md` §8 for the full
design rationale — this replaces the old `Std.HashSet`-witness-carrying
`structure FiniteReach`).

No `BEq`/`Hashable` needed on `State` for either definition — pure `Prop`,
no `Std.HashSet` involved. -/

/-- Canonical reachability: every `i ∈ initialStates` is reachable
(reflexively), and reachability is closed under one `succs`-step. -/
inductive Reachable {State : Type u} (initialStates : List State)
    (succs : State → Array State) : State → Prop where
  | base {i : State} (hi : i ∈ initialStates) : Reachable initialStates succs i
  | step {s t : State} (hs : Reachable initialStates succs s) (ht : t ∈ succs s) :
      Reachable initialStates succs t

/-- Bare existence certificate: the canonically-reachable set is finite.
`Reachable.base` already makes "every initial state is reachable" free, so
callers/downstream proofs never need a separate `∀ i ∈ initialStates, ...`
hypothesis alongside this one. -/
def FiniteReach {State : Type u} (initialStates : List State)
    (succs : State → Array State) : Prop :=
  {s | Reachable initialStates succs s}.Finite

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
  function, its initial states, a finite-reachability certificate (now a
  bare `Prop`, needed only to state the type — never inspected by `check`
  itself as data), and an accepting predicate. `initialStates` moves before
  `FiniteReach` since the latter's type now depends on it. -/
  check : (succs : State → Array State) → (initialStates : List State) →
    FiniteReach initialStates succs → (isAccepting : State → Bool) →
    EmptinessResult State
  /-- Soundness of `.nonEmpty`: a returned `stem`/`loop` is a genuine
  `AcceptingCycle` witness. The old `∀ x ∈ initialStates, fr.univ.contains x`
  hypothesis is gone — subsumed by `Reachable.base`. -/
  nonEmpty_valid : ∀ {succs : State → Array State} {initialStates : List State}
      {fr : FiniteReach initialStates succs} {isAccepting : State → Bool}
      {stem loop : List State},
    check succs initialStates fr isAccepting = .nonEmpty stem loop →
    ∃ ac : AcceptingCycle initialStates succs isAccepting,
      ac.stem = stem ∧ ac.cycle = loop.tail
  /-- Completeness of `.empty`: no `AcceptingCycle` exists. -/
  empty_no_cycle : ∀ {succs : State → Array State} {initialStates : List State}
      {fr : FiniteReach initialStates succs} {isAccepting : State → Bool} {n : Nat},
    check succs initialStates fr isAccepting = .empty n →
    ¬∃ _ac : AcceptingCycle initialStates succs isAccepting, True

end LTLLib
