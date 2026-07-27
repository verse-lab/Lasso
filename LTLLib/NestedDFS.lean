/-
  Generic Nested DFS emptiness check for Büchi automata.

  Implements the Courcoubetis-Vardi-Wolper-Yannakakis (CVWY) algorithm for
  detecting accepting cycles in a graph. This is the standard algorithm for
  on-the-fly LTL model checking.

  The algorithm is generic: parameterized by state type, successor function,
  and accepting predicate. It does not depend on any specific automaton type.

  No direct Isabelle correspondence — the LTL_to_GBA formalization does not
  include the emptiness check (it only produces the GBA). The emptiness check
  is part of the broader CAVA model checking framework.

  This file's `nestedDFS`/`innerDFS`/`outerDFSLoop` are the *abstract
  reference* definitions — `partial def`, unverified termination, kept for
  readability. This mirrors CAVA's own two-layer split (`Nested_DFS.thy`):
  the abstract `nested_dfs ≡ do { s ← it_dfs G accpt; RETURN (lasso s) }` is
  never deleted once the concrete, generated `nested_dfs_code` exists —
  both are kept, connected by a refinement theorem (`nested_dfs_impl`,
  `nested_dfs_code.refine`), and `nested_dfs_code`'s own precondition is an
  explicit `ASSERT (fb_graph G)` (finite/bounded-degree graph), threaded
  through rather than internally re-derived.

  The verified, total, actually-terminating counterpart here is
  `nestedDFSWF` (`NestedDFSTermination.lean`), playing `nested_dfs_code`'s
  role: it requires a `FiniteReach succs` witness as an explicit argument
  (the Lean analogue of `ASSERT (fb_graph G)`), is proven equal to
  `nestedDFS_fuel` for sufficient fuel (`nestedDFS_fuel_eq_nestedDFSWF`),
  and inherits both of Phase 5's correctness theorems for free
  (`nestedDFSWF_empty_no_cycle`, `nestedDFSWF_nonEmpty_valid`). Use
  `nestedDFSWF`, not this file's `nestedDFS`, wherever a verified result is
  needed.

  References:
  - Courcoubetis, Vardi, Wolper, Yannakakis: "Memory-efficient algorithms
    for the verification of temporal properties" (1992)
  - Baier & Katoen: "Principles of Model Checking", Section 4.3.4
-/

import Std

namespace LTLLib

/-- Result of the nested DFS emptiness check. -/
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

/-- Internal mutable state for the nested DFS algorithm. -/
private structure NDFSState (State : Type u) [BEq State] [Hashable State] where
  /-- States visited by the outer DFS. -/
  outerVisited : Std.HashSet State
  /-- States fully processed by completed inner DFS calls.
  These never need to be re-explored by future inner DFS calls
  (optimization from the CVWY paper). -/
  innerFinished : Std.HashSet State

/-- Inner DFS: search for a path from `current` back to `seed`.
If found, an accepting cycle exists.

Returns `some path` if a path back to `seed` is found, `none` otherwise. -/
private partial def innerDFS [BEq State] [Hashable State]
    (successors : State → Array State)
    (seed : State)
    (current : State)
    (innerVisited : Std.HashSet State)
    (st : NDFSState State)
    : Option (List State) × Std.HashSet State × NDFSState State :=
  if st.innerFinished.contains current then
    (none, innerVisited, st)
  else if innerVisited.contains current then
    (none, innerVisited, st)
  else
    let innerVisited := innerVisited.insert current
    let succs := (successors current).toList
    succs.foldl (init := (none, innerVisited, st))
      fun (result, innerVisited, st) succ =>
        match result with
        | some _ => (result, innerVisited, st)  -- already found, short-circuit
        | none =>
          if succ == seed then
            -- Found a cycle back to seed!
            (some [current], innerVisited, st)
          else
            match innerDFS successors seed succ innerVisited st with
            | (some cyclePath, iv, st') =>
              (some (current :: cyclePath), iv, st')
            | (none, iv, st') =>
              (none, iv, st')
    |> fun (result, innerVisited, st) =>
      match result with
      | some _ => (result, innerVisited, st)
      | none =>
        -- All successors explored without finding seed; mark as finished
        let st := { st with innerFinished := st.innerFinished.insert current }
        (none, innerVisited, st)

/-- Outer DFS with explicit stack. Processes one connected component.

The stack contains `(state, successors_list, remaining_successors)`.
`pathStack` records the DFS path from the root, used for stem extraction. -/
private partial def outerDFSLoop [BEq State] [Hashable State]
    (successors : State → Array State)
    (isAccepting : State → Bool)
    (stack : List (State × List State))  -- (state, remaining_successors)
    (pathStack : List State)  -- DFS path from root (for stem extraction)
    (st : NDFSState State)
    : EmptinessResult State × NDFSState State :=
  match stack with
  | [] => (.empty st.outerVisited.size, st)
  | (current, remaining) :: rest =>
    match remaining with
    | [] =>
      -- Backtracking from `current`: all successors explored
      if isAccepting current then
        -- Launch inner DFS from this accepting state
        let innerVisited := Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)
        match innerDFS successors current current innerVisited st with
        | (some cyclePath, _, st') =>
          -- Found accepting cycle!
          -- stem = pathStack (path to the accepting state, inclusive)
          -- loop = seed :: cyclePath (from seed, through cycle, back to seed)
          (.nonEmpty pathStack (current :: cyclePath), st')
        | (none, _, st') =>
          outerDFSLoop successors isAccepting rest pathStack.dropLast st'
      else
        outerDFSLoop successors isAccepting rest pathStack.dropLast st
    | succ :: remainingTail =>
      -- Process next successor
      let stack' := (current, remainingTail) :: rest
      if pathStack.contains succ then
        -- Schwoon-Esparza back-edge shortcut (`se_back_edge` in CAVA's
        -- `Nested_DFS.thy`): `succ` is cyan (currently on the outer stack),
        -- so a cycle can be reported directly, without launching innerDFS.
        -- Verified version + full derivation: `outerDFSLoop_fuel`/
        -- `outerDFSLoopWF` in `NestedDFSCorrectness.lean`/
        -- `NestedDFSTermination.lean`.
        if isAccepting current then
          if succ == current then
            -- degenerate case: current -> current is a literal self-loop.
            (.nonEmpty pathStack [current, current], st)
          else
            let loopTail := (pathStack.dropWhile (fun y => !(y == succ))).dropLast
            (.nonEmpty pathStack (current :: current :: loopTail), st)
        else if isAccepting succ then
          let stem := pathStack.takeWhile (fun y => !(y == succ)) ++ [succ]
          let loop := succ :: pathStack.dropWhile (fun y => !(y == succ))
          (.nonEmpty stem loop, st)
        else
          outerDFSLoop successors isAccepting stack' pathStack st
      else if st.outerVisited.contains succ then
        -- Already visited (finished, not on the stack): skip
        outerDFSLoop successors isAccepting stack' pathStack st
      else
        -- Visit new successor: push onto stack
        let st := { st with outerVisited := st.outerVisited.insert succ }
        let succChildren := (successors succ).toList
        let stack' := (succ, succChildren) :: stack'
        outerDFSLoop successors isAccepting stack' (pathStack ++ [succ]) st

/-- Run the nested DFS emptiness check.

Given:
- `initialStates`: the set of initial states to start DFS from
- `successors`: function computing successors of a state
- `isAccepting`: predicate identifying accepting states

Returns:
- `EmptinessResult.empty n`: no accepting cycle found, `n` states explored
- `EmptinessResult.nonEmpty stem loop`: an accepting cycle was found
  - `stem`: path from an initial state to an accepting state (inclusive)
  - `loop`: cycle from the accepting state back to itself (inclusive)

The algorithm (CVWY):
1. Outer DFS explores the graph depth-first, maintaining a visited set.
2. When backtracking from an accepting state `s`, launch inner DFS from `s`.
3. Inner DFS looks for a path from `s` back to `s` (avoiding `innerFinished`).
4. If found: accepting cycle exists → property is violated.
5. States fully explored by inner DFS are marked globally (`innerFinished`)
   to avoid redundant inner searches in subsequent iterations. -/
def nestedDFS [BEq State] [Hashable State]
    (initialStates : List State)
    (successors : State → Array State)
    (isAccepting : State → Bool)
    : EmptinessResult State :=
  let st : NDFSState State := {
    outerVisited := Std.HashSet.emptyWithCapacity 1024
    innerFinished := Std.HashSet.emptyWithCapacity 1024
  }
  go initialStates st
where
  go (remaining : List State) (st : NDFSState State) : EmptinessResult State :=
    match remaining with
    | [] => .empty st.outerVisited.size
    | init :: rest =>
      if st.outerVisited.contains init then
        go rest st
      else
        let st := { st with outerVisited := st.outerVisited.insert init }
        let succs := (successors init).toList
        match outerDFSLoop successors isAccepting
            [(init, succs)] [init] st with
        | (.nonEmpty stem loop, _) => .nonEmpty stem loop
        | (.empty _, st') =>
          go rest st'

end LTLLib
