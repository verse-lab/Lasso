/-
  Generic Nested DFS emptiness check for Büchi automata — abstract
  reference layer only. Not part of the verified pipeline; see "What this
  file actually is" below before relying on anything here.

  Implements the Courcoubetis-Vardi-Wolper-Yannakakis (CVWY) algorithm for
  detecting accepting cycles in a graph. This is the standard algorithm for
  on-the-fly LTL model checking.

  The algorithm is generic: parameterized by state type, successor function,
  and accepting predicate. It does not depend on any specific automaton type.

  No direct Isabelle correspondence — the LTL_to_GBA formalization does not
  include the emptiness check (it only produces the GBA). The emptiness check
  is part of the broader CAVA model checking framework.

  ## What this file actually is

  `nestedDFS`/`innerDFS`/`outerDFSLoop` below are `partial def`s: unverified
  termination, kept purely as human-readable pseudocode of the algorithm.
  Nothing in this codebase calls them — every actual computation and every
  correctness theorem goes through `nestedDFSWF` (`NestedDFS/NestedDFSTermination.lean`,
  well-founded, total) and the fuel-indexed proof device it's bridged to
  (`NestedDFS/NestedDFSCorrectness.lean`). That fuel-indexed version was independently
  hand-written to implement the same algorithm, not derived from or checked
  against this file — there is **no Lean theorem anywhere connecting this
  file's definitions to `nestedDFS_fuel`/`nestedDFSWF`**.

  This intentionally mirrors CAVA's own decision to keep its abstract
  `nested_dfs ≡ do { s ← it_dfs G accpt; RETURN (lasso s) }` (`Nested_DFS.thy`)
  around once the concrete, executable `nested_dfs_code` exists, rather than
  deleting it. It does **not** mirror CAVA's proof: in Isabelle, those two
  layers are connected by an actual refinement theorem (`nested_dfs_impl`,
  `nested_dfs_code.refine`) — CAVA proves `nested_dfs_code` refines
  `nested_dfs`'s abstract nondeterministic specification, via the Isabelle
  Refinement Framework. That refinement proof has not been ported here, and
  — unlike, say, `Product.finiteReach`'s `sorry` (`Product.lean`) — it isn't
  a gap that needs closing: this Lean port proves `nestedDFSWF`'s
  correctness via a completely different route
  (`NestedDFS/NestedDFSCorrectness.lean`'s fuel-indexed induction, directly on the
  concrete algorithm), which never needs an abstract reference
  implementation as an intermediate proof target the way CAVA's
  refinement-calculus style does. This file's only remaining job is
  documentation: readable pseudocode for anyone approaching the algorithm
  before diving into the well-founded/fuel machinery.

  The verified, total, actually-terminating counterpart is `nestedDFSWF`
  (`NestedDFS/NestedDFSTermination.lean`): it requires a `FiniteReach succs` witness as
  an explicit argument (the Lean analogue of `ASSERT (fb_graph G)`), and has
  both correctness directions proven unconditionally
  (`nestedDFSWF_empty_no_cycle`, `nestedDFSWF_nonEmpty_valid`). Use
  `nestedDFSWF`, never this file's `nestedDFS`, wherever a verified result is
  needed.

  References:
  - Courcoubetis, Vardi, Wolper, Yannakakis: "Memory-efficient algorithms
    for the verification of temporal properties" (1992)
  - Baier & Katoen: "Principles of Model Checking", Section 4.3.4
-/

import Std
import LTLLib.EmptinessCheck

namespace LTLLib

/-- Internal mutable state for the nested DFS algorithm. -/
private structure NDFSState (State : Type u) [BEq State] [Hashable State] where
  /-- States visited by the outer DFS. -/
  outerVisited : Std.HashSet State
  /-- States fully processed by completed inner DFS calls.
  These never need to be re-explored by future inner DFS calls
  (optimization from the CVWY paper). -/
  innerFinished : Std.HashSet State

/-- Inner DFS: search for a path from `current` back to `seed` — or, with the
Holzmann-Peled-Yannakakis shortcut, back to *any* state on the outer DFS's
current call stack (`cyan`). If found, an accepting cycle exists.

This is CAVA's `cyan`/`run_red_dfs` stop predicate (`Nested_DFS.thy:54,67-74`):
`λx. x = u ∨ x ∈ cyan s`. Any state on the outer stack is, by construction, an
ancestor of `seed` in the DFS tree, so the existing stack path is itself a
ready-made witness back to `seed` — no need to keep searching for the literal
seed once any ancestor is re-touched. See `NestedDFSPlan.md`'s
"Holzmann-Peled-Yannakakis inner-DFS shortcut" section for the full
CAVA-correspondence write-up.

Returns `some (path, target)` if a path to some `target ∈ {seed} ∪ cyan` is
found (CAVA's `Inr (vs, v)`), `none` otherwise. -/
private partial def innerDFS [BEq State] [Hashable State]
    (successors : State → Array State)
    (seed : State)
    (cyan : List State)
    (current : State)
    (innerVisited : Std.HashSet State)
    (st : NDFSState State)
    : Option (List State × State) × Std.HashSet State × NDFSState State :=
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
          if succ == seed || cyan.contains succ then
            -- Found a cycle back to seed, or (HPY shortcut) back to some
            -- other state currently on the outer DFS's stack.
            (some ([current], succ), innerVisited, st)
          else
            match innerDFS successors seed cyan succ innerVisited st with
            | (some (cyclePath, target), iv, st') =>
              (some (current :: cyclePath, target), iv, st')
            | (none, iv, st') =>
              (none, iv, st')
    |> fun (result, innerVisited, st) =>
      match result with
      | some _ => (result, innerVisited, st)
      | none =>
        -- All successors explored without finding seed/cyan; mark as finished
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
        match innerDFS successors current pathStack current innerVisited st with
        | (some (cyclePath, target), _, st') =>
          -- Found accepting cycle! `target` (HPY shortcut) may be `current`
          -- itself or any other state on `pathStack`. `stem` is unchanged;
          -- `loop` splices `cyclePath` (current ... target) with the
          -- existing stack tree-path from `target` back down to `current`'s
          -- own stack-parent (`chain_append_boundary`/`chain_getLast_edge`'s
          -- kind of reasoning, shared with the Schwoon-Esparza back-edge
          -- case). When `target = current` this collapses to exactly the
          -- previous `current :: cyclePath` formula, since the appended
          -- stack-suffix is then empty — no separate degenerate case needed.
          let loopTail := (pathStack.dropWhile (fun y => !(y == target))).dropLast
          (.nonEmpty pathStack (current :: cyclePath ++ loopTail), st')
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
        -- `outerDFSLoopWF` in `NestedDFS/NestedDFSCorrectness.lean`/
        -- `NestedDFS/NestedDFSTermination.lean`.
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
