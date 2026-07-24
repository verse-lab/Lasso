# Plan: Nested DFS Correctness (Phase 5)

## Overview

Prove that `nestedDFS` correctly decides whether a Büchi automaton has an accepting run.

Two directions:
- **Phase 5a**: `nonEmpty stem loop` → accepting run exists (output verification)
- **Phase 5b**: `empty` → no accepting run exists (algorithm invariants)

## Phase 5a: Output Verification ✅ DONE (~329 lines)

**Files**: `LTLLib/Lasso.lean` (~232 lines), `LTLLib/OutputVerify.lean` (~97 lines)

### Lasso.lean — Abstract Lasso Theory

- `lassoRun stem cycle default : Nat → State` — infinite run construction
  - Positions `0` to `stem.length - 2`: from stem
  - Position `stem.length - 1` onwards: cycles through `cycle`
- `ValidLasso A stem cycle` — structure with validity conditions:
  - `stem_nonempty`, `cycle_nonempty`
  - `stem_initial`: first state is initial
  - `stem_chain`: consecutive stem states are transitions
  - `overlap`: `stem.getLast = cycle.head`
  - `cycle_chain`: consecutive cycle states are transitions
  - `cycle_back`: last cycle state transitions to first
  - `cycle_accepting`: cycle head is accepting
- Key theorems:
  - `run_isRun`: the constructed run has valid transitions
  - `run_isAccepting`: the run visits accepting states infinitely often
  - `accepts_of_validLasso`: valid lasso → automaton accepts

### OutputVerify.lean — Connecting nestedDFS Output

- `ba_hasAcceptingRun_of_lasso`: given computational checks (Array.contains, isAccepting),
  constructs a `ValidLasso` and derives `∃ σ, isRun σ ∧ isAcceptingRun σ`
- `ba_hasAcceptingRun_of_ndfs_output`: takes raw nestedDFS output format
  (`loop` with duplicate seed, cycle = `loop.tail`) and reduces to the clean lasso theorem

## Phase 5b: Completeness (~800-1200 lines)

**Goal**: If `nestedDFS` returns `empty`, then no accepting run exists.

**Approach**: Fuel-based reasoning. Add fuel to make functions total, prove by
induction on fuel.

### Key CVWY Invariants

1. **Outer DFS invariant**: If an accepting cycle is reachable from any state in
   `outerVisited`, then `nonEmpty` would have been returned before reaching the
   current point.

2. **Inner DFS invariant**: If `innerDFS seed current` returns `none`, there is
   no path from `current` to `seed` that avoids `innerFinished` states.

3. **`innerFinished` soundness**: Every state in `innerFinished` cannot reach any
   accepting state that is currently on the outer DFS stack.

4. **Critical ordering property**: When backtracking from an accepting state `q`
   in the outer DFS, all states reachable from `q` that are in `outerVisited`
   have already been fully processed (they were discovered after `q` in DFS order).
   This means the inner DFS from `q` will explore all cycle-forming paths.

### Proof outline

1. Define `innerDFS_fuel` and `outerDFSLoop_fuel` (total versions with fuel)
2. Show they agree with the `partial` versions when fuel is sufficient
3. Prove inner DFS correctness by induction on fuel:
   - `some path` → path is valid and leads back to seed
   - `none` → no path to seed exists (avoiding innerFinished)
4. Prove outer DFS maintains invariant by induction on fuel
5. Conclude: `empty` result → invariant holds at termination → no accepting cycle

### The hardest part

The completeness direction requires showing that if an accepting cycle exists,
the algorithm *must* find it. The key insight is the **DFS ordering argument**:
among all accepting states on a cycle, the one that finishes last in the outer
DFS can reach itself through states not yet in `innerFinished`.

## Execution Order

1. **Phase 5a first** — quick win, ~200-400 lines
2. **Phase 5b later** — large effort, can be deferred

Phase 5a alone doesn't complete Path A (soundness-only end-to-end), but it
certifies counterexamples, which is independently useful.

Phase 5b is what's needed for Path A: `empty → all ξ satisfy φ`.

## Status update

Phases 5a, 5b, and 5c (soundness of a `nonEmpty` result — see `ProofPlan.md`
for the detailed writeup) are now all done; `NestedDFSCorrectness.lean` is
sorry-free and proves both directions of `nestedDFS_fuel`'s correctness.

## Future work (TODO): Schwoon-Esparza back-edge optimization

Our `innerDFS`/`outerDFSLoop` only implement the classic CVWY algorithm: a
cycle is detected exclusively by the *inner* DFS finding its way back to the
seed after backtracking from an accepting state. CAVA's Isabelle
implementation additionally has the Schwoon & Esparza (2005) shortcut: the
*outer* DFS can detect a cycle directly when it hits a back-edge to a state
already on the stack, without ever launching the inner DFS for that case
(`se_back_edge`/`on_back_edge` in CAVA's `Nested_DFS.thy`).

This is a performance optimization, not a correctness one — it lets the
algorithm terminate faster on graphs where cycles show up via back-edges,
without changing what counts as an accepting cycle. Adding it would mean:
- implementing the back-edge check in `outerDFSLoop`/`outerDFSLoop_fuel`,
- porting the `back_edge` case of CAVA's `lasso_inv` maintenance proof
  (`Nested_DFS.thy` ~437–489, the `se_back_edge_lasso_inv` lemma) alongside
  the `finish`-case we already have, for the soundness direction, and
- re-checking the completeness direction (Phase 5b) still holds with the new
  code path.

Not started; no immediate blocker, purely a future enhancement.
