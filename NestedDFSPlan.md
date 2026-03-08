# Plan: Nested DFS Correctness (Phase 5)

## Overview

Prove that `nestedDFS` correctly decides whether a Büchi automaton has an accepting run.

Two directions:
- **Phase 5a**: `nonEmpty stem loop` → accepting run exists (output verification)
- **Phase 5b**: `empty` → no accepting run exists (algorithm invariants)

## Phase 5a: Output Verification (~200-400 lines)

**Goal**: Given `nestedDFS` returns `nonEmpty stem loop`, verify that `stem ++ loop^ω`
forms an accepting run of the automaton.

**What "accepting run" means** for `BA.toSpec` (OASpec BAState α 1):
- `isRun σ`: `initial (σ 0) ∧ ∀ n, trans (σ n) (σ (n+1))`
- `runCompatible σ ξ`: `∀ n, labelCompat (σ n) (ξ n)`
- `isAcceptingRun σ`: `∀ n, ∃ j, acceptSet (σ (n+j))` (visits accepting states infinitely often)

**For a lasso `stem ++ loop^ω`**:
- `stem` is a path from an initial state to an accepting state `q`
- `loop` is a cycle: starts and ends at `q`, passes through `q`
- Since `q` is accepting and appears infinitely often, the Büchi condition is satisfied

**Proof structure**:
1. Define `lassoRun : List State → List State → (Nat → State)` that builds the ω-word
2. Prove `lassoRun_isRun`: valid transitions along stem and loop
3. Prove `lassoRun_accepting`: accepting state visited infinitely often
4. Theorem: `nestedDFS_nonEmpty_correct`: `nonEmpty stem loop` → `∃ accepting run`

**Key properties to verify on the output**:
- `stem.head` is an initial state
- Consecutive states in `stem` are successors
- `stem.getLast = loop.head = loop.getLast` (cycle connects)
- Consecutive states in `loop` are successors
- The accepting state (`loop.head`) satisfies `isAccepting`

**Note**: We prove this *abstractly* — given that stem/loop satisfy the above
properties, an accepting run exists. Whether `nestedDFS` actually produces valid
stem/loop is a separate (easier) argument from the algorithm structure.

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
