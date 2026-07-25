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

**Termination (Phase 2, see `ProofPlan.md`)**: the inner-DFS half of
fuel-sufficiency is done (`innerDFS_fuel_sufficient`,
`NestedDFSTermination.lean`). The outer-DFS half needs a genuine
`termination_by` conversion of `innerDFS`/`outerDFSLoop` (fuel-based
threshold-combining hit a real circularity and was abandoned) — see
`ProofPlan.md`'s Phase 2 section for the full design and resume plan.

**Update (2026-07-25)**: read CAVA's actual Isabelle sources
(`Param_DFS.thy`, `Nested_DFS.thy`, `DFS_Find_Path.thy`) directly rather than
relying on secondhand description. Corrected finding: CAVA's blue (outer) and
red (inner) DFS are **two independently-terminating functions**, each with
its own self-contained well-founded measure — not one mutually-recursive
definition needing a combined bound. The outer loop calls the inner one only
as an ordinary (already-total, in Isabelle: abstract `SPEC`-level oracle)
function call; its own termination proof never inspects the inner call's
step count. This is exactly what resolves the circularity the fuel-based
attempt hit, and it means the Lean port should convert `innerDFS` (own
measure `univ.size - iv.size`, needs a `FiniteReach` param and a
subtype-bundled return type because of its sibling-fold structure) and
*then* `outerDFSLoop` (own measure, calls the now-total `innerDFS` as a
plain helper — no subtype bundling needed here, since `outerDFSLoop` has no
sibling fold and its measure doesn't depend on `innerFinished` at all) as
two **separate** conversions, not a mutual one — followed by bridge lemmas
(`innerDFS = innerDFS_fuel N`, `outerDFSLoop = outerDFSLoop_fuel N`,
mirroring CAVA's own `it_dfsT_eq_it_dfs`) to transport the existing
~2000-line `NestedDFSCorrectness.lean` proof onto the real functions instead
of redoing it. See `ProofPlan.md`'s Phase 2 section for the full write-up,
including the verbatim Isabelle snippets. Not started; this is a plan
correction only.

**Update (2026-07-25, later same day): `innerDFS` converted.**
`innerDFSWF`/`innerDFSCore` in `NestedDFSTermination.lean`, 0 sorry, 0
warnings, whole project still builds (394 jobs). One correction to the note
directly above: the measure actually used is `Std.HashSet` set-difference
size (`(fr.univ \ iv).size`), *not* `univ.size - iv.size` (`Nat`
subtraction) as guessed there — found while implementing, this avoids ever
needing `iv ⊆ univ` as a maintained invariant, which in turn makes the
still-needed Subtype-bundled return type far lighter than expected (one `≤`
fact, not a closure invariant). See `ProofPlan.md`'s Phase 2 section for the
full write-up.

**Update (2026-07-25, later still): `outerDFSLoop` converted too.**
`outerDFSLoopWF` in `NestedDFSTermination.lean`, 0 sorry, 0 warnings, whole
project still builds. Confirmed simpler than `innerDFS`'s conversion as
predicted — no Subtype-bundled return type needed at all, since
`outerDFSLoop` has no fold over siblings. One wrinkle found while
implementing: proving "`innerDFSCore` never touches `outerVisited`" as a
*separate* lemma (via `innerDFSCore.induct`) doesn't work — Lean's
functional-induction-principle deriver fails outright on `innerDFSCore`
("Cannot derive functional induction principle... Internal error in
`foldAndCollect`"), apparently choking on the `omega`-generated proof terms
inside its `Subtype`-returning well-founded definition. Fixed by bundling
that fact directly into `innerDFSCore`'s own return type instead (a second
Subtype conjunct alongside step 1's measure-monotonicity fact) rather than
proving it afterward — cheap to add since the needed reasoning was already
in scope at each of `innerDFSCore`'s own definition sites. See
`ProofPlan.md`'s Phase 2 section for the full write-up. Both nested-DFS
functions are now off `partial`; next up is the fuel-bridge step
(`innerDFS = innerDFS_fuel N` / `outerDFSLoop = outerDFSLoop_fuel N`, to
transport `NestedDFSCorrectness.lean` without redoing it) and, separately,
`expand`'s termination. Neither started yet.

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
