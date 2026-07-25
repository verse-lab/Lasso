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
`expand`'s termination.

**Update (2026-07-25, later still): fuel-bridge started, hit one isolated
blocker — and root-caused it further than first thought.** The fold-level
half of the inner bridge (`innerDFS_fuel_fold_eq_innerDFSCore`,
`NestedDFSTermination.lean`) is fully proved for 3 of 4 branches; the 4th
(`innerDFSCore_fresh_eq`) is `sorry`. Initially diagnosed as a `hr`-binder
dependent-match issue and "fixed" by rewriting `innerDFSCore` to avoid `hr`
— but the *exact same* "motive is not type correct" failure persisted
anyway, for a deeper reason: `innerDFSCore`'s Subtype-returning `.eq_def`
unfolding can't be externally rewritten at all once its bundled property is
stated in terms of the value's own projections, `hr` or not. Confirmed
across every rewrite-family tactic (`rfl`, `rw`, `▸`, `generalize`,
`rcases h : e with pat`, tactic-mode `match`, `Subtype.ext`-based whole-term
rewriting) — genuine Lean 4 limitation, not a proof mistake.

**Real payoff from the investigation**: root-caused *why*
`innerDFSCore.induct` fails to generate (flagged as a dead end back in the
step-2 update above) — it's specifically `omega`-generated proof terms
inside `decreasing_by`, confirmed via a minimal reproduction. Replacing the
one `omega` call in `innerDFSCore`'s `decreasing_by` with explicit
`Nat.le_antisymm`/`Nat.le_trans` term combinators makes `innerDFSCore.induct`
generate successfully, with real per-case induction hypotheses — verified
directly. This fix is applied and kept (strict improvement, `innerDFSCore`
itself stays 0 sorry). The way forward for `innerDFSCore_fresh_eq` is to
stop trying to prove a standalone unfolding lemma (a dead end) and instead
redrive `innerDFS_fuel_fold_eq_innerDFSCore` itself via
`induction ... using innerDFSCore.induct` (swap which side drives the
induction, unfold `innerDFS_fuel`/`innerDFS_fuel_fold` — which have no
Subtype-return issue — via their own `.eq_def` on the other side). Real
restructuring, not attempted yet this session; see `ProofPlan.md`'s Phase 2
section for the full detail. `outerDFSLoopWF`'s own bridge to
`outerDFSLoop_fuel` is deferred until this resolves.

**Update (2026-07-25, later still): `innerDFSCore` rebuilt as an
explicit-stack loop, matching CAVA's actual architecture.** Asked to
re-check why the fold-based design (previous updates above) couldn't follow
CAVA's own strategy instead of patching around the `innerDFSCore_fresh_eq`
dead end. Re-reading `Param_DFS.thy`/`DFS_Find_Path.thy` directly found the
answer: CAVA's red DFS isn't a hand-written recursive function at all — it's
`find_path1_restr_spec`, an abstract `SPEC`, realized concretely via the
refinement framework's generic `FOREACHc` combinator, whose termination is a
single fact ("the iteration set shrinks by one per step") entirely
decoupled from the loop body's result. Both CAVA's blue and red DFS reduce
to the *same* generic `param_DFS`/`it_dfs` engine — one flat explicit-stack
loop, never nested recursive-descent-with-fold. That's exactly what our
fold-based `innerDFSCore` was missing, and exactly why it hit the
Subtype/"motive not type correct" dead end: nested recursive descent forces
the next fold-step's termination proof to depend on a fact about the
*previous* call's return value, a dependency CAVA's structure never creates.

Fixed by rebuilding `innerDFSCore` from scratch as an explicit-stack single
flat loop (structurally identical to `outerDFSLoopWF`, reusing its
measure/`decreasing_by` idioms) — no `Subtype`-bundled return type needed at
all. A second finding while proving the rebuild's own
`innerDFSCore_outerVisited_pres` lemma: even without the Subtype, threading
`fr.univ`-membership facts as *proof-carrying explicit arguments* still made
`rw`/`induction ... using .induct` fragile. Root cause: those facts were
never actually needed for the function's *value*, only locally for
`decreasing_by`'s measure decrease — so they were dropped from the signature
entirely, replaced by a runtime `if fr.univ.contains succ then … else
⟨defensive fallback⟩` check (a standard junk-value-on-out-of-domain-input
pattern). This made `innerDFSCore`'s type carry zero proof obligations,
which is what actually made the induction-based lemma go through cleanly.
Whole project builds clean (394 jobs); `innerDFSCore`,
`innerDFSCore_outerVisited_pres`, `innerDFSWF` (+ its two case lemmas), and
`outerDFSLoopWF` are all 0 sorry. See `ProofPlan.md`'s Phase 2 section for
the full write-up, including the CAVA source excerpts.

**Update (2026-07-25, later still): fold-level bridge redesigned and fully
proved — `NestedDFSTermination.lean` is now 0 sorry.** The redesign
(`innerDFS_fuel_chain`, a new stack-chaining auxiliary function, plus
`pathStack`-based rewrapping for its "found" case — verified algebraically
before implementing) bridges cleanly to `innerDFSCore` via
`innerDFS_fuel_chain_eq_innerDFSCore` (6 cases, `induction ... using
innerDFSCore.induct`). Along the way this surfaced one more genuine
subtlety — `innerDFS_fuel_chain` reuses fuel uniformly across stack frames,
while the real nested-call semantics decrements it once per "descend into a
fresh successor" — resolved with two more self-contained lemmas:
`innerDFS_fuel_add_preserves` (more fuel can't change a successful result)
and `innerDFS_fuel_exists` (sufficient fuel guarantees success — this is
the *content* of the very first, deleted `innerDFS_fuel_sufficient`,
resurrected here). `NestedDFSCorrectness.lean` was never touched throughout
any of this — still 0 sorry, still ~2000 lines, exactly as planned from the
start of Phase 2. See `ProofPlan.md`'s Phase 2 section for the full
write-up. **Current sorry count in `NestedDFSTermination.lean`: 0.**

**Update (2026-07-25, continued): `outerDFSLoopWF ↔ outerDFSLoop_fuel`
bridge done — Phase 2's nested-DFS termination work is complete.**
Re-checking CAVA first (per standing instruction) surfaced two pre-existing
issues in `outerDFSLoopWF`, both fixed before the bridge itself: (1) it still
carried `hstack_states`/`hstack_remaining` as proof-carrying arguments,
unlike the already-fixed `innerDFSCore` — stripped, matching CAVA's own
`step`/`DFS_invar` separation (`Param_DFS.thy`'s `param_dfs_variant_step`
takes the invariant only as a side hypothesis, never in `step`'s type); (2)
its accepting-leaf branch called `innerDFSCore` directly instead of
`innerDFSWF`, skipping the `innerFinished` short-circuit and omitting the
`current ::` prepend on the found cycle — both fixed (now calls `innerDFSWF`,
matching `outerDFSLoop_fuel`'s own call, and prepends `current`, matching
`outerDFSLoop_fuel_nonEmpty_witness`'s documented `loop[0]`-is-redundant
convention). With those fixed, the bridge itself was exactly as simple as
anticipated: same explicit-stack shape on both sides, so a direct
`induction ... using outerDFSLoopWF.induct` (7 cases) sufficed, no
`_chain`-style reindexing needed. One new subtlety: `outerDFSLoop_fuel`
spends fuel per *iteration*, not per *descend* (unlike inner), so there's no
closed-form fuel formula — resolved by proving fuel *existence* via
induction on the same lex measure `outerDFSLoopWF` already uses for
termination, mirroring how CAVA's own `it_dfsT_eq_it_dfs` never computes a
numeral bound either. Needed one new lemma, `outerDFSLoop_fuel_add_preserves`
(fuel monotonicity), for the one branch with two independent fuel
requirements sharing a slot. See `ProofPlan.md`'s Phase 2 section for the
full write-up. **`NestedDFSTermination.lean`: 0 sorry, 0 warnings, whole
project builds clean (394 jobs) — Phase 2's nested-DFS termination work is
done.** Remaining: `expand`'s own termination conversion, separately scoped.

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
