# Plan: Nested DFS Correctness (Phase 5)

## Overview

Prove that `nestedDFS` correctly decides whether a Büchi automaton has an accepting run.

Two directions:
- **Phase 5a**: `nonEmpty stem loop` → accepting run exists (output verification)
- **Phase 5b**: `empty` → no accepting run exists (algorithm invariants)

## Phase 5a: Output Verification ✅ DONE (~329 lines)

**Files**: `LTLLib/Lasso.lean` (~232 lines), `LTLLib/OutputVerifyBA.lean` (~97 lines)

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

### OutputVerifyBA.lean — Connecting nestedDFS Output

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
for the detailed writeup) are now all done; `NestedDFS/NestedDFSCorrectness.lean` is
sorry-free and proves both directions of `nestedDFS_fuel`'s correctness.

**Termination (Phase 2, see `ProofPlan.md`)**: the inner-DFS half of
fuel-sufficiency is done (`innerDFS_fuel_sufficient`,
`NestedDFS/NestedDFSTermination.lean`). The outer-DFS half needs a genuine
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
~2000-line `NestedDFS/NestedDFSCorrectness.lean` proof onto the real functions instead
of redoing it. See `ProofPlan.md`'s Phase 2 section for the full write-up,
including the verbatim Isabelle snippets. Not started; this is a plan
correction only.

**Update (2026-07-25, later same day): `innerDFS` converted.**
`innerDFSWF`/`innerDFSCore` in `NestedDFS/NestedDFSTermination.lean`, 0 sorry, 0
warnings, whole project still builds (394 jobs). One correction to the note
directly above: the measure actually used is `Std.HashSet` set-difference
size (`(fr.univ \ iv).size`), *not* `univ.size - iv.size` (`Nat`
subtraction) as guessed there — found while implementing, this avoids ever
needing `iv ⊆ univ` as a maintained invariant, which in turn makes the
still-needed Subtype-bundled return type far lighter than expected (one `≤`
fact, not a closure invariant). See `ProofPlan.md`'s Phase 2 section for the
full write-up.

**Update (2026-07-25, later still): `outerDFSLoop` converted too.**
`outerDFSLoopWF` in `NestedDFS/NestedDFSTermination.lean`, 0 sorry, 0 warnings, whole
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
transport `NestedDFS/NestedDFSCorrectness.lean` without redoing it) and, separately,
`expand`'s termination.

**Update (2026-07-25, later still): fuel-bridge started, hit one isolated
blocker — and root-caused it further than first thought.** The fold-level
half of the inner bridge (`innerDFS_fuel_fold_eq_innerDFSCore`,
`NestedDFS/NestedDFSTermination.lean`) is fully proved for 3 of 4 branches; the 4th
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
proved — `NestedDFS/NestedDFSTermination.lean` is now 0 sorry.** The redesign
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
resurrected here). `NestedDFS/NestedDFSCorrectness.lean` was never touched throughout
any of this — still 0 sorry, still ~2000 lines, exactly as planned from the
start of Phase 2. See `ProofPlan.md`'s Phase 2 section for the full
write-up. **Current sorry count in `NestedDFS/NestedDFSTermination.lean`: 0.**

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
full write-up. **`NestedDFS/NestedDFSTermination.lean`: 0 sorry, 0 warnings, whole
project builds clean (394 jobs) — Phase 2's nested-DFS termination work is
done.**

**Update (2026-07-25, continued): wiring finished — total `nestedDFSWF` +
top-level bridge, both correctness theorems transferred.** Checked CAVA on
two questions before starting. (1) Multi-root handling: `Nested_DFS.thy`'s
`nested_dfs ≡ do { s ← it_dfs G accpt; RETURN (lasso s) }` is a *single*
fused loop (root-selection folded into `step` via `get_new_root`, same
measure as everything else) — different from our `nestedDFS_fuel`/
`nestedDFS_fuel.go`'s two-loop split. Diagnosed this as a consequence of not
porting CAVA's generic `param_DFS` locale (out of scope), not a deviation in
the algorithm — so `nestedDFSWF` mirrors `nestedDFS_fuel`'s *existing*
two-loop shape rather than reopening Phase 5's already-proven ~2000 lines
for a purely organizational match. (2) Whether to delete the old `partial
def`s: checked CAVA's own `nested_dfs`/`nested_dfs_code` split —  CAVA never
deletes the abstract spec once the concrete, refined, `ASSERT (fb_graph G)`-
gated implementation exists; both are kept, linked by a refinement theorem.
Same here: `NestedDFS/NestedDFSRef.lean`'s `partial def`s stay (docstring updated to
point at `nestedDFSWF`), not deleted.

**Correction (later session, when this file was renamed `NestedDFSRef.lean`
and moved into `LTLLib/NestedDFS/`):** only the
*structural* decision was mirrored here, not CAVA's *proof*. CAVA's two
layers are connected by an actual refinement theorem (`nested_dfs_impl`/
`nested_dfs_code.refine`); no such theorem was ever ported to this codebase
— `nestedDFSWF`'s correctness is proven by an entirely different route
(fuel-indexed induction, `NestedDFS/NestedDFSCorrectness.lean`) that never needs the
abstract `partial def`s as a proof target. See `NestedDFSRef.lean`'s
docstring for the full explanation of why that's fine, not a gap.

Built: `nestedDFSWF` (plain structural recursion on `initialStates`, no
fuel/measure needed — only its one `outerDFSLoopWF` call per root needs the
already-built well-founded machinery); a `nestedDFS_fuel.go` equation-lemma
family + `nestedDFS_fuel_go_add_preserves` (mirroring the outer bridge's
fuel-monotonicity lemma, same reason: two independent fuel needs sharing one
slot on the "fresh root" branch); the main bridge
`nestedDFS_fuel_go_eq_nestedDFSWF_go` by induction on `remaining` directly
(no `.induct`, no fuel induction — simplest bridge in the file, since
`nestedDFSWF.go` has no well-founded recursion of its own at all); and the
top-level `nestedDFS_fuel_eq_nestedDFSWF`, from which
`nestedDFSWF_empty_no_cycle`/`nestedDFSWF_nonEmpty_valid` fall out for free
by substitution into the existing Phase 5 theorems. See `ProofPlan.md`'s
Phase 2 section for the full write-up. **`NestedDFS/NestedDFSTermination.lean`: 0
sorry, whole project builds clean (394 jobs) — Phase 2's nested-DFS work,
including wiring, is done.** Remaining: `expand`'s own termination
conversion, separately scoped.

**Update (2026-08-07): the "zero proof obligations via runtime
`fr.univ.contains succ` `dite` + defensive fallback" design described above
(2026-07-25 updates) has been superseded.** `FiniteReach` no longer carries a
`Std.HashSet` witness at all (`fr.univ`/`fr.closed` are gone) — it's now a
bare `Prop` existence certificate over a canonical `Reachable` closure
relation, and `innerDFSCore`/`outerDFSLoopWF` thread a new `RFrame` structure
(bundling an erased, per-frame `Reachable` proof) through their stack instead
of the old runtime check. This *does* reintroduce proof-carrying data into
the stack's own element type — the thing the 2026-07-25 updates deliberately
stripped out to keep `rw`/`induction ... using .induct` tractable — but
bundled *per-frame* (via `RFrame`) rather than as a *whole-stack* hypothesis
argument (the shape that failed before), combined with `grind` (immature
enough at the time of the original attempt to not be a reliable fallback)
handling the resulting one-step-unfolding goals that plain `rw`/`simp` still
cannot. See `## FiniteReach strict redesign (Option B)` below and
`FiniteReachRedesign.md` for the full design and findings.

## Schwoon-Esparza back-edge optimization

**Status: ✅ DONE (2026-07-27).** Implemented and fully proven the same day
the roadmap below was written, following it closely — the section below is
kept as the original porting analysis (still accurate as a design
description); this note records what actually landed and where it diverged.

**What changed, concretely:**
- `outerDFSLoop`/`outerDFSLoop_fuel`/`outerDFSLoopWF` (`NestedDFS/NestedDFSRef.lean`,
  `NestedDFS/NestedDFSCorrectness.lean`, `NestedDFS/NestedDFSTermination.lean`) all gained the
  same 3-way split on each successor: back-edge (`pathStack.contains succ`)
  → finished/blue (`outerVisited.contains succ`) → fresh. The back-edge
  branch further splits exactly as CAVA's `se_back_edge` does (source
  accepting → target accepting → neither), reporting `.nonEmpty` directly
  in the first two, matching this project's `loop`/`loop.tail`
  "redundant-duplicate-head" convention (`loop := current :: current ::
  loopTail`, mirroring the existing innerDFS-found case's `current ::
  cyclePath` shape) rather than CAVA's own `pr`/`pl` bookkeeping.
- New reusable list lemmas in `NestedDFS/NestedDFSCorrectness.lean`: `chain_take`,
  `chain_drop`, `chain_append_left`, `chain_append_right`,
  `chain_getLast_edge`, `chain_append_boundary`, `dropWhile_ne_head?_eq_some`,
  `head_eq_getLast_of_length_eq_one` — all proved via structural induction or
  explicit `getElem`-index arithmetic (never raw `rw` on a `List.takeWhile`/
  `dropWhile` value inside an un-introduced `∀`-goal or a `.head`/`.getLast`
  proof-argument position — see "Divergences" below).
- `outerDFSLoop_fuel_outerVisited_mono`, `outerDFSLoop_fuel_reach_closed`,
  `outerDFSLoop_fuel_empty_no_cycle`, `outerDFSLoop_fuel_nonEmpty_witness`
  (`NestedDFS/NestedDFSCorrectness.lean`) and `outerDFSLoop_fuel_eq_outerDFSLoopWF`
  plus its unfolding-lemma family (`NestedDFS/NestedDFSTermination.lean`) all extended
  with the matching new cases.
- Confirmed by *reading the actual proofs*, not just predicting: the
  completeness-direction theorems needed **zero new mathematics** — every
  new case is either a trivial `.nonEmpty ≠ .empty` contradiction or a
  verbatim copy of the existing skip-case reasoning, exactly matching CAVA's
  own trivial `back_edge` case in `i_no_accpt_cyle_in_finish`. All the real
  work is in `outerDFSLoop_fuel_nonEmpty_witness` and the matching terminal
  cases of the `outerDFSLoopWF` bridge, as predicted below.
- `outerDFSLoop_fuel_reach_closed` and `outerDFSLoop_fuel_nonEmpty_witness`
  both needed a new hypothesis (`hsv : ∀ s ∈ pathStack, st.outerVisited
  .contains s`) neither previously carried, threaded through their
  induction the same way `hps`/`hchain`/`hroot` already were — needed to
  derive `outerVisited.contains succ` from `succ ∈ pathStack` (a fact
  `outerDFSLoop_fuel_empty_no_cycle` already had for free via its existing
  `hps` + `OuterInvariant.stack_subset_visited`).

**Divergences from the plan below, found only while implementing:**
- **`set` is a Mathlib tactic** — `NestedDFS/NestedDFSCorrectness.lean`/
  `NestedDFS/NestedDFSTermination.lean` deliberately import only `Std`, not Mathlib
  (see this file's own header note on that boundary), so `set A := ... with
  hA_def` used elsewhere in this codebase (e.g. `Pipeline.lean`) isn't
  available here. Used `generalize hA_def : expr = A at h ⊢` instead (core
  Lean4, same effect) — with the equation in the *opposite* direction
  (`expr = A`, not `A = expr`), the one place that mattered.
  Naming the takeWhile/dropWhile slices via `generalize` (not left as raw
  repeated expressions) turned out to be load-bearing, not just cosmetic:
  `pathStack`'s own later rewrites would otherwise loop back through the
  *unnamed* `pathStack.takeWhile`/`dropWhile` subterms nested inside
  `heqAB`'s statement.
- **`List.getLast?`/`List.head?` (Option-valued) throughout, not
  `.getLast`/`.head` (proof-carrying) directly** — every fact relating a
  `takeWhile`/`dropWhile`/`dropLast` slice's head or last element back to
  `pathStack`'s was built by bridging through the non-dependent `Option`
  form (`List.head_eq_iff_head?_eq_some`, `List.getLast_eq_iff_getLast?
  _eq_some` and friends) and only converting back to `.head`/`.getLast` at
  the very end. Attempting the dependent form directly hits "motive is not
  type correct" — the same class of trap already documented elsewhere in
  this project's history for compiled-match rewriting, here triggered by
  `GetElem`'s implicit bound-proof argument instead.
- The plan below anticipated slicing via `takeWhile`/`dropWhile` with a
  *predicate*; a first attempt at fully generic `chain_takeWhile`/
  `chain_dropWhile` lemmas (proved by induction *on the predicate form
  itself*) hit the same rewrite trap and was abandoned in favor of index-
  based `chain_take`/`chain_drop` (ultimately not even needed once
  `chain_append_left`/`chain_append_right` — proved via `subst` on an
  explicit `l = a ++ b` hypothesis parameter, sidestepping the trap
  entirely — turned out to cover every actual use site). `chain_take`/
  `chain_drop` are kept as general-purpose, tested, reusable lemmas even
  though the final proof didn't end up needing them.
- The degenerate self-loop case (`succ = current`) needed one fix mid-proof:
  `outerDFSLoop_fuel`'s definition originally emitted `loop := [current]`
  for this case, which breaks the `loop`/`loop.tail`-redundant-head
  convention (`loop.tail` would be `[]`, violating `loop.tail.length ≥ 1`).
  Fixed to `loop := [current, current]` before starting the proof work,
  once the convention mismatch was noticed while planning the soundness
  argument — a genuine bug caught by working out the proof obligations
  first, not by the type-checker (the buggy version still type-checked; it
  would have failed a `#eval`/theorem-statement check instead).

The original porting analysis (unchanged, still an accurate design
description of the approach actually taken):

### 0. What CAVA actually bundles under this name

Re-reading Schwoon & Esparza (2005) directly (not just CAVA's code) shows
this is really **two historically separate optimizations**, both wired into
CAVA's actual emptiness check (`CAVA_LTL_Modelchecker_CAVA_Impl.thy:265`'s
`blue_dfs`, not just present in unused theory):

1. **Holzmann, Peled & Yannakakis (1996), "On Nested Depth First Search"**:
   the *inner* (red) DFS stops as soon as it reaches *any* state on the
   *outer* (blue) DFS's call stack — not only the literal seed — since any
   such state is guaranteed to reach the seed via the stack itself. In CAVA
   this is baked directly into `run_red_dfs`'s stop-predicate:
   `red_dfs (red s) (λx. x = u ∨ x ∈ cyan s) u` (`Nested_DFS.thy:71`,
   `cyan s ≡ set (stack s)`) — i.e. it lives *inside* the red search's own
   spec, not in a separate hook.
2. **Gastin, Moro & Zeitoun (2004)**, generalized slightly by **Schwoon &
   Esparza (2005)** themselves: the *outer* (blue) DFS can detect a cycle
   directly on a back-edge to an accepting state on the stack, or (Schwoon–
   Esparza's own generalization) when the *current* state is accepting and
   the edge goes back to *any* stack state — without ever launching the red
   search. This is `se_back_edge`/`on_back_edge` (`Nested_DFS.thy:76-93,
   101`).

**This section only analyzes porting (2)** — the outer-DFS shortcut, since
that's what our docs previously labeled "the Schwoon-Esparza back-edge
optimization" and what was asked about. (1) is a smaller, independent change
confined entirely to `innerDFS`'s stop condition (it would need a stack/cyan
set threaded into `innerDFS`'s signature, which it doesn't currently take at
all); worth flagging as a related follow-up, not analyzed further here.

### 1. Where this hooks into our control flow

CAVA's `param_DFS` framework classifies every edge `(u, v)` the blue DFS
processes into three cases: `discover` (v is white/fresh), `cross_edge` (v
is already finished/blue, not on the stack), `back_edge` (v is discovered
but not finished — i.e. **cyan**, currently on the call stack). `se_back_edge`
is exactly the `on_back_edge` handler for the third case.

Our `outerDFSLoop`/`outerDFSLoop_fuel`/`outerDFSLoopWF` currently only have a
**two-way** split at the successor-processing site:

```lean
| succ :: remainingTail =>
  if st.outerVisited.contains succ then    -- "already visited": skip
    ...
  else                                       -- fresh: push
    ...
```

`outerVisited` conflates CAVA's blue and cyan colors into one set — we never
distinguish "finished, popped off the stack" from "still an ancestor on the
current path." Porting the optimization means turning this into CAVA's
three-way split, by adding a check *before* the existing `outerVisited`
branch (since every cyan state is, by construction, already in
`outerVisited` — it was inserted at push time and never removed):

```lean
| succ :: remainingTail =>
  if succ ∈ pathStack then           -- NEW: back edge (cyan)
    if isAccepting current then      -- CAVA se_back_edge case 1
      (.nonEmpty ..., st)              -- report immediately, no innerDFS
    else if isAccepting succ then    -- CAVA se_back_edge case 2
      (.nonEmpty ..., st)
    else                              -- CAVA's "else NOOP s"
      outerDFSLoop ... stack' pathStack st   -- identical to today's skip case
  else if st.outerVisited.contains succ then  -- existing: finished, skip
    ...
  else                                          -- existing: fresh, push
    ...
```

Detection reuses a field we already thread through the recursion: `pathStack`
*is* CAVA's `rev (stack s)` (root-first list of exactly the states currently
on the outer stack — confirmed by the existing hypothesis
`hps : pathStack = (stack.map Prod.fst).reverse` in
`outerDFSLoop_fuel_nonEmpty_witness`). So `succ ∈ pathStack` is precisely
CAVA's `v ∈ cyan s` — no new state field is *required* for correctness.
(Performance note: `pathStack` is a `List`, so membership is `O(pathStack
.length)` per edge, versus CAVA's `O(1)` stack-bit/hash-table — Schwoon &
Esparza's own paper explicitly flags this cost tradeoff for the 3-bit
encoding. Still a net win, since it replaces an entire redundant inner-DFS
launch, but if the `O(n)` scan ever matters, a separate `cyan :
Std.HashSet State` field mirrored alongside `pathStack` would fix it — pure
performance follow-up, orthogonal to this port.)

### 2. The two constructive sub-cases, translated to our conventions

CAVA's `se_back_edge_lasso_inv` (`Nested_DFS.thy:436-539`) builds the witness
directly from `stack s` slices. Translating this to our `AcceptingCycle`
conventions (`stem`/`cycle` with `overlap : stem.getLast = cycle.head`,
i.e. the loop's entry state is *included* in `stem` too) needs care, because
**CAVA's own `pr`/`pl` convention is different from ours**: `lasso_inv`
(`Nested_DFS.thy:429-434`) only requires `∃v0∈V0. path E v0 pr (hd pl)` —
`pr` does *not* itself end at `hd pl`; there's an implicit extra edge from
`last pr` to `hd pl` supplied separately by the `path` relation. Our
`AcceptingCycle.stem_chain`/`overlap` fields have no such implicit edge —
`stem` must *literally* end where `cycle` begins. So each CAVA formula below
needed its list-slicing boundary shifted by one element to fit our shape,
not just copied.

Recall `current` = the state being finished/whose successors are being
walked, `succ` = the cyan target of the back edge, so `current → succ ∈ E`
is exactly the edge that triggered this branch, always available for free.

**Case 1 — `isAccepting current`** (CAVA: `accpt (hd (stack s))`, source of
the back-edge is accepting). The cycle is `current → succ → ⋯ → parent(current)
→ current` (the last step is the existing tree edge one level up the
stack). In our shape:
```
stem := pathStack                                                  -- unchanged!
loop := current :: (pathStack.dropLast.dropWhile (· ≠ succ))
```
This is the *same output shape* `(.nonEmpty pathStack (current :: X))` as
today's ordinary innerDFS-found case (`outerDFSLoop_fuel` line ~416) — only
`X` differs (sliced from `pathStack` instead of returned by `innerDFS`). That
means it can reuse the exact same `AcceptingCycle` field derivations that
case already has; only the proof that *this* `X` satisfies chain/nonempty/
back-edge facts is new.

**Degenerate case, must special-case explicitly**: if `succ = current` (a
literal self-loop, `current → current ∈ E`), the formula above breaks —
`pathStack.dropLast` excludes `current`, so `dropWhile (· ≠ succ)` over it
never finds `succ = current` at all. CAVA hits exactly this and special-cases
it (`Nested_DFS.thy:473-478`, `case True: ul = [hd (stack s)]`, i.e. cycle :=
`[current]`, a singleton). Our port needs the same explicit `if succ =
current then loop := [current] else loop := current :: ...` split. This also
explains why CAVA checks `accpt (hd (stack s))` *before* `accpt v` in its
`if/else if`: if `succ = current`, `accpt v = accpt succ = accpt current`,
so a self-loop can only ever be handled by Case 1's formula — Case 2's
formula (below) would slice a stack that doesn't even contain a distinguished
occurrence of `succ` past `current` in the right way. **The case-priority
order (current-accepting checked first) must be preserved, not incidental.**

**Case 2 — `isAccepting succ`** (CAVA: `accpt v`, target of the back-edge is
accepting; only reached when Case 1's guard is false, so `succ ≠ current`
here — no degenerate case needed). The cycle is `succ → ⋯ → current → succ`
(closing edge is the triggering back-edge itself):
```
stem := pathStack.takeWhile (· ≠ succ) ++ [succ]     -- CAVA's vr, boundary-shifted
loop := pathStack.dropWhile (· ≠ succ)                -- CAVA's vl, unchanged
```
(CAVA's own `vr := takeWhileNot v (rev (stack s))` excludes `v`; we append
`[succ]` to satisfy our `overlap` convention instead of relying on `path`'s
implicit edge.)

### 3. Blast radius — what needs a new case, and what's trivial

The good news, confirmed by actually reading `outerDFSLoop_fuel_nonEmpty_witness`
and `outerDFSLoop_fuel_empty_no_cycle`'s proofs: **all the genuinely new
mathematical content is confined to the soundness direction.** This mirrors
CAVA's own proof shape exactly — their `back_edge` case in
`i_no_accpt_cyle_in_finish` (the completeness-side invariant) is
`by (simp add: se_back_edge_def split: option.split)`, i.e. trivial, while
`se_back_edge_lasso_inv` (the soundness-side lemma) is the ~100-line one with
real content. Reason it transfers here too: the new branch either (a) returns
`.nonEmpty` immediately with no state mutation, or (b) falls through to
exactly today's existing "skip" behavior when neither state is accepting —
there is no new way to reach `.empty`, so nothing that already proves "empty
⟹ no cycle" needs new reasoning, only a new case to dismiss (by
constructor-mismatch) or copy (by identical behavior).

Three parallel copies currently implement this loop and all three need the
identical structural edit: `NestedDFS/NestedDFSRef.lean`'s `outerDFSLoop` (unverified
reference), `NestedDFS/NestedDFSCorrectness.lean`'s `outerDFSLoop_fuel`, and
`NestedDFS/NestedDFSTermination.lean`'s `outerDFSLoopWF`. Per-theorem effect:

- **`outerDFSLoop_fuel_outerVisited_mono`**: new case needed for any result
  (not just `.empty`). Trivial either way — Case 1/2 don't touch
  `outerVisited` at all (`st` unchanged), the non-accepting fallthrough is
  behaviorally identical to the existing visited-skip case.
- **`outerDFSLoop_fuel_reach_closed`** and the `OuterReachClosed`/
  `OuterInvariant` maintenance blocks inside the big theorems: new case
  needed. Case 1/2 sub-cases contradict the theorem's `= some (.empty n, st')`
  hypothesis outright (return shape mismatch) — dismissed the same way CAVA
  dismisses its `back_edge` case. The non-accepting fallthrough is a literal
  copy of the existing "succ already visited" invariant-maintenance proof
  (same recursive call, same `stack'`, same `st`).
- **`outerDFSLoop_fuel_nonEmpty_witness`**: the one theorem needing real new
  work. Two new sub-cases (Case 1, Case 2 above), each proving the sliced
  `stem`/`loop` satisfy the 8-fact tuple this theorem returns
  (`stem_head_initial`-equivalent, `stem_chain`, `overlap`, `cycle_chain`,
  `cycle_back`, `cycle_head_accepting`, nonemptiness). Built from `hchain`
  (already threaded as an explicit hypothesis at exactly this point in the
  induction) plus two **new small lemmas**, siblings of the existing
  `chain_dropLast`/`chain_append_singleton`/`chain_cons` family (same
  index-arithmetic proof technique, same file):
  - `chain_takeWhile`: a `takeWhile p l` prefix of a chain-list is a chain.
  - `chain_dropWhile`: a `dropWhile p l` suffix of a chain-list is a chain.
- **`outerDFSLoop_fuel_empty_no_cycle`**: new case needed, but *zero* new
  mathematics — Case 1/2 are dismissed by contradiction (can't produce
  `.empty`), non-accepting fallthrough is a verbatim copy of the existing
  visited-skip case's proof.
- **`outerDFSLoopWF`** (`NestedDFS/NestedDFSTermination.lean`): the new branch is an
  immediate return, exactly like the existing "innerDFS found a cycle" leaf
  — measure-trivial, no new termination argument.
- **`outerDFSLoop_fuel_eq_outerDFSLoopWF`** (the fuel↔WF bridge): needs a
  matching new case, but since both sides get the *identical* new branch
  (same condition, same formula), bridging it is mechanical — the same
  pattern every existing case in that bridge already follows.
- **`OutputVerifyBA.lean` (`AcceptingCycle`, `ValidLasso`, `toValidLasso`),
  `Lasso.lean`, `Pipeline.lean`: unaffected.** Confirmed by reading
  `AcceptingCycle`'s definition — its fields are pure facts about the final
  `stem`/`cycle` *values*, with no dependence on how `outerDFSLoop` derived
  them. Whatever theorem currently repackages
  `outerDFSLoop_fuel_nonEmpty_witness`'s 8-tuple into an `AcceptingCycle`
  continues to work unchanged, since the new cases produce the same shape of
  tuple, just via different values. `innerDFS`/`innerDFSWF`/`innerDFSCore`/
  `innerDFS_fuel` are also entirely untouched by this port (this
  optimization is blue-DFS-only; see §0 for the separate red-DFS
  optimization that *would* touch them).

### 4. Net effort shape

Mechanical/copy-paste: the non-accepting fallthrough case, everywhere it
appears (≈5 theorem sites, same pattern each time). Trivial-by-contradiction:
every completeness-direction site's new case (≈3-4 sites). Genuinely new
math: `chain_takeWhile`/`chain_dropWhile` (small, self-contained, same
technique as existing neighbors) plus the two `AcceptingCycle`-shaped
witness derivations in `outerDFSLoop_fuel_nonEmpty_witness` (the real work,
but scoped to one theorem, with the degenerate self-loop case called out
explicitly above so it isn't discovered mid-proof). No changes needed to
`innerDFS*`, `OutputVerifyBA.lean`, `Lasso.lean`, or `Pipeline.lean`.

Not started; no immediate blocker, purely a future enhancement.

## Holzmann-Peled-Yannakakis inner-DFS shortcut

**Status: started (2026-07-28).** The other of CAVA's two nested-DFS
optimizations flagged in §0 above — the inner (red) DFS stopping as soon as
it reaches *any* state on the outer (blue) DFS's call stack, not only the
literal seed. Per standing project practice, CAVA's actual Isabelle sources
(`thys/DFS_Framework/Examples/Nested_DFS.thy`,
`thys/DFS_Framework/Examples/DFS_Find_Path.thy`, fetched from the AFP mirror
and read in full) were read directly before any Lean design work, not
relied on secondhand.

### What CAVA actually does

**The stop predicate** (`Nested_DFS.thy:54,67-74`):
```isabelle
definition "cyan s ≡ set (stack s)"
definition run_red_dfs where
  "run_red_dfs u s ≡ case lasso s of None ⇒ do {
     redS ← red_dfs (red s) (λx. x = u ∨ x ∈ cyan s) u;
     RETURN (mk_blue_witness s redS) } | _ ⇒ NOOP s"
```
`red s` is CAVA's `innerFinished`. The stop predicate `λx. x = u ∨ x ∈ cyan s`
is checked identically to a literal-seed check, just widened — `u` is
trivially already a member of `cyan s` (the whole stack, including its own
top), so CAVA's own predicate is *itself* redundant in exactly the way a
naive Lean port would also be. This directly informed keeping both
disjuncts in the Lean port (`succ == seed || cyan.contains succ`) rather
than "simplifying" to a cyan-only check — matching CAVA, not over-cleaning
it up.

**The core invariant** (`Nested_DFS.thy:155-159`):
```isabelle
definition "blue_basic_invar s ≡
  case lasso s of None ⇒ restr_invar E (red s) (λx. x∈set (stack s)) ∧ red s ⊆ dom (finished s)
  | Some l ⇒ True"
```
where `restr_invar E R P ≡ E `` R ⊆ R ∧ R ∩ Collect P = {}`
(`DFS_Find_Path.thy:222-226`). This is *stronger* than what the pre-HPY Lean
proof establishes: it says `innerFinished` is simultaneously closed under
`succs` **and** disjoint from the *entire current stack*, not just from the
one seed that launched the most recent red search. `blue_basic_invar` is
proved as a genuine DFS-wide invariant via `is_invar`/`establish_invarI`
(structural induction over the whole execution trace) — CAVA proves this
**once**, persistently, rather than re-deriving "avoid the whole stack"
after each individual finish step.

**Where this mattered against our pre-existing proof**:
`outerDFSLoop_fuel_empty_no_cycle`'s accepting-leaf case composed *two
separately-derived* facts — `innerDFS_no_cycle_from_seed_finished`
(self-loop-only) plus a *separate* `ReachChain`-based argument for "can't
reach any *other* stack ancestor either" — glued together after the
inner-DFS call returned. CAVA's single `restr_invar E R' (λx. x∈set(stack
s))` postcondition gives **both facts at once**, directly from the widened
red-DFS's own postcondition, with no separate gluing step. The Lean port's
whole point is to let the widened inner-DFS fact absorb that separate
`ReachChain` composition, mirroring CAVA's actual (simpler) structure
rather than only its performance behavior.

**The witness construction** (`mk_blue_witness`, `Nested_DFS.thy:59-65`, and
`find_path1_restr_pred`'s `Inr` clause, `DFS_Find_Path.thy:336-339`):
```isabelle
definition "find_path1_restr_pred G P R ≡ λr. case r of
    Inl R' ⇒ R' = R ∪ E⁺``V0 ∧ restr_invar E R' P
  | Inr (vs,v) ⇒ P v ∧ vs≠[] ∧ (∃v0∈V0. path (E∩UNIV×-R) v0 vs v)"
definition mk_blue_witness s redS ≡ case redS of
    Inl R' ⇒ ⟨lasso=None, red=R'⟩
  | Inr (vs,v) ⇒ let rs = rev(stack s) in ⟨lasso = Some (rs, vs @ dropWhileNot v rs), red=red s⟩
```
When the red search finds a path, it returns the pair `(vs, v)` — the path
found *and* which cyan state `v` it actually hit (previously always `v =
u`; now can be any stack ancestor). The witness splices `vs` (path from `u`
to `v`) with `dropWhileNot v rs` (the stack suffix from `v` back down to
`u`) to close the cycle. This is structurally the same slicing pattern
already implemented for the Schwoon-Esparza back-edge port's "target
accepting" case above (`stem := pathStack.takeWhile (·≠succ) ++ [succ]` /
`loop := succ :: pathStack.dropWhile (·≠succ)`), so it reuses the same
already-proven helper lemmas (`chain_append_boundary`, `chain_getLast_edge`,
`dropWhile_ne_head?_eq_some`) rather than needing new ones. One genuine
simplification versus the SE port: HPY's branch is *only ever entered when
`current` is already known accepting* (`on_finish = if accpt u then
run_red_dfs u s else NOOP`, mirroring our own `outerDFSLoop`'s `if
isAccepting current then ... innerDFS ...`), so unlike SE's back-edge case
there is **no accepting-source-vs-accepting-target case split** — the
witness's accepting state is always `current` itself.

**Why this is sound**: any cyan (stack) state is, by construction, an
ancestor of the currently-finishing node in the DFS tree — the tree-path
down the stack is itself an already-existing witness that a cyan state can
reach the seed. So stopping red DFS the moment it touches *any* stack
state, not just literally re-finding the seed, cannot miss a genuine cycle:
whatever cyan state got hit, the existing stack-tree path already provides
the closing segment back to the seed — exactly what the already-built
`ReachChain`/`pathStack`-chain machinery (from the SE port) supplies.

### Design decisions for the Lean port

1. **New parameter `cyan : List State`**, distinct from `innerDFSCore`'s own
   pre-existing internal `pathStack` (its search-path-so-far bookkeeping
   from its explicit-stack redesign — a different concept). Passed through
   unchanged across the whole inner-DFS call, mirroring `seed`'s existing
   threading exactly (the outer stack never changes while the inner search
   runs). `outerDFSLoop`/`outerDFSLoop_fuel`/`outerDFSLoopWF` pass their own
   already-in-scope `pathStack` as this argument.
2. **Keep `seed` and check `succ == seed || cyan.contains succ`** (not
   cyan-only) — matches CAVA's own literal, redundant-looking predicate; see
   above.
3. **The "found" result changes from `Option (List State)` to `Option (List
   State × State)`** — path plus *which* state was actually hit (CAVA's
   `Inr (vs, v)`). A real, if mechanical, change to every "found"-result
   pattern-match site, more invasive than a pure parameter addition — flagged
   explicitly since today's code implicitly always assumes the hit target is
   `seed` and simply discards this information.
4. **No new termination argument.** The widened stop-check is one more
   early-return guard at the same site as the existing `succ == seed` check
   — same recursive/measure structure throughout, so `innerDFSCore`'s/
   `innerDFS_fuel_fold`'s termination proofs need no new argument.

### Theorem-by-theorem plan (CAVA lemma to check before each)

File order: `NestedDFS/NestedDFSRef.lean` → `NestedDFS/NestedDFSCorrectness.lean` →
`NestedDFS/NestedDFSTermination.lean`, matching the SE port's own sequencing.

- `NestedDFS/NestedDFSRef.lean`: `innerDFS` gains `cyan`, widened stop check, pair
  return; `outerDFSLoop`'s call site passes `pathStack` as `cyan` and
  consumes the pair, generalizing `loop := current :: cyclePath` to the
  target-aware slicing (checked to specialize back to today's exact formula
  when `target = current`).
- `NestedDFS/NestedDFSCorrectness.lean`, mechanical signature propagation only (no new
  CAVA content beyond confirming shape): `innerDFS_fuel_mono`,
  `innerDFS_fuel_fold_mono`, `innerDFS_fuel_current_blocked`,
  `innerDFS_fuel_fold_adds_current`, `innerDFS_fuel_iv_subset_finished`,
  `innerDFS_fuel_new_finished_subset_iv`, `innerDFS_fuel_outerVisited_eq`.
- **Genuine strengthening** (check `restr_invar`/`blue_basic_invar`,
  `Nested_DFS.thy:155-159`, first): `innerDFS_fuel_fold_succs_blocked` and
  `innerDFS_no_cycle_from_seed`/`innerDFS_no_cycle_from_seed_finished` —
  conclusion generalizes from "seed unreachable from itself" to "no `cyan`
  member is reachable."
- `innerDFS_fuel_new_no_edge_to_seed` generalizes to "no edge to any `cyan`
  member" (check `i_no_accpt_cyle_in_finish`'s use of this fact first,
  `Nested_DFS.thy:355-418`).
- `innerDFS_fuel_cyclePath_chain`: must additionally expose/relate to the
  hit target (check `find_path1_restr_pred`'s `Inr` clause,
  `DFS_Find_Path.thy:336-339`, first).
- `outerDFSLoop_fuel`'s call site + `outerDFSLoop_fuel_nonEmpty_witness`:
  check `mk_blue_witness`'s `Inr` branch (`Nested_DFS.thy:64-65`) before
  writing the new target≠current sub-case; reuse
  `chain_append_boundary`/`chain_getLast_edge`/`dropWhile_ne_head?_eq_some`.
- `outerDFSLoop_fuel_empty_no_cycle`: check `i_no_accpt_cyle_in_finish`
  (`Nested_DFS.thy:355-418`) first; attempt to simplify by dropping the
  separate `ReachChain`-based composition once the widened inner-DFS fact is
  available.
- `outerDFSLoop_fuel_outerVisited_mono`/`outerDFSLoop_fuel_reach_closed`:
  mechanical, reuse `innerDFS_fuel_outerVisited_eq`.
- `NestedDFS/NestedDFSTermination.lean`: `innerDFSCore`/`innerDFSWF` gain `cyan`
  (careful not to collide with `innerDFSCore`'s own existing internal
  `pathStack`), widened stop check, pair-return; `outerDFSLoopWF` passes
  `pathStack` as `cyan` and mirrors the outer-loop consumption change; the
  fuel↔WF bridges (`innerDFS_fuel_chain`, `innerDFS_fuel_chain_eq_innerDFSCore`,
  `innerDFS_fuel_eq_innerDFSWF`, outer analogues) thread `cyan` through
  symmetrically — expected mechanical given the identical stop-check shape
  on both sides. No new termination/measure work expected.

### Status: ✅ DONE (2026-07-28)

Implemented across all three files following the plan above closely; whole
project builds clean (759 jobs, 0 sorry, 0 new warnings — the one
pre-existing `unused variable ac` warning in `NestedDFS/NestedDFSCorrectness.lean`
predates this work, confirmed via `git stash`). Findings worth recording,
where reality diverged from or refined the plan:

- **No degenerate case needed, unlike the SE port.** The uniform witness
  formula `current :: cyclePath ++ (pathStack.dropWhile (·≠target)).dropLast`
  collapses to exactly the pre-HPY `current :: cyclePath` formula when
  `target = current`, verified algebraically before implementing (the
  appended slice becomes `(pathStack.dropWhile (·≠current)).dropLast =
  [current].dropLast = []`, since `current` is `pathStack`'s own last
  element at the call site) — confirmed correct once proved. This is
  *simpler* than the Schwoon-Esparza back-edge port, which needed an explicit
  `succ = current` split; here the same `cyclePath0 ++ B.dropLast` shape
  handles both sub-cases uniformly, because `cyclePath` (from `innerDFS`)
  already carries the "path to the target" information as real data, unlike
  SE's direct one-hop edge which had nothing to fall back on but list
  slicing.
- **The `ReachChain` simplification happened, exactly as predicted.**
  `outerDFSLoop_fuel_empty_no_cycle`'s `hno_stack_reach` — previously
  composed from a self-loop-only fact (`hno_unrestricted`) plus a separate
  `ReachChain.reaches_head` argument — is now derived directly from a single
  generalized fact (`hno_unrestricted_all`/`hno_restricted_all`, both stated
  `∀ t, (t = current ∨ t ∈ pathStack) → ...`) via a new small lemma,
  `PathTo.no_reach_of_closed_no_incoming` (generalizes the existing
  `no_self_loop_of_closed_no_incoming` from a fixed self-loop target to an
  arbitrary one — a one-line proof, since the underlying
  `avoids_closed_of_no_incoming` was already fully general). The
  `ReachChain`-based derivation is gone from this theorem's proof entirely.
- **One genuinely new lemma needed beyond the plan's prediction:**
  `chain_append` (concatenating two `succs`-chains given a boundary edge) —
  the plan anticipated reusing `chain_append_boundary`/`chain_getLast_edge`
  alone, but the general (non-degenerate) witness case needed the *whole*
  spliced list's chain property, not just the boundary edge. Proved by
  induction on the first list (not raw index arithmetic like its siblings)
  specifically to avoid a dependent-rewrite trap when the second list's
  index shifts to `0` — the same class of issue this file's history already
  flags for `getElem`/`head`/`getLast` proof-argument positions.
- **The return-type change (`Option (List State)` → `Option (List State ×
  State)`) was exactly as invasive as flagged**, touching every "found"-case
  pattern match across both files — mechanical per site, but pervasive
  (roughly a dozen sites in `NestedDFS/NestedDFSCorrectness.lean`, another dozen in
  `NestedDFS/NestedDFSTermination.lean`'s fuel-bridge section).
- **`by_cases`/`simp [hse]` on the widened `succ == seed || cyan.contains
  succ` condition was less reliable than the plan assumed** for the simple
  mechanical-propagation theorems — `simp [hse] at h` (which worked fine for
  the old single-`==` condition) intermittently left unresolved goals or hit
  "no progress" against the compound `||` condition. Fixed by switching to
  `split at h` (letting Lean's own case-splitting introduce the right
  hypothesis form) rather than manually asserting the boolean equation via
  `by_cases`, and by deriving the needed `≠`/`∉` facts through `simp_all`
  (robust to whichever exact syntactic form `split` produces) rather than
  through targeted `Bool.or_eq_false_iff`-style rewriting (fragile to the
  same class of mismatch).
- **Mechanical parameter-threading was done via scoped `sed`**, not
  per-theorem manual edits: `succs seed ` → `succs seed cyan `/`succs fr
  seed ` → `succs fr seed cyan ` across each section's line range, plus
  `Option (List State)` → `Option (List State × State)`. This worked
  cleanly once broadened to catch *every* call site (including calls to
  sibling helper theorems, not just to `innerDFS_fuel`/`innerDFS_fuel_fold`
  themselves) in a single pass — an initial narrower pass (matching only
  literal `innerDFS_fuel succs seed fuel`-shaped calls) missed the many
  calls using induction-bound fuel variables (`n`, `k + 1`, ...) instead of
  the literal identifier `fuel`.
- `ROADMAP.md`'s "Known non-goals" entry for this item updated to done.

## FiniteReach strict redesign (Option B)

**Status: ✅ DONE (2026-08-07).** Full design record and findings in
`FiniteReachRedesign.md` (especially §8/§8.6.1) — this section is a short
pointer plus the parts most relevant to *this* file's own history, since it
directly reverses a design call made earlier in the `## Status update` log
above (2026-07-25).

**What changed.** `FiniteReach` used to be a structure carrying a real
`Std.HashSet` "universe" witness (`fr.univ`, `fr.closed`), and
`innerDFSCore`/`outerDFSLoopWF` checked `fr.univ.contains succ` at runtime
via a `dite` with a defensive dead-fallback branch — chosen specifically so
neither function's *type* carried proof obligations (see the 2026-07-25
entries above). `FiniteReach` is now a bare `Prop`, no data at all
(`{s | Reachable initialStates succs s}.Finite`, over a new canonical
inductive `Reachable` closure relation in `EmptinessCheck.lean`), and the
runtime check is gone entirely — `innerDFSCore`/`outerDFSLoopWF` now thread a
new `RFrame` structure through their explicit stack, bundling each frame's
own erased `Reachable`/suffix proof, so a fresh successor's reachability
comes from `Reachable.step` at zero runtime cost. This matches CAVA's own
`fb_graph`/`ASSERT`-once discipline literally, not just in spirit.

**Why the earlier "strip proof obligations" call didn't block this.** The
2026-07-25 finding was that threading `fr.univ`-membership facts as
*explicit, whole-stack-quantified* hypothesis arguments made `rw`/
`induction ... using .induct` fragile. `RFrame` sidesteps that specific
failure mode by bundling the proof *per stack frame* (in the element type)
rather than as a separate whole-stack hypothesis — Lean's definitional proof
irrelevance means no `rw`/`.induct` call ever needs to know *which* proof
populates an `RFrame`'s `hreach` field. This was validated in isolation
first, via a standalone toy spike, before touching the real ~2000-line file
(`FiniteReachRedesign.md` §8.6).

**The other key finding, useful for any future well-founded-recursion work
in this codebase**: plain `rw [<fn>.eq_def]` and blanket `simp [<fn>, ...]`
both fail (the former leaves the nested match/if unresolved even given the
pinning hypothesis; the latter loops) on the one-step-unfolding goals this
kind of proof-carrying-argument threading produces. `rw [<fn>.eq_2]; grind`
does not — `Lean` only ever splits a well-founded def's auto-generated
equation lemmas at its own *outermost* recursion-justifying match (so
`explore.eq_2`/`innerDFSCore.eq_2` covers the entire `frame :: rest` case,
nested `match`/`if`s and all, unsplit), and `grind` reliably resolves what's
left using whatever case-specific hypotheses (`hrem`, `hse`, `hblocked`,
`heq`, …) are already in scope. This is the concrete, mechanical reason this
attempt succeeded where the 2026-07-25 one didn't: `grind`'s current
maturity, not a cleverer proof shape.

**Downstream**: `Product.lean`'s `hashSetProd` (a genuine `Std.HashSet`
cross-product materialization) is deleted outright; `BA.finiteReach`/
`Product.finiteReach` are now pure existence proofs, never surfacing
`FiniteReach`-derived data. `ModelCheck.lean`/`Pipeline.lean` got signature
updates (`initialStates` now precedes the `FiniteReach`/`fr` argument
everywhere, since `FiniteReach`'s type depends on it). Both Schwoon-Esparza
and Holzmann-Peled-Yannakakis optimizations (below) are untouched in logic —
only mechanically re-threaded onto `RFrame`; if you're reading those
sections' code snippets, mentally substitute `RFrame`-typed stack elements
for the bare `(State, List State)` pairs they were written against. Full
project `lake build` clean, zero `sorry`; both example programs verified to
still produce correct model-checking results after the rewrite.

## Where this fits now (2026-07-27)

`nestedDFSWF` (the total, well-founded entry point this file tracks the
construction of) is now composed, alongside the rest of the LTL-to-GBA
pipeline, into `Pipeline.lean`'s `fullPipeline` — a single total function
with an unconditional end-to-end satisfiability-decision correctness
guarantee. See `README.md`/`ProofPlan.md`'s "Track B" section for the
composition and the two extra pieces that assembly needed (a
`numAcceptSets = 0` case and a pumping lemma connecting accepting runs to
accepting cycles) beyond what's recorded in this file. This file remains
an accurate record of the nested-DFS termination/wiring work itself.
