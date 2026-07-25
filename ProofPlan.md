# LTLLib Proof Porting Plan

This document outlines the plan for porting correctness proofs from the Isabelle/HOL [LTL_to_GBA](https://www.isa-afp.org/entries/LTL_to_GBA.html) formalization to Lean 4.

## Current state

- **Build integrity**: `LTLLib.lean` now imports all 23 source files (previously only 13 — see
  "Build-integrity fix" note under Phase 6 below for what that was hiding). A clean rebuild (stale
  `.lake/build` artifacts removed first) succeeds with 0 errors, 0 sorry, 394 build jobs.
- **Phase 2 (Termination) is substantially done for nested DFS**: both `innerDFS` and `outerDFSLoop`
  are now genuinely well-founded-recursive (`innerDFSWF`/`innerDFSCore` and `outerDFSLoopWF`,
  `NestedDFSTermination.lean`, 0 sorry, 0 warnings, 2026-07-25) — converted as two **independent**
  single-measure recursions (not mutual), exactly matching CAVA's own blue/red DFS structure once the
  actual AFP sources were read. `expand`'s termination is not yet done, and the fuel-bridge step
  (transporting `NestedDFSCorrectness.lean`'s ~2000 sorry-free lines from the fuel-based functions
  onto these real ones) hasn't started either — see Phase 2's write-up below for the detailed design,
  the fuel-based attempt that was tried and abandoned, the CAVA-verified corrected plan, and both
  conversions' own write-ups for the measure-choice correction and a Lean functional-induction-
  principle limitation found while implementing them.
- Phases 1 (Semantics), D (Degeneralization), 4.1 (Soundness), 4.2 (Completeness) are **DONE** — sorry-free
- **Phase 4.3 (GraphComplete) is now fully DONE** — `GraphComplete.lean` is entirely sorry-free, and
  `expandOASpec_completeness_weak` is a **fully unconditional completeness theorem** (no longer
  gated behind an assumed `GraphComplete`/`WeakGraphComplete` hypothesis)
- **Phase 3 (Invariants) is now fully DONE** — `mergeIncoming_incoming`'s
  remaining gap closed via `Std.HashSet.contains_union` (a `@[simp]` library
  lemma giving `(m₁ ∪ m₂).contains k = (m₁.contains k || m₂.contains k)`,
  requiring only `[EquivBEq α] [LawfulHashable α]`, trivially satisfied by
  `Nat`); no hand-rolled fold characterization needed after all
- **constructGBA bridge** completed — computational GBA ↔ abstract automaton (Bridge.lean, ~777 lines)
- **degeneralize bridge** completed — computational BA ↔ proof-level degeneralization (DegeneralBridge.lean, ~429 lines)
- **FSet abstraction** completed — abstract finite set typeclass with HashSet/TreeSet instances
- **2** `partial` functions remain: `innerDFS` and `outerDFSLoop` (NestedDFS.lean)
- `expand` uses `partial_fixpoint` (provides equational rewriting + `partial_correctness` induction)
- **Phase 5 (Nested DFS Correctness) is now fully DONE, both directions** —
  `NestedDFSCorrectness.lean` is sorry-free and unconditionally proves both
  `.empty` result ⟹ no accepting cycle exists (`nestedDFS_fuel_empty_no_cycle`,
  Phase 5b) and `.nonEmpty stem loop` result ⟹ `(stem, loop.tail)` is a
  genuine accepting cycle (`nestedDFS_fuel_nonEmpty_valid`, Phase 5c). The
  fuel-based nested DFS is a fully verified decision procedure (modulo
  Phase 2's not-yet-proved termination/finiteness). `OutputVerify.lean`'s
  `ba_hasAcceptingRun_of_lasso`/`ba_hasAcceptingRun_of_ndfs_output` remain
  unwired (they take the chain facts as hypotheses rather than deriving them
  from a real run) — connecting them to `nestedDFS_fuel_nonEmpty_valid` for a
  BA-level semantic conclusion is optional follow-up work, not required for
  Phase 5c's stated goal (a genuine `AcceptingCycle` witness).
- **Phase 6 (End-to-end pipeline, GBA-level scope) is now DONE** —
  `constructGBA_correct_weak` (`GraphComplete.lean`) matches Isabelle's
  `create_name_gba_correct` accept-iff clause: `createGraph φ = some st → ∀
  ξ, (constructGBA φ st).toSpec.accepts ξ ↔ ξ ⊨ φ`, now fully unconditional.
  A broader "runnable `nestedDFS_fuel`-based decision procedure" (GBA →
  degeneralize → BA → nestedDFS) was explicitly scoped out — see Phase 6's
  write-up for what that would still need.
- **0** `sorry` total in the whole codebase — **fully sorry-free**,
  **0** warnings, **~10034 lines**

**Build-integrity fix (2026-07-24)**: discovered that `LTLLib.lean` (the
library root) only transitively imported 13 of 23 `.lean` files — everything
from Phase 3 onward (`Invariants.lean`, `Soundness.lean`, `Completeness.lean`,
`GraphComplete.lean`, `Bridge.lean`, `DegeneralBridge.lean`, `Lasso.lean`,
`OutputVerify.lean`, `NestedDFSCorrectness.lean`) was **never actually checked
by `lake build`** — `.lake/build/lib/lean/LTLLib/` only had 6 `.olean` files on
disk. `lake build`'s "success" and the sorry-grep were both true but vacuous
for that majority of the codebase. Standalone `lake env lean <file>` checks
(bypassing the build cache) confirmed every orphaned file compiles clean
**except** `NestedDFSCorrectness.lean`, which had a real error: in
`fold_cyclePath_chain_aux`'s cons-case (Phase 5c), `simp only [hse, if_false]
at h` silently failed to collapse `if (succ == seed) then _ else _` (wrong
simp lemma for a `Prop`-decidable `ite`, not the `Bool.cond` form `if_false`
matches), leaving a stale `if` wrapping the match whose branches then produced
unreachable/misnamed pattern variables (`iv_mid`/`st_mid`/`heq2` reported as
"unknown identifier" a few lines later — a parsing-adjacent symptom of the
same class of compiled-match fragility already documented in Phase 4.3's
gotchas, just triggered via a different mechanism this time: a dead `if`, not
a dead `match` arm). Fixed by replacing `simp only [hse, if_false] at h` +
`generalize hm : ... = r at h; match r, h with ...` with `rw [if_neg hse] at
h` + a direct `rcases hres : innerDFS_fuel ... with _ | ⟨cp, iv_mid,
st_mid⟩` (nesting a second `rcases cp with _ | cyclePath0`) — no change to the
underlying mathematical argument, purely a Lean-tactics fix. `LTLLib.lean` now
imports all 23 files; a clean rebuild (`.lake/build` artifacts removed first)
succeeds with 0 errors, 0 sorry, 394 build jobs (up from 384).

## What the Isabelle formalization proves

The top-level correctness theorem is **language equivalence**:

```isabelle
theorem create_name_gba_correct:
  "create_name_gba φ ≤ SPEC(λ𝔄. gba 𝔄 ∧ finite (g_V 𝔄) ∧
    (∀ξ. gba.accept 𝔄 ξ ↔ ξ ⊨ᵣ φ))"
```

The generated GBA accepts exactly the ω-words satisfying the LTL formula. This decomposes into:

- **Soundness (L4_9)**: If the GBA has an accepting run labeled by ξ, then `ξ ⊨ φ`. ✅ DONE
- **Completeness (L4_10)**: If `ξ ⊨ φ`, then there exists an accepting run of the GBA labeled by ξ. ✅ DONE, unconditionally (`expandOASpec_completeness_weak`)
- **Termination**: `expand` always terminates (well-founded recursion). Not started
- **Finiteness**: The generated state space is finite. Not started

---

## Completed proof phases

### Phase 1: Semantic foundations ✅ DONE

**File**: `LTLLib/LTL/Semantics.lean` (~152 lines, 0 sorry)

- `OmegaWord`, `tla_release`, `NNF.toPred`, `NNF.satisfies`
- `NNF.neg_correct`, `Formula.toNNF_correct`, `Formula.directSatisfies_eq_satisfies`

### Phase D: Degeneralization correctness ✅ DONE

**File**: `LTLLib/Acceptance.lean` (~359 lines, 0 sorry)

- `OASpec` (unified automaton spec with k acceptance sets)
- `degeneralize_correct`: degeneralized BA accepts ↔ GBA accepts
- `GBA.toSpec`, `BA.toSpec`: computational-to-proof-level bridges

### Phase 3: Structural invariants — ✅ DONE

**File**: `LTLLib/LTLtoGBA/Invariants.lean` (~1803 lines), 0 sorry. The
formerly-open `mergeIncoming_incoming` case split closed with
`Std.HashSet.contains_union` (`(m₁ ∪ m₂).contains k = (m₁.contains k ||
m₂.contains k)`, needs only `[EquivBEq α] [LawfulHashable α]`) plus `simp`
using the two `contains = false` hypotheses already in scope — no hand-rolled
fold/insertMany characterization needed, the library lemma existed already.

- `ExpandSpec` — 11 invariant properties
- `createGraph_spec`: `createGraph φ = some st → ExpandSpec φ st`
- Uses `expand.partial_correctness` (no termination proof needed)

### Phase 4.1: Soundness ✅ DONE

**File**: `LTLLib/LTLtoGBA/Soundness.lean` (~369 lines, 0 sorry)

- `old_implies_satisfied` (L4_8): ψ ∈ old(σ n) → ξ.drop(n) ⊨ ψ
- `expandOASpec_soundness`: expandOASpec accepts ξ → ξ ⊨ φ

### Phase 4.2: Completeness ✅ DONE (modulo GraphComplete)

**File**: `LTLLib/LTLtoGBA/Completeness.lean` (~164 lines, 0 sorry)

- `GraphComplete`: abstract completeness hypothesis
- `expandOASpec_completeness`: GraphComplete + ξ ⊨ φ → expandOASpec accepts ξ
- `expandOASpec_correct`: accepts ξ ↔ ξ ⊨ φ

### constructGBA bridge ✅ DONE

**File**: `LTLLib/LTLtoGBA/Bridge.lean` (~777 lines, 0 sorry)

- `constructGBA_iff_expandOASpec`: computational GBA ↔ abstract automaton
- HashMap fold reasoning for all GBA construction steps

### degeneralize bridge ✅ DONE

**File**: `LTLLib/DegeneralBridge.lean` (~429 lines, 0 sorry)

- `degeneralize_bridge`: `BA.toSpec.accepts ξ ↔ OASpec.degeneralize.accepts ξ`
- Double fold reasoning (outer over states, inner over counter values)

### Phase 4.3: GraphComplete from createGraph ✅ DONE

**Goal**: Prove `GraphComplete φ st.toNodes` from `createGraph φ = some st` — i.e. show
the expand algorithm is exhaustive: for every satisfiable "type" (consistent set of
subformulas), the algorithm generates a matching node.

**File**: `LTLLib/LTLtoGBA/GraphComplete.lean` (~1613 lines, 0 sorry). Ends in
`expandOASpec_completeness_weak`: a fully unconditional completeness theorem (uses
`WeakGraphComplete`, a slightly weaker but sufficient variant of `GraphComplete` that
doesn't need the `old ↔` reverse direction — see `Completeness.lean` vs this file's
`expandOASpec_completeness_weak`/`expandOASpec_completeness`).

- `expand_exist_aux` (Theorem 1, ports Isabelle's `expand_prop_exist`): if all formulas
  in a node are satisfied by ξ, the output contains a finished node also satisfying ξ.
- `expand_all` (Theorem 3, ports Isabelle's `expand_prop_all`): every semantically-valid
  finished node has a semantically-valid successor at `ξ.drop 1`. This is the theorem
  that actually drives graph completeness, and it needed a structurally different proof
  strategy from Theorem 1 — see below.

**Quirks worth knowing before touching this file again**:
1. The compiled `if`/`matches` chain in `expand`'s body doesn't `split` cleanly
   one-branch-per-case — each `split at h_result` call can surface a spurious dead
   branch first (hypothesis literally `false = true`, an artifact of how the nested
   pattern match is compiled) before reaching the real branch; dismissed with
   `exact absurd h (by decide)`. Once a hypothesis like `h_nottt : node.new.head! = tt →
   False` is already in scope from an *outer* level, a fresh `split` at a *deeper* level
   can also land on a genuinely-live "wrong branch" goal (not a compiler artifact) whose
   only closing move is `exact absurd <the-outer-equation> h` — don't reach for
   `by decide` reflexively; check whether the branch is truly dead first.
2. `until` cannot be used as a bare `cases ... with | until μ η => ...` alternative
   name — some dependency (likely Mathlib/Aesop) registers it as a reserved token,
   giving a confusing "unexpected token" error. Escape it with guillemets:
   `| «until» μ η => ...`.
3. Passing `ExpandAssmExist`/`ExpandRsltExistProp`/`ExpandAssmExist` values across a
   record that differs *only* in one field (e.g. a renamed node, `name := nm1`) is NOT
   accepted by `apply`/`exact` via defeq, even though the structure in question never
   inspects that field. Every field must be manually re-projected into a fresh
   anonymous-constructor value (`⟨h.new_sat, h.old_sat, ...⟩`) — bare term reuse fails
   with a confusing "Application type mismatch" pointing at an unrelated hypothesis.
4. **`expand_all`'s proof needed a genuinely different trick from `expand_exist_aux`**:
   `expand.partial_correctness`'s induction only ever hands you an `expand_ih`-typed
   equation for recursive sub-calls (a bound placeholder standing in for "the recursive
   call"), which cannot be fed to already-proven lemmas about the *real* `expand`
   (`expand_exist`, `expand_nodesPreservedInc`, `expand_key_eq_name`) — those need a
   genuine `expand node st = some r`. Isabelle sidesteps this because its refinement
   framework hands every recursive step an explicit `f x ≤ expand x` monotonicity fact
   (`f_sup`) it can compose via `order_trans`; Lean's `partial_fixpoint`-generated
   induction doesn't expose an equivalent. The fix: bundle `expand node st = some r`
   itself as an extra conjunct in the induction's own motive (alongside the desired
   property), proven generically by mirroring `h_result`'s own case split. Once that's
   available via `ih`, the already-proven external lemmas can be invoked freely on
   recursive sub-calls, exactly like Isabelle's `order_trans` composition.
5. `expand_key_eq_name` (new lemma, key-equals-`.name` structural invariant) was needed
   because `expand_all`'s hypothesis was changed from `h_name_ident` (injectivity of
   `.name` among stored nodes) to the stronger, purely structural `h_key_eq : ∀ k n,
   st.nodes[k]? = some n → n.name = k` — the former isn't preserved by insertion without
   knowing a fresh key doesn't collide with some *other* key's stored `.name`, which is
   exactly what `h_key_eq` (trivial to establish, since every insertion in `Expand.lean`
   uses `<value>.name` as the key) gives for free.

### Phase 5: Nested DFS Correctness — ✅ DONE (5b and 5c both complete)

**Goal**: Prove that `nestedDFS` correctly decides emptiness — i.e. match CAVA's
`blue_dfs_correct`, which proves **both** directions in one theorem: `None ⟹ no
accepting cycle` (completeness), and `Some(pr,pl) ⟹ pr/pl are a genuine witness`
(soundness).

**Correction (2026-07-24)**: this section previously claimed "both directions...
are unconditionally proved," which was **wrong**. Re-checking against CAVA's
`blue_dfs_correct` (which proves both cases of its `case lasso s of ...` in one
shot) surfaced that only the completeness direction (Phase 5b, `.empty` ⟹ no
cycle) is actually unconditional in our codebase. The soundness direction
(`.nonEmpty` ⟹ genuine cycle) only exists as the *conditional* lemmas in
`OutputVerify.lean` (`ba_hasAcceptingRun_of_lasso` /
`ba_hasAcceptingRun_of_ndfs_output`): "**if** the reported `stem`/`loop` satisfy
these chain/overlap/back-edge facts, **then** they witness a real accepting run."
Nothing in the codebase proves the algorithm's actual `.nonEmpty` output always
satisfies those hypotheses — `grep -rln` confirms these two theorems are not
called anywhere else in `LTLLib/`. (Their hypothesis shapes were re-checked and
are *not* buggy — `loop[1]` correctly denotes the seed's duplicate, matching
`current :: cyclePath` where `cyclePath` itself already starts at the seed — so
no fix is needed there, just the missing linking proof.) This gap is now tracked
as **Phase 5c** below.

**Phase 5a (output verification, conditional lemmas) — DONE, but not yet wired up**:
- `LTLLib/Lasso.lean` (~232 lines): Abstract lasso theory — `ValidLasso` structure, `lassoRun` construction, proofs that valid lassos yield accepting runs
- `LTLLib/OutputVerify.lean` (~97 lines): Bridge from computational checks to `ValidLasso`, connecting nestedDFS output format to the abstract theory. Both theorems here take the chain/overlap/back-edge facts as *hypotheses*; Phase 5c's job is to discharge those hypotheses from the real algorithm run.

**Phase 5b (emptiness completeness) — ✅ DONE**:

**File**: `LTLLib/NestedDFSCorrectness.lean` (~2013 lines), **0 sorries** —
fully sorry-free. Both `outerDFSLoop_fuel_empty_no_cycle` and the top-level
`nestedDFS_fuel_empty_no_cycle` are proved unconditionally.

**Why this matters**: this is the direction that makes a "no counterexample found"
(PASS) result trustworthy, as opposed to Phase 5a which only certifies that a
reported counterexample is real. With both directions done, the fuel-based
nested DFS emptiness check is now a **fully verified decision procedure**
(modulo the not-yet-proved termination/finiteness, Phase 2 below).

**Isabelle source studied**: AFP `DFS_Framework` (Lammich), specifically
`Nested_DFS.thy` (the `BlueDFS`/`red_dfs` development), plus supporting theory
`DFS_Find_Path.thy` (`restr_invar`, `find_path1_restr_spec`) and `Param_DFS.thy`
(`discovered_closed`, `nc_finished_eq_reachable`). Key realization: the correctness
argument is **not** a "who finishes last on the cycle" post-order argument (that
was our first, incorrect guess) — it's a local closedness argument, re-derived
fresh at each `finish` event, that never needs to reason about other cycle states
at all. This is considerably simpler to port than initially feared.

**The CAVA mechanism**:
1. `restr_invar E R P ≡ E``R ⊆ R ∧ R ∩ P = {}` — the inner "find path" search
   returns a set that is closed under the graph relation *by construction* (it's
   literally the forward-reachable set from the search root).
2. `closed_restrict_aux`/`rel_restrict_tranclI`: if a search restricted to avoid
   set `R` (closed, and not containing the search root) finds no path back to the
   root, then *no unrestricted path exists either* — because any unrestricted path
   that dipped into `R` could never escape (`R` closed) and so could never return
   to the root (root ∉ `R`).
3. This gives a **permanent, DFS-state-independent** fact `(u,u) ∉ E⁺` the moment
   `u` finishes — no reasoning about *other* accepting states on a hypothetical
   cycle is ever needed.
4. Separately, `nc_finished_eq_reachable`: once the search completes with an empty
   stack, `finished` is closed and contains the roots, so it contains everything
   reachable (generic closure-induction, orthogonal to the accepting-cycle logic).

**Mapping to our code**: `innerDFS_no_cycle_from_seed_finished` (already proved,
line 555) is exactly CAVA's *restricted* fact. What's missing is the closedness
upgrade (2–3) and the reachability-completeness fact (4).

**Implementation plan** (phases are mostly independent; A/C first, since they
don't depend on anything else and let the approach be validated early):

- [x] **Phase A** — DONE. `OuterInvariant` now has `finished_closed` (new) and
  `finished_no_cycle` restated as the plain, state-independent
  `∀ s, innerFinished.contains s → ¬PathTo succs (fun _ => False) s s`.
  `finished_no_cycle_mono` retired (confirmed unused elsewhere).

- [x] **Phase B** — DONE. Four new theorems, all in `section InnerCorrectness`,
  right before `end InnerCorrectness`:
  - `fold_new_succs_blocked_aux` / `innerDFS_fuel_new_succs_blocked`: same
    fuel/fold double-induction template as `fold_iv_subset_finished_aux` /
    `innerDFS_fuel_iv_subset_finished`. Every state newly visited during a call
    has *all* its successors blocked (`iv'` or `innerFinished'`) by the end, not
    just `current`'s direct successors (which `innerDFS_fuel_fold_succs_blocked`
    already gives).
  - `fold_new_finished_subset_iv_aux` / `innerDFS_fuel_new_finished_subset_iv`:
    an extra lemma the plan hadn't anticipated — the *converse* of
    `innerDFS_fuel_iv_subset_finished`. Needed because
    `innerDFS_fuel_new_succs_blocked` is stated in terms of "newly in `iv`," but
    `innerDFS_new_finished_closed` needs to case on "newly in `innerFinished`";
    bridging the two requires knowing every newly-finished state was already in
    `iv` (true because `innerDFS_fuel`'s only `innerFinished`-insertion point —
    the fold's nil case — always inserts a `current` that was placed in `iv`
    first). This lemma takes an explicit `iv.contains current` precondition,
    since that fact is a property of *how* the fold is invoked, not part of its
    type signature.
  - `innerDFS_new_finished_closed`: combines both plus `innerDFS_fuel_mono` and
    `innerDFS_fuel_iv_subset_finished` to show that if the old `innerFinished`
    was closed and `current` (the top-level call's seed) wasn't already in it,
    the new `innerFinished` is closed too — the Lean analogue of CAVA's
    `red_closed`.
  Gotcha hit: `simp only [Std.HashSet.contains_insert] at hs` left a boolean
  `match`/`||` term rather than a clean `∨`, so `rcases hs with rfl | h2` failed
  with a "Dependent elimination failed" error; fixed by using full `simp`
  (not `simp only`), matching the precedent elsewhere in the file.

- [x] **Phase C** — DONE. Added three lemmas right after `PathTo.weaken`
  (the Lean port of `closed_restrict_aux`/`rel_restrict_tranclI`):
  `PathTo.mem_of_closed` (unrestricted path from a closed-set member stays
  inside the set), `PathTo.of_unrestricted_avoiding_closed` (an unrestricted
  path between two non-members of a closed set must avoid the set entirely),
  and `PathTo.no_self_loop_of_closed` (the corollary actually needed in Phase D:
  restricted no-self-cycle + closedness + non-membership ⇒ unrestricted
  no-self-cycle). Main gotcha during implementation: `induction h` on a
  `PathTo` hypothesis whose target index (`t`) is shared by another live
  hypothesis (`hnotF_t`) silently produces a *fresh*, distinct `t✝` unless that
  hypothesis is `revert`ed first too — cost a couple of confusing
  "expected `F t✝` but got `F t`" errors before reverting both `hnotF_s` and
  `hnotF_t` up front. Also: Lean's `induction ... with | through hmid _ hrest ih`
  leaves the implicit `mid` inaccessible when `hunblocked` is also matched via
  `_` (both count as "inaccessible", so `rename_i` grabs the wrong one) — fixed
  by using the `@through _ mid _ hmid _ hrest ih` positional-binding form
  instead of `rename_i`.

- [~] **Phase D** — Rewrite `outerDFSLoop_fuel_empty_no_cycle`'s proof by
  induction on `fuel`, mirroring the definition's 5-way case split. **5 of 6
  branches done** (stack=[]; both inner-DFS-contradiction branches; the
  non-accepting leaf; both successor-push branches). The 6th (accepting leaf,
  inner DFS returns `none` — the actual mathematical content) surfaced a real
  gap in Phase A's `finished_no_cycle` design, described below. The other
  5 branches' proofs are already in the file and are not expected to need
  further changes once `OuterInvariant` is corrected — only the "accepting
  leaf" branch's proof (still `sorry`) needs the revised argument.

  **The gap, and why it's not an algorithm bug.** The natural first attempt
  case-splits the accepting-leaf branch on `st.innerFinished.contains current`
  (already-finished vs. fresh). This looked necessary because inner DFS only
  checks `succ == seed` — never "is this successor currently on the *outer*
  stack" — so in principle a *different* accepting state's inner DFS traversal
  could incidentally walk through and mark `current` (an ancestor, still on
  the stack) as `innerFinished`, without ever checking *current's own*
  self-cycle.

  To check whether this is a genuine soundness gap (not just a proof
  wrinkle), several graphs designed to trigger exactly this were run through
  the actual `nestedDFS_fuel` via `#eval` (scratch file, not checked in).
  Every case still correctly reported `nonEmpty`. The reason: reaching an
  ancestor `current` via inner DFS from some other seed `w` is only possible
  via a back-edge — but `current`, being `w`'s DFS-tree ancestor, necessarily
  has a tree-path back down to `w` among its own successors. So exploring
  from `current` is *guaranteed* to rediscover `w` itself (`succ == seed`
  fires on that tree-path), and the whole algorithm halts immediately with
  `nonEmpty` — it never reaches a point where `current` is silently marked
  and *then* separately skipped later, because reaching `.empty` at all
  requires that no such incident ever occurred anywhere in the run.

  This means `finished_no_cycle` should **not** be unconditional over all of
  `innerFinished` (Phase A's current design) — it only needs to hold for
  states that are *accepting and no longer on the stack* (mirroring CAVA's
  `dom (finished s)`, which is a *different, separate* set from `red`/
  `innerFinished`, growing by exactly one state per finish-event). States
  merely touched incidentally by someone else's traversal don't need
  `finished_no_cycle` established for them yet — their own turn (and
  justification) comes later, when the outer DFS itself pops them.

  **Revised `OuterInvariant` fields** (two new fields, one rescoped):
  ```lean
  structure OuterInvariant (succs) (isAccepting) (st) (stackStates) : Prop where
    accepting_finished : ∀ s, st.outerVisited.contains s →
      isAccepting s → s ∉ stackStates → st.innerFinished.contains s
    finished_closed : ∀ s, st.innerFinished.contains s →
      ∀ t ∈ succs s, st.innerFinished.contains t
    finished_subset_visited :  -- NEW
      ∀ s, st.innerFinished.contains s → st.outerVisited.contains s
    finished_stack_disjoint :  -- NEW
      ∀ s ∈ stackStates, ¬st.innerFinished.contains s
    finished_no_cycle :        -- RESCOPED: was unconditional, now accepting ∧ ¬on-stack
      ∀ s, isAccepting s → s ∉ stackStates → st.outerVisited.contains s →
        ¬PathTo succs (fun _ => False) s s
  ```
  `finished_stack_disjoint` is what eliminates the "already finished"
  case-split entirely: `current` (head of stack) is always covered by it, so
  `¬st.innerFinished.contains current` comes for free and
  `innerDFS_no_cycle_from_seed_finished` always applies directly.

  **Why `finished_stack_disjoint` needs `finished_subset_visited` as a
  prerequisite**: maintaining disjointness through the "push a fresh
  successor `succ`" transition requires knowing `succ` (¬`outerVisited`
  before the push) isn't already `innerFinished` — i.e. the contrapositive of
  `innerFinished ⊆ outerVisited`. Establishing *that* through the "accepting
  leaf, run inner DFS" transition requires knowing everything inner DFS might
  touch from `current` was already `outerVisited` *before* the call — which
  is the standard DFS fact "by the time a node finishes, everything reachable
  from it is already discovered" (CAVA's generic `discovered_closed`). This
  is genuinely new infrastructure, not previously built — see Phase D.0 below.

- [x] **Phase D.0** — DONE. `OuterReachClosed succs st stack` (new structure,
  right before `OuterInvariant`), with three fields plus a helper structural
  fact:
  - `stack_chain : ReachChain succs (stack.map Prod.fst)` — a new inductive
    helper `ReachChain` (right after `PathTo.trans`, in the generic "Graph
    paths" section) encoding "every list element can reach the *previous*
    one," so with the stack's top at the head, every ancestor can reach every
    descendant further down. This replaces the originally-planned "pending"
    exclusion as the mechanism for handling stack members: reaching an
    ancestor via inner DFS, combined with `ReachChain.reaches_head` +
    `PathTo.trans`, directly gives `current` a self-loop, contradicting
    `innerDFS_no_cycle_from_seed_finished` — so Phase D.1 never actually
    needs to reason about "pending vs. processed" successors of *other*
    stack frames, only of `current` itself.
  - `done_closed` — CAVA's `discovered_closed` conjunct 1 (outer-done states'
    successors are visited), as originally planned.
  - `stack_processed_visited` — CAVA's conjunct 2 (non-pending successors of
    every stack frame are visited), as originally planned; still needed to
    seed the "current's direct successors are visited" base case.
  - `stack_remaining_subset` — an extra field the plan hadn't anticipated:
    `∀ p ∈ stack, ∀ t ∈ p.snd, t ∈ succs p.fst`. Needed because `stack_chain`
    requires "current reaches the freshly-pushed successor," which needs
    "the pushed state is a genuine successor of current" — true by
    construction (a frame's `remaining` always starts as the full
    `(succs state).toList` and only shrinks from the front) but not
    otherwise derivable from the other three fields.

  Maintained via `outerDFSLoop_fuel_reach_closed`, proved **fully** (0 sorry)
  by its own induction on fuel mirroring the same 5-way case split as
  `outerDFSLoop_fuel_empty_no_cycle`. Also needed a small standalone helper,
  `innerDFS_fuel_outerVisited_eq` (in `InnerCorrectness`, same fuel/fold
  double-induction template as everything else in that section): inner DFS
  never touches `outerVisited` (only `innerFinished`), so the "accepting
  leaf, recurse" branch's `OuterReachClosed`-maintenance proof is literally
  identical to the "non-accepting leaf" branch's, just bridged through this
  equation.

  Gotchas hit: (1) `subst` on `s = current` silently eliminated `current`
  instead of `s` (picked the "wrong" direction since both were free local
  variables), causing a confusing "unknown identifier `current`" error later
  in the same proof — fixed by avoiding `subst` and using `hsc ▸ ht` instead.
  (2) `List.Chain'` (Mathlib) turned out to be deprecated in favor of
  `List.IsChain` and its API wasn't a good fit anyway (needed `import
  Mathlib.Data.List.Chain` to even find it) — simpler and more robust to
  define the custom `ReachChain` recursor directly, matching the file's
  existing style of building `PathTo` itself from scratch rather than
  reaching for a library graph theory.

- [x] **Phase D.1** — DONE. `outerDFSLoop_fuel_empty_no_cycle` is fully proved,
  0 sorry. Signature now also takes `hrc : OuterReachClosed succs st stack`,
  threaded alongside `hinv` through all 5 branches (the 4 non-accepting-leaf
  branches largely reuse the `OuterReachClosed`-update snippets already
  written for `outerDFSLoop_fuel_reach_closed`, plus straightforward
  weakening for the `OuterInvariant` fields).

  **New supporting lemmas** (all proven, 0 sorry), needed because the natural
  first attempt — apply `PathTo.no_self_loop_of_closed` with
  `F := st''.innerFinished` (state right after `current`'s own inner-DFS
  call) — doesn't typecheck: `current` always ends up *inside*
  `st''.innerFinished` by the end of its own successful call, so the required
  `¬F current` is simply false.
  - `PathTo.false_of_mem_closed_reaches` / `avoids_closed_of_no_incoming` /
    `no_self_loop_of_closed_no_incoming` (near `PathTo.no_self_loop_of_closed`):
    a second closure-upgrade route that doesn't need `s ∉ F` — only that
    *nothing in F has an edge back to s* (`hno_edge`), a weaker,
    differently-shaped fact inner DFS gives us for a different reason (its
    own `succ == seed` check).
  - `innerDFS_fuel_new_no_edge_to_seed` (+ `fold_new_no_edge_to_seed_aux`,
    `InnerCorrectness` section): after a `none`-returning call, no newly
    visited state has `seed` as a successor — if it did, the fold's own
    `succ == seed` check would have fired and the call would have returned
    `some (...)`, not `none`. Combined with `finished_closed` +
    `finished_stack_disjoint` (ruling out the old-finished case), this gives
    the `hno_edge` fact `no_self_loop_of_closed_no_incoming` needs.
  - `innerDFS_fuel_new_reachable` (+ `fold_new_reachable_aux`): every state
    newly visited during a `none`-returning call is reachable from `current`
    (`s = current ∨ PathTo current s`). Used both to show *ancestors* can't
    become newly finished (combining `PathTo current ancestor` with `PathTo
    ancestor current`, via `ReachChain.reaches_head` + `PathTo.trans`, would
    give `current` a self-loop) and as the entry point for `finished_subset_visited`.
  - `stack_subset_visited` (new `OuterInvariant` field): every state on the
    stack is already `outerVisited` — trivial by construction, needed so
    `current` itself is known-visited.
  - **`PathTo.closed_of_no_escape`** — direct Lean port of CAVA's
    `closed_restrict_aux` (`Nested_DFS.thy`, top of file), the piece that
    actually unblocked `finished_subset_visited`. Re-reading how CAVA proves
    `R' ⊆ dom (finished s)` in `red_dfs_pres_bbi` showed the ad-hoc "induct
    along one specific witnessed path" approach sketched earlier was
    reinventing exactly this generic lemma, just less cleanly: *if `F`'s
    successors stay in `F ∪ S`, and nothing reachable from `x` (an
    `F`-member) escapes into `S`, then everything reachable from `x` stays in
    `F`* — applied with `F := outer-done`, `S := current stack`. This handles
    "extend visitedness along an arbitrary reachable path" in one generic
    shot instead of bespoke induction at each use site, exactly mirroring
    CAVA's own structure (establish the closedness fact once, apply it
    generically) rather than reinventing it per call site.

  Gotchas hit: (1) the fuel passed to `innerDFS_no_cycle_from_seed_finished`/
  `innerDFS_new_finished_closed` must be in `k + 1` form (their signatures
  peek at the first unfolding step explicitly), while every other lemma here
  is generic over fuel — needed an explicit `obtain ⟨k, rfl⟩ : ∃ k, m = k + 1`
  extraction (via `cases m`) before calling them. (2) Repeated instances of
  the `@direct`/`@through` positional-binding requirement when a case's own
  bound name collides with an already-existing outer name of the same
  spelling (reusing "x" for both crashed the same way "current" did earlier
  — fixed by using a distinct fresh name for the case-local binding). (3)
  Two genuine bugs from moving fast: mixing up `iv` (inner DFS's own
  fuel-local visited-set, starts empty) with `innerFinished` when feeding
  arguments to `innerDFS_fuel_new_no_edge_to_seed`/`innerDFS_fuel_new_reachable`
  (needed `innerDFS_fuel_new_finished_subset_iv` as a bridge, plus the
  trivial "`∅` contains nothing" fact, not `hold`); and a missing
  monotonicity fact (`innerDFS_fuel_mono`) to lift an old `innerFinished`
  membership fact across the call in `accepting_finished`'s else-branch.

- [x] **Phase E** — DONE. `nestedDFS_fuel_go_correct` (new `GoCorrectness`
  section): composes `OuterReachClosed`/`OuterInvariant` across the whole
  `initialStates` loop, mirroring `outerDFSLoop_fuel_reach_closed`'s style but
  for `nestedDFS_fuel.go`'s own 3-way recursion (fuel=0 / `remaining=[]` /
  `init::rest`, the latter split into already-visited vs. fresh, with fresh
  further split on `outerDFSLoop_fuel`'s 3 outcomes). This is the Lean
  analogue of CAVA's `nc_finished_eq_reachable`, adapted to our *explicit*
  `initialStates` loop — CAVA's generic multi-root DFS framework handles the
  looping internally via `V0`, so they don't need a separate composed
  theorem; we do, since `nestedDFS_fuel.go` is a concrete recursive `List`
  walk rather than a framework-level abstraction.
  - Conclusion: `∃ st', OuterReachClosed succs st' [] ∧ OuterInvariant succs
    isAccepting st' [] ∧ (old outerVisited ⊆ new) ∧ (∀ i ∈ remaining,
    outerVisited' i)`. The "fresh init" branch constructs `OuterReachClosed`/
    `OuterInvariant` for the freshly-pushed singleton stack `[(init,
    succsList)]` from the empty-stack versions (same construction pattern as
    `outerDFSLoop_fuel`'s own "push" branches, just starting from `[]`
    instead of a nonempty stack), then feeds it through the *already-proved*
    `outerDFSLoop_fuel_reach_closed`/`outerDFSLoop_fuel_empty_no_cycle`.
  - New supporting lemma: `outerDFSLoop_fuel_outerVisited_mono` — `outerVisited`
    only grows across an `outerDFSLoop_fuel` call, for *any* result (not just
    `.empty`; needed here since the fresh-init branch must relate the
    pushed-but-not-yet-run state to the post-call state generically). Same
    5-way induction template, but the "found a cycle" branch is a genuine
    base case here (unlike the `.empty`-specific theorems, where it's a
    contradiction) — was initially copy-pasted as a contradiction by mistake
    and had to be corrected to a direct case.
  - Gotcha: the same `rcases ... with rfl | ...` "eliminates the wrong
    variable" issue hit repeatedly in Phase D.1 recurred here (`init` vs `s`
    this time) — same fix, name the equality and use `▸` instead of `rfl`.

- [x] **Phase F** — DONE. `nestedDFS_fuel_empty_no_cycle` fully proved, 0
  sorry — **`NestedDFSCorrectness.lean` is now 100% sorry-free.** Follows
  CAVA's `blue_dfs_correct` almost exactly:
  1. Unfold `nestedDFS_fuel` to `nestedDFS_fuel.go ... initialStates st₀
     fuel`, and apply Phase E with trivial `hrc₀`/`hinv₀` for the empty
     starting state (every field holds vacuously — nothing is visited yet).
  2. Given a hypothetical `ac : AcceptingCycle`, use `chain_reaches` (new
     generic lemma: converts `AcceptingCycle`'s index-based `stem_chain`/
     `cycle_chain` into a `PathTo` witness, or an equality if the list is a
     singleton) plus Phase E's `hroots` to place `ac.stem.head` — hence, via
     `ac.overlap` and `PathTo.closed_of_no_escape` (with the escape set `S :=
     False`, i.e. CAVA's `discovered_closed`-style closure with no restriction
     at all) — `ac.cycle.head` in `outerVisited`.
  3. `hinv'.accepting_finished` (stack `= []`) places it in `innerFinished`.
  4. `chain_reaches` again on `ac.cycle` plus `ac.cycle_back` builds a genuine
     `PathTo succs (fun _ => False) cycle.head cycle.head` self-loop witness.
  5. `hinv'.finished_no_cycle` directly contradicts it. `False`, done.

  This is exactly CAVA's own argument structure (`nc_finished_eq_reachable`
  step ↔ our step 2; `no_accpt_cycle_in_finish` ↔ our step 3/5) — the only
  real difference is steps 2–4 needing an explicit `PathTo`-witness
  reconstruction from `AcceptingCycle`'s list-based fields, since CAVA works
  directly with `(v,v) ∈ E⁺` (trancl) rather than an explicit witness
  structure.

- [x] **Phase 5c** — ✅ DONE. Soundness of a `.nonEmpty` result:
  `nestedDFS_fuel_nonEmpty_valid` proves that whenever `nestedDFS_fuel`
  returns `.nonEmpty stem loop`, `(stem, loop.tail)` genuinely witnesses an
  accepting cycle — packaged directly as an `AcceptingCycle` value. CAVA's
  analogue is the `Some (pr,pl)` branch of `blue_dfs_correct`, backed by
  `lasso_inv` (`Nested_DFS.thy` ~430–655) and the generic framework fact
  `stack_is_path` (`DFS_Invars_Basic.thy` ~670). We don't have CAVA's
  Schwoon-Esparza back-edge optimization (`se_back_edge`) — our algorithm
  only ever finds a cycle inside `innerDFS`'s own search — so we only needed
  the `finish`-case half of `lasso_inv`'s proof, not the `back_edge` case.

  **New lemmas** (all proven, 0 sorry):
  - `chain_dropLast` / `chain_append_singleton` / `chain_cons` (generic list
    lemmas, near `chain_reaches`): dropping a chain-list's last element, or
    appending/prepending a genuine-successor edge, keeps it a `succs`-chain.
    Needed because `AcceptingCycle`'s fields are literal per-index chain
    facts (`stem[i+1] ∈ succs stem[i]`), not abstract `PathTo` reachability
    witnesses — `PathTo`/`ReachChain` (used throughout Phase D–F) don't carry
    enough information to reconstruct a *specific* list's chain property.
  - `head_dropLast_eq` / `head_append_singleton_eq` (generic list lemmas):
    dropping a list's last element, or appending a singleton, doesn't change
    its head. Needed for `outerDFSLoop_fuel_nonEmpty_witness`'s `root`
    tracking (below) — proved by plain `cases`/`rfl`, no induction needed.
  - `outerDFSLoop_fuel_nonEmpty_witness` — the core theorem, in
    `OuterCorrectness` (formerly `outerDFSLoop_fuel_pathStack_chain`, renamed
    and extended once it became clear `loop`'s facts needed the same
    induction, not a separate one). Proves, whenever `outerDFSLoop_fuel`
    returns `.nonEmpty stem loop`:
    - `stem` is a genuine `succs`-chain (via `pathStack`'s literal chain
      invariant, threaded like every other `OuterReachClosed`/`OuterInvariant`
      field — the Lean analogue of CAVA's `stack_is_path`), *and*
      `stem.head = root` for a tracked root parameter (needed since `stem`
      could be produced arbitrarily deep in the recursion; `root` is the
      value `pathStack.head` is pinned to at the top-level call).
    - `loop.tail` (not `loop`!) is a genuine `succs`-chain with a back-edge
      into its own head, which is accepting. Getting this wrong once cost a
      re-derivation: `loop := current :: cyclePath` where `cyclePath` (by
      `innerDFS_fuel_cyclePath_chain`, next bullet) *already* starts with a
      copy of `current`, so `loop = [current, current, x₁, ..., xₘ]`. `loop`
      itself is NOT a chain (`current ∈ succs current` isn't guaranteed) —
      only `loop.tail = cyclePath` is. This matches `OutputVerify.lean`'s
      pre-existing convention of indexing from `loop[1]`, confirming that
      file's hypothesis shapes were correct all along, not a bug as first
      suspected.
  - `fold_cyclePath_chain_aux` / `innerDFS_fuel_cyclePath_chain` (in
    `InnerCorrectness`, same fuel/fold double-induction template as
    everything else in that section, `ih_inner`-parametrized like
    `innerDFS_fuel_fold_mono_aux`): whenever `innerDFS_fuel`/
    `innerDFS_fuel_fold` returns `some (some cyclePath, ..)`, `cyclePath`
    is a genuine `succs`-chain starting at the call's own `current` argument
    and ending with an edge into `seed`. The Lean analogue of `lasso_inv`'s
    `finish`-case core argument (CAVA's `path E (hd (stack s)) vs v`,
    established there via `find_path1_restr_spec`'s abstract postcondition —
    ours is direct since `innerDFS_fuel` is concrete code, not a framework
    call). Needed an extra `hremaining` hypothesis ("every element of
    `remaining` is a genuine successor of `current`") to justify the very
    first edge, true at the top-level call and preserved as `remaining`
    shrinks — the same shape of bookkeeping as `OuterReachClosed.
    stack_remaining_subset`.
  - `nestedDFS_fuel_go_nonEmpty_witness` — composes
    `outerDFSLoop_fuel_nonEmpty_witness` across `nestedDFS_fuel.go`'s
    `initialStates` loop (mirroring `nestedDFS_fuel_go_correct`'s structure
    exactly, including reusing its `hrc_pushed`/`hinv_pushed`/`hps_pushed`
    construction verbatim), additionally proving `stem.head ∈ remaining` by
    threading the `root` parameter through as `init` at each freshly-pushed
    call. Same CAVA asymmetry noted for Phase E: their generic multi-root
    framework gets this for free from `lasso_inv` being a `param_DFS`-level
    invariant (covering `new_root` transitions automatically via
    `is_invarI`'s induction), so they need no separate composition theorem.
  - `nestedDFS_fuel_nonEmpty_valid` — final assembly, structurally the mirror
    image of `nestedDFS_fuel_empty_no_cycle`: unfold `nestedDFS_fuel`, apply
    the vacuous empty-state `hrc₀`/`hinv₀` (copied verbatim from that
    theorem), invoke `nestedDFS_fuel_go_nonEmpty_witness`, and package the 8
    resulting facts directly into an `AcceptingCycle` value. CAVA's assembly
    step is `mk_blue_witness`'s `Inr` case plus `lasso_inv`'s conclusion,
    packaged directly into `blue_dfs_correct`'s `Some` branch — no separate
    "loop composition" theorem needed there for the reason above.

  **Gotchas hit**: (1) the same `rw [← heq]`-on-a-`match`-result trap as
  earlier phases, this time triggered by stating the conclusion as `match
  result with | .nonEmpty stem _ => P | .empty _ => True` — Lean's dependent
  match compilation auto-generalizes any OTHER hypothesis mentioning `result`
  (here, `h` itself), breaking `rw`. Fixed by specializing the hypothesis
  type directly to `some (.nonEmpty stem loop, st')` instead (matching
  `outerDFSLoop_fuel_empty_no_cycle`'s existing style for `.empty`), rather
  than trying to handle both result shapes in one statement. (2) Once
  discovered, `subst` (not `rw`/`▸`) is the reliable way to eliminate an
  injectivity-derived equation between the match's freshly-introduced pattern
  variables and a theorem's own implicit result variables — used repeatedly
  in the "found" branches of both new theorems to sidestep dependent-rewrite
  motive errors entirely, rather than fighting them with `▸`-chains.
  (3) Initially believed `OutputVerify.lean`'s `ba_hasAcceptingRun_of_ndfs_output`
  had a bug (indexing `loop[1]` instead of `loop[0]`) — tracing through
  `innerDFS_fuel_fold`'s actual recursion by hand (the `f(x)` derivation
  above) showed it was correct; the confusion came from initially assuming
  `cyclePath` starts at whatever the *first recursed-into successor* is,
  rather than realizing the top-level call sets `seed := current` and the
  initial `current`-argument to the *same* value, so `cyclePath` already
  starts with a duplicate of `current`/`seed`.

  **Traced exactly how the raw output is built** (`NestedDFS.lean`/
  `NestedDFSCorrectness.lean`'s `innerDFS_fuel`/`innerDFS_fuel_fold`): define
  `f(x)` as what a `some (some _)`-returning fold at node `x` returns. Base
  case (some successor of `x` equals `seed`): `f(x) = [x]`. Recursive case
  (recursing into successor `y ≠ seed`): `f(x) = x :: f(y)`. Unrolled:
  `f(x₀) = [x₀, x₁, ..., xₘ]` with `xᵢ₊₁ ∈ succs(xᵢ)` and `seed ∈ succs(xₘ)`.
  The top-level call in `outerDFSLoop_fuel` uses `seed := current` **and**
  `x₀ := current` (the same accepting state), so `cyclePath = f(current) =
  current :: x₁ :: ... :: xₘ` already starts with a copy of `current`. Then
  `loop := current :: cyclePath = [current, current, x₁, ..., xₘ]` — so
  `loop.tail = cyclePath` is the "real" cycle: head `= current` (accepting),
  internal chain `current → x₁ → ... → xₘ`, and `current ∈ succs(xₘ)` (the
  wraparound edge). This is exactly `AcceptingCycle.cycle` if we set
  `cycle := loop.tail`, confirming `OutputVerify.lean`'s existing hypothesis
  shapes are the right target, not a bug.

  **Planned steps, staying close to CAVA's structure**:
  1. Port `stack_is_path` (CAVA: generic `param_DFS` framework invariant,
     proved by inducting on `discover`/`finish` transitions, tracking that
     the reversed DFS stack is a tree-path from some `v0 ∈ V0`). Our analogue:
     prove `pathStack` is a literal `succs`-edge chain from an initial state
     to `current`, by induction on `outerDFSLoop_fuel`'s fuel — simpler than
     CAVA's version since we track `pathStack` explicitly as a list rather
     than deriving it from tree edges, and simpler than Phase D.0–F's
     closure-induction lemmas since this is a plain forward invariant with no
     closedness argument needed. Needs threading through
     `nestedDFS_fuel_go`'s `initialStates` loop (CAVA: folded into the
     framework's `V0` handling), reusing the Phase E composition pattern.
  2. Prove `innerDFS_fuel`'s cycle-found case matches the `f(x)` chain
     description above: a new lemma (fuel/fold double induction, same
     template as everything in `InnerCorrectness`) stating that whenever
     `innerDFS_fuel_fold`/`innerDFS_fuel` returns `some (some cyclePath, ..)`
     from call-argument `current`, `cyclePath = current :: ...`, forms a
     genuine `succs`-chain, and ends with an edge into `seed`. This is the
     CAVA analogue of `lasso_inv`'s `finish`-case core argument (the
     `path E (hd (stack s)) vs v` fact, established there via
     `find_path1_restr_spec`'s abstract postcondition — ours is direct since
     `innerDFS_fuel` is concrete code, not a framework call).
  3. Assemble: combine steps 1–2 at the point `outerDFSLoop_fuel` returns
     `.nonEmpty pathStack (current :: cyclePath)`, thread through
     `nestedDFS_fuel_go`'s loop (mirroring Phase E's composition), and land
     on either an `AcceptingCycle` value or `OutputVerify.lean`'s exact
     hypothesis set for `ba_hasAcceptingRun_of_ndfs_output`. CAVA's assembly
     step is `mk_blue_witness`'s `Inr` case plus `lasso_inv`'s conclusion,
     packaged directly into `blue_dfs_correct`'s `Some` branch — no separate
     "loop composition" theorem needed there since their `V0`-loop is
     framework-internal (same asymmetry noted for Phase E above).

### Phase 6: End-to-end Pipeline — ✅ DONE (GBA-level scope)

**Goal**: Connect the already-unconditional pieces into a single theorem
matching Isabelle's `create_name_gba_correct`'s accept-iff clause.

**Scope decision**: a research pass (2026-07-24) surfaced that "Phase 6"
could mean two different things: (a) the GBA-level theorem literally
described above — pure assembly of already-unconditional pieces, zero new
math — or (b) a genuinely *runnable* LTL→emptiness-check pipeline wiring GBA
→ degeneralize → `BA` → `nestedDFS_fuel`, which needs several more pieces,
at least one of which is real new proof content (constructing a concrete
label-compatible `ξ` from a lasso witness — `OutputVerify.lean`'s theorems
only conclude `isRun ∧ isAcceptingRun`, not a genuine `.accepts ξ`). Per
explicit user choice, Phase 6 was scoped to (a); (b) remains future work
(not tracked as a phase here — see "Track B" notes below if resuming it).

**Done**: `LTLLib/LTLtoGBA/GraphComplete.lean`, `constructGBA_correct_weak`
(end of file) — combines `constructGBA_iff_expandOASpec` (Bridge.lean) with
`expandOASpec_soundness` (Soundness.lean, needs only `ExpandSpec`) and
`expandOASpec_completeness_weak` + `createGraph_weakGraphComplete` (this
file, needs only the unconditional `WeakGraphComplete`) to get:

```lean
theorem constructGBA_correct_weak
    [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {φ : NNF α} {st : ExpandState α S}
    (hcg : createGraph φ = some st) (ξ : OmegaWord α) :
    (constructGBA φ st).toSpec.accepts ξ ↔ NNF.satisfies ξ φ
```

Fully unconditional (the `mergeIncoming_incoming` sorry it was threaded
through, via `createGraph_spec`, has since been closed — see Phase 3). Had to
live in `GraphComplete.lean` (not `Bridge.lean`, where the analogous
`GraphComplete`-gated `constructGBA_correct` already lives) because of import
order: `GraphComplete.lean` imports `Bridge.lean`, not the other way around.

Isabelle's `gba 𝔄 ∧ finite (g_V 𝔄)` conjuncts weren't ported: in the Lean
port, `GBA.states`/`GBA.successors` are concrete `Std.HashSet`/`Std.HashMap`
values by construction (no infinite-cardinality states are representable at
all), so finiteness isn't a separate proof obligation the way it is in
Isabelle's abstract `graph_rec_scheme` locale, and `GBA.WellFormed`
(`GBA.lean`) is an independent structural fact not needed for this
accept-iff correspondence.

**Track B notes (future work, not started)**: for a genuinely runnable
`nestedDFS_fuel`-based decision procedure, would additionally need: (1)
`(constructGBA φ st).WellFormed` proved (needed by `degeneralize_bridge`'s
`hwf` hypothesis — currently proved nowhere); (2) a connecting lemma from
`AcceptingCycle initialStates ba.getSuccessors ba.isAccepting` (as produced
by `nestedDFS_fuel_nonEmpty_valid`) to `OutputVerify.lean`'s raw hypothesis
bundle — mechanical, currently missing; (3) constructing a concrete
label-compatible `ξ` from a lasso witness to get a genuine `.accepts ξ`
rather than just `isRun ∧ isAcceptingRun` — real new proof content, not
mechanical; (4) an actual `def` chaining `createGraph → constructGBA →
GBA.degeneralize → nestedDFS_fuel` together — none exists currently, every
stage is a free-standing function never composed.

### Phase 2: Termination — IN PROGRESS (not blocking)

Remove `partial`/`partial_fixpoint` from `expand`, `innerDFS`, `outerDFSLoop`.

**Isabelle source studied**: AFP `Param_DFS.thy` (`param_dfs_variant`, the
generic DFS framework's termination proof), `Nested_DFS.thy`/`DFS_Find_Path.thy`
(how the blue/red DFS pair is actually wired together), and `LTL_to_GBA.thy`'s
"Termination proof" section (`expand_ord`). Sources fetched directly from the
AFP GitHub mirror (`isabelle-prover/mirror-afp-devel`) and read in full for
this section — see the two write-ups below, which quote the relevant
definitions/lemmas verbatim. CAVA proves termination from a single finiteness
hypothesis in each case — `fb_graph` (finite reachable-state locale assumption)
for the DFS framework, and the finite subformula-closure `subfrmlsr φ` for
`expand`. We port the same strategy: assume finiteness explicitly (a
`FiniteReach` structure below), rather than trying to prove termination
unconditionally (which is simply false for `innerDFS`/`outerDFSLoop` — a
`State`/`successors` pair with an infinite reachable set never terminates;
CAVA doesn't claim otherwise either).

**Correction (2026-07-25)**: an earlier version of this section claimed
CAVA's `RECT`/WF-recursion package "uses `wf param_dfs_variant` directly...
with no separate fuel parameter ever threaded through the code" and concluded
from that alone that there was "nothing to combine across nested calls." That
conclusion was right, but the stated reason was incomplete — re-reading the
actual sources (below) shows the *real* reason is structural, not just "no
fuel": CAVA never defines one jointly-recursive function containing "outer
calls inner, then continues." This distinction matters for the Lean port —
see "Planned next step," which changes as a result.

**`expand`'s termination (`LTL_to_GBA.thy`), verified**: `expand` itself is
defined with the *partial*-correctness combinator `REC` (no termination
proof needed to define it — this is the Isabelle analogue of our
`partial_fixpoint`). A second, *total*-correctness version `expand⇩T` is
defined with `RECT`, and that is what the termination section actually
proves well-founded, via:

```isabelle
abbreviation "old_next_pair n ≡ (old n, next n)"
abbreviation "old_next_limit φ ≡ Pow (subfrmlsr φ) × Pow (subfrmlsr φ)"
lemma old_next_limit_finite: "finite (old_next_limit φ)"
  using subfrmlsr_finite by auto

definition expand_ord where
  "expand_ord φ ≡ inv_image (finite_psupset (old_next_limit φ) <*lex*> less_than)
                             (λ(n, ns). (old_next_pair ` ns, size_set (new n)))"
lemma expand_ord_wf[simp]: "wf (expand_ord φ)"
  using finite_psupset_wf[OF old_next_limit_finite] unfolding expand_ord_def by auto
```

i.e. a lexicographic `inv_image`: (1) primary — the set of `(old,next)`
signatures across already-finished nodes, ordered by strict superset,
well-founded because it's bounded by the finite universe
`Pow(subfrmlsr φ) × Pow(subfrmlsr φ)` (`finite_psupset`, the standard
"bounded-by-a-finite-set, strict-superset" WF relation from
`Refine_Monadic`); (2) secondary tie-break — `size_set (new n)`, the current
node's still-to-expand formulas' total AST size under plain `<`, which
strictly shrinks every time a formula is split into its (structurally
smaller) sub-formulas:

```isabelle
lemma new1_less_sum: "size_set (new1 φ) < size_set {φ}"
lemma new2_less_sum: "size_set (new2 φ) < size_set {φ}"
```

An invariant `expand_inv` (`new/old/next ⊆ subfrmlsr φ`, all finite) is
carried alongside, needed so the state stays inside the bounded universe. A
single per-recursive-call-site lemma, `expand_inv_impl`, discharges both
"argument decreases in `expand_ord φ`" and "invariant preserved" together for
all three of `expand`'s recursive-call shapes (finish-a-node / split via
`new1`+`next1` / split via `new2`) in one shot. The whole proof is then
`RECT_rule[pre, V]` + `wf V` (`expand_ord_wf`) + `expand_inv_impl` at each
call site. Location: `thys/LTL_to_GBA/LTL_to_GBA.thy` lines 279 (`expand`
def), 836–1130 (termination section).

This maps onto our codebase directly: `NNF.subformulas` (`Subformulas.lean`)
is already the Lean `subfrmlsr`, and `Invariants.lean`'s `old_subformula`/
`next_subformula` `ExpandSpec` fields already establish (for the *partial*
`expand`, via `partial_correctness`) exactly the subset-closure fact
`expand_inv` needs — this groundwork transfers to the termination proof
essentially unchanged; the new work is the measure itself (signature-set
superset growth + `new`'s AST-size shrink) and the per-branch decrease
proof.

**Nested DFS termination, verified — structurally different from what was
previously assumed here**: the important discovery is that CAVA does **not**
define one jointly-recursive function where "outer DFS calls inner DFS, then
continues the outer traversal" is a single recursive definition needing a
combined measure. Instead:

- The generic DFS (`Param_DFS.thy`) is an ordinary `WHILE`/`WHILET` loop
  (`it_dfs`/`it_dfsT`), terminating via its own self-contained measure:
  ```isabelle
  definition "param_dfs_variant ≡ inv_image
    (finite_psupset reachable <*lex*> finite_psubset <*lex*> less_than)
    (λs. (dom (discovered s), pending s, length (stack s)))"
  ```
  a 3-way lexicographic order: discovered-set growth (bounded by the
  `finite reachable` hypothesis, i.e. `fb_graph`), then pending-successor
  shrinkage, then stack-length as a final tie-break. Proved well-founded via
  `param_dfs_variant_wf`, then plugged into the library's
  `WHILET_eq_WHILE_tproof` to get total correctness of the loop.
- `Nested_DFS.thy`'s outer ("blue") DFS is *one more instantiation* of this
  same generic `param_DFS` locale — its `on_finish` hook (called when
  backtracking from an accepting state) is `run_red_dfs`, which invokes the
  inner ("red") DFS not as a concrete recursive call but as an **abstract
  monadic oracle**, `find_path1_restr_spec` — a `SPEC(...)` postcondition,
  not a program:
  ```isabelle
  definition find_path1_restr_spec G P R ≡ do {
    ASSERT (fb_graph (graph_restrict G R)); SPEC (find_path1_restr_pred G P R) }
  ```
  The outer loop's own termination proof (`param_dfs_variant_step`) only has
  to show that after `step` — which may invoke this oracle — the *outer*
  state's `(discovered, pending, stack)` triple has strictly decreased. It
  treats the oracle's result opaquely via its postcondition; it never
  inspects how many internal steps the inner DFS took. **This is exactly
  what avoids the "combine two independently-derived bounds" problem** we
  hit with the fuel-based attempt below.
- The *concrete* red DFS realizing that oracle (`find_path1_restr`,
  `DFS_Find_Path.thy`) is proved terminating completely separately: it's
  *yet another*, wholly independent `param_DFS` instantiation (locale `fp0`)
  over its *own* graph/state, with its *own* `param_dfs_variant`, and is
  then shown, via Isabelle's refinement-calculus order `≤` on the `nres`
  monad, to *refine* the abstract spec `find_path1_restr_spec` — a separate
  lemma, in a separate theory, with no shared measure whatsoever with the
  blue DFS's proof.
- The two proofs are glued only by `nres`/refinement-calculus composition
  (`≤` is monotone w.r.t. `bind`, so "outer computation treating inner as an
  oracle satisfying `SPEC`" composes for free with "inner computation
  refines that `SPEC`" — termination/`nofail` included, no joint measure
  needed).

Locations: `thys/DFS_Framework/Param_DFS.thy` lines 342–343 (`it_dfs`/
`it_dfsT`), 1042–1132 (`param_dfs_variant` + `wf` + `WHILET_eq_WHILE_tproof`
application); `thys/DFS_Framework/Examples/Nested_DFS.thy` lines 48–133
(`BlueDFS_defs`, `run_red_dfs`, requires `fb_graph G`);
`thys/DFS_Framework/Examples/DFS_Find_Path.thy` lines 33–70, 336–430 (`fp0`
locale, `find_path1_restr_spec`/`find_path1_restr`, the refinement lemma).

**Key realization (nested DFS, `NestedDFSTermination.lean`)**: the two
`partial` functions in `NestedDFS.lean` don't need equally-hard termination
arguments. `innerDFS_fuel`'s `fuel : Nat` argument is *not* a depleting
total-work counter — every sibling call inside `innerDFS_fuel_fold` (one per
successor of `current`) gets the *same* fuel value, not a further-decremented
share, because `fuel` is a plain value, not a threaded/returned resource. So
fuel there acts as a *maximum recursion depth* cap, reusable across branches:
`universe.size + 1` uniformly suffices for any call, proved by a strong
induction on `universe.size - iv.size`. This is now **done** —
`innerDFS_fuel_sufficient` in `NestedDFSTermination.lean`, 0 sorry, following
the same fuel/fold double-induction template used throughout
`NestedDFSCorrectness.lean`.

This reuse phenomenon does **not** carry over to `outerDFSLoop_fuel`: its own
recursion is a single non-branching chain (no fold over siblings), so fuel
there really is consumed once per actual step of the whole outer traversal.

**Outer-DFS: fuel-based attempt tried and abandoned (2026-07-24)**. Bounding
`outerDFSLoop_fuel`'s fuel needs the *full* CAVA-style lexicographic potential
function `(discovered, pending, stack-length)` from `param_dfs_variant`. A
proof was attempted in `NestedDFSTermination.lean` (`OuterFuelInv`, `pendingSum`,
nested `Nat.strongRecOn` on `(A, B) := (univ.size - outerVisited.size,
pendingSum stack + stack.length)`, mirroring the file's usual fuel/fold
induction style) but hit a genuine circularity: the "accepting leaf, launch
inner DFS, then continue the outer traversal" branch needs to combine two
sub-obligations — `innerDFS_fuel_sufficient`'s concrete bound (fine, it's a
closed formula) and the *outer* induction's own recursively-obtained
threshold for the state *after* the inner-DFS call runs. But that
post-inner-DFS state isn't known until a fuel value is already fixed, and
picking that fuel value is exactly what the threshold is supposed to
determine — combining two independently-quantified `∃ threshold, ∀
fuel≥threshold, ...` facts via `max` silently assumed a monotonicity property
("succeeds at fuel F ⟹ succeeds at any F′≥F") that hadn't been proved. This
attempt was reverted; `NestedDFSTermination.lean` now contains only the
completed, verified inner-DFS half (`innerDFS_fuel_sufficient`,
`innerDFS_fuel_fold_sufficient_aux`, plus small `Std.HashSet` cardinality
helpers: `size_le_of_subset`, `size_pos_of_contains`, `size_lt_of_ssubset`,
`length_le_size_of_pairwise_subset` — the last needs Mathlib's `LawfulBEq`
only, reusable elsewhere if a nodup-list/`HashSet`-cardinality bound is ever
needed again).

**Root cause, and the redirect this points to (corrected 2026-07-25)**: the
circularity came from treating `innerDFS`/`outerDFSLoop` as if they needed a
*single, combined* well-founded measure — i.e. from implicitly assuming
CAVA's termination argument is "mutual." Having now actually read
`Nested_DFS.thy`/`Param_DFS.thy`/`DFS_Find_Path.thy` (previous version of
this note relied on secondhand description, not the source), that assumption
was wrong: **CAVA's blue and red DFS are two separately-terminating
functions**, each with its own self-contained measure, and the outer one
calls the inner one as an ordinary (already-total) function whose internal
step count is irrelevant to the outer measure. There is no combined bound to
construct in the first place. The fuel-based encoding failed not because
fuel is the wrong *technique* in general, but because our fuel attempt kept
`innerDFS_fuel`'s and `outerDFSLoop_fuel`'s fuel arguments coupled (needing a
`max` of two existentially-quantified thresholds); CAVA's structure shows the
fix is to decouple them completely, matching the source.

**Planned next step (not started): convert `innerDFS`, then `outerDFSLoop`,
separately** via `termination_by`, in that order — not as a mutual
definition:

1. **`innerDFS` becomes a standalone well-founded recursion first — ✅ DONE
   (2026-07-25), `NestedDFSTermination.lean`, 0 sorry, 0 warnings, whole
   project still builds (394 jobs).** `FiniteReach` (`univ : Std.HashSet
   State`, `closed : ∀ s, univ.contains s → ∀ t ∈ succs s, univ.contains t`)
   was added there (not `NestedDFS.lean` itself yet — see below) as a
   genuine **explicit parameter**, our analogue of `fb_graph`/CAVA's own
   `finite reachable` hypothesis, assumed rather than derived, exactly as
   planned.

   **Correction found empirically while implementing this**: the measure is
   **not** `univ.size - iv.size` (`Nat` subtraction) as this note originally
   proposed — that measure needs `iv ⊆ univ` maintained as an inductive
   invariant just to stay well-defined (Nat subtraction truncates), which is
   exactly what reintroduces "the hard part" below in its *worst* form. The
   actual measure used is **`(fr.univ \ iv).size`** (`Std.HashSet`
   set-difference size) — well-defined and meaningful regardless of whether
   `iv` has elements outside `univ`, so no closure invariant on `iv` itself
   is ever needed, only a one-line fact (`HashSet.sdiff_insert_lt`, reusing
   the already-proved `HashSet.size_lt_of_ssubset` directly, no fresh
   extensionality argument — `Std.HashSet` doesn't expose one) that
   inserting a fresh (`univ`-member, not-yet-`iv`) state strictly shrinks
   `univ \ iv`.

   **The hard part correctly anticipated, but overstated in scope**:
   `innerDFS` folds over `current`'s successors, and the "continue with the
   rest of the list after exploring a fresh successor" call needs a fact
   about the *previous* recursive call's *result* — specifically, that
   exploring that successor didn't *increase* the measure (plain, non-strict
   monotonicity) — and no correctness theorem about the not-yet-defined
   function can supply that externally. The fix is exactly what this note
   already said: bundle the fact into `innerDFSCore`'s own return type
   (`Subtype`, `{p // (fr.univ \ p.2.1).size ≤ (fr.univ \ iv).size}`) rather
   than a plain tuple — but the bundled fact itself is *much lighter* than
   originally feared (one `≤` on a `Nat`, not a full `⊆`-style closure
   invariant), a direct consequence of the measure correction above.

   **Structure actually implemented** (`NestedDFSTermination.lean`, new
   section `InnerDFSWellFounded`): two definitions, not one, mirroring the
   file's own established fuel/fold split:
   - `innerDFSCore succs fr seed current remaining iv st hcurrent hremaining`
     — the real recursive engine. Takes `current` as **already known-fresh
     and already inserted into `iv`** by its caller (this is what keeps the
     "already finished/already visited" checks to a single place rather than
     once per fold level). `hcurrent : fr.univ.contains current` and
     `hremaining : ∀ x ∈ remaining, x ∈ succs current` are threaded explicit
     hypotheses (erased at runtime, not bundled in the return type — they're
     only ever *consumed*, never *produced*, so there's no circularity in
     passing them as ordinary parameters). `termination_by ((fr.univ \
     iv).size, remaining.length)` — Lean picks up `Prod.instWellFoundedRelation`
     (genuinely lexicographic) automatically for a `Nat × Nat` measure
     expression, no manual `WellFoundedRelation` instance needed.
   - `innerDFSWF succs fr seed current hcurrent iv st` — thin, **non-recursive**
     wrapper matching the original `partial def innerDFS`'s public shape
     (does the top-level "already finished"/"already visited" check once,
     then inserts `current` and delegates to `innerDFSCore`). Named `...WF`
     rather than `innerDFS` as a deliberate staging choice — it lives
     alongside (not yet in place of) `NestedDFS.lean`'s still-`partial`
     `innerDFS`, to avoid forcing `outerDFSLoop`'s signature to change
     before its own conversion (step 2) is actually ready; the rename/swap-in
     happens together with step 2.
2. **`outerDFSLoop` second, using the now-total `innerDFS` as a plain
   helper call — ✅ DONE (2026-07-25), `outerDFSLoopWF`,
   `NestedDFSTermination.lean`, 0 sorry, 0 warnings, whole project still
   builds (394 jobs).** Confirmed exactly as this note predicted: this step
   *is* simpler than `innerDFS`'s. `outerDFSLoopWF` takes `FiniteReach` plus
   two threaded closure hypotheses (`hstack_states`/`hstack_remaining`,
   mirroring `NestedDFSCorrectness.lean`'s `OuterReachClosed.
   stack_remaining_subset` bookkeeping), re-derived structurally at every
   call site — never needing a fact about a *previous* call's *result*, so
   (as anticipated) **no Subtype-bundled return type at all**, unlike
   `innerDFSCore`. Measure: `((fr.univ \ st.outerVisited).size, pendingSum
   stack + stack.length)` — same `\`-based (not `Nat`-subtraction-based)
   design as `innerDFSCore`'s, for the same reason (no `outerVisited ⊆ univ`
   invariant needs to be maintained). `pendingSum` (CAVA's `pending s`) is a
   straightforward `List.sum` over each stack frame's remaining-successors
   length.

   Both structural predictions held: (a) **no fold over siblings** — a
   single, non-branching self-call per branch (four call sites total: leaf
   backtrack × {accepting, non-accepting}, successor × {already-visited,
   fresh}), so there's never a "previous sibling's result" dependency chain
   within one equation; (b) the outer measure depends only on
   `outerVisited`/`stack`, and `innerDFSCore` provably never touches
   `outerVisited` — but *this* fact turned out to need one adjustment from
   the plan: rather than a **separate** lemma
   (`innerDFS_fuel_outerVisited_eq`-style, proved by induction *after* the
   fact), it had to be **bundled directly into `innerDFSCore`'s own return
   type** (as a second Subtype conjunct, alongside the measure-monotonicity
   fact from step 1) — attempting the "separate lemma via
   `innerDFSCore.induct`" route first, Lean's functional-induction-principle
   deriver **failed outright** ("Cannot derive functional induction
   principle... Internal error in `foldAndCollect`") on `innerDFSCore`,
   apparently unable to reduce through the `omega`-generated proof terms
   inside a `Subtype`-returning well-founded definition. Bundling the fact
   at definition time (where the needed local reasoning was already in
   scope from step 1's own proof obligations) sidesteps that limitation
   entirely — a small but real "no free lunch" correction to (b)'s framing:
   the fact was still cheap to get, just not via the *route* originally
   envisioned. With that fact directly available via `r.2.2` at the call
   site (no induction needed), the "accepting leaf, call `innerDFSCore`,
   then recurse" branch's decrease proof never needs anything about
   `innerDFSCore`'s *internal* recursion — only that it returns *some*
   result (guaranteed, already total) and that `outerVisited` is unchanged.
   This is the Lean-native mirror of CAVA gluing blue/red via `nres`
   refinement instead of a joint measure.
3. **Bridge to the existing correctness proofs, instead of re-proving
   them.** `NestedDFSCorrectness.lean` (~2000 sorry-free lines) is proved
   against `innerDFS_fuel`/`outerDFSLoop_fuel`, not the real functions.
   Redoing that whole proof against the new WF-recursive definitions would
   be wasteful. CAVA itself does the analogous thing rather than reprove
   `it_dfs`'s properties from scratch for `it_dfsT`: `WHILET_eq_WHILE_tproof`
   /`it_dfsT_eq_it_dfs` show the total-correctness loop *equals* the
   partial one once termination holds. Our analogue: once `innerDFS`/
   `outerDFSLoop` are total, prove `innerDFS ... = innerDFS_fuel N ...`/
   `outerDFSLoop ... = outerDFSLoop_fuel N ...` for `N` above the already-
   established sufficiency threshold (`innerDFS_fuel_sufficient`, and its
   still-to-be-proved `outerDFSLoop` analogue — note this sufficiency proof
   is now easier too, for the same reason step 2 is: it no longer needs a
   combined bound, just the outer-only measure). Every existing theorem in
   `NestedDFSCorrectness.lean` then transports across this equation for
   free — no proof content needs to be redone, only restated.

   **Verified precisely (2026-07-25), and worth recording exactly**: read
   `Nested_DFS.thy`'s actual top-level theorem, `blue_dfs_correct`, to check
   this bridge-lemma idea against CAVA's own practice, not just against
   `Param_DFS.thy`'s generic machinery in isolation.
   ```isabelle
   lemma blue_dfs_correct:
     assumes NC: "¬ cond s"
     shows "case lasso s of
       None ⇒ ¬(∃v0∈V0. ∃v. (v0,v) ∈ E⁺ ∧ accpt v ∧ (v,v) ∈ E⁺)
     | Some (pr,pl) ⇒ (∃v0∈V0. ∃v.
         path E v0 pr v ∧ accpt v ∧ pl≠[] ∧ path E v pl v)"
   ```
   Its proof (`nc_finished_eq_reachable` + the file's own
   `no_accpt_cycle_in_finish`/`s_lasso_inv`) is stated and proved entirely
   at the abstract "state `s` satisfies `¬cond s`" level — termination-
   agnostic, exactly matching how our `nestedDFS_fuel_empty_no_cycle`/
   `nestedDFS_fuel_nonEmpty_valid` don't need termination either. The
   executable function is separately:
   ```isabelle
   definition "nested_dfs G accpt ≡ do {
     ASSERT (fb_graph G); s ← it_dfs TYPE('a) G accpt; RETURN (lasso s) }"
   ```
   So the precise shape is: **`blue_dfs_correct` itself never invokes
   `it_dfsT_eq_it_dfs`** — the termination bridge is applied one layer
   further out, at `nested_dfs`'s definition/refinement level (`ASSERT
   (fb_graph G)` licenses `param_dfs_variant`'s well-foundedness; a further
   `impl`/`tailrec_impl` refinement layer produces actual generated code).
   The overall shape we want to port still holds — invariant-based
   correctness proved once, termination-agnostic; executability bridged in
   separately, never re-proved against it — but CAVA realizes it as a
   multi-step `nres`-refinement chain (nofail-under-`fb_graph`, then
   `it_dfs`/`it_dfsT` equivalence, then code-level refinement) because
   that's the vocabulary its monadic framework has. We have no such
   refinement calculus and don't need one: a single direct equation
   `innerDFS = innerDFS_fuel N` does the same job as CAVA's whole chain in
   one step, since Lean functions are already "code" — there's no separate
   code-generation refinement layer to route through.
4. **`nestedDFS`** (the public entry point) unwraps `innerDFS`/
   `outerDFSLoop`'s internal `Subtype`/invariant-bundled return values at
   the very end, so its own external signature stays a plain
   `EmptinessResult` and callers don't see `FiniteReach` leak through
   unnecessarily deep — though `nestedDFS` itself does need `∀ i ∈
   initialStates, univ.contains i` alongside `FiniteReach`, matching
   `BlueDFS`'s own locale assumption.
5. **`expand`'s termination is fully independent of 1–4** and can be done
   before, after, or in parallel — a genuine rewrite from
   `partial_fixpoint` to well-founded recursion with the `expand_ord`
   measure (verified above: signature-set superset growth, then `new`'s
   AST-size shrink as tie-break), which risks needing changes to the
   induction principle used throughout `Invariants.lean`/`Bridge.lean`/
   `GraphComplete.lean` (those currently rely on `expand.partial_correctness`).

**Scope estimate (revised 2026-07-25)**: no longer "mutual" well-founded
recursion — `innerDFS` and `outerDFSLoop` are two *independent*
single-measure conversions, chained by an ordinary function call plus (for
step 3) an equality bridge to already-proved fuel-based results. Still a
real undertaking (step 1's subtype-bundled return in particular is a less
common Lean pattern), but meaningfully smaller than the previous "comparable
to Phase 5b's Phases D–F" estimate, since step 3 reuses ~2000 lines of
existing proof rather than redoing it, and step 2 no longer needs invariant
bundling at all. `expand`'s conversion (step 5) is separately scoped and not
smaller just because of this correction. Not started as of 2026-07-25 — this
section records the corrected plan, implementation to follow in a later
session.

---

## Key challenges vs. Isabelle

1. **No refinement framework**: Isabelle's `REC`/`RECT_rule` provides well-founded recursion in a monadic setting. In Lean, we use `partial_fixpoint` + `partial_correctness` induction.

2. **Automation gap**: Isabelle's `auto`/`force`/`blast` vs Lean's `simp`/`omega`/`grind`. Set membership and HashMap fold reasoning required more manual work.

3. **Bridge proofs**: The Isabelle formalization uses refinement to connect abstract specs to implementations. In Lean, we proved explicit bridge theorems (`Bridge.lean`, `DegeneralBridge.lean`) with ~1200 lines of HashMap/HashSet fold reasoning.

4. **Proof size**: The Isabelle formalization is ~3200 lines. Our Lean port is ~8058 lines (larger due to explicit bridge proofs and less automation for set-theoretic reasoning).

5. **No exposed monotonicity fact for recursive calls**: Isabelle's refinement framework
   hands every recursive step an explicit `f x ≤ expand x` fact (`f_sup`) usable via
   `order_trans` to compose already-proven lemmas about `expand` at a recursive call site.
   Lean's `partial_fixpoint`-generated `expand.partial_correctness` only ever gives an
   `expand_ih`-typed equation, with no equivalent bridge back to the real `expand`. The
   workaround (used in `expand_all`, see Phase 4.3 above): bundle `expand node st = some r`
   itself into the induction's motive as an extra conjunct, proven alongside the actual
   property — then it's available via `ih` wherever an external `expand`-based lemma is
   needed on a recursive sub-call.
