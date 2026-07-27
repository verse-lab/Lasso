# LTLLib Proof Porting Plan

This document outlines the plan for porting correctness proofs from the Isabelle/HOL [LTL_to_GBA](https://www.isa-afp.org/entries/LTL_to_GBA.html) formalization to Lean 4.

## Current state

- **Track B (end-to-end runnable pipeline) is now fully DONE (2026-07-27)** —
  `LTLLib/Pipeline.lean`'s `fullPipeline` is a genuine, total, verified LTL
  satisfiability decision procedure: `fullPipeline φ = .empty n → ∀ξ,
  ¬(ξ⊨φ)` and `.nonEmpty stem loop → ∃ξ, ξ⊨φ`, both unconditional. This
  closes what Phase 6 originally scoped out as "Track B, future work" — see
  the "Items 2 + 4" write-up under Phase 6 below for the two genuine gaps
  found and closed along the way (a `numAcceptSets = 0` case
  `degeneralize_bridge` never covered, and a missing pumping lemma
  connecting graph-cycle-level to word-level emptiness — CAVA's own
  `accepted_lasso`, which turned out to be needed on our side too, just as
  it is on CAVA's).
- **Build integrity**: `LTLLib.lean` now imports all 23 source files (previously only 13 — see
  "Build-integrity fix" note under Phase 6 below for what that was hiding). A clean rebuild (stale
  `.lake/build` artifacts removed first) succeeds with 0 errors, 0 sorry, 394 build jobs.
- **Phase 2 (Termination) is DONE for nested DFS, fully wired**: both `innerDFS` and `outerDFSLoop`
  are genuinely well-founded-recursive (`innerDFSWF`/`innerDFSCore` and `outerDFSLoopWF`,
  `NestedDFSTermination.lean`, 0 sorry, 0 warnings, 2026-07-25) — converted as two **independent**
  single-measure recursions (not mutual), exactly matching CAVA's own blue/red DFS structure once the
  actual AFP sources were read. Both are bridged (for sufficient fuel) to the pre-existing,
  already-verified fuel-based definitions, and a total top-level `nestedDFSWF` composes them,
  inheriting Phase 5's correctness theorems (`nestedDFSWF_empty_no_cycle`/`nestedDFSWF_nonEmpty_valid`)
  for free — see Phase 2's write-up below for the full design, the fuel-based attempt that was tried
  and abandoned, the CAVA-verified corrected plan, both conversions' own measure-choice write-ups, and
  the final wiring/bridge write-up. **`expand`'s termination is now also DONE** (`ExpandTermination.lean`,
  0 sorry, 2026-07-26) — `expand_term` (well-founded-recursive, mirroring `expand_body`'s 8 branches and
  CAVA's `expand_ord`/`expand_inv_impl` measure exactly) plus `createGraph_term` (totality of the whole
  construction, mirroring `create_graph_finite`); see its write-up below for the full design, including a
  genuine CAVA-vs-Lean divergence (a name-freshness invariant CAVA doesn't need, required here only because
  `ExpandState.nodes` is a name-keyed `Std.HashMap` rather than CAVA's set-of-records) and a couple of
  Lean-elaborator-specific traps (unrelated to the math) hit and fixed along the way.
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
- **2** `partial` functions remain in `NestedDFS.lean` (`innerDFS`, `outerDFSLoop`) — kept
  deliberately, as the abstract reference layer, mirroring CAVA's own choice to keep `nested_dfs`
  around once `nested_dfs_code` exists (see Phase 2's wiring write-up). The verified, total,
  actually-usable entry point is `nestedDFSWF` (`NestedDFSTermination.lean`), not this file.
- `expand` uses `partial_fixpoint` (provides equational rewriting + `partial_correctness` induction)
- **Phase 5 (Nested DFS Correctness) is now fully DONE, both directions** —
  `NestedDFSCorrectness.lean` is sorry-free and unconditionally proves both
  `.empty` result ⟹ no accepting cycle exists (`nestedDFS_fuel_empty_no_cycle`,
  Phase 5b) and `.nonEmpty stem loop` result ⟹ `(stem, loop.tail)` is a
  genuine accepting cycle (`nestedDFS_fuel_nonEmpty_valid`, Phase 5c), and both now transfer to the
  well-founded `nestedDFSWF` too (`nestedDFSWF_empty_no_cycle`/`nestedDFSWF_nonEmpty_valid`, Phase 2's
  wiring). `nestedDFSWF` is a fully verified, terminating decision procedure (given a `FiniteReach`
  witness). `OutputVerify.lean`'s
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

#### Track B: CAVA analysis + detailed roadmap for the 4 items (2026-07-27)

Supersedes the terse note above with a full analysis. Read the actual
CAVA/AFP sources for each of the 4 items directly (fetched from the AFP
GitHub mirror, not from memory): `CAVA_Automata/{Automata,Lasso,Digraph}.thy`,
`CAVA_LTL_Modelchecker/{CAVA_Abstract,CAVA_Impl}.thy`,
`DFS_Framework/Examples/Nested_DFS.thy`, `LTL_to_GBA/LTL_to_GBA.thy`, and
cross-checked each against what already exists in this codebase (not
assumed). Three of the four items turn out to have a close CAVA analogue and
are smaller than the terse note above suggests, because the needed
supporting lemmas already exist in `Bridge.lean`/`Invariants.lean` for other
reasons and just haven't been assembled. One item (constructing a concrete
`ξ`) has **no** direct CAVA analogue at all — the reason why, and the
workaround, are under item 3 below.

**Item 1 — `GBA.WellFormed` (+ a new `BA.WellFormed`)**

*CAVA's approach*: the `gba` locale (`CAVA_Automata/Automata.thy:164-167`,
built on `graph`'s `Digraph.thy:59-64`) requires exactly `V0 ⊆ V` and
`E ⊆ V × V` — literally our `GBA.WellFormed.initial_mem`/`succ_mem`
(`GBA.lean:88-91`), field for field. (`gb_graph` layers on
`finite_F`/`F_ss : gbg_F ⊆ Pow V`, and `gba` itself adds
`L_ss : gba_L G q l → q ∈ V`, but our port never needed those two extra
conjuncts — `degeneralize_bridge`'s `hwf` hypothesis only asks for the
two-field `GBA.WellFormed`, so there's nothing extra to port.) CAVA proves
it almost by definition:
```isabelle
definition create_gba_from_nodes φ qs ≡ ⟨
  g_E = {(q, q'). q∈qs ∧ q'∈qs ∧ name q∈incoming q'}, ... ⟩
lemma create_gba_from_nodes__invar: "gba (create_gba_from_nodes φ qs)"
  apply unfold_locales
  apply (auto intro!: finite_vimageI subfrmlsr_finite injI
    simp: create_gba_from_nodes_def)
```
The reason this is nearly free: `q∈qs ∧ q'∈qs` is baked directly into the
*definition* of `g_E` as an inline filter, so `E ⊆ V×V` unfolds to a
tautology; `unfold_locales; auto` closes the rest without a real argument.

*Why we can't literally copy this*: `buildSuccessors` (`Construction.lean`)
does not filter against `gba.states` inline — it inserts whatever names
appear in each node's `incoming` set, keyed by predecessor name, with no
explicit "and this name is a real state" conjunct built into the
construction the way CAVA's set-builder syntax has it. So the Lean version
needs an actual proof, not a definitional unfold.

*What already exists, found by grep, not written for this purpose*:
`buildSuccessors_mem_iff` (`Bridge.lean:235`):
```lean
theorem buildSuccessors_mem_iff ... :
    q' ∈ (buildSuccessors nodeMap)[q]?.getD #[] ↔
      ∃ node, nodeMap[q']? = some node ∧ node.incoming.contains q = true
```
The forward direction's conclusion, `∃ node, nodeMap[q']? = some node`, *is*
exactly `succ_mem`'s content once `states` is related to `nodeMap`'s keys
(next paragraph) — this lemma exists already only because
`constructGBA_iff_expandOASpec` needed it; nobody has assembled it into a
`GBA.WellFormed` value.

*Plan*:
1. `constructGBA`'s `states := allStates := nodes.fold (init := ∅) fun acc name _ =>
   acc.insert name` (`Construction.lean:107-109`) — prove
   `allStates.contains q ↔ nodeMap.contains q` by a short fold-induction (the
   fold only ever inserts keys it's iterating over — same shape of argument
   as `buildSuccessors_mem_iff`'s own fold-induction skeleton, expect ~10
   lines).
2. Combine with `buildSuccessors_mem_iff` to get `succ_mem`.
3. `initial_mem`: `buildInitialStates` (`Construction.lean:89-92`) only ever
   inserts `node.name` for `node`s obtained by folding over `nodes` itself —
   same "fold only inserts real keys" argument as step 1; may be able to
   generalize a single helper lemma for both `allStates` and
   `buildInitialStates` rather than proving it twice.
4. Package into `constructGBA_wellFormed : (constructGBA φ st).WellFormed`.
5. **New**: `BA.WellFormed` does not exist yet in `BA.lean` (confirmed by
   grep — only `GBA.WellFormed` exists). Add it mirroring `GBA.WellFormed`'s
   two fields exactly, then prove `GBA.degeneralize` (`BA.lean:111-155`)
   preserves it: `degeneralize`'s `succMap`/`allStates` are built by the same
   "fold that only inserts real, in-range names" pattern (`(gbaState, i)`
   pairs for `i < k`, successors computed via `gba.getSuccessors` composed
   with the already-established `succ_mem`), so this should follow the exact
   same proof technique as steps 1-3, not a new argument.
6. Package a `FiniteReach ba.getSuccessors` witness
   (`NestedDFSTermination.lean`'s `FiniteReach` structure, `univ`/`closed`,
   line 111) with `univ := ba.states` and `closed` from the new
   `BA.WellFormed.succ_mem` — this is the prerequisite every downstream call
   to `nestedDFSWF` (item 4) needs.

**Item 1 — ✅ DONE (2026-07-27).** Implemented exactly the 6-step plan above,
verified against a clean rebuild (`.lake/build/lib/lean/LTLLib` removed
first — 758 jobs, 0 errors, 0 sorry, no new warnings). Stayed close to
CAVA's own structure at every step, deviating only where already noted above
(no inline filter to unfold, so a real proof instead of `unfold_locales;
auto`):

1. **`buildStates` factored out** (`Construction.lean`) — the plan's step 1
   needed `allStates.contains q ↔ nodeMap.contains q`, which needs the fold
   itself to be a *named* thing to state a theorem about. Rather than
   proving it about an anonymous `let`-bound expression, factored the inline
   `let allStates := nodes.fold ...` out into a top-level `def buildStates`,
   matching CAVA's own `qs` being an independently-named entity (not
   inlined) and matching this file's own existing style (`buildSuccessors`/
   `buildInitialStates`/`buildLabeling`/`buildAcceptSets` were already
   separate `def`s — `allStates` was the only GBA component that wasn't).
   Purely a factoring — `constructGBA`'s type and behavior are unchanged.
2. **`buildStates_mem_iff`** (`Bridge.lean`, next to `buildSuccessors_mem_iff`/
   `buildInitialStates_correct`) — proved via a new unconditional-insert fold
   helper `HashSet_foldl_insert_contains'` (the no-predicate special case of
   the file's existing `HashSet_foldl_insert_contains`) plus
   `Std.HashMap.contains_eq_isSome_getElem?` to bridge `nodeMap[q]? = some _`
   to `nodeMap.contains q`. ~15 lines, matching the estimate.
3. **`constructGBA_wellFormed`** (`Bridge.lean`, end of file) — assembled
   `buildStates_mem_iff` + `buildSuccessors_mem_iff` +
   `buildInitialStates_correct` + the pre-existing `createGraph_nameConsistent`
   (already used by `constructGBA_toSpec_refines_expandOASpec` for the exact
   same reason), following that theorem's own established idiom
   (`have hname := createGraph_nameConsistent φ hcg` first, then
   `simp only [GBA.isInitial/GBA.getSuccessors, constructGBA] at h` to unfold
   the field access down to the raw `build*` calls). Both `WellFormed`
   fields reduce to one shared `have hcontains` helper.
4. **`BA.WellFormed`** (`BA.lean`) — added verbatim-mirroring
   `GBA.WellFormed`'s two fields, per the plan.
5. **`degeneralize_wellFormed`** (`DegeneralBridge.lean`) — the one step that
   needed genuinely new infrastructure beyond the plan's estimate: proving
   `GBA.degeneralize` preserves well-formedness needs a *states*-membership
   characterization for the degeneralized `BA`'s `.states` field, which
   didn't exist yet (`DegeneralBridge.lean`'s existing double-fold lemmas —
   `degeneralize_initialStates_contains`, `degeneralize_getSuccessors_mem` —
   never needed one, because `BA.toSpec` itself never references `.states`
   at all, only `getSuccessors`/`initialStates`/`isAccepting` — confirmed by
   reading `BA.toSpec`'s definition directly). Added `outer_fold_states_mem`
   (private helper, mirrors `outer_fold_successors`'s double-fold-induction
   template exactly, specialized to `HashSet.contains` instead of `HashMap`
   key lookup) and `degeneralize_states_contains` (the public iff, matching
   the file's existing `degeneralize_*_contains` naming/shape convention).
   `degeneralize_wellFormed` itself then composes cleanly: `initial_mem` from
   `degeneralize_initialStates_contains` + `hwf.initial_mem`; `succ_mem` from
   `degeneralize_states_contains` + `degeneralize_getSuccessors_mem` +
   `hwf.succ_mem`, with `Nat.mod_lt` closing the "counter just advanced"
   case of the resulting `if`. Docstring cross-references CAVA's own
   `degen_invar`-style development (`Automata.thy:800-1130`) as the
   structural analogue, though no specific CAVA lemma was ported line-by-line
   here (CAVA's `degen` invariant-preservation is folded into its generic
   `to_gba`/`to_gbg` locale machinery, not a standalone lemma with a direct
   Lean counterpart).
6. **`BA.finiteReach`/`BA.initialStates_subset_finiteReach`**
   (`NestedDFSTermination.lean`, new `BAFiniteReach` section, after
   `TopLevelFuelBridge`) — thin packaging, exactly as planned: `univ :=
   ba.states`, `closed` directly from `BA.WellFormed.succ_mem`. Matches
   CAVA's `nested_dfs_code`/`ASSERT (fb_graph G)` shape precisely (an
   argument-level assumption, never internally re-derived) — see this
   file's own "Wiring" section above for where that comparison was first
   made for `FiniteReach` in general.

No `GraphComplete.lean`/`Invariants.lean` changes needed — every dependency
(`createGraph_nameConsistent`, `buildSuccessors_mem_iff`,
`buildInitialStates_correct`) already existed from Phase 4.3/Bridge work,
confirming the "already 90% there, just not assembled" assessment above.
Total new code: `Construction.lean` (+8 lines, `buildStates`), `Bridge.lean`
(+50 lines), `BA.lean` (+8 lines, `WellFormed`), `DegeneralBridge.lean`
(+65 lines), `NestedDFSTermination.lean` (+2 lines import, +26 lines new
section) — noticeably smaller than items 2-4, as anticipated by the
execution-order note below.

**Item 2 — connecting `AcceptingCycle` to a genuine witness**

*CAVA's approach*: `Nested_DFS.thy`'s `blue_dfs_correct` (already the source
for our Phase 5b/5c, done):
```isabelle
lemma blue_dfs_correct: "¬cond s ⟹ case lasso s of
    None ⇒ ¬(∃v0∈V0. ∃v. (v0,v)∈E* ∧ accpt v ∧ (v,v)∈E+)
  | Some (pr,pl) ⇒ (∃v0∈V0. ∃v. path E v0 pr v ∧ accpt v ∧ pl≠[] ∧ path E v pl v)"
```
The `Some` branch's raw `(pr, pl)` witness is turned into an actual infinite
accepting run via `CAVA_Automata/Lasso.thy`:
```isabelle
definition run_of_lasso L ≡ lasso_reach L ⌢ (lasso_cycle L)^ω
lemma lasso_accepted: "is_lasso L ⟹ is_acc_run (run_of_lasso L)"
```
and CAVA's own top-level driver (`CAVA_Impl.thy`'s `ndfs_find_ce`, ~line
270) does the repackaging in one line:
```isabelle
RETURN (Some (Some (map_lasso fst (lasso_of_prpl l))))
```
i.e. wrap the raw `(pr,pl)` as a `lasso` record via `lasso_of_prpl`, project
away the degeneralization counter via `map_lasso fst`.

*Mapping to our code — already an almost 1:1 port, just not wired*:
`Lasso.lean` (`lassoRun`, `ValidLasso`, `run_isRun`/`run_isAccepting`) *is*
the existing Lean port of `Lasso.thy`'s `run_of_lasso`/`lasso_accepted`.
Phase 5c's `AcceptingCycle` (`NestedDFSCorrectness.lean:471-487`) is
field-for-field the same shape as `is_lasso_prpl_pre` — compared directly:

| `AcceptingCycle` field | `is_lasso_prpl_pre` conjunct |
|---|---|
| `stem_head_initial` | `v0 ∈ V0` |
| `stem_chain` | `path E v0 pr va` |
| `overlap` | (implicit: `pr`'s last = `pl`'s head) |
| `cycle_chain` | `path E va pl va` |
| `cycle_back` | (wraparound edge, part of `path ... pl va`) |
| `cycle_head_accepting` | `accpt va` |

So the only missing piece is exactly CAVA's one-liner above: instantiate
`OutputVerify.lean`'s hypothesis bundle (currently 8 loose arguments to
`ba_hasAcceptingRun_of_lasso`/`ba_hasAcceptingRun_of_ndfs_output`) from a
real `AcceptingCycle` value, translating `List`/`∈` membership
(`AcceptingCycle`'s vocabulary) into `Std.HashSet.contains _ = true`/
`Array.contains _ = true` (`OutputVerify.lean`'s vocabulary — `BA` stores
`states`/`initialStates` as `Std.HashSet` and `getSuccessors` returns
`Array`).

*Plan*:
1. Add a variant of `ba_hasAcceptingRun_of_lasso` (or overload it) taking an
   `AcceptingCycle ba.initialStates.toList ba.getSuccessors ba.isAccepting`
   value directly, discharging each of the 8 old hypotheses from
   `AcceptingCycle`'s corresponding field via the translation table above —
   purely mechanical (`List.mem_iff_contains`-style rewriting), no new
   mathematics, matching CAVA's own one-line `map_lasso fst ∘ lasso_of_prpl`
   move in spirit (repackaging a witness into a different but
   information-equivalent shape).
2. Note the `initialStates` argument must be `ba.initialStates.toList` (a
   `List`, to match `AcceptingCycle`'s signature) — this requires actually
   calling `nestedDFSWF` with the concrete `BA`'s data, which is the same
   instantiation item 4 needs, so items 2 and 4 should be done together.

**Item 3 — constructing a concrete `ξ` — no direct CAVA analogue, and why**

This took the most digging, because at first glance CAVA's
`abs_model_check` *does* produce a genuine counterexample word. Reading
closer shows it never solves the actual problem we have.

*CAVA's labeling is relational, same as ours* — confirmed directly:
```isabelle
(* Automata.thy:474 *)
igba_L :: "'Q ⇒ 'L ⇒ bool"
(* Automata.thy:173 *)
definition "accept w ≡ ∃r. is_acc_run r ∧ (∀i. L (r i) (w i))"
```
This is structurally identical to our `OASpec.labelCompat`/`OASpec.accepts`
(`Acceptance.lean:39,62-63`) — a compatibility *relation*, not a function.
So CAVA's own automaton layer has exactly the same "which word?" ambiguity
ours does, and never resolves it at this layer either.

*Where CAVA actually gets a concrete word*: one layer up, at the
system-intersection product. `CAVA_Abstract.thy`'s top-level correctness
theorem:
```isabelle
theorem abs_model_check_correct: "...
  | Some (Some r) ⇒ graph_defs.is_run sys r ∧ sa_L sys ∘ r ∉ language_ltlc φ ..."
```
The returned counterexample is a **run of the system** `r`, not a word —
and `sa_L sys : 's ⇒ 'prop set` (a Kripke structure's labeling) is a
genuine **total, deterministic function** on system states, unlike the
automaton's relational `L`. So `sa_L sys ∘ r` is a word "for free," by
function composition, no existence proof needed. `CAVA_Impl.thy`'s
`ndfs_find_ce` confirms this pattern holds all the way down the
implementation stack too — it only ever manipulates **runs**
(`'q lasso`/`'q word`), never manufactures a `'prop set` word from an
automaton state in isolation.

*Why this doesn't carry over*: our project has no system/Kripke-structure
layer at all (checked — grepping `LTLLib/` for anything resembling `sa_L`
or a "system" type turns up nothing). Track B is scoped to checking the
GBA's *own* realizability directly (`constructGBA_correct_weak`'s
`∀ξ, accepts ξ ↔ ξ ⊨ φ`), so there is no deterministic system-labeling
function anywhere to inherit a word from — we are stuck exactly at the
layer CAVA always sidesteps.

*The workaround — genuinely new, but mechanical, not "real math" the way
the terse note above feared*: build our own deterministic per-state
labeling function, playing the role CAVA's `sa_L` plays, using pieces that
already exist for other reasons:
- `Bridge.lean`'s `buildLabeling_pos_correct`/`buildLabeling_neg_correct`
  (`Bridge.lean:394,412`): `pos.contains a ↔ node.oldHas (.prop a)` and the
  `.nprop` analogue for `neg`.
- `Invariants.lean`'s `literal_consistent` (`Invariants.lean:219`):
  `oldHas (.prop a) → ¬oldHas (.nprop a)`.

Chained, these give `pos.contains a → ¬neg.contains a` at every node — i.e.
`pos`/`neg` are always disjoint, for free.

*Plan*:
1. Define `canonicalLabel (labeling : Std.HashMap Nat (HashSet α × HashSet α))
   (q : Nat) : α → Prop := fun a => (labeling[q]?).elim False (fun (pos,_) => pos.contains a)`.
2. Prove `labelCompat q (canonicalLabel labeling q)` unconditionally from the
   two `buildLabeling_*_correct` lemmas plus `literal_consistent` — the
   `pos.contains a → v a` half is definitional; the `neg.contains a → ¬v a`
   half is exactly the disjointness fact above.
3. For any run `σ` over GBA/BA states, `ξ := canonicalLabel labeling ∘ σ`
   gives `runCompatible σ ξ` unconditionally — the literal Lean-side
   construction of what CAVA gets for free from `sa_L sys ∘ r`.
4. Combine with item 2's `AcceptingCycle`-derived run to upgrade
   `∃σ, isRun σ ∧ isAcceptingRun σ` to a genuine
   `ba.toSpec.accepts (canonicalLabel ba.labeling ∘ lassoRun stem cycle _)`.

**Item 3 — ✅ DONE for steps 1-3 (2026-07-27)** (step 4 completed together
with items 2+4 in a later session — see the "Items 2 + 4" write-up below).
Re-read the CAVA sources once more before
implementing (`Automata.thy:173,474` for `igba_L`/`accept`,
`CAVA_Abstract.thy:97-105` for `abs_model_check_correct`'s `sa_L sys ∘ r`)
to confirm the divergence analysis above still holds — it does; CAVA's own
`gba`/`igba` locales never resolve a relational labeling into a concrete
word either, they only ever compose an already-deterministic *system*
labeling with a run. Implemented exactly the 4-step plan (steps 1-3; step 4
folded into item 2's own upcoming work), plus a BA-level corollary that
turned out to be a free byproduct:

1. **`canonicalLabel`/`canonicalLabel_compat`** (`Acceptance.lean`, right
   after `GBA.toSpec`/`BA.toSpec`) — exactly the planned definition and
   proof shape. `canonicalLabel` needed `[BEq α] [Hashable α]` added to its
   own signature (missed in the initial draft — `Std.HashSet α` needs these
   instances just to name the type, not only to call `.contains`).
   `canonicalLabel_compat`'s `hdisjoint` hypothesis was phrased as
   `∀ a, pos.contains a → neg.contains a → False` rather than the plan's
   `pos.contains a → neg.contains a = false` — definitionally the same fact,
   but the `False`-shaped version composes directly with `absurd`-free
   `exact` at the call site instead of needing an extra `Bool` round-trip.
2. **`createGraph_literal_consistent`** (`Bridge.lean`, new subsection right
   after `createGraph_nameConsistent`) — ported `ExpandSpec.literal_consistent`
   (`Invariants.lean`, the *abstract* `NodeData`-level fact, already
   established for `createGraph`'s output via `createGraph_spec`, Phase 3)
   down to a concrete `GBANode` via `ExpandState.liftNode`/
   `liftNode_mem_toNodes` — the exact same "abstract fact → concrete
   `GBANode` fact via `liftNode`" move `Bridge.lean` already uses throughout
   `constructGBA_toSpec_refines_expandOASpec` for other `ExpandSpec` fields,
   just not yet done for `literal_consistent` specifically. (There is a
   *second*, more directly `GBANode`-shaped `literal_consistent` living
   inside `ProcessingInv`/`StateInv`, `Invariants.lean:219` — considered
   using that instead, since it needs no existential-unwrapping through
   `liftNode`, but it's internal, unexported plumbing local to the
   `createGraph_spec` proof itself, not part of the file's public API the
   way `ExpandSpec`/`liftNode` are — reusing the public route kept this
   change self-contained within `Bridge.lean`, no new `Invariants.lean`
   exports needed.)
3. **`buildLabeling_disjoint`** (`Bridge.lean`, right after
   `createGraph_literal_consistent` — *not* right after
   `buildLabeling_neg_correct` where it was first drafted; it needs
   `createGraph_nameConsistent`, defined later in the file, so file order
   forced the later placement) — chains `buildLabeling_pos_correct`/
   `buildLabeling_neg_correct` (both pre-existing) with the new
   `createGraph_literal_consistent` to get disjointness for any
   `createGraph`-produced node's computed `(pos, neg)` pair.
4. **`constructGBA_canonicalLabel_compat`** (`Bridge.lean`, end of file,
   after `constructGBA_wellFormed`) — assembles 1-3:
   `(constructGBA φ st).toSpec.labelCompat q (canonicalLabel (constructGBA φ
   st).labeling q)` for any `q` with a stored node. Deliberately hypothesis-
   based (`hnode : st.nodes[q]? = some node`) rather than universally
   quantified over all `q : Nat` — a fully unconditional version would have
   needed a *reverse* fold-membership direction for `buildLabeling`
   ("`(buildLabeling nodeMap)[q]? = some _ → q` was a real key") that
   doesn't exist yet and isn't needed: any `q` actually reached by a
   `GBA.toSpec.isRun σ` already comes with exactly this `hnode` fact for
   free, via the same `buildSuccessors_mem_iff`/`buildInitialStates_correct`
   existence step `constructGBA_toSpec_refines_expandOASpec` already
   performs — so the run-level `runCompatible` corollary (this file's
   original step 3) needs no strengthening here, just instantiating this
   lemma at each `σ n` using facts item 2's wiring will already have in
   hand.
5. **`degeneralize_canonicalLabel_compat`** (`DegeneralBridge.lean`, right
   after `degeneralize_labeling`) — the BA-level half, and a genuinely free
   corollary: since `(gba.degeneralize).labeling = gba.labeling`
   (`degeneralize_labeling`, pre-existing) and `GBA.toSpec`/
   `BA.toSpec.labelCompat` share the identical `match` shape (just keyed by
   `s.gbaState` on the BA side), `canonicalLabel`-compatibility transports
   across degeneralization for free — no `createGraph`/`constructGBA`
   specifics needed, generic over any `GBA`. This wasn't explicitly listed
   in the original 4-step plan (which left "GBA/BA states" as one bullet)
   but turned out to be worth stating separately once it was clear it needed
   zero new proof content beyond composing two existing facts.

Verified via a genuinely clean rebuild (`.lake/build/lib/lean/LTLLib`
removed first): 758 jobs, 0 errors, 0 sorry, no new warnings. New code:
`Acceptance.lean` (+35 lines), `Bridge.lean` (+55 lines across 3 new
theorems + 1 new subsection), `DegeneralBridge.lean` (+13 lines). Step 4
(combining with item 2's `AcceptingCycle` to reach a genuine
`ba.toSpec.accepts ξ`) remains deferred to item 2, exactly as planned —
`constructGBA_canonicalLabel_compat`/`degeneralize_canonicalLabel_compat`
are the two pieces item 2's wiring will import and instantiate at each
position of the lasso-derived run.

**Item 4 — the composed pipeline `def`**

*CAVA's approach*: `CAVA_Abstract.thy:68-88`, a 3-step monadic chain:
```isabelle
definition abs_model_check ... ≡ do {
  gba ← ltl_to_gba_spec (Not_ltlc φ);
  (Gprod, map_state) ← inter_spec sys gba;
  ce ← find_ce_spec Gprod;
  case ce of ... }
theorem abs_model_check_correct: "abs_model_check ... ≤ SPEC (...)"
  unfolding abs_model_check_def ltl_to_gba_spec_def inter_spec_def find_ce_spec_def
  apply (refine_rcg refine_vcg ...) apply auto done
```
— once each of the three stages' own correctness `SPEC` is separately
established, the composed correctness proof is a single automated
`refine_rcg` call gluing the postconditions together; no new mathematical
content at the composition step itself. `CAVA_Impl.thy`'s `ndfs_find_ce`
(read in full, lines 258-315) does the analogous thing one level down:
given `igb_graph.degeneralize`, `blue_dfs`, and
`lasso_of_prpl`/`map_lasso fst` are each separately correct, composing them
and pushing the witness back up through degeneralization
(`degen.accepted_lasso` → `degen_acc_run_sound`) is again pure composition,
no new argument.

*Mapping to our code*: we have no `inter_spec`/system-intersection stage
(see item 3), so our pipeline is *shorter* than CAVA's full
`abs_model_check` — closer to `create_name_gba_correct` combined directly
with a `find_ce_spec`-shaped oracle (`nestedDFSWF`'s two correctness
theorems). Checked specifically whether the "push the BA-level witness back
up through degeneralization to the GBA level" step (CAVA's
`degen_acc_run_sound`) already exists on our side: **yes** —
`degeneralize_bridge` (`DegeneralBridge.lean`) composed with
`degeneralize_correct` (`Acceptance.lean`, Phase D, already done) already
gives `BA.toSpec.accepts ξ ↔ GBA.toSpec.accepts ξ` directly. This half of
item 4 needs no new lemma at all, just invoking what's already there.

*Plan*:
1. `def fullPipeline (φ : NNF α) : EmptinessResult` — chain
   `createGraph → constructGBA → GBA.degeneralize → nestedDFSWF`, using item
   1's `FiniteReach` witness for the `nestedDFSWF` call (needs `createGraph`
   to have actually succeeded — `createGraph_term`, already done, guarantees
   this: `∃ st, createGraph φ = some st ∧ ...`).
2. Top-level theorem, structurally mirroring `abs_model_check_correct`'s
   composition but written as ordinary Lean `rw`/`exact` chaining (no
   refinement calculus needed on our side, matching the same asymmetry noted
   throughout Phase 2 — Lean functions are already "code," there's no
   separate code-generation layer to route through): chain
   `constructGBA_correct_weak` (GBA ↔ φ, done) + `degeneralize_bridge` +
   `degeneralize_correct` (BA ↔ GBA, both done) + items 1-3's new lemmas
   (`nestedDFSWF_empty_no_cycle`/`nestedDFSWF_nonEmpty_valid`, now
   word-level via item 3) into a single
   `∀φ, fullPipeline φ = .empty ↔ (∀ξ, ξ ⊨ φ)`-shaped theorem.
3. **Wrinkle to watch, not a blocker**: `k = 0` (no Until-subformulas) —
   `GBA.degeneralize` (`BA.lean:112`) clamps `k := if acceptSets.size == 0
   then 1 else acceptSets.size` computationally, but the *abstract*
   `OASpec.degeneralize` (`Acceptance.lean:92`) takes an explicit
   `hk : k > 0` argument keyed on `gba.numAcceptSets` (which could genuinely
   be `0`). `DegeneralBridge.lean` is already sorry-free against this, so
   this case is already handled *somewhere* in the existing 429 lines — just
   needs confirming which lemma covers it and threading the right
   instantiation through, not new proof content.

**Execution order**: item 1 blocks item 4 directly (no `FiniteReach`
witness without it) and also gates item 2 (need `ba.initialStates.toList`
from a well-formed, concretely-instantiated `BA`). Item 3 is fully
independent and can be done any time. Items 2 and 4 are best done together
since wiring `nestedDFSWF` to a concrete `BA` *is* most of item 4's assembly
work. Suggested order: **1 → 3 (parallel-safe) → 2+4 together**.

**Items 2 + 4 — ✅ DONE (2026-07-27), including two genuine gaps found and
closed along the way that weren't in the original 4-item scope.** Followed
the recommended order exactly. Re-read CAVA's sources once more before
writing any code (`Nested_DFS.thy`'s `blue_dfs_correct`, `Lasso.thy`'s
`lasso_of_prpl`/`accepted_lasso`, `CAVA_Abstract.thy`'s `abs_model_check`),
confirmed the analysis above still held, then implemented item 2's plan
essentially as written — but item 4's assembly surfaced two things the
original plan didn't anticipate, both closed rather than deferred (explicit
user decision on each, given both looked like they might need "huge
proofs" per this project's standing instruction to pause and check first).

**Item 2, as planned** — `AcceptingCycle.toValidLasso` (`OutputVerify.lean`):
pure field repackaging from `AcceptingCycle` to `ValidLasso`, exactly
mirroring CAVA's one-line `map_lasso fst (lasso_of_prpl l)` — every field
except `stem_initial`/`cycle_accepting` transfers directly (same `∈`/`=`
vocabulary on both sides), those two need a one-line `Std.HashSet` `List`/
`contains` bridge. Also added the membership induction the plan's item 3
step 4 needs: `AcceptingCycle.stem_states_mem`/`cycle_states_mem`
(`OutputVerify.lean`) — direct analogues of `DegeneralBridge.lean`'s
`run_states_mem`, over `AcceptingCycle`'s explicit list-index chain instead
of an abstract `Nat`-indexed run — and `AcceptingCycle.run_states_mem`,
combining them across `lassoRun`'s own stem/cycle case split.

**Gap found #1 — `numAcceptSets = 0`, closed (`DegeneralBridge.lean`).**
Re-verified before writing item 4's assembly: every one of
`degeneralize_bridge`/`degeneralize_wellFormed`/`degeneralize_states_contains`/
`degeneralize_getSuccessors_mem` requires `hk : gba.numAcceptSets > 0`. This
directly contradicts this file's own earlier note above ("this case is
already handled *somewhere* in the existing 429 lines") — that note was
wrong, unverified speculation; correcting it here. `numAcceptSets = 0`
arises for any formula with no Until-subformula (`prop a`, pure boolean
formulas, `next`-only formulas) — common, not an edge case. Considered the
"`gba' := gba` with `acceptSets := #[gba.states]`, a trivial always-accepting
set" workaround floated when this was first raised, but the *direct* route
turned out cleaner: proved `BA.toSpec.accepts ξ ↔ GBA.toSpec.accepts ξ`
straight from the definitions for `numAcceptSets = 0` (`degeneralize_accepts_zero`),
bypassing `OASpec.degeneralize` entirely — it needs `hk` just to construct
`Fin k`, but at `k = 0` both sides' acceptance conditions are already
trivial (`GBA.toSpec.isAcceptingRun` vacuous over `Fin 0`; the computational
BA's `k = 1` clamp makes *every* state accepting, so `j = 0` always works).
New lemmas, mirroring the `hk`-gated ones one-for-one but fixing `k := 1`
and threading `h0 : gba.acceptSets.size = 0` in place of `hk`:
`mem_computeBASuccs_zero`, `degeneralize_successors_eq_zero`,
`degeneralize_getSuccessors_mem_zero`, `degeneralize_states_contains_zero`,
`degeneralize_wellFormed_zero`, `GBA.isAccepting_zero_of_empty`,
`degeneralize_accepts_zero`. Then two small `dite`-based unifying wrappers,
`degeneralize_wellFormed_any`/`degeneralize_accepts_any`, combine both cases
into single unconditional (modulo `gba.WellFormed`) theorems — what
`degeneralize_wellFormed`/`degeneralize_bridge`+`degeneralize_correct`
"should have been" if `OASpec.degeneralize` didn't need `hk` just to
typecheck. These `_any` wrappers are what the pipeline actually calls.

**Gap found #2 — the pumping lemma, closed (`NestedDFSTermination.lean`,
new `PumpingLemma` section).** `nestedDFSWF_empty_no_cycle`'s conclusion is
graph-cycle-level (`¬∃ AcceptingCycle`), not word-level
(`∀ξ, ¬accepts ξ`) — connecting them needs the *reverse* lasso direction,
CAVA's `gb_graph.accepted_lasso` (`finite reachable ∧ is_acc_run r → ∃
lasso`), which `Lasso.lean` never ported (only the forward direction,
lasso→accepting-run, existed). Checked precisely whether this is really
needed by re-reading `blue_dfs_correct` (graph-cycle-level, like ours — no
gap *there*) versus `find_ce_spec` (CAVA's actual consumed interface,
stated at the *run* level) and `ndfs_find_ce`'s refinement proof, which
explicitly invokes `degen.accepted_lasso` to bridge exactly this gap — so
CAVA needs it too, just one layer further out than `blue_dfs_correct`
itself. Ported it, but via a more concrete route than CAVA's abstract
`limit`/`ipath` machinery: since this project only ever needs it for a
*single* acceptance set (never the general multi-acceptance-set
`igb_graph` case), the argument reduces to a **finite** pigeonhole (sample
`univ.size + 1` accepting-visit indices; two coincide) rather than CAVA's
argument about the infinite limit set. New lemmas: `accIdxSeq` (+ 3 spec
lemmas) builds the increasing accepting-index subsequence via
`Classical.choose`; `exists_dup_of_size_lt` is the pigeonhole itself,
proved by threading an accumulator `HashSet` through the sampled prefix
(reusing `HashSet.size_le_of_subset` for the "no duplicate ever found"
contradiction case); `exists_acceptingCycle_of_run` assembles the two
repeated-index positions directly into `stem`/`cycle` as explicit
`List.range`-mapped segments of the run, checking all 8 `AcceptingCycle`
fields against the two pigeonhole indices `p < q` (`σ p = σ q`, accepting).
Two small `AskUserQuestion` pauses happened before writing either gap's
fix, per this project's standing instruction to check before diving into
proofs that might turn out large — both times the user chose "close it now"
over deferring.

**Item 4 assembly (`LTLLib/Pipeline.lean`, new file)** — `fullPipeline`
chains `createGraph → constructGBA → GBA.degeneralize → nestedDFSWF`
exactly as planned, using `createGraph_term` for totality (the `none`
branch is genuinely dead code, a defensive default). One Lean-specific
snag, unrelated to the math: proving `fullPipeline_eq` (the unfolding
lemma relating `fullPipeline φ` to a concrete `st`) by `simp`/`unfold`
against the definition's own `match hcg : createGraph φ with` failed
repeatedly with a stuck-typeclass or "no progress" error depending on the
exact tactic tried — the same class of "rw through a compiled match" trap
flagged repeatedly elsewhere in this file (Phase 4.3's gotchas, Phase 5's
build-integrity fix). Fixed with the same established workaround: `split`
+ explicit `Option.some.inj` reconciliation between the match's own
freshly-bound state variable and the external one, rather than trying to
rewrite through the compiled match directly. `fullPipeline_nonEmpty_sat`/
`fullPipeline_empty_unsat` then assemble cleanly: `constructGBA_correct_weak`
+ `degeneralize_accepts_any` (GBA ↔ BA, unconditional now) +
`nestedDFSWF_nonEmpty_valid`/`_empty_no_cycle` + item 2's
`AcceptingCycle.toValidLasso`/`run_states_mem` + item 3's
`constructGBA_canonicalLabel_compat`/`degeneralize_canonicalLabel_compat`
(nonEmpty case) + the new pumping lemma (empty case, to rule out a
hypothetical satisfying `ξ` by deriving an `AcceptingCycle` from its
accepting run and contradicting `nestedDFSWF_empty_no_cycle`). Final
theorems:
```lean
theorem fullPipeline_nonEmpty_sat (φ : NNF α) {stem loop : List BAState}
    (h : fullPipeline φ = .nonEmpty stem loop) :
    ∃ ξ : OmegaWord α, NNF.satisfies ξ φ

theorem fullPipeline_empty_unsat (φ : NNF α) {n : Nat}
    (h : fullPipeline φ = .empty n) :
    ∀ ξ : OmegaWord α, ¬ NNF.satisfies ξ φ
```
`fullPipeline` is a genuine, total, verified LTL satisfiability decision
procedure — call it on any `φ`, and whichever branch it returns comes with
an unconditional correctness guarantee, no side hypotheses beyond `φ`
itself. This is what "a fully verified, fully functional... model checker"
(the original framing that kicked off Track B) actually cashes out to,
now that all four items are done.

Verified via a genuinely clean rebuild (`.lake/build/lib/lean/LTLLib`
removed first): 759 jobs (up from 758 — `Pipeline.lean` is new), 0 errors,
0 sorry, no new warnings beyond the pre-existing ones in `GraphComplete.lean`.
New/changed files this session: `OutputVerify.lean` (+~40 lines),
`DegeneralBridge.lean` (+~160 lines across the gap-#1 closure and the two
`_any` wrappers), `NestedDFSTermination.lean` (+~130 lines, the pumping
lemma), `Pipeline.lean` (new, ~115 lines).

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
   them — IN PROGRESS (2026-07-25), significant progress, one isolated
   blocker.** `NestedDFSCorrectness.lean` (~2000 sorry-free lines) is proved
   against `innerDFS_fuel`/`outerDFSLoop_fuel`, not the real functions.
   Redoing that whole proof against the new WF-recursive definitions would
   be wasteful. CAVA itself does the analogous thing rather than reprove
   `it_dfs`'s properties from scratch for `it_dfsT`: `WHILET_eq_WHILE_tproof`
   /`it_dfsT_eq_it_dfs` show the total-correctness loop *equals* the
   partial one once termination holds. Our analogue: once `innerDFS`/
   `outerDFSLoop` are total, prove `innerDFS ... = innerDFS_fuel N ...`/
   `outerDFSLoop ... = outerDFSLoop_fuel N ...` for `N` above the already-

   **Status**: `innerDFS_fuel_fold_eq_innerDFSCore` (`InnerFuelBridge` section,
   `NestedDFSTermination.lean`) — the fold-level half of the inner bridge,
   strengthening the old (now-deleted) `innerDFS_fuel_fold_sufficient_aux` to
   assert *equality* with `innerDFSCore`, not just "returns `some`" — is
   **fully proved, 0 sorry**, for 3 of 4 branches (nil, seed-found,
   already-blocked-skip) directly, and the 4th (fresh successor, recurse)
   modulo one lemma, `innerDFSCore_fresh_eq`, which is currently `sorry`.

   **The blocker, precisely, and how it was root-caused (2026-07-25,
   continued session)**: `innerDFSCore_fresh_eq` needs to show
   `(innerDFSCore ... (succ::rest) ...).1` equals a plain `match` on the
   nested call `(innerDFSCore ... succ ...).1`. The *first* diagnosis
   (dependent `match hr : r.1 with | pat => ⟨value, proof-using-hr⟩`, `hr`
   needed because the `proof` part of each branch used it even though
   `value` didn't) was real but turned out to be only **half the story**.
   `innerDFSCore` was rewritten (see step 1's write-up above, revised) to
   match only on `r.1.1` (the `Option` component alone) and reference
   `r.1.2.1`/`r.1.2.2` directly rather than via a `hr`-bound pattern — this
   *did* eliminate the `hr`-specific dependency. But the exact same class of
   "motive is not type correct" failure **persisted anyway**, for a deeper
   reason: `r.2` (the Subtype's *own* bundled property) is itself stated in
   terms of `r.1`'s projections (`(fr.univ \ p.2.1).size ≤ ...`), so *any*
   attempt to externally rewrite what `r.1` equals invalidates `r.2`'s type,
   regardless of whether a `hr`-binder is involved. Confirmed by trying
   (and failing on) `rfl`, `rw`/`▸`/`generalize`/`rcases h : e with pat`,
   tactic-mode `match h : e with`, rewriting only isolated projections
   (`.1.1` alone, then `.1.2.1`/`.1.2.2` separately — still fails, since the
   `⟨value, proof⟩` pair needs *all three* substituted in one consistent
   step), and `Subtype.ext`-based whole-term rewriting (`r = ⟨(rcyc,riv,rst),
   hrval ▸ r.2⟩`, still fails — the goal's *other* occurrences of the same
   expression aren't tied to this one substitution). This is a genuine,
   deep Lean 4 limitation: a well-founded-recursive definition returning a
   `Subtype` whose property is stated in terms of the *value*'s own
   projections cannot have its unfolded form externally rewritten at all —
   not a proof mistake, a property of how `.eq_def` compiles such
   definitions.

   **Real, validated finding**: while investigating this, root-caused why
   `innerDFSCore.induct` (the auto-derived functional induction principle)
   fails to generate at all (flagged as a Lean elaborator limitation back in
   step 2's write-up). It is **not** caused by the `Subtype` return type in
   general — it is caused specifically by **`omega`-generated proof terms**
   inside `decreasing_by` (confirmed by a minimal reproduction: a
   `Subtype`-returning well-founded definition with the *exact* same shape,
   `decreasing_by` proved via `omega`, fails `.induct` generation with the
   identical `Lean.Omega.Constraint...` "cannot reduce" error; the same
   definition with `decreasing_by` proved via explicit `Nat.le_antisymm`/
   `Nat.le_trans`/`Prod.Lex.left`/`.right` term combinators instead of
   `omega` generates `.induct` successfully). Applied this fix to the real
   `innerDFSCore` (`decreasing_by`'s one remaining `omega` call replaced
   with `Nat.le_antisymm (Nat.le_trans r.2.1 hlt) h'`) — confirmed via a
   direct probe that `innerDFSCore.induct` now generates, with 5 real cases
   (matching the 5 branches: nil, seed-found, blocked-skip, fresh+cycle-found,
   fresh+continue) and genuine, usable induction hypotheses for the
   recursive-call cases. This fix is applied and kept (it's a strict
   improvement, costs nothing) — `innerDFSCore`'s own definition remains
   0 sorry, 0 warnings.

   **Conclusion — the actual way forward**: `innerDFSCore_fresh_eq` as
   currently scoped (an external "unfolding lemma" proved by rewriting
   `.eq_def`'s output) is a dead end for the *reason above* — no amount of
   tactic cleverness fixes it, because the underlying issue is structural,
   not tactical. But `innerDFSCore.induct` genuinely works now. The right
   redesign is to **stop trying to prove a standalone unfolding lemma and
   instead drive `innerDFS_fuel_fold_eq_innerDFSCore` itself via
   `induction ... using innerDFSCore.induct`** (mirroring the 5 real cases
   directly), unfolding `innerDFS_fuel`/`innerDFS_fuel_fold` on the *other*
   side via their own (non-`Subtype`, unproblematic) `.eq_def` — i.e. swap
   which side drives the induction, since `innerDFSCore`'s own induction
   principle now hands over genuine per-case IHs natively instead of
   requiring external "unfold and match" reasoning. This requires `fuel`
   to become universally quantified *inside* the motive (since
   `innerDFSCore.induct` doesn't induct on `fuel` itself) — a real
   restructuring of the existing (3.5-of-4-branches-proved) lemma, not a
   small patch, but with the hard uncertainty now resolved: the tool needed
   to finish this exists and works, confirmed empirically. Not attempted
   yet in this session — this is exactly the kind of "might need to write a
   large proof" moment your CLAUDE.md notes ask to flag before diving in
   further, and this session was already long by the time this was found.
   `innerDFSCore_fresh_eq` is currently `sorry` (isolated, documented) with
   this as its resolution path.

   `outerDFSLoopWF`'s own bridge to `outerDFSLoop_fuel` hasn't been started
   yet and remains deferred until the inner bridge completes, since
   `outerDFSLoopWF` calls `innerDFSCore` and would need the same equation
   (though, per `outerDFSLoopWF`'s own write-up, it may not need anything
   this heavy — it never destructures `innerDFSCore`'s result beyond
   `.1.1`/`.2` in a way that hit this issue, worth re-checking once the
   inner bridge sets the pattern).
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

**Update (2026-07-25, later still): `innerDFSCore` rebuilt as an
explicit-stack loop — the `innerDFSCore_fresh_eq` dead end above is now
moot, superseded by a structural redesign, not a tactic fix.** Asked (by the
user) to re-check *why* the fold-based design couldn't follow CAVA's own
strategy, rather than pushing further into patching it. Re-reading
`Param_DFS.thy`/`DFS_Find_Path.thy` directly (not secondhand) surfaced the
actual answer, missed in the step-1/2/3 write-ups above: **CAVA's red DFS is
not a hand-written recursive function at all.** `Nested_DFS.thy` defines
`red_dfs` as literally `find_path1_restr_spec` (an abstract `SPEC`); its
concrete realization, `find_path1_restr` (`DFS_Find_Path.thy`), is built
from the refinement framework's generic `FOREACHc` combinator:

```isabelle
definition find_path1_restr G P R ≡
  FOREACHc (g_V0 G) is_Inl (λv0 s. do {
    let R = projl s;
    f0 ← find_path0_restr_spec (G⦇g_V0 := g_E G `` {v0}⦈) P R;
    case f0 of Inl _ ⇒ RETURN f0 | Inr (vs,v) ⇒ RETURN (Inr (v0#vs,v))
  }) (Inl R)
```

`FOREACHc`'s termination is a single **generic** fact — "the iteration set
shrinks by one element per step" — proved once for the combinator itself,
completely independent of what the loop body computes (the body here runs a
*whole nested DFS*, `find_path0_restr_spec`, and `FOREACHc` never needs to
know anything about *that* computation's outcome to justify continuing to
the next iteration). Correctness of the threaded accumulator is proved
*separately*, via `FOREACHc_rule`'s Hoare-style invariant-preservation
obligation, which gets to *assume* the invariant as an induction hypothesis
— never mixed into the termination argument. **Both CAVA's blue and red DFS
ultimately reduce to the same generic `param_DFS`/`it_dfs` engine**: one
flat explicit-stack `WHILE` loop, never nested recursive-descent-with-fold.

This is exactly the mechanism our fold-based `innerDFSCore` (steps 1–3
above) was missing, and exactly *why* it hit the Subtype/"motion is not type
correct" dead end: it used genuine nested Lean recursive calls ("descend
into a fresh successor's subtree, then continue the fold over remaining
siblings using the *returned* visited set"), which forces the *next*
recursive call's termination proof to depend on a fact about the
*previous* call's actual return value — a dependency CAVA's algorithm
structure never creates, because it has no nested calls at all, only
single-step transitions on an explicit stack (which is *exactly* how
`outerDFSLoopWF` was already built, from `NestedDFS.lean`'s own original
design — this is *why* that conversion needed no `Subtype` and went
smoothly).

**Fix applied**: `innerDFSCore` rebuilt from scratch as an explicit-stack
single flat loop, structurally identical to `outerDFSLoopWF`: `stack : List
(State × List State)` (deepest/active frame at the head) plus a `pathStack`
mirroring `outerDFSLoopWF`'s own `++[x]`/`.dropLast` bookkeeping — which,
since it always holds exactly the states of the frames currently on
`stack`, doubles as the witness path the moment a successor equal to `seed`
is found (no more "unwind and prepend `current ::`" step needed). Reuses
`outerDFSLoopWF`'s exact measure/`decreasing_by` idioms (`(fr.univ \
iv).size`, `pendingSum stack + stack.length`), already proven to work
there. **No `Subtype`-bundled return type any more** — every recursive
call's termination is justified purely from *local* facts about that call's
own arguments, never from a fact about a sibling/previous call's result.

**Second finding, found while getting the replacement's own
`innerDFSCore_outerVisited_pres` lemma to go through**: even *without* the
Subtype, threading `hstack_states : ∀ p ∈ stack, fr.univ.contains p.1`/
`hstack_remaining` as **proof-carrying explicit arguments** (the design
used for the first attempt at this rebuild) made `rw
[innerDFSCore.eq_def]`/`induction ... using innerDFSCore.induct`
intermittently fail to fire depending on exactly how those proof terms were
phrased at each call site, with no simp/rw/unfold combination proving
reliable across all branches. Root cause: these hypotheses were *never
actually needed for the function's value* — only for justifying
`decreasing_by`'s measure decrease (`fr.closed current hcurrent succ
hsucc_mem`, used solely to derive `hsucc_univ` for `HashSet.sdiff_insert_lt`).
**Fix**: drop them from the signature entirely, and re-derive the one fact
`decreasing_by` actually needs via a plain runtime check —
`if hsucc_univ : fr.univ.contains succ then ⟨descend, uses hsucc_univ
locally⟩ else ⟨defensive fallback: treat as blocked⟩` — a standard "junk
value on out-of-domain input" pattern. The fallback branch is dead code for
any call reachable from `innerDFSWF` (whose `current` is `fr.univ`-closed
under `succs` transitively via `fr.closed`), but its existence means
`innerDFSCore`'s *type* now carries zero proof obligations, so every
later equation-lemma/induction-based proof about it is an ordinary
(non-dependent) one — this is what actually made
`innerDFSCore_outerVisited_pres` provable (`induction ... using
innerDFSCore.induct`, 6 cases, closed by `unfold innerDFSCore; dsimp only;
try simp_all; try (rename_i ih; simpa using ih)` per case — the fold case's
`let st' := {...}` also had to be inlined directly into its recursive call
rather than left as a named `let`, since a `let`-vs-inlined-literal mismatch
was blocking the last case's `exact`/`simpa` closer even after everything
else resolved). `innerDFSWF`, `innerDFSWF_blocked`, `innerDFSWF_fresh`, and
`outerDFSLoopWF`'s call site were all updated to match the simplified
(no-proof-args) signature. Whole project builds clean (394 jobs) with this
rebuild in place; `innerDFSCore`, `innerDFSCore_outerVisited_pres`,
`innerDFSWF`, `innerDFSWF_blocked`, `innerDFSWF_fresh`, `outerDFSLoopWF` are
all 0 sorry.

**What this supersedes**: the old fold-based `innerDFSCore` and its dead-end
`innerDFSCore_fresh_eq` lemma (described in step 3's write-up above) no
longer exist in the file — deleted, not patched. The `InnerFuelBridge`
section's fold-level lemma (`innerDFS_fuel_fold_eq_innerDFSCore`, which
related the *old* fold-shaped `innerDFSCore` to `innerDFS_fuel`) was removed
too, since its statement no longer typechecks against the new stack-shaped
`innerDFSCore` — this needed a **fresh design**, not a port, because it had
to relate two *structurally different* traversal orders (`innerDFS_fuel`'s
recursive-descent-with-fold vs. `innerDFSCore`'s explicit-stack).

**Update (2026-07-25, later still): the fold-level bridge redesigned and
proved — `NestedDFSTermination.lean` is now completely `sorry`-free.**
The redesign (`innerDFS_fuel_chain`, a new auxiliary function) chains
`innerDFS_fuel_fold` calls across an explicit stack of pending frames — the
fuel-side companion to `innerDFSCore`'s own `stack` argument. Its "found"
case needed care: `innerDFS_fuel_fold`'s own "found" result is always
*relative* to its own frame (`current :: suffix`, built by the pre-existing
nested-call wrapping), not the absolute witness path, so `innerDFS_fuel_chain`
carries a `pathStack` (mirroring `innerDFSCore`'s own bookkeeping) and
replaces the leading `current` with the full `pathStack` on propagation —
verified algebraically for both the "descend"/"backtrack" transitions before
implementing, and both checked out exactly.

Bridging `innerDFS_fuel_chain` to `innerDFSCore` (`innerDFS_fuel_chain_eq_innerDFSCore`,
driven by `induction ... using innerDFSCore.induct`, 6 cases matching
`innerDFSCore`'s own branches) surfaced one further, genuine subtlety not
anticipated in the design phase: **fuel bookkeeping across stack frames.**
`innerDFS_fuel_chain` reuses one *uniform* fuel value throughout (matching
how the bridge theorem's own induction keeps `fuel` fixed across all cases
— needed for the induction to even typecheck), but the *actual*
`innerDFS_fuel`/`innerDFS_fuel_fold` semantics genuinely decrement fuel by
one on every "descend into a fresh successor" (confirmed via the
`innerDFS_fuel_fresh` unfolding lemma). Reconciling a uniform fuel value
against the naturally-decremented one needed two more self-contained
lemmas, both added to `NestedDFSTermination.lean`:
- `innerDFS_fuel_add_preserves`/`innerDFS_fuel_fold_add_preserves`: more
  fuel than needed can't change an already-successful result (proved by the
  same fuel/fold mutual-induction template `innerDFS_fuel_mono` already
  uses in `NestedDFSCorrectness.lean`).
- `innerDFS_fuel_exists`/`innerDFS_fuel_fold_exists_aux`: sufficient fuel
  (per `innerFuelMeasure`) *guarantees* success — the existence
  counterpart, resurrecting the *content* of the very first (deleted)
  `innerDFS_fuel_sufficient` from this file's original fold-based attempt,
  now in the mutual-aux style used throughout this section.

Together these let the "fresh push" case show that the uniform-fuel value
`innerDFS_fuel_chain` hands to a pushed frame computes the *same* result as
the naturally-decremented amount the real nested call would have used
(given the decremented amount was already sufficient, which
`innerDFuelMeasure`'s own monotonicity under `iv`'s growth guarantees). A
handful of small helper facts rounded this out: one-step unfolding lemmas
for `innerDFS_fuel`/`innerDFS_fuel_fold`/`innerDFS_fuel_chain` (ordinary
structural/fuel recursion, so these go through by plain
`unfold`/`rw [.eq_def]` reliably, unlike the old fold-shaped `innerDFSCore`),
and `innerDFS_fuel_fold_cyclePath_head`/`innerDFS_fuel_chain_singleton`
(needed to align `innerDFSWF`'s own singleton-stack entry point with
`innerDFS_fuel`'s top-level call in the final composition,
`innerDFS_fuel_eq_innerDFSWF`).

`NestedDFSCorrectness.lean` itself was never touched — still the
fold-shaped `innerDFS_fuel`, still 0 sorry, still ~2000 lines exactly as
before; the entire redesign was scoped to the bridge lemma (plus its
supporting infrastructure) alone, preserving the existing correctness proof
exactly as planned from the start of Phase 2. **Current sorry count in
`NestedDFSTermination.lean`: 0.** Whole project builds clean (394 jobs).

### `outerDFSLoopWF ↔ outerDFSLoop_fuel` bridge — ✅ DONE (2026-07-25, continued)

Completed the same session, after re-checking CAVA's `Param_DFS.thy` once
more before starting (per standing instruction to always re-verify against
CAVA before diverging). Two findings from that re-check, both acted on:

1. **`outerDFSLoopWF` still carried `hstack_states`/`hstack_remaining` as
   proof-carrying arguments** (unlike the already-fixed `innerDFSCore`).
   Re-reading `Param_DFS.thy` confirmed this was the wrong shape, not just a
   style nit: CAVA's own `step : ('v,'es) state_scheme ⇒ ('v,'es) state_scheme
   nres` carries no invariant in its type either — `DFS_invar` is proved as a
   wholly external SPEC-level fact, and `param_dfs_variant_step` takes
   `DFS_invar G param s` only as a *side hypothesis* when proving the
   variant decreases, never as part of `step`'s own signature. Fixed by
   stripping both hypotheses from `outerDFSLoopWF`'s signature entirely,
   replacing the `fr.univ` membership check with a runtime `dite` (mirroring
   `innerDFSCore`'s own `hsucc_univ` check) with a defensive
   "treat as already-visited" fallback branch — dead code under `fr.closed`,
   exactly like `innerDFSCore`'s analogous fallback. The two closure facts
   now live only in the bridge theorem's own hypotheses, exactly as
   `DFS_invar` lives only in CAVA's separate correctness lemmas about `step`.

2. **`outerDFSLoopWF`'s accepting-leaf branch called `innerDFSCore` directly**
   (bypassing `innerDFSWF`'s blocked-check and `iv.insert current` step) —
   pre-existing, from before this session. Two consequences, both fixed:
   - It skipped the "already `innerFinished`" short-circuit that
     `innerDFSWF`/`innerDFS_fuel` both have, diverging from `outerDFSLoop_fuel`'s
     own call (`innerDFS_fuel succs current fuel current innerVisited st`,
     which *does* go through the check internally). Fixed by calling
     `innerDFSWF succs fr current current innerVisited st` instead — this is
     also what makes the bridge reuse `innerDFS_fuel_eq_innerDFSWF` directly
     rather than needing fresh inner-DFS reasoning. Needed one new one-line
     lemma, `innerDFSWF_outerVisited_pres` (thin wrapper around
     `innerDFSCore_outerVisited_pres`), for `outerDFSLoopWF`'s own
     `decreasing_by`.
   - It omitted the `current ::` prepend that `outerDFSLoop_fuel` applies to
     the found `cyclePath` before wrapping it in `.nonEmpty`. Tracing both
     `innerDFS_fuel_fold`'s equations and `innerDFSCore`'s stack-based
     accumulation by hand confirmed `outerDFSLoop_fuel`'s prepend is
     *not* a bug to route around: `outerDFSLoop_fuel_nonEmpty_witness`'s own
     docstring confirms `loop = current :: cyclePath` deliberately carries a
     redundant duplicate at `loop[0]` (`cyclePath` already starts with
     `current`), matching `OutputVerify.lean`'s existing convention of
     indexing the loop from `loop[1]`. Fixed by adding the same prepend to
     `outerDFSLoopWF`'s branch, restoring bit-for-bit agreement with
     `outerDFSLoop_fuel`.

With both fixed, the bridge (`outerDFSLoop_fuel_eq_outerDFSLoopWF`) turned
out exactly as simple as anticipated: `outerDFSLoopWF` and `outerDFSLoop_fuel`
share the same explicit-stack shape from the start (`outerDFSLoop` was never
fold-based, unlike `innerDFS`), so a direct `induction ... using
outerDFSLoopWF.induct` sufficed — no `_chain`-style reindexing function
needed, unlike the inner bridge. `outerDFSLoopWF.induct` produces 7 cases
(one more than `innerDFSCore`'s 6, since the accepting-leaf branch's
`innerDFSWF` call further splits into found/not-found); the 7th
(defensive "successor not in `fr.univ`" fallback) is vacuous given the
bridge's own closure hypotheses, closed via `fr.closed`.

One genuinely new subtlety, flagged and resolved without needing to pause:
`outerDFSLoop_fuel` spends exactly one fuel unit per *loop iteration*
(every recursive call pattern-matches `fuel = _ + 1` and passes the
decremented value on), unlike `innerDFS_fuel`/`innerDFS_fuel_fold` which
only spent fuel on a *descend* — so there is no single closed-form `Nat`
measure playing `innerFuelMeasure`'s role (the iteration count isn't bounded
by `(fr.univ \ outerVisited).size` alone; backtrack/skip transitions leave it
unchanged while still costing fuel). Re-checking CAVA confirmed this is
expected: `it_dfsT_eq_it_dfs` never computes a numeral fuel bound either —
it transports `WHILET` to `WHILE` via `WHILET_eq_WHILE_tproof`, an abstract
well-founded argument keyed on `param_dfs_variant`'s lex order directly, no
step-count formula anywhere. Followed the same approach: the bridge proves
*existence* of a sufficient fuel by induction on `outerDFSLoopWF`'s own
recursion (i.e. on the same lex measure), never a formula in `fuel` — which
is exactly what's needed, since the existing fuel-based correctness theorems
in `NestedDFSCorrectness.lean` (e.g. `nestedDFS_fuel_empty_no_cycle`) already
take an arbitrary implicit `fuel` and assume only *success*, never a lower
bound. Every branch of the induction has exactly one nested computation to
solve for fuel, except the "accepting, cycle not found" branch, which has
two independent ones (the `innerDFS_fuel` call and the "continue with `rest`"
recursive call) sharing the same fuel slot — needed its own new
fuel-monotonicity fact, `outerDFSLoop_fuel_add_preserves` (structural
induction on `fuel`, proved first via a small family of one-step unfolding
equation lemmas mirroring `innerDFS_fuel_blocked`/`innerDFS_fuel_fresh`;
same `conv => lhs; rw [...]`-restricted-to-LHS discipline as before, needed
whenever an equation lemma's RHS also mentions the function being unfolded),
to reconcile the two to a shared value, exactly mirroring
`innerDFS_fuel_add_preserves`'s earlier role in the inner bridge.

**Current sorry count in `NestedDFSTermination.lean`: 0.** Whole project
builds clean (394 jobs). This completes Phase 2's nested-DFS termination
work in full — both `innerDFS` and `outerDFSLoop` are now well-founded,
sorry-free, and proven equal (for sufficient fuel) to the pre-existing
fuel-based definitions whose correctness `NestedDFSCorrectness.lean` already
establishes, so every existing correctness theorem there transfers across
the bridge for free. Remaining Phase 2 scope: `expand`'s own termination
conversion (`partial_fixpoint` → well-founded recursion via an
`expand_ord`-style measure) — separately scoped, untouched by this work.

### Wiring: total `nestedDFSWF` + top-level fuel bridge — ✅ DONE (2026-07-25, continued)

Closes the "finish wiring nested DFS" follow-up: a total, well-founded
top-level entry point, bridged to `NestedDFSCorrectness.lean`'s existing
Phase 5 correctness theorems, so they now hold of a *real, terminating*
function rather than only of the fuel-indexed proof device.

**Checked CAVA first, as instructed, on two separate questions:**

1. **Does `nested_dfs` handle multiple initial states as one fused loop, or
   two nested loops (matching our `nestedDFS_fuel`/`nestedDFS_fuel.go`
   split)?** `Nested_DFS.thy`: `nested_dfs G accpt ≡ do { s ← it_dfs G accpt;
   RETURN (lasso s) }` — a *single* call into the generic `it_dfs` engine,
   which folds root-selection into `step` itself via `get_new_root`/
   `do_new_root` (fired whenever the stack is empty), covered by the *same*
   `param_dfs_variant` measure used for ordinary successor discovery. So
   CAVA's real architecture is one fused loop, not two — our own
   `nestedDFS_fuel`/`nestedDFS_fuel.go` two-loop split (Phase 5, ✅ done,
   ~2000 sorry-free lines) doesn't match this literally. Diagnosed why: it's
   a consequence of not having ported CAVA's generic, reusable `param_DFS`
   locale (a substantially larger undertaking, out of scope), not a
   deviation from the CVWY algorithm itself, which is identical either way.
   Rebuilding `nestedDFS_fuel`/`outerDFSLoop_fuel` to match CAVA's
   single-loop *code shape* would mean reopening and re-proving all of
   Phase 5's already-complete work for a purely organizational gain, so
   `nestedDFSWF` mirrors `nestedDFS_fuel`'s *existing* two-loop shape
   instead — matching the algorithm CAVA proves, not necessarily CAVA's
   specific code organization where that organization is a
   framework-engineering artifact rather than part of the algorithm.
   `nestedDFSWF.go`'s own recursion is *plain* structural recursion on
   `remaining : List State` — no fuel, no well-founded measure needed at
   all; only its one call into `outerDFSLoopWF` per root needs the
   well-founded machinery already built.

2. **Should the old `partial def innerDFS`/`outerDFSLoop`/`nestedDFS` be
   deleted/replaced once `nestedDFSWF` exists?** Checked CAVA's own
   treatment of this exact question: CAVA never deletes its abstract
   `nested_dfs` once the concrete, Autoref-generated `nested_dfs_code`
   exists — both are kept permanently, connected by a refinement theorem
   (`nested_dfs_impl`/`nested_dfs_code.refine`), and `nested_dfs_code`'s own
   precondition is an explicit `ASSERT (fb_graph G)` (finite/bounded graph)
   threaded through as an argument-level assumption, not internally
   re-derived — exactly the role `FiniteReach succs` plays for `nestedDFSWF`.
   So: **not deleted.** `NestedDFS.lean`'s `partial def`s are kept as the
   abstract reference layer (readable, unverified termination), with a new
   docstring pointing to `nestedDFSWF` as the verified, total counterpart —
   mirroring CAVA's own two-layer split precisely, rather than inventing a
   new one.

**What was built** (`NestedDFSTermination.lean`, `TopLevelWF` +
`TopLevelFuelBridge` sections): `nestedDFSWF` (total, mirrors
`nestedDFS_fuel`'s shape per finding 1 above); a `nestedDFS_fuel.go`
one-step-unfolding equation-lemma family plus `nestedDFS_fuel_go_add_preserves`
(fuel monotonicity, mirroring `outerDFSLoop_fuel_add_preserves` — needed for
the same reason: `nestedDFS_fuel.go`'s "continue to next root" and the
`outerDFSLoop_fuel` call it makes share one fuel slot); the main bridge
`nestedDFS_fuel_go_eq_nestedDFSWF_go`, proved by induction on `remaining`
directly (not on `fuel`, not via a `.induct` principle — there's no
well-founded recursion at this level at all, so this is the simplest bridge
in the file); and the top-level `nestedDFS_fuel_eq_nestedDFSWF`, composing
straight through. Two corollaries, `nestedDFSWF_empty_no_cycle` and
`nestedDFSWF_nonEmpty_valid`, transport Phase 5's `nestedDFS_fuel_empty_no_cycle`/
`nestedDFS_fuel_nonEmpty_valid` across the bridge essentially for free —
`nestedDFS_fuel_empty_no_cycle` itself takes an *arbitrary* implicit `fuel`
and only assumes success, no lower bound, so existence of *some* sufficient
fuel (not a closed formula) is exactly what's needed, same pattern as the
outer bridge.

**Current sorry count in `NestedDFSTermination.lean`: 0.** Whole project
builds clean (394 jobs). `nestedDFSWF` + its two correctness theorems are
now the verified, total, actually-usable nested-DFS emptiness check —
callers supply a `FiniteReach succs` witness and get back a result with a
proof obligation-free correctness guarantee, matching CAVA's own
`nested_dfs_code`/`ASSERT (fb_graph G)` shape.

### `expand`'s termination — ✅ DONE (2026-07-25/26, `ExpandTermination.lean`)

Started by reading CAVA's full termination proof (`LTL_to_GBA.thy:836-1229`)
end to end before writing anything, per explicit instruction to understand it
fully first, given the size of the undertaking.

**CAVA's exact strategy** (`expand_ord`, `expand_inv`, `expand_inv_impl`,
`expand_term_prop`, `expand_eq_expand⇩T`, `create_graph_finite`): a lex
measure — primary component `old_next_pair `` ns` (the set of `(old,next)`
signatures already used by finished nodes), ordered by `finite_psupset`
toward the fixed finite bound `Pow(subfrmlsr φ) × Pow(subfrmlsr φ)`; secondary
`size_set (new n) = Σ (2·size(x)+1)` over the node's pending formulas — a
**weighted syntactic-size sum**, not cardinality (an initial misreading,
caught by checking `LTL.thy:519`'s actual definition — weighting each
element is what makes splitting a compound formula into smaller immediate
parts strictly decrease the sum even though the *set* can grow). Proved via
`RECT_rule` (Noetherian induction dressed in the SPEC-monad) against a
*separate* `expand⇩T := RECT expand_body`, bridged back to the abstract
`expand := REC expand_body` via the generic library lemma `RECT_eq_REC`.

**Checked what Lean's `partial_fixpoint` offers before assuming the
nested-DFS fuel-mirror playbook would carry over — it doesn't need to.**
`Lean.Order` (`Init/Internal/Order/`) is architecturally the same idea as
CAVA's `REC` (both least fixpoints over a CCPO), but has no `RECT`/
`RECT_eq_REC` analogue: `partial_fixpoint`'s generated induction principle
(`expand.partial_correctness`, already used ~13 places in this codebase) is
Scott/fixpoint induction, and is *structurally* conditional
(`Option.admissible_eq_some : admissible (x = some y → P)`) — provably
incapable of establishing totality, only "if it succeeds, then P" (the same
reason CAVA itself needs the separate `RECT` layer, not a Lean-specific
gap). What Lean *does* give unconditionally is `expand`'s own one-step
unfolding equation (`unfold expand`, already used throughout
`GraphComplete.lean`) — enough to prove totality *directly* by well-founded
induction on the same measure, without a fuel-indexed mirror function at
all: written as a recursive `theorem` with `termination_by
(expandMeasure1 topFormula st, expandMeasure2 node)` / `decreasing_by`, the
exact same lex-pair idiom already proved out for `innerDFSCore`/
`outerDFSLoopWF`.

**Built so far, all compiling, 0 sorry**: the `Pow(subfrmlsr φ)` universe
ported directly via Mathlib's `Finset.powerset`/`Finset.card_powerset`
(Mathlib is an actual project dependency — `lakefile.toml`, already used in
`Acceptance.lean`/`Soundness.lean` — so no hand-rolled encoding needed); the
`IsSubformula ↔ subformulas`-list bridge (`new1_subformula`/`new2_subformula`/
`next1_subformula` already existed from Phase 4 and needed no changes — only
their target, `subformulas`, needed a fresh finiteness argument via a small
`NNF.fold` monotonicity lemma family); `weightedSize` + `new1_less_sum`/
`new2_less_sum` (Lean's own auto-derived `sizeOf` behaves exactly like
Isabelle's auto-generated `size` — closed by `cases φ <;> simp [...] <;>
omega` per constructor, no surprises); `ExpandInv`/`NodeBounded`/
`NodesBounded` (mirrors `expand_inv` — Lean drops CAVA's explicit
`finite(...)` conjuncts entirely, since `List`/`Std.HashSet`/`Std.HashMap`
are automatically finite); `expandMeasure1`/`expandMeasure2` plus
`nodeSignature`/`signatureUniverse`/`usedSignatures` and their bounding
lemmas; a `findDuplicate`-returns-`none` negative spec
(`findDuplicate_spec_none`, needed since Lean has no automatic negation from
an `if`/`else` split on a `∃`-statement the way CAVA's `expand_inv_impl`
gets one for free) plus a `nodeSignature`/`sameSignature` bridge, giving
`nodeSignature_fresh_of_findDuplicate_none` — the direct analogue of what
CAVA calls inline in `expand_term_prop`'s own case 2.

**Name-freshness gap, resolved — confirmed to be a Lean/HashMap artifact, not
a CAVA requirement.** Writing `expand_term`'s body hit a real gap in the
"fresh successor" case: needs `st.nodes[node.name]? = none`, propagated
through recursion (needed again for the second half of the nondeterministic
split, where the recursed-into node's *name* comes from the first call's own
result). Re-reading `expand_inv_impl`/`expand_term_prop` closely confirmed
**CAVA's own measure and proof never depend on node names at all** —
`expand_ord`'s primary component is purely the `(old,next)` signature set,
and `ns : 'a node set` is a genuine mathematical set of full records, so
`insert n ns` can never silently overwrite/lose data. This project's
`ExpandState.nodes : Std.HashMap Nat (GBANode α S)` is a *name-keyed* map
(a pre-existing `Expand.lean` design choice, presumably for O(1) lookup) —
`st.nodes.insert node.name node` genuinely *can* overwrite a previously
finished node if the name were reused, which would break both
`usedSignatures` monotonicity and the measure-decrease argument itself. So
the freshness invariant is real and necessary, but it's a
**representation-compensating patch**, not a mistranslation of CAVA — it
restores, for the HashMap encoding, a guarantee CAVA's set encoding gets for
free. Resolved as planned: `expand_term` takes the same three hypotheses
`expand_invariants` (`Invariants.lean:346-428`, Phase 4, unchanged) needs,
and at the nondeterministic split's second call — the one place a later
call's precondition depends on an earlier call's *output* — invokes
`expand_invariants` as a black box on the first call's `h_result` to extract
exactly the needed `nameFresh`/`freshInv`/`nameBound` facts. Everywhere else
the three hypotheses just carry over unchanged (same `st`, same
`node.name`) or come from the already-proven `insert_fresh_key`/
`insert_freshInv` (un-privatized from `Invariants.lean` for reuse, along
with `mergeIncoming_preserves_absent`/`mergeIncoming_freshInv`/
`mergeIncoming_nextName`, `oldHas_insert`, `addAllToSet_inv`,
`addToNew_inv`, `fset_fold_cons_mem` — all pre-existing Phase-4 lemmas that
just needed their `private` modifier dropped, not reproving).

**Invariant vocabulary switched from `subformulas`-list membership to
`NNF.IsSubformula`**, matching an existing, fully-proven theorem discovered
mid-session: `expand_subformula_closure` (`Invariants.lean:997-1138`) already
establishes, case-by-case across all of `expand_body`'s branches, exactly the
`old`/`next` boundedness-propagation facts `expand_term` needs — phrased via
`IsSubformula`, the vocabulary `new1_subformula`/`new2_subformula`/
`next1_subformula` already use throughout this file. Refactoring
`NodeBounded`/`NodesBounded` to use `IsSubformula` directly (keeping
`Finset.powerset`/`subformulas.toFinset` only where the *measure* needs a
genuine `Finset`, bridged once via `IsSubformula.mem_subformulas`) let
`expand_term`'s per-branch reasoning mirror `expand_subformula_closure`'s
existing case analysis directly (same `h_old_ins`-style insert-preserves-
bound argument, same `(new1_subformula h2).trans hφ_sub`/`(new2_subformula
h2).trans hφ_sub`/`(next1_subformula h2).trans hφ_sub` composition for the
det/nondet cases) rather than re-deriving it from scratch.

**A Lean elaborator performance/correctness trap, unrelated to CAVA,
root-caused and fixed**: `rw [if_pos h]`/`rw [if_neg h]` against a
`by_cases h : x matches Ctor`-obtained hypothesis intermittently produced
either a `(deterministic) timeout at whnf` (up to 4,000,000 heartbeats) or a
silent "did not find an occurrence" failure, depending on what else was in
local context. Root cause, confirmed via scratch-file bisection: Lean's
`matches` sugar, elaborated in a context where *other* hypotheses mention
the same scrutinee, can spuriously generalize over those unrelated
hypotheses, producing a differently-shaped (but pretty-prints identically)
match term — so two syntactically-identical-looking `x matches Ctor`
occurrences at different call sites are not always the same term. Fix:
never `by_cases`/`rw` on a raw `matches` proposition once other φ-dependent
hypotheses are in scope; use plain `x = Ctor` (decidable equality, immune to
this) for control flow, and close the resulting goal with `simp only
[htt_eq, if_true]`/`simp only [htt_eq, hff_eq, Bool.false_eq_true,
if_false]` instead of `rw [if_pos/if_neg]` — `simp`'s congruence-based
matching isn't affected the same way. Separately, a genuinely expensive
`rfl` (the *original* reported timeout, in the merge branch) was caused by
leaving an application argument as `_` and expecting unification to infer
it by reducing through `mergeIncoming`'s `match` on a *stuck* (opaque local
variable) scrutinee — fixed by proving the `mergeIncoming = {st with ...}`
equation explicitly first (via the `Prop`-level hypothesis `htarget`, which
sidesteps the stuck reduction) and supplying every argument concretely
afterward. Both lessons are pure Lean-elaboration issues, not modeling
detours — see `ExpandTerminationPlan.md` for the full scratch-file
reproduction trail.

**Final state**: `expand_term` (`ExpandTermination.lean`) is a complete,
`sorry`-free, well-founded-recursive `theorem` — all 8 branches (empty-new
merge/fresh-successor; literal-contradiction/insert; tt-insert; ff;
deterministic-split; both halves of the nondeterministic split) plus their
`decreasing_by` obligations, mirroring `expand_body`'s exact structure and
`expand_inv_impl`'s exact case-2/case-3 measure arguments
(`new1_less_sum`/`new2_less_sum`). `createGraph_term` assembles this at the
concrete initial node (mirroring `create_graph_finite`/`create_graph_nofail`)
with trivially-satisfiable freshness hypotheses (`initState.nodes` empty),
giving `∃ st, createGraph φ = some st ∧ NodesBounded φ st`. Whole project
builds clean (758 jobs, 0 sorry, 0 errors) — the only knock-on change was
removing two now-duplicate `private` lemmas from `GraphComplete.lean`
(`addAllToSet_inv`/`fset_fold_cons_mem`) that collided with the
newly-public `Invariants.lean` originals once un-privatized; all of
`GraphComplete.lean`'s call sites work unchanged against the public
versions (identical signatures, just already existed).

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
