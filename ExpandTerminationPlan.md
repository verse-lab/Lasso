# `expand` Termination — Session Findings & Plan (2026-07-25/26)

Companion to `ProofPlan.md`'s `expand`-termination section (kept separate,
mirroring how `NestedDFSPlan.md` accompanied the nested-DFS wiring work,
since this is a large enough sub-effort to warrant its own tracking doc).

**Status: ✅ DONE.** `LTLLib/LTLtoGBA/ExpandTermination.lean` is complete —
`expand_term` (all 8 branches, `decreasing_by` obligations closed) and
`createGraph_term` are both `sorry`-free, and the whole project builds
clean (758 jobs, 0 errors). Sections 1-4 below are the working notes from
getting there (kept as-is, since they're still an accurate record of the
reasoning); §6 records what changed to close it out, and §5's plan is now
fully executed.

## 1. What CAVA actually does (`LTL_to_GBA.thy:836-1229`)

- `expand := REC expand_body` — abstract, possibly-diverging least fixpoint
  (Isabelle's `nres`/CPO theory). `expand⇩T := RECT expand_body` — a
  *separate* definition via `RECT`, a different fixpoint combinator whose
  construction is checked well-founded up front against an explicit measure.
  `expand_eq_expand⇩T` (via the generic library lemma `RECT_eq_REC`) proves
  the two agree once termination is known, letting all downstream reasoning
  use the (much easier to reason about) `expand⇩T`/`RECT_rule` and then
  transport back to the "real" `expand`.
- **Measure** `expand_ord φ := inv_image (finite_psupset (old_next_limit φ)
  <*lex*> less_than) (λ(n,ns). (old_next_pair `` ns, size_set (new n)))`
  - `old_next_pair n := (old n, next n)` — a node's *signature*.
  - `old_next_limit φ := Pow(subfrmlsr φ) × Pow(subfrmlsr φ)` — finite,
    since `subfrmlsr φ` (all subformulas of `φ`) is finite.
  - `finite_psupset A` relates `(X, Y)` with `Y ⊂ X ⊆ A` — i.e. the
    *recursive-call* value is a **larger** subset of a **fixed finite
    universe** than the current value. Well-founded because a subset of a
    finite set can't grow forever. Same idiom as this project's nested-DFS
    measures (`(fr.univ \ iv).size`), just phrased as growth-toward-a-bound
    rather than shrinkage-of-a-complement.
  - `size_set S := Σ_{x∈S} (2·size(x)+1)` (`LTL.thy:519`) — a **weighted
    sum of syntactic formula complexity**, *not* set cardinality. This is
    what makes splitting a compound formula into two syntactically-smaller
    parts (`new1`/`new2`) strictly decrease the sum even though the set can
    grow from one formula to two.
- **Invariant** `expand_inv φ (n,ns)`: `n`'s (and every finished node in
  `ns`'s) `old`/`new`/`next` are all `⊆ subfrmlsr φ`, plus finiteness
  (automatic in Lean, since everything here is a `List`/`Std.HashSet` by
  construction).
- **Per-transition lemma** `expand_inv_impl`: given `ψ ∈ new n` and one of
  three shapes for `n'` (literal-absorb, deterministic-split via `new1`,
  nondeterministic-split-first-half via `new2`), shows `((n',ns'),(n,ns)) ∈
  expand_ord φ`. Crucially, its hypothesis on `ns'` is only
  `old_next_pair `` ns ⊆ old_next_pair `` ns'` (**non-strict**) — the
  strict decrease comes from `size_set(new n') < size_set(new n)`
  (`new1_less_sum`/`new2_less_sum`) alone; whether the primary component
  grew is irrelevant to this lemma's conclusion (Isabelle's `auto` picks
  whichever of "primary strictly grew" / "primary equal, secondary
  strictly shrank" applies).
- **Main theorem** `expand_term_prop`, via `RECT_rule` (Noetherian
  induction dressed as the `SPEC` monad), 8 branches matching
  `expand_body`: merge / fresh-successor / literal-contradiction /
  literal-insert / tt-insert / ff / deterministic / nondeterministic
  (both halves). The **fresh-successor** transition is proved *directly*
  (not via `expand_inv_impl`) from `old_next_pair n ∉ old_next_pair `` ns`
  — itself immediate from "no duplicate found".
- `create_graph_finite`/`create_graph_nofail`: top-level assembly at the
  concrete initial node, giving the ultimate finiteness/non-divergence
  guarantee for the whole construction.

## 2. Where the Lean port *necessarily* diverges from CAVA, and why

### 2a. No `RECT`/`RECT_eq_REC` analogue — direct well-founded induction instead

Lean's `partial_fixpoint` (`expand`'s actual definition mechanism) is
architecturally CAVA's `REC`: both are least fixpoints over a CCPO
(Lean's `Lean.Order`, Isabelle's `nres` theory). But Lean has no `RECT`
layer. `partial_fixpoint`'s generated induction principle
(`expand.partial_correctness`) is Scott/fixpoint induction, which is
*structurally* conditional — `Option.admissible_eq_some : admissible (x =
some y → P)` — it can only prove "if `expand` returns `some y`, then P",
never existence. This is inherent to admissibility (a non-terminating
chain's every finite approximation could fail to reach `some`), not a Lean
gap, and is *exactly* why CAVA itself needs the separate `RECT` layer.

What Lean *does* give unconditionally is `expand`'s own one-step unfolding
equation (`expand.eq_def`, the auto-generated `unfoldThmSuffix` theorem —
see §4 below for why this matters over raw `unfold expand`). That is
enough to prove totality *directly* by well-founded induction on the same
measure, using `termination_by`/`decreasing_by` on a **recursive
`theorem`** (the same lex-pair idiom already used for `innerDFSCore`/
`outerDFSLoopWF` in `NestedDFSTermination.lean`) — entirely avoiding a
separate fuel-indexed mirror function (the nested-DFS playbook). This is a
genuine simplification, found by checking what `partial_fixpoint` actually
offers before assuming the nested-DFS approach would carry over verbatim.

### 2b. A name-freshness invariant CAVA does not need, but this port does

Confirmed by rereading `expand_inv_impl`/`expand_term_prop` closely: **CAVA's
measure and proof never depend on node *names* at all.** `expand_ord`'s
primary component is purely the `(old, next)` *signature* set; `ns : 'a
node set` is a genuine mathematical set of full records. `insert n ns` can
never silently destroy data — Isabelle sets have no notion of "key".

This codebase's `ExpandState.nodes : Std.HashMap Nat (GBANode α S)` is a
**name-keyed map**, not a set of records (a pre-existing design choice in
`Expand.lean`, presumably for O(1) lookup). `st.nodes.insert node.name
node` *overwrites* whatever was previously at that key — something
structurally impossible in CAVA's encoding. If `node.name` were ever
already in use, the insert would silently lose a previously-finished
node's data, breaking both `usedSignatures` monotonicity and the
`expandMeasure1` decrease argument itself (an overwrite can even *drop*
the used-signature count). So a name-freshness invariant
(`st.nodes[node.name]? = none`, propagated through recursion) is a real,
necessary addition — but it is a **representation-compensating patch**,
not a mistranslation of anything CAVA does. It restores, for the
HashMap encoding, a guarantee CAVA's set encoding gets for free.

The fix does not require reinventing this from scratch: Phase 4 already
proved exactly this fact as `ExpandInvariants`/`expand_invariants`
(`Invariants.lean:346-428`, `nameFresh`/`freshInv`/`nameBound`/
`nextNameMono`) — itself proved via `expand.partial_correctness`, i.e.
*conditional* on an already-given `h_result : expand node st = some r`.
Plan: `expand_term` carries the same three input hypotheses
`expand_invariants` needs (`h_not_in`/`h_fresh`/`h_name`), and at the one
place a later call's precondition depends on an *earlier* call's *output*
(the second half of the nondeterministic split — see §3), invoke
`expand_invariants` as a black box on the first call's now-established
`h_result` to extract exactly the freshness fact needed for the second
call. Everywhere else, the three hypotheses carry over unchanged (same
`st`, same `node.name`) or are discharged by the already-public
`insert_fresh_key`/`insert_freshInv` (`Invariants.lean`, un-privatized
this session for reuse — see §4).

### 2c. `IsSubformula`, not `subformulas`-list-membership, for the invariant

Originally built `NodeBounded`/`NodesBounded` using `x ∈
topFormula.subformulas` (a `List` membership fact) with a from-scratch
`Finset.powerset`-based measure. Partway through writing `expand_term`'s
body, found `Invariants.lean` already has a **fully proven** theorem,
`expand_subformula_closure` (lines 997-1138), establishing *exactly* the
old/next boundedness-propagation fact needed here — but phrased via
`NNF.IsSubformula ψ φ_top` (the inductive relation), matching the
vocabulary used throughout the rest of `Invariants.lean`
(`new1_subformula`/`new2_subformula`/`next1_subformula`, all stated over
`IsSubformula`). Its proof (Scott induction, same shape as
`expand_invariants`) walks *every* branch of `expand_body` and, for each,
constructs exactly the per-step facts needed
(`h_head_sub`/`h_tail_sub`/`h_old_insert_sub`, and for the nondeterministic
case, `(new1_subformula h2).trans h_φ_sub` / `(new2_subformula
h2).trans h_φ_sub` / `(next1_subformula h2).trans h_φ_sub`).

Refactored `NodeBounded`/`NodesBounded` to use `NNF.IsSubformula x
topFormula` directly (dropping the `subformulas`-list layer from the
*invariant*), keeping the `Finset.powerset`/`subformulas.toFinset` layer
only where the *measure* genuinely needs a `Finset` (`nodeSignature`/
`signatureUniverse`/`usedSignatures`), bridging the two with the
already-built `IsSubformula.mem_subformulas` at that single point
(`nodeSignature_mem_signatureUniverse`). This means `expand_term`'s own
per-branch boundedness proofs can now **directly mirror**
`expand_subformula_closure`'s existing case-by-case reasoning line for
line (copying the pattern, not calling it as a black box — MY proof
needs these facts threaded through genuine well-founded recursion, for
the measure argument, not just as a post-hoc fact about the final `r`,
so Scott induction's `ih` can't literally serve here; but every
"single-step" `have` in that proof transfers verbatim).

Practical corollary: `oldHas_insert`, `addAllToSet_inv`, `addToNew_inv`
(all `private` in `Invariants.lean`, used internally by
`expand_subformula_closure`'s proof) were un-privatized this session too,
so `ExpandTermination.lean` can reuse them instead of re-deriving.

## 3. Where things stand right now

`ExpandTermination.lean` compiles with **all infrastructure sections at 0
sorry**: subformula-finiteness bridge, weighted-size measure
(`new1_less_sum`/`new2_less_sum`), `NodeBounded`/`NodesBounded`/`ExpandInv`
(now `IsSubformula`-based), `nodeSignature`/`signatureUniverse`/
`usedSignatures`/`expandMeasure1`/`expandMeasure2`, `expandMeasure1_lt`/
`expandMeasure1_le` (measure-decrease lemmas), `weightedSize_addToNew_le`,
`NodesBounded_insert`/`NodesBounded_mergeIncoming`,
`usedSignatures_insert_fresh_subset`/`_insert_matching_subset`,
`findDuplicate_spec_none` (new negative counterpart to the existing
`findDuplicate_spec`), `nodeSignature_fresh_of_findDuplicate_none`.

`expand_term`'s statement (final form):

```
theorem expand_term (topFormula : NNF α) (node : GBANode α S) (st : ExpandState α S)
    (hinv : ExpandInv topFormula node st)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName) :
    ∃ r : Nat × ExpandState α S, expand node st = some r ∧
      usedSignatures st ⊆ usedSignatures r.2 ∧ NodesBounded topFormula r.2
termination_by (expandMeasure1 topFormula st, expandMeasure2 node)
```

Branches done (proven, not `sorry`): **merge** (`node.new = []`, duplicate
found) and **fresh-successor** (`node.new = []`, no duplicate — the one
genuinely recursive, state-changing, primary-measure-decrease branch).

Branches remaining (currently `sorry`): literal-contradiction,
literal-insert, tt-insert, ff, deterministic-split, and the
nondeterministic split's two calls (the one CAVA-nontrivial case, needing
`expand_invariants` as described in §2b). All of these are single- or
double- recursive calls with **unchanged `st`** except the
nondeterministic split's second call — meaning `h_not_in`/`h_fresh`/
`h_name` are simply reused unchanged for every branch except that one
call, and the measure argument reduces to a pure `weightedSize` (secondary
component) decrease via `new1_less_sum`/`new2_less_sum`, exactly mirroring
`expand_inv_impl`'s case 2/3.

## 4. A Lean-specific performance trap hit and fixed (not a CAVA issue)

While writing the merge branch, `rw [expand.eq_def, if_pos h_empty, h_fd];
rfl` inside a `refine ⟨w, ?_, ?_, ?_⟩` (existential witness `w` shared by
sibling goals mentioning `usedSignatures w.2`/`NodesBounded topFormula
w.2`) triggered a `(deterministic) timeout at whnf` even at 4,000,000
heartbeats. Root-caused via scratch-file bisection (not a math problem —
confirmed the *statement* elaborates instantly with `sorry`; only tactic
proof steps were affected):

- **`unfold expand` vs `expand.eq_def`**: `partial_fixpoint` auto-generates
  a real equation lemma (`unfoldThmSuffix = "eq_def"`,
  `Lean/Meta/Eqns.lean:53`) via a *cached*, already-proven unfolding
  (`Lean/Elab/PreDefinition/PartialFixpoint/Eqns.lean`'s `mkUnfoldEq`).
  Using `rw [expand.eq_def]` instead of raw `unfold expand` avoids
  redoing that unfolding's cost from scratch inside every proof — cheap on
  its own either way, so not the actual culprit, but worth keeping as the
  more idiomatic tool (same fix already needed once by `GraphComplete.lean`'s
  `expand_exist_aux`, which carries `set_option maxHeartbeats 800000 in`).
- **Actual root cause**: leaving an application argument as `_` (e.g.
  `usedSignatures_insert_matching_subset st existingName _ target htarget
  ...`) forces Lean to *infer* that argument by unifying the lemma's
  conclusion against the goal — here, against `usedSignatures
  (mergeIncoming st node existingName)`. But `mergeIncoming st node
  existingName` is a `match st.nodes[targetName]? with | some target =>
  {st with nodes := ...} | none => st` expression, and
  `st.nodes[targetName]?` is *stuck* (an opaque local variable, not a
  concrete value) — the match cannot reduce, so unification against `{st
  with nodes := st.nodes.insert k ?n}` has no head symbol to match against
  and falls into pathological backtracking rather than failing cleanly.
- **Fix**: never let unification resolve an implicit against a term that's
  stuck behind an opaque `match`. Instead, first prove the *equation*
  `mergeIncoming st node existingName = { st with nodes := st.nodes.insert
  existingName merged }` explicitly (using the *propositional* hypothesis
  `htarget : st.nodes[targetName]? = some target` via `rw`, which works
  fine on `Prop`-level equalities even when the term itself won't reduce
  definitionally), `set`/name the merged node, then apply the lemma with
  everything concrete. Verified in isolation (scratch `.lean` files) that
  this reduces the same proof from a 4M-heartbeat timeout to ~4 seconds.
  Applying this discipline (explicit `have`s for every equation, never a
  bare `_` next to a `match`-headed term) throughout the remaining
  branches.

This is purely a Lean elaboration-performance lesson, unrelated to any
CAVA modeling decision — flagging here so it isn't mistaken for a
correctness detour if re-read later.

## 5. Plan for finishing (in order)

1. Literal-contradiction (terminal) and literal-insert (single recursive
   call, unchanged `st`) — mirrors `expand_subformula_closure`'s
   `h_old_insert_sub`/`h_tail_sub` pattern directly; measure argument is
   `weightedSize (tail!) < weightedSize node.new` (trivial, since
   `node.new = head! :: tail!`).
2. tt-insert (same shape as literal-insert, `old := insert node.old φ`)
   and ff (terminal).
3. Deterministic split (`and`/`next`, single recursive call, `new :=
   addToNew node' (new1 φ)`) — measure via `new1_less_sum` +
   `weightedSize_addToNew_le`, mirroring `expand_inv_impl` case `n'def:2`.
4. Nondeterministic split (`or`/`until`/`release`, two recursive calls):
   - First call: identical shape/measure argument to the deterministic
     case (same `new1`-based construction).
   - Second call: needs `st.nodes[nm]? = none` where `nm` is the *first*
     call's returned name — obtained via `expand_invariants` applied to
     the first call's `h_result` (see §2b). Measure argument: `new :=
     addToNew node' (new2 φ)`, via `new2_less_sum` +
     `expandMeasure1_le` (non-strict primary, since `st` may have grown
     during the first call) composed with `Prod.Lex.right`/`.left` as
     appropriate — mirrors `expand_inv_impl` case `n'def:3` exactly,
     including CAVA's own observation that the primary-component
     hypothesis there is only ever non-strict.
5. `decreasing_by`: one goal per recursive call above; same
   `Prod.Lex.left _ _ h`/`Prod.Lex.right _ h` idiom already used for
   `innerDFSCore`/`outerDFSLoopWF`.
6. Once `expand_term` is `sorry`-free: derive `createGraph`-level
   finiteness/totality (mirroring `create_graph_finite`/
   `create_graph_nofail`), instantiating `expand_term` at the concrete
   initial node (`name := 1`, `incoming := {0}`, `new := [φ]`, `old :=
   next := ∅`) with trivially-satisfiable freshness hypotheses (empty
   `st.nodes`).
7. Update `ProofPlan.md`'s `expand`-termination section with the final
   completed write-up; this file (`ExpandTerminationPlan.md`) can then be
   folded into a short pointer, matching how `NestedDFSPlan.md` ended up
   once nested-DFS wiring was done.

## 6. How it actually closed out

Steps 1-6 above were executed largely as planned, with two additional
findings surfaced along the way (both now folded into §2 above, not
repeated here) and one more Lean-elaboration trap on top of §4's:

- **`NNF.IsSubformula` refactor**: mid-way through writing the det/nondet
  branches, found `Invariants.lean`'s `expand_subformula_closure`
  (lines 997-1138) already proves — case by case, across all of
  `expand_body` — exactly the boundedness-propagation facts `expand_term`
  needs, but phrased via `NNF.IsSubformula` rather than the
  `subformulas`-list membership `NodeBounded`/`NodesBounded` originally
  used. Refactored to match (§2c in the main write-up above), which let
  every det/nondet branch's invariant proof become a direct copy of that
  theorem's existing reasoning (`(new1_subformula h2).trans hφ_sub` etc.)
  instead of independent derivation. Needed un-privatizing three more
  small helpers (`oldHas_insert`, `addAllToSet_inv`, `addToNew_inv`) that
  `expand_subformula_closure`'s own proof already depended on internally.

- **A second Lean elaboration trap — `matches` sugar generalizing over
  unrelated context hypotheses.** Beyond §4's stuck-`match`-unification
  issue, the `tt`/`ff` branches hit a *different* bug: `by_cases htt : φ
  matches NNF.tt` followed by `rw [if_pos htt]` against `expand`'s own
  (separately-elaborated) `φ matches NNF.tt` condition failed with "did
  not find an occurrence of the pattern" — *even when the printed goal and
  the sought pattern were character-for-character identical*. Isolated via
  a minimal repro (`MatchesTest2.lean` et seq., scratchpad): the moment
  another hypothesis mentioning the same scrutinee (e.g. `hlit : ¬isLiteral
  φ = true`) was in the local context, Lean's `matches`-sugar elaboration
  span spuriously *generalized over that unrelated hypothesis too*,
  producing a differently-shaped underlying match term that merely
  *pretty-prints* the same way. Fix: never `by_cases`/`rw` on a raw
  `matches` proposition once other φ-dependent hypotheses are already in
  scope — use plain decidable equality (`φ = NNF.tt`) for control flow
  instead (immune to this, since it's an ordinary `Eq`, not sugar-compiled),
  and close the resulting goal via `simp only [htt_eq, if_true]` /
  `simp only [htt_eq, hff_eq, Bool.false_eq_true, if_false]` rather than
  `rw [if_pos/if_neg]` — `simp`'s matching isn't syntax-exact the way `rw`
  is, so it isn't tripped up by the same instance mismatch. This is,
  like §4, a pure Lean-tooling lesson with no bearing on the math.

- **One knock-on fix in `GraphComplete.lean`**: un-privatizing
  `addAllToSet_inv`/`fset_fold_cons_mem` in `Invariants.lean` collided
  with GraphComplete.lean's own (older, `private`) copies of the same two
  lemmas — Lean's `private` restricts cross-file *visibility*, not
  same-name *declaration*, so a public and a private declaration of the
  same simple name in the same namespace still clash once both are
  in scope via import. Deleted GraphComplete.lean's duplicates (identical
  statements up to currying) rather than renaming Invariants.lean's; all
  five call sites in `GraphComplete.lean` type-checked unchanged against
  the now-shared public versions.

Final theorem shapes (`ExpandTermination.lean`):

```
theorem expand_term (topFormula : NNF α) (node : GBANode α S) (st : ExpandState α S)
    (hinv : ExpandInv topFormula node st)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName) :
    ∃ r : Nat × ExpandState α S, expand node st = some r ∧
      usedSignatures st ⊆ usedSignatures r.2 ∧ NodesBounded topFormula r.2
termination_by (expandMeasure1 topFormula st, expandMeasure2 node)

theorem createGraph_term (φ : NNF α) :
    ∃ st : ExpandState α S, createGraph φ = some st ∧ NodesBounded φ st
```

Both `sorry`-free. Whole project: 758 jobs, 0 errors, 0 sorry (at the time
this was written; now 759 jobs with `Pipeline.lean` added — see below).

## 7. Where this fits now (2026-07-27)

`createGraph_term` is one of the pieces `Pipeline.lean`'s `fullPipeline`
depends on directly (it's what justifies `fullPipeline`'s `none` branch
being genuine dead code — `createGraph` always succeeds). See `README.md`
and `ProofPlan.md`'s "Track B" section for how this connects to the fully
composed, total, verified LTL satisfiability decision procedure. This file
remains an accurate record of the termination work itself and is not
expected to need further updates unless `expand`'s algorithm changes.
