# FiniteReach redesign — research record

Status: **DONE — Option B (strict proof-carrying redesign) implemented and
merged into the working tree, 2026-08-07.** `lake build` is clean across the
whole project, zero `sorry`, zero `fr.univ`/`.contains`-style runtime touch
of `FiniteReach`'s data on any executable path (verified by grep — every
remaining `fr.univ` mention in the codebase is inside a docstring describing
the *old* design for historical comparison). Both Schwoon-Esparza and
Holzmann-Peled-Yannakakis optimizations verified behaviorally unchanged: the
two example programs (`Examples/ModelCheckExample.lean`/
`ModelCheckCounterExample.lean`) still produce the correct
counterexample/no-counterexample results after the rewrite. Files touched
beyond the ones scoped in §8.7: `Pipeline.lean` (a downstream consumer of
`nestedDFSWF`/`BA.finiteReach`, discovered mid-implementation, not originally
in the file list — same treatment applied). `veil-dev`'s hand-built
`FiniteReach` is now broken, as expected and intentional (out of scope here,
per explicit instruction). This section and §8 below are kept as the design
record; the rest of this document (§1-§7) is superseded history explaining
*why* Option B was chosen over Option A.

Original status before this session picked it back up: **investigation
complete, no implementation started.** This document
captures everything found so far so the work can resume without re-deriving
it. Two viable design options are laid out at the end; no decision has been
made between them yet.

## 1. The problem

`LTLLib/EmptinessCheck.lean:76-79` defines:

```lean
structure FiniteReach {State : Type u} [BEq State] [Hashable State]
    (succs : State → Array State) where
  univ : Std.HashSet State
  closed : ∀ s, univ.contains s → ∀ t ∈ succs s, univ.contains t
```

Every caller of `modelCheck` (`LTLLib/ModelCheck.lean`) must construct a
concrete `FiniteReach` for their own system — meaning materializing a
`Std.HashSet` containing literally every state reachable from their initial
states. For large state spaces this is a real memory burden the caller
should not have to pay, especially since the whole point of the on-the-fly
`Product` construction (`Product.lean`) is to *avoid* ever materializing the
full product graph — `FiniteReach.univ` was quietly reintroducing exactly
the eager-enumeration cost that design was supposed to sidestep, just one
level down (the system's own reachable set, not the product's).

The original ask: can `FiniteReach` be changed so a caller only proves
*existence* of such a universe, never supplies a concrete witness?

## 2. First-pass analysis (mine, before delegating research)

My first read: `fr.univ` is not merely a proof-obligation field, it is
genuinely touched by the *executable* algorithm in
`LTLLib/NestedDFS/NestedDFSTermination.lean`:

- `innerDFSCore` and `outerDFSLoopWF` each contain a runtime check
  `if h : fr.univ.contains succ then <explore> else <fallback: treat as
  blocked>` (lines ~257, ~1044).
- Both use `termination_by ((fr.univ \ iv).size, ...)` (lines ~268, ~1051).

I initially believed a `Nat`-typed `termination_by` measure is *not* erased
at runtime in Lean 4 — that Lean's well-founded-recursion compiler
recognizes `Nat`-valued measures and compiles them via `WellFounded.Nat.fix`
(`Init/WF.lean`), a genuinely computable fuel-based fixpoint that **calls
the measure function at runtime**. This turned out to be correct *in
general* but **wrong for this specific code** — see §4.3 below, where a
dedicated Plan agent caught and corrected this. The measures here are
`Nat × Nat` tuples, not bare `Nat`, and tuples don't hit that fast path.

The user then made a sharper observation directly: given a *legitimately
constructed* `FiniteReach` (closed + `∀ x ∈ initialStates, fr.univ.contains
x`), every state actually reached during traversal is provably in
`fr.univ` by induction on `fr.closed`. So the `.contains` check's `else`
branch is **dead code**, not just "usually true" — and this is explicitly
acknowledged in the file's own docstring
(`NestedDFSTermination.lean:219-236`, "No proof-carrying arguments"):

> "The membership facts (`current`/`succ ∈ fr.univ`) are only ever needed
> *locally*, to justify the `decreasing_by` measure — they were never
> needed for the function's own *value* computation. So instead of
> threading them as hypotheses, they're re-checked with a plain runtime `if
> fr.univ.contains …` and a defensive fallback (treat as blocked) on
> failure... For any call reachable from `innerDFSWF`... the fallback
> branch is dead code; it exists purely so the *type* of `innerDFSCore`
> carries no proof obligations at all, making every later equation/
> induction-based proof about it an ordinary (non-dependent) one."

Crucially, this same docstring records that an **earlier draft did try**
threading the membership fact as a dependent hypothesis argument instead of
a runtime check, and it was abandoned:

> "**No proof-carrying arguments** (revised again, same day, after the
> first plain-return version still proved fragile to `rw`/`induction ...
> using .induct`-based external reasoning about calls with dependent
> `hstack_states : ∀ p ∈ stack, …`/`hstack_remaining` hypotheses in their
> argument list — `rw [innerDFSCore.eq_def]` intermittently failed to fire
> depending on how those proof terms were phrased at the call site, and
> `exact`-based defeq never bridges well-founded recursive calls at all, so
> *any* dependent argument threading here becomes a recurring tax on every
> future lemma)."

So: the dead branch is real, but removing it re-opens a design fight this
codebase already lost once.

Given this, the goal set for the redesign is to move away from the runtime
fuel/fallback mechanism entirely and replace it with proof-carrying
arguments, even if that ripples into larger changes across previously
completed proofs. Concretely: track that every element pushed onto the
stack belongs to some finite, closed universe, but have `FiniteReach`
certify that such a universe *exists* rather than require the caller to
hand over a concrete witness for it. The target end state is that
`FiniteReach.univ` is not touched on any executable path of
`NestedDFSTermination` at all — with a full analysis of what that implies,
including a look at how CAVA's Isabelle development handled the analogous
problem.

This triggered three parallel research agents plus a Plan agent, in plan
mode. Their full findings follow.

## 3. Research agent findings (verbatim synthesis)

### 3.1 Agent 1 — full map of `FiniteReach`/`.univ`/`.closed` usage

**Direct answers to two specific sub-questions:**
1. `EmptinessChecker.check`'s signature (`EmptinessCheck.lean:119-120`)
   literally requires `FiniteReach succs` as a positional argument:
   `check : (succs) → FiniteReach succs → (isAccepting) → List State →
   EmptinessResult State`.
2. `nonEmpty_valid`/`empty_no_cycle` (`EmptinessCheck.lean:123-133`) are
   Prop-level but *do* name `.univ` directly, via an explicit hypothesis
   `(∀ x ∈ initialStates, fr.univ.contains x)`.

**`LTLLib/EmptinessCheck.lean`**
- L76-78: `structure FiniteReach` definition.
- L119-120: `EmptinessChecker.check` field type — executable-path
  signature every algorithm implementing this interface must accept.
- L123-125, 130-132: `nonEmpty_valid`/`empty_no_cycle` — proof-only,
  Prop-level hypotheses/statements referencing `fr.univ.contains`.

**`LTLLib/NestedDFS/NestedDFSTermination.lean`**

Executable path (def bodies / `termination_by` / `decreasing_by`):
- L238-273 `innerDFSCore`: L257 `if hsucc_univ : fr.univ.contains succ
  then ... else` fallback branch (dead per docstring); L268
  `termination_by ((fr.univ \ iv).size, ...)`; L272 `decreasing_by` uses
  `hsucc_univ`.
- L284-293 `innerDFSWF`: thin wrapper, threads `fr` through.
- L385-386 `innerFuelMeasure` (private def, proof-bookkeeping only):
  `fr.univ.size - iv.size`.
- L1000-1064 `outerDFSLoopWF`: L1044 same dead-runtime-check pattern;
  L1051 `termination_by ((fr.univ \ st.outerVisited).size, ...)`; L1063
  `decreasing_by` uses `_hsucc_univ`.
- L1588-1607 `nestedDFSWF`/`.go`: threads `fr` through.
- L1862-1867 `nestedDFSChecker : EmptinessChecker State`: executable glue.
- L1891-1893 `BA.finiteReach`: **constructs** a `FiniteReach` with
  `univ := ba.states` — this is where the "enumerate the whole state
  space" cost is *actually* incurred today, but note `ba.states` is small
  (bounded by LTL formula size), never the expensive half.

Proof-only (heavy `fr.univ.contains`/`fr.closed` usage, all Prop-level):
- L299-395, L587-770 (`innerDFS_fuel_fold_exists_aux`,
  `innerDFS_fuel_exists`, `innerDFS_fuel_chain_eq_innerDFSCore` — bridge to
  the separate fuel-based track in `NestedDFSCorrectness.lean`).
- L836-963 (`innerDFS_fuel_eq_innerDFSWF` region).
- L1325-1542 (`outerDFSLoop_fuel_eq_outerDFSLoopWF` bridge).
- L1735-1846 (`nestedDFS_fuel_go_eq_nestedDFSWF_go`,
  `nestedDFS_fuel_eq_nestedDFSWF`, `nestedDFSWF_empty_no_cycle` L1824-1831,
  `nestedDFSWF_nonEmpty_valid` L1835-1843) — the file's **top-level**
  correctness theorems; `hinitial : ∀ x ∈ initialStates, fr.univ.contains
  x` is a required hypothesis here.
- L1898-1900 `BA.initialStates_subset_finiteReach`.
- L2043-2054 `exists_acceptingCycle_of_run` — pigeonhole/cardinality
  argument via `fr.univ` (L2054 `exists_dup_of_size_lt fr.univ`).

**`LTLLib/NestedDFS/NestedDFSCorrectness.lean`**
Does **not** reference `FiniteReach`/`.univ`/`.closed` anywhere in actual
code (one docstring mention only, L710). This entire file's
`innerDFS_fuel`/`outerDFSLoop_fuel`/`nestedDFS_fuel` machinery is a
self-contained, `Nat`-fuel-parameterized, totally independent track, used
purely as the correctness-transport device the `NestedDFSTermination.lean`
bridge proofs lean on.

**`LTLLib/Product.lean`**
- L107-125 `Product.finiteReach` (executable): builds a `FiniteReach` for
  the product graph via `hashSetProd sysFR.univ (ba.finiteReach
  hbawf).univ` — a real runtime full-enumeration of the cross product of
  both state sets, including the caller's (potentially huge) `sysFR.univ`.
- `hashSetProd`/`hashSetProd_mem` (L79-90): support def/lemma; `hashSetProd`
  itself is executable (full enumeration), `hashSetProd_mem` is proof-only.

**`LTLLib/ModelCheck.lean`**
- L81 `modelCheck` signature: `(sysFR : FiniteReach sysSucc)` — required,
  executable-path argument, the caller-supplied pre-materialized witness.
- L87 body: passes it into `Product.finiteReach`, triggering the full
  product-`HashSet` construction above.

**Examples** (`ModelCheckExample.lean`/`ModelCheckCounterExample.lean`):
manually construct a small literal `FiniteReach` for a 3-state demo system
— executable, illustrative only.

**`ProbMC/`**: no `FiniteReach`/`.univ`/`.closed` references anywhere.

### 3.2 Agent 2 — CAVA Isabelle source correspondence

No `.thy`/AFP/Isabelle source is vendored anywhere reachable from this
repo (checked repo-wide, `.lake/packages/lentil`, `.lake/packages/mathlib`
— all empty/no hits). However, `ProductModelChecker.md` and `ProofPlan.md`
at the repo root **quote extensive excerpts directly** from the AFP GitHub
mirror, explicitly sourced ("fetched directly from the AFP GitHub mirror").
These quotes are sufficient to answer the question.

**Finding: `fb_graph` is a pure `ASSERT`-style Prop precondition, never
materialized or queried by generated code.**

```isabelle
definition find_path1_restr_spec G P R ≡ do {
  ASSERT (fb_graph (graph_restrict G R)); SPEC (find_path1_restr_pred G P R) }
```
(`ProofPlan.md:1497-1499`, quoting `DFS_Find_Path.thy`) — `fb_graph` gates
entry into the `nres` monad's `SPEC`; discharged once, as a proof
obligation, never referenced again downstream. Same pattern for
`nested_dfs`'s entry point: `ASSERT (fb_graph G); s ← it_dfs G accpt;
RETURN (lasso s)` (`ProofPlan.md:1822`, `:2213`), and at the
product-automaton level: `ASSERT (sa sys); ASSERT (finite ((g_E
sys)⇧* `` g_V0 sys))` (`ProductModelChecker.md:272-273,360-364`).

**Finding: the termination measure is a proof-layer object, never a
runtime-computed quantity.** The generic engine's measure
(`Param_DFS.thy`, quoted `ProofPlan.md:1481-1483`):

```isabelle
definition "param_dfs_variant ≡ inv_image
  (finite_psupset reachable ×lex× finite_psubset ×lex× less_than)
  (λs. (dom (discovered s), pending s, length (stack s)))"
```

A lexicographic well-founded relation over `(discovered, pending, stack)`.
The bound on the first component comes from `fb_graph`'s `finite
reachable` hypothesis — but `reachable` itself is **never computed**; it
only appears inside `finite_psupset reachable`, a well-foundedness
argument discharged once (`param_dfs_variant_wf`), then consumed by
`WHILET_eq_WHILE_tproof` to convert the nondeterministic `WHILET` loop into
an ordinary deterministic `WHILE` loop with *proven* (not checked)
termination. Isabelle's code generator then extracts that
already-proven-terminating loop as ordinary ML/Haskell — **no fuel, no
decreasing counter, no "universe" witness is threaded through the
generated code at runtime.**

The only genuinely materialized runtime data is `discovered`/`dom
(discovered s)` — the algorithm's own growing visited-set (Autoref-refined
to a hash table for `nested_dfs_code`) — functionally analogous to this
repo's `iv`/`outerVisited`, i.e. the algorithm's *own* bookkeeping, never a
separately-materialized stand-in for the finiteness assumption itself.

Additionally: blue/red DFS are proved **independently terminating**, glued
only via `nres`-refinement monotonicity — no combined runtime-measure
question at all (`ProofPlan.md:1490-1519`).

### 3.3 Agent 3 — Lean 4 `termination_by` computability mechanics

**Question asked:** can a `termination_by` measure be `noncomputable`
(classically derived) while the surrounding `def` stays fully computable —
i.e. is the well-foundedness machinery erased at compile time?

**Answer: it's complicated — depends on which of two elaboration paths is
taken**, determined by `isNatLtWF`
(`Lean/Elab/PreDefinition/WF/Fix.lean:236-246`):

- **Path A — bare `Nat`-valued measure.** `elabWFRel` synthesizes a
  `WellFoundedRelation β` instance for the measure codomain `β`
  (`Rel.lean:57-69`); when `β = Nat`, this resolves to `Nat.lt_wfRel`, and
  `mkFix` emits `WellFounded.Nat.fix` (`Fix.lean:259-260`) — a genuinely
  computable, fuel-based definition (`Init/WF.lean:481-486`) that
  **literally calls the measure function `h x` at runtime** to compute
  fuel ("this fixpoint operator reduces on closed terms... when `h x`
  evaluates to a ground value"). **If `h` is noncomputable, this reference
  is not erased — the compiler refuses to generate code and demands
  `noncomputable def`.**
- **Path B — non-`Nat` / custom `WellFoundedRelation`.** `mkFix` instead
  builds generic `WellFounded.fix α motive rel wf`, wrapped via
  `Lean.opaqueId` (`Fix.lean:264`) to block unfolding. `WellFounded.fix`
  itself is `noncomputable` — but `Init/WFComputable.lean` supplies a
  `@[csimp]` swap `fix_eq_fixC : @fix = @fixC` (`WFComputable.lean:94`)
  to a fully computable replacement whose recursion is driven purely by
  `Acc.recC`'s structural unfolding of the (erased, proof-irrelevant)
  accessibility witness — **the relation/measure never gets evaluated as
  data, only referenced inside a `Prop`.** In this path a classical
  measure/witness, so long as it appears only inside the `Prop`-valued
  relation or `WellFounded` proof (never fed to `Nat.fix` as data), is
  fully erased and does not infect the `def`.

**Practical implication:** to keep a `def` computable while using a
classically-justified measure, the measure's *codomain* must not be a bare
`Nat` (avoid the `Nat.lt_wfRel` fast path) — use a custom
`WellFoundedRelation`/`Acc` proof instead. `decreasing_by` proofs are
unaffected either way (`solveDecreasingGoals` only ever produces `Prop`
obligations, erased regardless of path).

**Mathlib precedent:** no existing example found of a classically-derived
measure feeding `termination_by` directly (grepped
`.lake/packages/mathlib` for `Classical`/`Nonempty.some`/`Classical.choose`
co-located with `termination_by`) — the idiomatic pattern is Path B
(opaque `WellFounded`/`Acc` proofs on custom relations), not a classical
`Nat`.

## 4. My synthesis after the three agents

- CAVA's `finite_psupset reachable`-based measure is exactly a Path-B-style
  custom well-founded relation (strict superset order on `discovered`,
  bounded by mere *existence* of a finite `reachable`) — not a `Nat` size.
  This is the CAVA-faithful target shape for any Lean redesign.
- `FiniteReach` could become a `Prop`-level existence statement
  (`∃ univ, closed univ`, or similar) without needing `Classical.choice`
  anywhere in the *existing proof-only* call sites — ordinary
  `Exists.elim`/`obtain` suffices whenever the surrounding goal is itself a
  `Prop` (which all the proof-only usages listed in §3.1 are). Classical
  reasoning would only be needed, if at all, inside a one-time
  well-foundedness proof for a new custom relation.
- The one open question I could not resolve without a dedicated design
  pass: does deleting the `.contains` runtime check plus swapping to a
  Path-B custom relation actually require **zero** new proof-carrying
  arguments through the recursion (my hope), or does something about the
  existing correctness-proof shape implicitly depend on the deleted
  check's evidence? I delegated this specifically to the Plan agent below,
  asking it to verify rather than assume.

## 5. Plan agent's findings (the decisive report)

*(Full agent report preserved verbatim/near-verbatim below — this is the
most load-bearing part of this document.)*

### 5.1 Two corrections to the stated premise

**5.1.1 The "`Nat`-typed `termination_by` forces `Nat.fix`" claim does not
apply to this file's actual measures.** `isNatLtWF` only takes the
`WellFounded.Nat.fix` fast path when the measure codomain `β` is *literally*
`Nat`. `innerDFSCore`'s `termination_by ((fr.univ \ iv).size, pendingSum
stack + stack.length)` (`:268`) and `outerDFSLoopWF`'s analogous clause
(`:1051`) are both **`Nat × Nat` tuples**, not bare `Nat` — `β` unifies to
`Nat × Nat`, the `isDefEq β (mkConst Nat)` check fails, and elaboration
falls to Path B (`WellFounded.fix`, erased). Confirmed empirically via
`set_option pp.all true in #print foo._unary` on a minimal repro showing
`@WellFounded.fix`, not `@WellFounded.Nat.fix`. **So today's
`termination_by` clauses do not evaluate `(fr.univ \ iv).size` at runtime.**
`innerFuelMeasure` (`:385-386`) is a red herring for this concern too —
referenced only inside `theorem` statements (Prop, erased), never as an
actual `termination_by` measure anywhere.

**5.1.2 The real, correctly-diagnosed problem is the `dite` checks, not the
measure.** What genuinely touches `fr.univ` at runtime is the ordinary
`dite` inside each function's *returned-value* computation
(`innerDFSCore:257`, `outerDFSLoopWF:1044`) — the chosen branch is part of
what the compiled function actually does, so `fr.univ` must exist and be
queried on every step. This is the real target; the underlying memory
complaint (materializing all reachable states up front) is completely
valid.

### 5.2 Central finding: full elimination is not a small gap

**Claim tested:** can the `dite` fallback be deleted and termination proved
via a custom Path-B `WellFoundedRelation` derived from mere existence,
*without* threading any new proof-carrying argument through the recursion?

**Answer: no — and this is structural, not a missed trick.**

Walking through the "push a fresh successor" branch after deleting the
`dite`: `decreasing_by` must prove the new visited-set is smaller, in the
new well-founded order, than the old one. Any well-founded order able to
bound growth at all must be some variant of "strict superset, bounded by a
fixed finite set `reach`" — i.e. `rel a b` must entail `a ⊆ reach`. To
discharge `rel iv' iv` *locally*, the proof needs, at that exact call site,
the fact `succ ∈ reach`. There are exactly three ways to obtain that fact
locally, at a `decreasing_by` proof site:

1. **A decidable local check** (the `dite` being deleted) — the mechanism
   by which the needed fact is obtained *for free*, with no argument
   threading. Once `FiniteReach` is a bare `Prop` with no decidable
   membership test, this is categorically unavailable — you cannot build
   executable control flow (an `if`/`dite` whose branch is part of the
   computed value) out of a classical/`Prop`-only fact without making the
   function `noncomputable`.
2. **A threaded proof-carrying hypothesis argument** (e.g. `hstack_states :
   ∀ p ∈ stack, Reachable … p.1`) — exactly the design this file's own
   docstring records as **already tried and abandoned** (§2 above), not
   hypothetically fragile but *actually* hit: `rw [innerDFSCore.eq_def]`
   "intermittently failed to fire depending on how those proof terms were
   phrased," and "`exact`-based defeq never bridges well-founded recursive
   calls at all."
3. **A universally-quantified, call-independent fact** (`∀ s t, t ∈ succs s
   → rank t < rank s` for some global ranking) — phraseable without
   per-call threading since it doesn't depend on call history, *but*
   requires **every** edge in `succs` — including ones in totally
   unreachable parts of a possibly-infinite `State` type — to respect a
   global well-founded rank. This is strictly stronger than CAVA's own
   `fb_graph`/"reachable-from-initials is finite," and is false for
   perfectly legitimate systems (e.g. `SysState := Nat`, `sysSucc n :=
   #[n+1]` for `n ≥ 100`, with a finite reachable loop on `{0,1,2}` —
   finitely reachable from initials, but with an infinite unreachable
   chain elsewhere in the type). Not acceptable to silently impose on
   callers.

This tracks how Lean's `decreasing_by` obligations are scoped: locally, per
syntactic recursive call, from that call's own bare arguments and
case-split hypotheses only (confirmed by reading `solveDecreasingGoals` in
`WF/Fix.lean`) — never from an externally-proven global invariant unless
that invariant is threaded as a local hypothesis (option 2). There is no
third way to get "a global invariant, proven once, available for free at
every call site" given how Lean's WF-recursion elaborator works.

*(I additionally considered, independently, whether hand-rolling the
recursion via manual `Acc.rec`/`WellFounded.fix` invocation — indexing the
recursion over `(state, ghost-proof)` pairs rather than a named argument —
could sidestep this. I believe this is the same idea in different clothes
(subtype/sigma-based recursion), likely to hit the same equation-lemma/
induction fragility, possibly worse since it's hand-rolled rather than
elaborator-assisted. Not independently verified via a spike.)*

### 5.3 Recommended resolution: relax "zero data" to "zero *enumerated*
data"

The actual stated pain is about **enumeration**, not "any data field
whatsoever." Recommended redefinition:

```lean
structure FiniteReach {State : Type u} (succs : State → Array State)
    (initialStates : List State) where
  isReachable  : State → Bool
  initial_mem  : ∀ i ∈ initialStates, isReachable i = true
  closed       : ∀ s, isReachable s = true → ∀ t ∈ succs s, isReachable t = true
  finite       : {s : State | isReachable s = true}.Finite   -- Prop-level only
```

Properties:
- Keeps `innerDFSCore`/`outerDFSLoopWF`'s `dite` mechanism **unchanged in
  shape**, mechanically substituting `fr.isReachable succ` for
  `fr.univ.contains succ`. `termination_by` stays the same `Nat × Nat`
  shape, already erased per §5.1.1 — **no rework of the ~1500 lines of
  fuel-bridge proof machinery** needed on that account.
- Directly kills the memory problem: a caller with, say, a bounded counter
  state writes `isReachable := fun s => s.counter < bound` (O(1), no
  allocation) and proves `finite` with a short Mathlib lemma — **no
  `Std.HashSet` of all reachable states is ever built.**
- Drops the `BEq`/`Hashable`/`LawfulHashable` requirement on `State` from
  `FiniteReach` itself.
- Large-but-mechanical diff: most of the §3.1 map becomes a find-and-
  replace from `fr.univ.contains`/`fr.closed` to `fr.isReachable … =
  true`/`fr.closed`.
- Does **not** satisfy the fully literal requirement ("never supplying a
  concrete witness" / "zero use of FiniteReach's data in any executable
  code path") — `fr.isReachable` genuinely is called at runtime, just
  cheaply and without materialization.

Folding in `initialStates` (confirms my §4 synthesis, with one correction):
recommend **not** parameterizing the `FiniteReach` *structure* by
`initialStates` at the level that would require threading it as a new
argument through `innerDFSCore`/`outerDFSLoopWF`'s ~15 call sites — instead
have `innerDFSCore`/`outerDFSLoopWF`/etc. take `{initialStates}` implicit,
inferred from `fr`'s own type at each call. `EmptinessChecker.check`
reorders to `(succs) → (initialStates : List State) → FiniteReach succs
initialStates → (isAccepting) → EmptinessResult State`. This lets
`nonEmpty_valid`/`empty_no_cycle`/`nestedDFSWF_empty_no_cycle`/
`nestedDFSWF_nonEmpty_valid`/etc. **drop** the now-redundant `(∀ x ∈
initialStates, fr.univ.contains x)` hypothesis entirely (implied by
`fr.initial_mem`).

**Mathlib tooling confirmed available** for this design:
- `Set.Finite.wellFoundedOn (hs : s.Finite) : s.WellFoundedOn r`
  (`Mathlib/Order/WellFoundedSet.lean:529`, needs `[IsStrictOrder α r]`) —
  usable if a genuinely custom `WellFoundedRelation` is ever wanted (not
  required under this design, since `termination_by` stays as today).
- `Set.ncard_lt_ncard`, `Set.encard_diff`/`encard_diff_add_encard_of_subset`
  (`Mathlib/Data/Set/Card.lean:198,809`) — `Set`-level analogues of
  `HashSet.size_lt_of_ssubset`/`size_le_of_subset` for the new proofs.
- `Set.Infinite.exists_ne_map_eq_of_mapsTo (hs : s.Infinite) (hf : MapsTo f
  s t) (ht : t.Finite) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y`
  (`Mathlib/Data/Set/Finite/Basic.lean:873`) — a direct, much shorter
  replacement for the file's hand-rolled `exists_dup_of_size_lt`
  (`NestedDFSTermination.lean:1974-2020`, ~47 lines) — apply with `s :=
  Set.univ ℕ`, `f := fun k => σ (accIdxSeq … k)`, `t := {s |
  fr.isReachable s = true}`. Should shrink the `PumpingLemma` section.
- `Set.Finite.finite_subsets`/`Set.Finite.prod` — useful for
  `Product.finiteReach`'s finiteness argument.

### 5.4 File-by-file plan under the recommended design

| File | Change size | Risk | Notes |
|---|---|---|---|
| `EmptinessCheck.lean` | small | low | Do first; sets the contract everything else follows |
| `NestedDFS/NestedDFSTermination.lean` §`*WellFounded` (defs) | small | low (medium-high if pursuing strict redesign instead) | Mechanical `.contains`→predicate swap; termination proofs untouched |
| `NestedDFS/NestedDFSTermination.lean` §Fuel bridges (~1000 lines) | **large** | medium | Dominant cost; pervasive but mechanical `HashSet.size`→`Set.ncard` substitution |
| `NestedDFS/NestedDFSTermination.lean` §PumpingLemma | medium | low | Net simplification via `Set.Infinite.exists_ne_map_eq_of_mapsTo` |
| `NestedDFS/NestedDFSTermination.lean` §BAFiniteReach | small | low | `ba.states` stays concrete/cheap |
| `NestedDFS/NestedDFSCorrectness.lean` | **none** | — | No `FiniteReach` dependency at all |
| `Product.lean` | medium | low-medium | `hashSetProd` deleted outright; genuine memory win; drops `[LawfulBEq SysState] [LawfulHashable SysState]` requirement on this path |
| `ModelCheck.lean` | small | low | Signature-only (`sysFR : FiniteReach sysSucc sysInit`) |
| `Examples/*.lean` | small | low | Becomes *simpler* than today (see below) |

Details by file:

- **`EmptinessCheck.lean`**: replace `structure FiniteReach` with the
  predicate form; reorder `EmptinessChecker.check`; drop the redundant
  hypothesis from `nonEmpty_valid`/`empty_no_cycle`.
- **`NestedDFSTermination.lean` defs**: `fr : FiniteReach succs` →
  `fr : FiniteReach succs initialStates` (implicit `initialStates`); every
  `fr.univ.contains x` → `fr.isReachable x = true`; `fr.closed` calls
  unchanged in shape; `termination_by`/`decreasing_by` **unchanged**.
- **Fuel bridges**: every `hiv`/`hstack_states`/`hfin`-style hypothesis
  (`fr.univ.contains x`) becomes `fr.isReachable x = true`; `fr.closed`
  calls unchanged in shape; `innerFuelMeasure` (`fr.univ.size - iv.size`)
  can be **deleted outright** rather than reformulated — per §5.1.1 it was
  never actually used as a real `termination_by` measure, only as
  proof-phrasing scaffolding; replace its role with `Set.ncard`-based
  reasoning per the Mathlib lemmas above. Flagged as the dominant cost:
  expect to touch essentially every lemma in these ~1000 lines, though
  induction templates and case splits carry over unchanged.
- **`BAFiniteReach`**: `BA.finiteReach` becomes `isReachable :=
  ba.states.contains`, `closed` unchanged in shape, `finite` a one-liner
  (`ba.states` is a concrete, small `HashSet`).
- **`PumpingLemma`**: net *simplification* via the Mathlib pigeonhole
  lemma replacing the hand-rolled 47-line version.
- **`Product.lean`**: delete `hashSetProd`/`hashSetProd_mem` outright;
  `Product.finiteReach`'s `isReachable := fun (s, q) => sysFR.isReachable s
  && ba.states.contains q` — no cross-product materialization at all,
  cheap regardless of `sysFR`'s cost; `finite` via `Set.Finite.prod` +
  `Set.Finite.subset`.
- **`ModelCheck.lean`**: `sysFR : FiniteReach sysSucc` → `sysFR :
  FiniteReach sysSucc sysInit`. A caller with e.g. `SysState := Nat × Nat`
  (two bounded counters) now supplies `⟨fun (a,b) => a < 100 && b < 100,
  by …, by …, by …⟩` instead of enumerating/hashing 10,000 states. A
  caller whose reachable set is shaped by runtime data (not a static
  bound) supplies a structural `isReachable` test plus whatever
  `Set.Finite` argument fits their domain — strictly more expressive than
  today's forced full enumeration.
- **Examples**: `lightFR` becomes, e.g., `isReachable := fun _ => true`,
  `finite := Set.toFinite _` (free, since `Light` is a `Fintype`) — simpler
  than today's manual `Std.HashSet` literal.

### 5.5 What's not achievable as scoped

Requirement 2 read fully literally ("zero use of `FiniteReach`'s data...
never inside a `def`'s computed VALUE") is not achievable without either
(a) a genuinely uncertain research spike re-attempting proof-carrying-
argument threading (already tried and abandoned once in this exact
codebase), or (b) requiring a strictly-stronger global well-founded ranking
over all of `State` that would reject legitimate finitely-reachable
systems. Recommendation: relax requirement 2 to "zero
*enumeration/materialization*" and adopt the predicate-based design — it
delivers the memory win, is `fb_graph`-faithful in spirit (predicate +
finiteness-of-image, matching CAVA's own phrasing), and confines the real
cost to a large-but-mechanical rewrite rather than an open-ended
proof-engineering risk on the core recursive definitions.

If the strict version is pursued anyway, scope it as an isolated,
standalone spike first: a minimal WF-recursive toy function taking a `∀ x,
P x → …`-style hypothesis argument (mirroring `innerDFSCore`'s shape one
level down), to establish whether `.eq_def`/`.induct`-based reasoning can
be made to work reliably in this Lean version, *before* committing the
~2000-line `NestedDFSTermination.lean` proof suite to it.

## 6. The two options, side by side

### Option A — Predicate-based `FiniteReach` (recommended)

- **What it is**: `FiniteReach` becomes `isReachable : State → Bool` +
  `initial_mem`/`closed` (unchanged shape) + a `Prop`-level `finite :
  {s | isReachable s = true}.Finite` certificate. See §5.3 for the exact
  structure and §5.4 for the file-by-file plan.
- **What it achieves**: eliminates all *enumeration*/materialization of
  the reachable-state universe. A caller with a cheap structural test
  (bounds check, tag check, etc.) never builds a `Std.HashSet` at all.
  CAVA-`fb_graph`-faithful in spirit.
- **What it does not achieve**: does not eliminate the runtime `.contains`-
  style check inside `innerDFSCore`/`outerDFSLoopWF` — `fr.isReachable
  succ` is still called on every step, just cheaply (no hash-table lookup
  against a huge materialized structure).
- **Size/risk**: large-but-mechanical, concentrated in ~1000 lines of fuel-
  bridge proofs in `NestedDFSTermination.lean`; low-to-medium risk
  throughout, since the induction/case-split *shape* of every touched proof
  survives, only the specific `HashSet`-vs-`Set` lemmas change. `Product.
  lean`, `ModelCheck.lean`, `Examples/*` are small, low-risk, and the
  examples actually get simpler.
- **Not touched at all**: `NestedDFSCorrectness.lean` (zero `FiniteReach`
  dependency, confirmed by grep).

### Option B — Strict proof-carrying redesign

- **What it is**: literally satisfy "zero use of FiniteReach's data in any
  executable path" by threading a dependent membership-proof argument
  (e.g. `hstack_states : ∀ p ∈ stack, Reachable succs initialStates p.1`)
  through `innerDFSCore`/`outerDFSLoopWF`'s recursive calls, replacing the
  `dite` check entirely, and proving termination via a genuinely custom
  Path-B `WellFoundedRelation` (e.g. strict-superset order on the visited
  set, well-founded by classical/`Exists`-elimination reasoning from
  `FiniteReach`'s bare existence — no witness ever touched by the compiled
  function).
- **Why it's hard**: this is *exactly* the design this codebase's own
  earlier draft attempted and abandoned
  (`NestedDFSTermination.lean:219-236`) — not a hypothetical risk but a
  previously-hit wall (`rw [innerDFSCore.eq_def]` failing intermittently
  depending on proof-term phrasing; `exact`-based defeq not bridging
  well-founded recursive calls). See §5.2 for the full three-option
  structural analysis of why there's no way around threading *something*
  locally at each `decreasing_by` site.
- **What it would require, concretely, to even attempt safely**: per the
  Plan agent's recommendation, first build an **isolated toy spike** — a
  small WF-recursive function one level simpler than `innerDFSCore`, taking
  a `∀ x, P x → …`-style dependent hypothesis argument through its
  recursive calls, and confirm `.eq_def`/`.induct`-based reasoning about it
  is tractable in this Lean version (4.28.0) *before* committing the
  ~2000-line `NestedDFSTermination.lean` proof suite to the same pattern.
  This spike itself is unscoped work — no size/risk estimate exists yet
  because it depends entirely on whether the spike succeeds.
- **If the spike succeeds**: full rewrite of `innerDFSCore`/
  `outerDFSLoopWF`'s argument shapes (dependent types), and consequently of
  essentially all downstream proofs in `NestedDFSTermination.lean` that
  currently do equation/induction-based reasoning about their recursive
  structure (the ~2000 lines flagged throughout §3.1/§5.1), *plus* the same
  downstream propagation into `Product.lean`/`ModelCheck.lean`/`Examples`
  as Option A, but with the extra complexity of proof-carrying-argument
  shapes rather than a flat predicate swap.
- **If the spike fails**: back to Option A, having spent the spike's cost
  to confirm it.
- **Genuine benefit over Option A if it works**: literally zero runtime
  touch of any `FiniteReach`-derived data, not even a cheap predicate call
  — matches the fully literal original requirement and CAVA's `ASSERT`-only
  purity exactly.

## 7. Resuming this work (superseded by §8 — decision made)

~~To pick this back up: decide between Option A and Option B (or commission
the Option-B spike first, as a bounded precursor decision). If Option A:
start with `EmptinessCheck.lean` per §5.4's dependency order. If Option B:
start with the isolated toy spike described above, independent of the main
codebase, before touching `NestedDFSTermination.lean` at all.~~

**Decision made: Option B, in full, no fallback to Option A.** See §8 for
the concrete design and file-by-file implementation plan. This section is
kept for history; §8 is the authoritative next-steps document.

## 8. Decision and finalized design — Option B (strict proof-carrying redesign)

Status as of this write-up: **design complete, implementation not started.**
This section is self-contained — a future session can execute directly from
here without re-reading §1-§7, though those sections remain useful history
for *why* Option A was rejected.

### 8.1 The decision

Pursue Option B in full: `FiniteReach` becomes a pure existence certificate
(`Prop`, no data fields at all), and — critically — **no `FiniteReach`-derived
data is touched on any executable path, not even a cheap predicate call.**
This applies throughout: `innerDFSCore`, `outerDFSLoopWF`, `BA.finiteReach`,
`Product.finiteReach`, `ModelCheck.modelCheck`. This matches CAVA's own
`ASSERT (fb_graph G)`-once-at-entry discipline exactly (confirmed via the
AFP-derived quotes in `ProofPlan.md`/`ProductModelChecker.md` — see §8.2).

**Out of scope, explicitly:**
- The two existing optimizations in `outerDFSLoopWF` — the
  **Holzmann-Peled-Yannakakis shortcut** (inner DFS may return to any state
  on `pathStack`, not just the seed) and the **Schwoon-Esparza back-edge
  shortcut** (`pathStack.contains succ` detects a cycle directly, without
  launching an inner DFS) — are both already CAVA-faithful, confirmed present
  in the current code (labeled by name in comments and in four dedicated
  unfolding lemmas `outerDFSLoop_fuel_back_edge_skip/current_acc/succ_acc`/
  `_push`). Neither touches `fr.univ`. Both must survive this change
  completely unchanged in logic — only mechanically re-threaded where they
  touch the stack's element type (see §8.4).
- LTLLib's two-loop `nestedDFS`/`innerDFS` split (vs. CAVA's single fused
  `param_DFS`/`it_dfs` engine with inner DFS as an abstract `nres` oracle,
  glued only by refinement-monotonicity) is a previously-accepted, documented
  architectural deviation. **Not being revisited here.** This change is
  scoped strictly to eliminating `FiniteReach`'s runtime data touch.
- Mathlib use is **not** restricted in this design (an earlier-session
  constraint to minimize Mathlib dependence no longer applies) — use it
  freely wherever it makes a proof easier, e.g. `Set.Finite`/`Set.ncard`
  machinery below.
- Any breakage to downstream consumers outside this repo (e.g. `veil-dev`,
  which hand-builds a `FiniteReach` the current way) is expected and
  intentional — this redesign is *supposed* to break that call site; fixing
  it is separate, later work and not a concern for this change.

### 8.2 CAVA correspondence (confirmed via fresh research this session)

- `fb_graph` is asserted once, at entry, never touched again:
  `ASSERT (fb_graph G)` in `nested_dfs`'s own definition, and
  `ASSERT (fb_graph (graph_restrict G R))` at the red-DFS oracle's entry
  (`find_path1_restr_spec`). At the product/top level:
  `ASSERT (finite ((g_E sys)⇧* `` g_V0 sys))` — critically, this is finiteness
  of the **canonical reachability closure** (reflexive-transitive closure of
  the edge relation from the initial vertices), not an arbitrary
  caller-named closed superset. This directly motivates §8.3's `Reachable`
  design below.
- The termination measure never evaluates the finiteness witness as data:
  `param_dfs_variant ≡ inv_image (finite_psupset reachable ×lex× ...) (λs.
  (dom (discovered s), pending s, length (stack s)))` — `reachable` appears
  only inside a well-foundedness argument (`finite_psupset reachable`),
  discharged once, never touched by the extracted/generated code. The only
  genuinely materialized runtime data is `discovered`/`dom (discovered s)` —
  the algorithm's own growing visited-set, functionally this repo's
  `iv`/`outerVisited`, which stay exactly as they are today; this redesign
  does not touch them.
- Blue/red DFS composition (single fused engine, `nres`-refinement gluing) is
  architectural and out of scope per §8.1.

### 8.3 The new `FiniteReach`

```lean
-- EmptinessCheck.lean, replacing the current `structure FiniteReach`

/-- Canonical graph reachability from a set of roots, mirroring CAVA's
`(g_E)⇧* `` g_V0` exactly. -/
inductive Reachable {State : Type u} (initialStates : List State)
    (succs : State → Array State) : State → Prop where
  | base {i : State} (hi : i ∈ initialStates) : Reachable initialStates succs i
  | step {s t : State} (hs : Reachable initialStates succs s) (ht : t ∈ succs s) :
      Reachable initialStates succs t

/-- Bare existence certificate — CAVA's `finite ((g_E sys)⇧* `` g_V0 sys)`
verbatim. No data fields; nothing here can ever be "touched" on an
executable path because there is nothing to touch. -/
def FiniteReach {State : Type u} (initialStates : List State)
    (succs : State → Array State) : Prop :=
  {s | Reachable initialStates succs s}.Finite
```

A bare `def`, not a one-field structure — `Set.Finite` already carries the
needed Mathlib API (`.subset`, `.prod`, `.insert`, …). `Reachable.base` makes
"every initial state is reachable" free (a constructor application), so the
current `(∀ x ∈ initialStates, fr.univ.contains x)` hypothesis on
`EmptinessChecker.nonEmpty_valid`/`empty_no_cycle` disappears entirely rather
than being reformulated — same for `BA.initialStates_subset_finiteReach` and
`exists_acceptingCycle_of_run`'s `hinitial` parameter.

`EmptinessChecker.check`'s argument order changes so `initialStates` is bound
before `FiniteReach` needs it: `(succs) → (initialStates) → FiniteReach
initialStates succs → (isAccepting) → EmptinessResult State`.

### 8.4 Frame encoding for `innerDFSCore`/`outerDFSLoopWF` — and whether it's "on the executable path"

**This was the user's direct question this session — answered precisely
here, since it's the crux of the whole design.**

```lean
structure RFrame {State : Type u} (initialStates : List State)
    (succs : State → Array State) where
  state : State
  hreach : Reachable initialStates succs state
  remaining : List State
  hsuffix : remaining <:+ (succs state).toList
```

`stack : List (RFrame initialStates succs)` replaces today's `stack : List
(State × List State)` as the actual recursion argument of `innerDFSCore`/
`outerDFSLoopWF`.

**Is `RFrame` "part of the executable path"? Yes and no, and the distinction
is the entire point:**

- `.state : State` and `.remaining : List State` are ordinary data — the
  *exact same* data as today's `(current, remaining)` pair. `remaining`
  bookkeeping (which successors are still left to explore from this frame)
  is **not new** — it's the algorithm's own explicit-stack state, CAVA's
  `pending s`, already present in the current code today, untouched by this
  redesign. So yes: the algorithm still needs to track "which successors are
  left," exactly as it always has.
- `.hreach : Reachable initialStates succs state` and `.hsuffix : remaining
  <:+ (succs state).toList` are **`Prop`-valued fields**. Lean 4 erases
  `Prop`-typed structure fields at compile time (proof irrelevance — the
  same mechanism that makes `Subtype`/`{x // p x}` compile down to just `x`
  at runtime, with `.property` never actually stored or computed). So these
  two fields cost **zero** at runtime: not stored, not computed, never
  branched on, never inspected. They exist purely so the type-checker can
  produce the `decreasing_by` proof terms once, during compilation/proof
  checking.
- Net effect: `RFrame` compiles to a runtime representation **isomorphic to
  today's `(State × List State)` pair** — same memory footprint, same
  computation, same algorithm. What's eliminated is the runtime `fr.univ.
  contains succ` check (a real `Std.HashSet` lookup against a materialized
  set, executed on every push) — that's replaced by `Reachable.step
  frame.hreach hmemsuccs`, a proof term built at *compile time* from already
  in-scope proof obligations, never evaluated as code.

So: no new bookkeeping is introduced by this redesign beyond what the
algorithm already does; the only thing added to the frame type is erased
proof content, and the only thing *removed* is the real runtime `HashSet`
lookup this whole redesign targets.

**Why bundle `hreach`/`hsuffix` per-frame rather than as one whole-stack
hypothesis** (`hstack_states : ∀ p ∈ stack, …`, which is what was tried and
abandoned before, per §2/§5.2 above): a whole-stack quantified hypothesis
forces Lean's well-founded equation compiler to transport that fact through
each match arm's generalization — exactly where `rw [innerDFSCore.eq_def]`
intermittently failed previously. Bundling the proof into each frame's own
*element* type instead makes destructuring `stack : List (RFrame …)` into
`frame :: rest` ordinary dependent pattern matching, and proof irrelevance
means no `rw`/`.induct` call ever needs to inspect which proof populates
`hreach`/`hsuffix`. This is also structurally unrelated to the *other*,
separate historical failure mode (a `Subtype` bundled into a **return**
type, self-referentially over a call's own not-yet-known result, which hit
"motive is not type correct") — bundling an erasable proof about
already-available **input** data into an **argument**'s element type is a
different, better-behaved shape. This claim is exactly what the mandatory
toy spike (§8.5) tests before it's trusted at the scale of the real file.

Frame bookkeeping mechanics (routine `List.IsSuffix`/`Array.mem_toList_iff`):
- **Push a fresh successor** `succ`: new frame's `remaining := (succs
  succ).toList`, `hsuffix := List.suffix_refl _`, `hreach := .step
  frame.hreach hmemsuccs` where `hmemsuccs : succ ∈ succs frame.state` comes
  from `frame.hsuffix.mem` applied to `succ ∈ frame.remaining` — no runtime
  check of any kind.
- **Continue the same frame** after consuming `succ` (`remaining = succ ::
  tl`): `hsuffix' := (List.suffix_cons succ tl).trans hsuffix`.
- `initialStates` becomes an **implicit** argument of `innerDFSCore`/
  `outerDFSLoopWF` (`{initialStates : List State}`), inferred from `fr`'s/
  `stack`'s type.

### 8.5 Termination measure

Stays a `Nat × Nat` tuple (as today), so elaboration stays on the erased
`WellFounded.fix` path (`Nat.fix`'s fast path only triggers when the
*top-level* codomain is literally `Nat`, confirmed via direct read of
`Lean/Elab/PreDefinition/WF/Fix.lean`'s `isNatLtWF`, and empirically
corroborated since today's real code already runs with an analogous tuple):

```lean
termination_by
  (({s | Reachable initialStates succs s} \ {x | iv.contains x}).ncard,
   pendingSum stack + stack.length)
```

using a `Set.ncard`-based analogue of the deleted `HashSet.sdiff_insert_lt`:

```lean
theorem Set.ncard_diff_insert_lt {State : Type u} {univ : Set State} (hfin : univ.Finite)
    {visited : Set State} {x : State} (hx_univ : x ∈ univ) (hx_nvisited : x ∉ visited) :
    (univ \ insert x visited).ncard < (univ \ visited).ncard := by
  apply Set.ncard_lt_ncard _ (hfin.subset Set.diff_subset)
  constructor
  · intro y hy
    simp only [Set.mem_diff, Set.mem_insert_iff, not_or] at hy ⊢
    exact ⟨hy.1, hy.2.2⟩
  · intro hsub
    exact (hsub ⟨hx_univ, hx_nvisited⟩).2 (Set.mem_insert x visited)
```

Delete `HashSet.size_le_of_subset`/`size_pos_of_contains`/
`size_lt_of_ssubset`/`HashSet.sdiff_insert_lt` (no longer needed). All other
`decreasing_by` cases (`Prod.Lex.right _ (by simp)`) are untouched.

### 8.6 Mandatory toy spike (gate before touching real code)

Given the documented history of `.eq_def`/`.induct` fragility, **do not
touch `NestedDFSTermination.lean` until this spike passes.** Create a
standalone `LTLLib/Spike/FiniteReachSpike.lean` (excluded from
`LTLLib.lean`'s import list; delete/archive once the verdict is reached):

```lean
import Mathlib.Data.Set.Card
import Std.Data.HashSet

namespace Spike

variable {State : Type} [BEq State] [Hashable State] [LawfulBEq State]

inductive Reachable (initialStates : List State) (succs : State → Array State) : State → Prop where
  | base {i} (hi : i ∈ initialStates) : Reachable initialStates succs i
  | step {s t} (hs : Reachable initialStates succs s) (ht : t ∈ succs s) :
      Reachable initialStates succs t

def FiniteReach (initialStates : List State) (succs : State → Array State) : Prop :=
  {s | Reachable initialStates succs s}.Finite

structure RFrame (initialStates : List State) (succs : State → Array State) where
  state : State
  hreach : Reachable initialStates succs state
  remaining : List State
  hsuffix : remaining <:+ (succs state).toList

def pendingSum {initialStates : List State} {succs : State → Array State}
    (stack : List (RFrame initialStates succs)) : Nat :=
  (stack.map (fun f => f.remaining.length)).sum

def explore {initialStates : List State} (succs : State → Array State)
    (fr : FiniteReach initialStates succs)
    (stack : List (RFrame initialStates succs))
    (visited : Std.HashSet State) (log : List State) :
    Std.HashSet State × List State :=
  match stack with
  | [] => (visited, log)
  | frame :: rest =>
    match hrem : frame.remaining with
    | [] => explore succs fr rest visited log
    | succ :: tl =>
      have hsuf' : tl <:+ (succs frame.state).toList :=
        (List.suffix_cons succ tl).trans (hrem ▸ frame.hsuffix)
      let stack' := { frame with remaining := tl, hsuffix := hsuf' } :: rest
      if hvis : visited.contains succ then
        explore succs fr stack' visited log
      else
        have hmemrem : succ ∈ frame.remaining := hrem ▸ List.mem_cons_self
        have hmemsuccs : succ ∈ succs frame.state :=
          Array.mem_toList_iff.mp (frame.hsuffix.mem hmemrem)
        let newFrame : RFrame initialStates succs :=
          { state := succ, hreach := .step frame.hreach hmemsuccs,
            remaining := (succs succ).toList, hsuffix := List.suffix_refl _ }
        explore succs fr (newFrame :: stack') (visited.insert succ) log
termination_by
  (({s | Reachable initialStates succs s} \ {x | visited.contains x}).ncard,
   pendingSum stack + stack.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.left _ _ (by
      apply Set.ncard_lt_ncard _ (fr.subset Set.diff_subset)
      constructor
      · intro y hy
        simp only [Set.mem_diff, Set.mem_insert_iff, not_or] at hy ⊢
        exact ⟨hy.1, fun h => hy.2 (by simpa [h] using Std.HashSet.contains_insert)⟩
      · intro hsub
        exact (hsub ⟨hmemsuccs, by simpa using hvis⟩).2 (Std.HashSet.mem_insert.mpr (Or.inl rfl)))

end Spike
```

**Tests, in order, hard pass/fail:**

1. Compiles as-is (adjust lemma names against the vendored Mathlib/Std as
   needed — not pre-verified). `termination_by`/`decreasing_by` rejecting the
   `RFrame`-typed `stack` is an immediate hard stop.
2. `#print Spike.explore.induct` — confirm the auto-generated induction
   principle exists with the expected per-branch case shape. Failure mirrors
   the historical `Subtype`-in-return-type failure; hard stop.
3. Prove a thin-wrapper unfolding equation via `rw [explore.eq_def]` (try
   both `rw [...]` and `unfold explore; simp [...]`, note which succeeds),
   mirroring `innerDFSWF_blocked`/`innerDFSWF_fresh`.
4. Prove a preservation lemma via `induction stack, visited using
   explore.induct (succs := succs) (fr := fr); all_goals (unfold explore;
   dsimp only; try simp_all; try (rename_i ih; simpa using ih))` — a
   verbatim transplant of the tactic recipe already working today for
   `innerDFSCore_outerVisited_pres`. **Single most important test.**

**Verdict**: tests 3-4 both succeeding (minor `simp`-set tweaks OK; needing
fundamentally different machinery or `sorry`s does not count) is the go/no-go
signal. Persistent failure across reasonable variations (moving `hsuffix` to
a separate structure, trying `grind`/`omega`, the raw `WellFounded.fix`
eliminator) → **stop and report back before touching the real file.**

### 8.6.1 Spike result: PASS (run 2026-08-07)

The spike (`LTLLib/Spike/FiniteReachSpike.lean`) compiles clean (`lake env
lean`, zero errors, one cosmetic unused-variable warning). Both critical
tests passed. Findings, in order of relevance to the real port:

1. **`rw [explore.eq_def]` alone does *not* work** — leaves the nested
   `match hrem : frame.remaining with ...` unreduced even after
   `simp [heq]`, reproducing the historical fragility exactly. **Neither
   does blanket `simp [explore, ...]`** — it triggers a genuine "possibly
   looping simp theorem" (`explore.eq_2` combined with `RFrame.consumeOne`/
   `Std.HashSet.contains_iff_mem` re-firing), hitting max recursion depth.
2. **`rw [explore.eq_2]; grind` *does* work**, cleanly, for both the
   one-step unfolding lemma (`explore_skip_visited`, mirroring
   `innerDFSWF_blocked`/`innerDFSWF_fresh`) and every leaf of the
   `.induct`-based preservation proof (`explore_log_pres`, mirroring
   `innerDFSCore_outerVisited_pres`). **`grind` is the load-bearing
   ingredient** — this is the concrete difference from the abandoned prior
   attempt, which predates `grind` being the powerful, mature tactic it now
   is in this Lean version. Recommendation for the real port: default to
   `rw [<fn>.eq_N]; grind` (or `simp only [<fn>.eq_N]; grind` if `rw` is too
   rigid about the exact goal shape) as the standard idiom for every
   one-step unfolding lemma, rather than attempting bare `rw [.eq_def]`.
3. **Only 2 equation lemmas get generated (`explore.eq_1`/`explore.eq_2`),
   not 4**, even though `.induct` generates 4+ cases. Equation lemmas split
   only at the function's own outermost recursion-justifying match (here:
   `stack = [] | frame :: rest`); the nested `match hrem : frame.remaining
   with ...`/`if hvis` stay embedded inside `eq_2`'s RHS, unsplit. Induction
   cases split at every leaf of the full case tree, a different granularity.
   Real-port implication: expect to reference `innerDFSCore.eq_1`/`.eq_2`
   style names keyed to the *outer* `stack`/`remaining`-shape match, not one
   equation per `if`/`dite` branch.
4. **`induction ... using explore.induct` generates an extra, unnamed-in-the-
   valid-names-list goal for `fr` itself** (`case fr : ⊢ FiniteReach
   initialStates succs`) — closed trivially via `exact fr`, but must be
   handled explicitly (`all_goals first | exact fr | rw [...eq_1] | (rw
   [...eq_2]; grind)` was the working recipe). Worth expecting the same for
   the real `innerDFSCore.induct`/`outerDFSLoopWF.induct`.
5. **Well-founded recursive `def`s do not reduce via `rfl`** (unlike
   structurally-recursive ones) — the base-case induction leaf needed
   `rw [explore.eq_1]`, not `rfl`. Easy to forget, cheap to fix.
6. **Real, non-cosmetic instance-scoping gotcha**: `def`-level
   auto-inclusion of `variable`-declared instances is based only on what the
   *signature* needs, not what `decreasing_by`'s tactic proof needs (unlike
   `theorem`s, which appear to auto-include more liberally). `explore`
   needed `[LawfulBEq State] [LawfulHashable State]` listed *explicitly* on
   its own signature — relying on the ambient `variable [...]` line silently
   left them unavailable inside `decreasing_by`, causing a "failed to
   synthesize instance" error there specifically (and, as a knock-on effect,
   made unrelated simp lemmas like `pendingSum_cons` silently fail to fire
   inside `decreasing_by` too, since simp couldn't instantiate *their*
   spurious auto-included `LawfulBEq`/`LawfulHashable` params either — same
   root cause, two symptoms). Real-port implication: `innerDFSCore`/
   `outerDFSLoopWF` must list every instance their `decreasing_by` proofs
   need directly in their own signatures, not rely on file-level `variable`
   auto-inclusion. `Reachable`/`FiniteReach`/`RFrame`/`pendingSum` were kept
   fully classless (no `BEq`/`Hashable` at all) specifically to sidestep this
   class of bug — worth doing the same for the real port's analogous defs.

**Conclusion: proceed with the real redesign (§8.7) using the `RFrame`
per-frame-bundled encoding as designed, with `rw [<fn>.eq_N]; grind` as the
standard one-step-unfolding idiom throughout** (replacing the plan's
original, more tentative `rw [.eq_def]`/`unfold` phrasing wherever it
appears in §8.7's file-by-file notes).

### 8.7 File-by-file plan (contingent on the spike)

**`EmptinessCheck.lean`**: per §8.3/§8.4.

**`NestedDFS/NestedDFSTermination.lean`** (largest file):
- `innerDFSCore`: `stack : List (RFrame initialStates succs)`. The
  `hblocked`/`hsucc_univ` cascade drops from 4 branches to 3 — the `else if
  hsucc_univ : fr.univ.contains succ then <push> else <fallback>` pair
  collapses into an **unconditional push** (fallback deleted outright, not
  just made unreachable). `termination_by`/`decreasing_by` per §8.5.
- `innerDFSWF`: gains one new argument, `hcurrent_reach : Reachable
  initialStates succs current`, seeding the initial singleton `RFrame`.
  Non-recursive — purely mechanical, no equation-lemma risk.
- `innerDFSWF_blocked`/`innerDFSWF_fresh`/`innerDFSCore_outerVisited_pres`/
  `innerDFSWF_outerVisited_pres`: re-proved against new signatures — exactly
  what the spike's tests 3-4 de-risk.
- `outerDFSLoopWF`: same `RFrame`-list `stack`. **Schwoon-Esparza and HPY
  branches untouched in logic** — only mechanical `RFrame`-threading where
  they build `stack'`; HPY's `innerDFSWF` call needs `hcurrent_reach` sourced
  from the active frame's own `.hreach`. Final `_hsucc_univ`-`dite` cascade
  collapses into an unconditional push exactly as in `innerDFSCore`.
- `nestedDFSWF`/`.go`: ordinary structural recursion — no `.eq_def`/`.induct`
  fragility concern regardless of hypothesis shape; use the same
  `List.IsSuffix` idiom for consistency.
- Fuel↔WF bridge sections (`InnerFuelBridge`/`OuterFuelBridge`/
  `TopLevelFuelBridge`, ~1000 lines, **dominant cost center**): fuel-side
  functions (`NestedDFSCorrectness.lean`) are untouched, carry no
  `FiniteReach`/dependent arguments (confirmed via grep). Every bridge
  theorem must be rephrased so the `RFrame`-list is primary and the
  fuel-side plain list is derived from it by a forgetful erasure map
  (`stack.map (fun f => (f.state, f.remaining))`) — **never** the reverse
  direction (that would reintroduce the "prove a global fact about existing
  plain data, then build dependent data from it" pattern `RFrame` was chosen
  to avoid). Expect to touch essentially every lemma in these sections;
  induction templates/case splits carry over, but each needs its list
  argument re-typed. If this bridging doesn't work smoothly across the ~15
  lemmas here (some need `max`-of-two-fuel-thresholds reconciliation),
  that's a second de-risking question the §8.6 spike doesn't cover — consider
  a follow-up mini-spike (fuel-side plain recursion vs. `RFrame`-based WF
  recursion) before pushing further.
- `BA.finiteReach`: becomes a pure proof — `ba.states`/`hwf.succ_mem` used
  only as internal proof tooling, never surfacing as `FiniteReach` data.
  Delete `BA.initialStates_subset_finiteReach` (subsumed by
  `Reachable.base`).
- `PumpingLemma`: replace the 47-line hand-rolled `exists_dup_of_size_lt`
  with Mathlib's `Set.Infinite.exists_ne_map_eq_of_mapsTo`
  (`Mathlib/Data/Set/Finite/Basic.lean:873`), `s := Set.univ ℕ`, `f k := σ
  (accIdxSeq σ isAccepting hacc k)`, `t := {s | Reachable initialStates
  succs s}`. `exists_acceptingCycle_of_run`'s `hinitial` parameter drops
  entirely.

**`Product.lean`**: delete `hashSetProd`/`hashSetProd_mem` outright.
`Product.finiteReach` becomes a pure existence proof via a new
`Product.reachable_imp` lemma (induction on `Reachable` for the product
graph, reusing the existing `hcompat`/`Array.mem_flatMap`/`Array.mem_map`
case split already present in today's `finiteReach.closed`, retargeted at
`.step` conclusions instead of `.contains` conclusions — mechanical
retargeting of already-working combinatorial reasoning, not new
mathematical content) combined via `Set.Finite.prod` + `Set.Finite.subset`.
Audit `[LawfulBEq SysState] [LawfulHashable SysState]` for removal (only
needed for the now-deleted `hashSetProd_mem`).

**`ModelCheck.lean`**: signature-only change matching `check`'s new argument
order and `Product.finiteReach`'s new signature.

**`Examples/*.lean`**: gets strictly simpler. If the example state type
derives `Fintype`, `Set.toFinite _` gives finiteness for free, replacing the
current 5-line `where univ := {...}; closed := by ...` with a one-liner.

### 8.8 Verification

- `lake build` stays `0 sorry` by the end.
- The two optimizations' actual returned `stem`/`loop` witnesses must be
  byte-identical to before on the existing examples — only the
  reachability-check mechanism changed, never the search logic.
- Grep the final diff for `fr.univ`/`.contains` inside any `def` body (not
  `theorem`/tactic block) in `NestedDFSTermination.lean`/`Product.lean`/
  `ModelCheck.lean` — zero matches is the literal acceptance criterion.
