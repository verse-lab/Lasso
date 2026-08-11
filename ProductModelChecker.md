# Plan: Product Construction for External Model Checking

## Goal

Give any external model checker a **clean interface**: supply
`initialStates`, a `successors` function, and a per-state proposition
labeling for their system, and get back an `EmptinessResult` for "does this
system satisfy `φ`" — without the caller ever needing to know about `GBA`,
`BA`, degeneralization, or `nestedDFS` internals. The product between their
system and our property automaton is built **on-the-fly**, mirroring CAVA,
not materialized as an explicit graph.

`fullPipeline` (`LTLLib/Pipeline.lean`) currently only decides satisfiability
of `φ` in isolation (`createGraph → constructGBA → degeneralize →
nestedDFSWF`). There is no system in that picture at all. This plan adds the
missing product-construction layer in between.

## What CAVA actually does (verified against AFP source)

Fetched directly from `isa-afp.org/browser_info/current/AFP/CAVA_Automata/Automata.html`
(locale `igba_sys_prod_precond`) and `CAVA_LTL_Modelchecker/CAVA_Impl.html`
(locale `cava_inter_impl_loc`, the executable refinement) — not from memory,
since an earlier answer in this conversation initially got the direction of
the label check backwards and had to be corrected against the primary source.

The system side is a plain record with three fields
(`Automata.html:1275`, `sa_rec`):

```isabelle
record ('Q,'L) sa_rec = "'Q graph_rec" +   -- graph_rec already has g_V0, g_E
  sa_L :: "'Q ⇒ 'L"
```

confirmed by the two concrete instantiations in `CAVA_Impl.thy` (BoolProgs,
Promela), e.g.:

```isabelle
bpc_to_sa bpc ≡ ⦇
  g_E  = E_of_succ (set o BoolProgs.nexts bp),   -- successor function
  g_V0 = {c0},                                    -- initial states
  sa_L = λc. bs_α (snd c)                          -- state → prop valuation
⦈
```

i.e. exactly "initial states + a successor function + a labeling function" —
nothing more. This is precisely the interface we want to expose.

The abstract product (`Automata.html:1300-1312`, `igba_sys_prod_precond.prod`):

```isabelle
prod ≡ ⦇
  g_V = igba.V × sa.V,
  g_E = { ((q,s),(q',s')). igba.L q (sa.L s) ∧ (q,q')∈igba.E ∧ (s,s')∈sa.E },
  g_V0 = igba.V0 × sa.V0,
  igbg_num_acc = igba.num_acc,
  igbg_acc = λ(q,s). if s∈sa.V then igba.acc q else {} ⦈
```

and the executable/on-the-fly refinement (`CAVA_Impl.html:404-416`,
`cava_inter_impl_loc`) computes this same thing as a plain successor
function, never a materialized edge set:

```isabelle
g_E = E_of_succ (λ(q,s).
  if igba.L q (sa.L s) then
    (successors of s in sa.E) × (successors of q in igba.E)
  else {})
```

Four things worth being precise about, since they're easy to get backwards:

1. **The label check is a source-state self-consistency gate, not a
   destination check.** `igba.L q (sa.L s)` is evaluated on the *current*
   product state `(q,s)` before computing *its* successors — it gates
   whether `(q,s)` has any outgoing edges at all. It is **not** a check on
   the freshly-entered `(q',s')`.
2. **Initial states are the unfiltered full product** `igba.V0 × sa.V0`, no
   compatibility pre-filter. An incompatible initial pair simply has no
   successors once the gate above is evaluated, and is harmless dead weight
   for the DFS — CAVA doesn't bother filtering it out either.
3. **Acceptance is inherited entirely from the automaton side**,
   `igbg_acc (q,s) = igba.acc q` (guarded by `s ∈ sa.V`, a well-formedness
   technicality for an *explicit* state set that doesn't apply to an
   open-world successor function — see below).
4. **Finite-reachability of the product is a direct corollary**
   (`prod_finite_reachable`, `Automata.html:1335`): reachable pairs of the
   product are a subset of `reachable(igba) × reachable(sa)`, proved by
   induction over the reflexive-transitive closure. This is the one lemma
   worth porting rather than re-deriving from scratch — though our
   `FiniteReach` (see below) is stated as a one-step closure property, so
   the port is simpler than CAVA's `rtrancl_induct2` argument (no induction
   over paths needed).

This lines up closely with what's already in this repo: `nestedDFS`/
`nestedDFSWF` (`LTLLib/NestedDFS/NestedDFSRef.lean:208`, `LTLLib/NestedDFS/NestedDFSTermination.lean:1594`)
already take a bare `initialStates`/`successors : State → Array State` pair
with no automaton-specific record — exactly CAVA's on-the-fly successor
function style. `BA`'s labeling (`LTLLib/BA.lean:63-65`, `LTLLib/GBA.lean:47-52`)
is already the same `positiveProps(q) ⊆ l ∧ negativeProps(q) ∩ l = ∅` shape as
`igba.L`. The only missing piece is the product itself.

## Design

### 1. `BA.compatible` — port of `igba.L` (in `LTLLib/BA.lean`)

```lean
/-- Label-compatibility check, corresponds to CAVA's `igba.L q l`
(`Automata.html`, `igba_rec.gba_L`): a BA state accepts a valuation `l` iff
its positive propositions are all present and none of its negative
propositions are present. -/
def compatible (ba : BA α) (s : BAState) (valuation : Std.HashSet α) : Bool :=
  let (pos, neg) := ba.getLabeling s
  pos.all valuation.contains && !neg.any valuation.contains
```

### 2. `LTLLib/Product.lean` — the product itself, no new record type

Per the explicit ask ("clean interface any external model checker can use")
and matching `nestedDFS`'s own "no automaton-specific record" stance, the
external interface is three bare arguments, not a bundled `System`
structure:

- `sysInit : List SysState`
- `sysSucc : SysState → Array SysState`
- `sysLabel : SysState → Std.HashSet α`

State type: `SysState × BAState` (Lean-natural `(system, automaton)` order;
CAVA's `(q,s)` is `(automaton, system)` — noted inline as a comment rather
than fighting Lean's usual `(input, automaton)` ordering).

```lean
namespace Product

/-- Corresponds to CAVA's `g_V0 = igba.V0 × sa.V0` (`Automata.html:1311`,
`igba_sys_prod_precond.prod`) — the *unfiltered* full product, no
compatibility pre-filter (see design note 2 above). -/
def initialStates (ba : BA α) (sysInit : List SysState) :
    List (SysState × BAState) :=
  sysInit.flatMap fun s => ba.initialStates.toList.map fun q => (s, q)

/-- Corresponds to CAVA's on-the-fly `g_E` in `cava_inter_impl_loc`
(`CAVA_Impl.html:404-416`): computed as a plain function of the current
product state, never materialized. The `compatible` gate is evaluated on
the *source* state `(s, q)` — see design note 1 above, this is the detail
that's easy to get backwards. -/
def getSuccessors (ba : BA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) :
    (SysState × BAState) → Array (SysState × BAState) :=
  fun (s, q) =>
    if ba.compatible q (sysLabel s) then
      (sysSucc s).flatMap fun s' => (ba.getSuccessors q).map fun q' => (s', q')
    else #[]

/-- Corresponds to CAVA's `igbg_acc = λ(q,s). if s∈sa.V then igba.acc q else
{}` (`Automata.html:1312`) — minus the `s ∈ sa.V` guard, which only makes
sense for an explicit state set. It's meaningless for an open-world
successor function (same reasoning `nestedDFS`/`nestedDFSWF` already apply
by never assuming a `states` set for their generic `State` parameter). -/
def isAccepting (ba : BA α) : (SysState × BAState) → Bool :=
  fun (_, q) => ba.isAccepting q

end Product
```

### 3. `Product.finiteReach` — port of `prod_finite_reachable`

**Superseded (2026-08-07)**: this whole section documents the design as it
stood immediately after this implementation pass — `FiniteReach` as a
`Std.HashSet`-witness-carrying structure, `Product.finiteReach` built via a
`hashSetProd`/`hashSetProd_mem` cross-product. That has since been replaced
by a strict "Option B" redesign: `FiniteReach` is now a bare `Prop`
(`{s | Reachable initialStates succs s}.Finite`, no data), `hashSetProd` is
deleted outright, and `Product.finiteReach`/`BA.finiteReach` are pure
existence proofs — no `[LawfulBEq SysState] [LawfulHashable SysState]`
needed anywhere in this file any more, and no `Std.HashSet` cross-product is
ever materialized. Current signature: `Product.finiteReach (ba) (hbawf)
(sysSucc) (sysLabel) (sysInit) (sysFR : FiniteReach sysInit sysSucc) :
FiniteReach (Product.initialStates ba sysInit) (Product.getSuccessors ba
sysSucc sysLabel)`. Full design record and findings: `FiniteReachRedesign.md`
(§8/§8.6.1). The rest of this section is kept as a historical record of the
original design pass.

The caller must supply their own `FiniteReach sysSucc` witness (their system
being finite-state / finitely-reachable is *their* proof obligation, exactly
as CAVA's `inter_spec` takes `finite (sa.E* `` sa.V0)` as a precondition, not
something it derives). Given that plus `ba.finiteReach hbawf`
(`LTLLib/NestedDFS/NestedDFSTermination.lean:1873`, already exists):

```lean
/-- Corresponds to CAVA's `prod_finite_reachable` (`Automata.html:1335`):
the product's reachable states are contained in `reachable(sys) ×
reachable(ba)`. Simpler here than CAVA's `rtrancl_induct2` proof because our
`FiniteReach.closed` is a one-step closure property, not a reachable-set
characterization — no induction over paths needed. -/
def finiteReach (ba : BA α) (hbawf : ba.WellFormed)
    (sysFR : FiniteReach sysSucc) :
    FiniteReach (Product.getSuccessors ba sysSucc sysLabel) where
  univ := sysFR.univ ×ˢ (ba.finiteReach hbawf).univ  -- HashSet cartesian product
  closed := by
    -- unfold getSuccessors, split on the `compatible` guard (else-branch
    -- vacuous), combine `sysFR.closed`/`(ba.finiteReach hbawf).closed`
    -- pointwise on the flatMap/map
    sorry
```

(This was left as a `sorry` placeholder for the implementation pass, then
proven afterward. The actual proof (`Product.lean`) keeps the same shape —
unfold `getSuccessors`, `cases` on the `compatible` guard, combine
`sysFR.closed`/`(ba.finiteReach hbawf).closed` — but goes through a private
`hashSetProd_mem` lemma rather than the informal `×ˢ` notation sketched
above, and needed `[LawfulBEq SysState] [LawfulHashable SysState]` added to
`finiteReach`'s signature for the `Std.HashSet` membership lemmas involved.)

### 4. `LTLLib/ModelCheck.lean` (new file) — top-level `modelCheck`

Kept **separate from `Product.lean`**, mirroring `fullPipeline`'s shape
(`LTLLib/Pipeline.lean:35-42`) and corresponding to CAVA's `abs_model_check`
(`CAVA_Abstract.thy`, already referenced in `Pipeline.lean`'s own docstring
as the thing `fullPipeline` is *missing* the `inter_spec`/system stage of).
Standard automata-theoretic model checking: system satisfies `φ` iff the
product against `¬φ`'s BA is empty.

**Correction made during implementation, worth recording:** the first draft
of this function took `φ : NNF α` and negated via `NNF.neg`, mirroring
`fullPipeline`'s own `φ : NNF α` signature. Re-reading CAVA's
`abs_model_check` line more carefully caught the mistake:
```isabelle
abs_model_check _ _ _ _ sys φ ≡ do {
  gba ← ltl_to_gba_spec (Not_ltlc φ); ... }
```
`Not_ltlc φ` wraps the **surface**-syntax formula in negation *before* any
NNF conversion runs — CAVA never takes an already-NNF formula and negates
that. `fullPipeline` gets away with `NNF α` only because it never negates
anything (it checks `φ`'s own satisfiability directly); `modelCheck` does
need a negation, so — to stay faithful to where CAVA performs it — it needs
to take the surface `Formula α` (`LTL/Syntax.lean`), not `NNF α`, and fold
"negate, then normalize" into the single call `φ.toNNF false` (`toNNF`'s
`pos`-flag convention makes `(Formula.not φ).toNNF true` and `φ.toNNF false`
definitionally the same NNF — see `LTL/Syntax.lean:180-210`). The `NNF.neg`
version wasn't unsound, just doing the negation at the wrong layer relative
to CAVA and redoing normalization work `toNNF false` already does in one
pass.

**Superseded (2026-08-07)**: the snippet below predates both the `checker :
EmptinessChecker ... := nestedDFSChecker` default parameter (added later,
also unreflected here) and the `FiniteReach` strict redesign. Current
signature: `modelCheck (φ) (sysInit) (sysSucc) (sysLabel) (sysFR :
FiniteReach sysInit sysSucc) (checker := nestedDFSChecker)`, calling
`checker.check (Product.getSuccessors ...) (Product.initialStates ...)
(Product.finiteReach ba hbawf sysSucc sysLabel sysInit sysFR)
(Product.isAccepting ba)` — see `ModelCheck.lean` for the exact current
body. `FiniteReachRedesign.md` (§8/§8.6.1) has the full record.

```lean
/-- Corresponds to CAVA's `abs_model_check` (`CAVA_Abstract.thy`), the piece
`fullPipeline` (`Pipeline.lean`) deliberately left out (see its docstring).
`φ` is the surface `Formula α`, matching `Not_ltlc φ` above — negates via
`φ.toNNF false`, builds the resulting NNF's `BA`, products it against the
caller's system, and runs the existing verified `nestedDFSWF` emptiness
check — exactly `gba ← ltl_to_gba_spec (Not_ltlc φ); (Gprod, _) ← inter_spec
sys gba; find_ce_spec Gprod` collapsed into one total function,
`createGraph`'s `none` branch staying defensive dead code as in
`fullPipeline`. -/
def modelCheck (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysSucc) : EmptinessResult (SysState × BAState) :=
  let negNNF := φ.toNNF false
  match createGraph (S := S) negNNF with
  | some st =>
    let ba := (constructGBA negNNF st).degeneralize
    let hbawf := degeneralize_wellFormed_any _ (constructGBA_wellFormed (by exact _))
    nestedDFSWF (Product.getSuccessors ba sysSucc sysLabel)
      (Product.finiteReach ba hbawf sysFR) (Product.isAccepting ba)
      (Product.initialStates ba sysInit)
  | none => .empty 0
```

`Formula.toNNF` already exists (`LTLLib/LTL/Syntax.lean:180`) — no new
negation machinery needed.

## Explicitly out of scope for this pass — track separately, do not start without checking in

Per `.claude/CLAUDE.md` ("pause whenever you think you might need to write
huge proofs... explain the situation, then we can chat"): the correctness
theorems bridging `modelCheck`'s `.empty`/`.nonEmpty` results back to an
actual "system satisfies/violates φ" statement are **not** part of this
plan.

**Update (2026-08-11): done — see `ModelCheckCorrectnessPlan.md`.** Scoped
out in full there (CAVA references re-verified against the AFP source for
each item, Lean signatures sketched, file-by-file plan, execution order),
then implemented and merged the same day: `modelCheck_empty_unsat`/
`modelCheck_nonEmpty_sat` (`ModelCheck.lean`) are the correctness theorems
this section originally deferred, `lake build` clean, 0 `sorry`. The rest
of this section is kept as the original scoping discussion that plan was
built from — see the plan doc's §10 for what changed between that scoping
and the actual implementation.

### The target shape

CAVA's own top-level correctness theorem, `abs_model_check_correct`
(`CAVA_Abstract.html:111-122`), states — verified against source, not
memory:

```isabelle
theorem abs_model_check_correct:
  "abs_model_check T1 T2 T3 T4 sys φ ≤ do {
    ASSERT (sa sys);
    ASSERT (finite ((g_E sys)⇧* `` g_V0 sys));
    SPEC (λres. case res of
      None ⇒ sa.lang sys ⊆ language_ltlc φ
    | Some None ⇒ ¬ sa.lang sys ⊆ language_ltlc φ
    | Some (Some r) ⇒ graph_defs.is_run sys r ∧ sa_L sys ∘ r ∉ language_ltlc φ)
  }"
```

i.e. two directions: "no counterexample" implies every system word is in
`φ`'s language, and a returned counterexample `r` is a genuine system run
whose labeled word is *not* in `φ`'s language. The `Product`/`Formula`-level
analogues we'd want are exactly the `modelCheck` counterparts of
`fullPipeline_nonEmpty_sat`/`fullPipeline_empty_unsat` (`Pipeline.lean:61-118`).

### What's missing to get there

- ~~**Not yet defined**: a notion of "system run" / "system language"~~ —
  **done (2026-08-11)**: `Sys.toSpec` (`Product.lean`), CAVA's `sa.is_run`/
  `sa.lang` ported directly via `OASpec` at `k = 0` — see
  `ModelCheckCorrectnessPlan.md` §2 for the full correspondence.
- ~~**Not yet ported**: Lean counterparts of CAVA's `prod_run`/`prod_acc`/
  `gsp_correct1`~~ — **done (2026-08-11)**: `Product.run_decompose`/
  `run_combine`/`acc_iff`/`gsp_correct1`/`gsp_correct2` (`Product.lean`) —
  see `ModelCheckCorrectnessPlan.md` §3 for the full correspondence,
  including `gsp_correct2` (CAVA's completeness direction, not separately
  called out in this original bullet but needed and ported alongside
  `gsp_correct1`). The effort estimate below held up: comparable in size to,
  not larger than, `Product.lean`'s existing proof content.
  - **New consideration (2026-08-11), not present when this bullet was
    first written**: `Product.getSuccessors` no longer steps through the
    caller's raw `sysSucc` — it steps through `Product.totalizeSucc sysSucc`
    (`Product.lean`), which inserts a self-loop on any state with no
    outgoing edges, since LTL/Büchi semantics need an infinite run and a
    genuinely terminal client state has none (see README.md's "Terminal
    states, and a deliberate divergence from CAVA", and the worked example
    `LTLLib/Examples/ModelCheckTerminalStateExample.lean`). `Sys.toSpec`
    (the "system run"/`sa.is_run` notion this bullet was originally asking
    for — since built, see `ModelCheckCorrectnessPlan.md` §2) is stated over
    `totalizeSucc sysSucc`, not `sysSucc` directly, exactly per this note.
    This is a genuine, deliberate divergence from CAVA's own `sa.is_run`,
    which is defined directly over the client's `g_E` with no such wrapper
    — though not an *invented* one: `CAVA_Automata/Stuttering_Extension.thy`
    formalizes this exact same self-loop-insertion construction
    (`stutter_extend_edges`) with its own reachability/bisimulation
    preservation proofs, just as infrastructure for the SM/BoolProgs/Promela
    concrete-system-encoding layer to apply by hand before building its own
    `sa_rec`, never wired into `inter_spec`/`abs_model_check` automatically
    the way `totalizeSucc` is wired into `Product.getSuccessors` here (full
    writeup: README.md's "Terminal states" section, `Product.totalizeSucc`'s
    own docstring).
- ~~**Not yet proven**: `Product.finiteReach`'s `closed` field~~ — done, then
  **superseded (2026-08-07)**: the `hashSetProd_mem`/`LawfulBEq`/
  `LawfulHashable` machinery this bullet describes no longer exists.
  `Product.finiteReach` is now a pure existence proof (`reachable_imp` +
  `Set.Finite.prod`/`.subset`) needing no `Std.HashSet` reasoning and no
  `LawfulBEq`/`LawfulHashable SysState` requirement at all — "every
  `modelCheck` caller must now also supply a `LawfulHashable` instance" is no
  longer true on account of `finiteReach` (though `modelCheck`/`Product` may
  still require `LawfulHashable SysState` for unrelated reasons — check
  `ModelCheck.lean`'s `variable` block if this matters to you). See
  `FiniteReachRedesign.md` (§8/§8.6.1).

### What's *not* a gap (already covered, or matched deliberately)

- **The automaton side's own correctness** — that `BA.compatible`/
  `getSuccessors`/`isAccepting` faithfully reflect `φ`'s semantics — is
  already established by the existing `Bridge.lean`/`Soundness.lean`/
  `Completeness.lean`/`DegeneralBridge.lean` machinery that `fullPipeline`'s
  own theorems already lean on (`constructGBA_correct_weak`,
  `degeneralize_accepts_any`, `degeneralize_canonicalLabel_compat`). Nothing
  new needed there; the product proof reuses it as-is.
- **System finite-reachability isn't proven generically by CAVA either.**
  Its own `inter_spec` (`Automata.html:1300-1312`) takes
  `finite (sa.E⇧* `` sa.V0)` as an `ASSERT`ed precondition, proved
  separately per concrete system (BoolProgs, Promela) outside
  `CAVA_Automata`/`CAVA_Abstract`. `sysFR : FiniteReach sysSucc` being a
  caller-supplied argument to `modelCheck` is a faithful match, not a
  shortcut we're taking that CAVA avoids.
- **Already available and worth reusing when this phase starts**:
  `Formula.toNNF_correct_aux`'s negative-polarity half
  (`LTL/Semantics.lean:137-140`) already proves
  `¬ φ.directSatisfies ξ ↔ (φ.toNNF false).satisfies ξ` — i.e. `modelCheck`'s
  internal `negNNF := φ.toNNF false` is already known to correctly represent
  `¬φ` at the semantic level. The future correctness theorem gets this
  connection for free; it doesn't need to re-derive it.

This plan only builds the *executable* product + wiring (sections 1-4
above), which is what's needed to actually run the model checker against a
real system. The correctness-proof phase gets scoped and discussed
separately once this lands and the interface shape has been exercised by an
actual example.

## Design note: keeping the correctness proof algorithm-agnostic

Standing question for when the proof phase above starts: `modelCheck`
currently calls `nestedDFSWF` directly. If a future SCC-based emptiness
checker replaces it, we don't want to re-derive `modelCheck`'s (and
`Product`'s) correctness theorems from scratch — they should be provable
once, against *any* algorithm satisfying the right contract, the same way a
correctness proof for `fullPipeline` shouldn't need to know `nestedDFSWF`
is a nested DFS specifically.

**CAVA already does exactly this, and it's the load-bearing reason the
project is structured the way it is** — verified against source
(`CAVA_Abstract.html:64-72`), not assumed by analogy:

```isabelle
definition find_ce_spec
  :: "('q,_) igb_graph_rec_scheme ⇒ 'q word option option nres"
  ― ‹Check Generalized Buchi graph for emptiness, with optional counterexample›
  where "find_ce_spec G ≡ do {
    ASSERT (igb_graph G);
    ASSERT (finite ((g_E G)⇧* `` g_V0 G));
    SPEC (λres. case res of
      None ⇒ (∀r. ¬igb_graph.is_acc_run G r)
    | Some None ⇒ (∃r. igb_graph.is_acc_run G r)
    | Some (Some r) ⇒ igb_graph.is_acc_run G r
    )}"
```

`abs_model_check` (section above) is defined purely against this abstract,
algorithm-free `SPEC`, and `abs_model_check_correct` is proven *once*,
entirely in terms of `find_ce_spec`'s contract. Nested DFS (`find_ce_impl`,
`CAVA_Impl.thy:159`) is then proven to *refine* `find_ce_spec` — i.e.
satisfy its `SPEC` — as a completely separate obligation. Swapping in a
different emptiness-check algorithm later means proving a new refinement
against the same `find_ce_spec`; `abs_model_check_correct` itself needs no
change. (One honest divergence worth flagging: `find_ce_spec`'s `Some None`
case allows "confirmed nonempty, no witness computed" — weaker than what we
have. Our `EmptinessResult`/`nestedDFSWF` always produces a concrete
`stem`/`loop` witness when nonempty, so our contract below is strictly
stronger than CAVA's abstract one, not a divergence that causes problems.)

**We already had the Lean analogue of `find_ce_spec`'s contract — it just
wasn't packaged as an explicit interface.** `AcceptingCycle` was a purely
graph-theoretic structure (stem + cycle satisfying chain/accepting
conditions over `initialStates`/`succs`/`isAccepting` alone — no mention of
`nestedDFSWF` or any algorithm). `nestedDFSWF_nonEmpty_valid`/
`nestedDFSWF_empty_no_cycle` (`NestedDFS/NestedDFSTermination.lean:1830-1849`) are
exactly the two halves of `find_ce_spec`'s `SPEC` case split, proven for
`nestedDFSWF` specifically. `fullPipeline_nonEmpty_sat`/
`fullPipeline_empty_unsat` (`Pipeline.lean`) already call *only* these two
theorems, never unfolding `nestedDFSWF`'s own recursion — so the existing
code already had the right shape, it just wasn't enforced by an explicit
interface a second algorithm could implement against.

**Status: implemented**, and — per a follow-up request — pulled out of the
nested-DFS files entirely into their own file, `LTLLib/EmptinessCheck.lean`,
since none of this is specific to nested DFS as an algorithm:

- `EmptinessResult` (moved from `NestedDFS/NestedDFSRef.lean`), `AcceptingCycle` (moved
  from `NestedDFS/NestedDFSCorrectness.lean`), `FiniteReach` (moved from
  `NestedDFS/NestedDFSTermination.lean`), and the new `EmptinessChecker` structure all
  live in `EmptinessCheck.lean` now. That file imports nothing but `Std` and
  mentions no concrete algorithm anywhere — `NestedDFS/NestedDFSRef.lean`/
  `NestedDFS/NestedDFSCorrectness.lean`/`NestedDFS/NestedDFSTermination.lean` import *it*, not
  the other way around.
- `nestedDFSChecker : EmptinessChecker State`, the one existing refinement
  (`check := nestedDFSWF`, with `nonEmpty_valid`/`empty_no_cycle` discharged
  by `nestedDFSWF_nonEmpty_valid`/`nestedDFSWF_empty_no_cycle`), stays in
  `NestedDFS/NestedDFSTermination.lean` — it *is* nested-DFS-specific, unlike the
  interface it implements.
- `modelCheck` (`ModelCheck.lean`) takes `checker : EmptinessChecker
  (SysState × BAState) := nestedDFSChecker` and calls `checker.check`
  instead of `nestedDFSWF` directly. A future algorithm (e.g. an SCC-based
  checker) plugs in by providing a new `EmptinessChecker` instance in its
  own file; nothing in `EmptinessCheck.lean`, `ModelCheck.lean`, or a future
  correctness proof needs to change.

`fullPipeline` (`Pipeline.lean`) was **not** retrofitted to take a `checker`
parameter — left calling `nestedDFSWF` directly, since it wasn't asked for
and isn't blocking anything.

## Files touched

- `LTLLib/EmptinessCheck.lean` (new) — `EmptinessResult`, `AcceptingCycle`,
  `FiniteReach`, `EmptinessChecker`. Imports only `Std`.
- `LTLLib/NestedDFS/NestedDFSRef.lean` — `EmptinessResult` moved out to
  `EmptinessCheck.lean`; now imports it.
- `LTLLib/NestedDFS/NestedDFSCorrectness.lean` — `AcceptingCycle` moved out.
- `LTLLib/NestedDFS/NestedDFSTermination.lean` — `FiniteReach` moved out;
  `EmptinessChecker` moved out; `nestedDFSChecker` (the concrete instance)
  stays.
- `LTLLib/BA.lean` — add `BA.compatible`.
- `LTLLib/Product.lean` (new) — `Product.initialStates`, `Product.getSuccessors`,
  `Product.isAccepting`, `Product.finiteReach`.
- `LTLLib/ModelCheck.lean` (new) — `modelCheck (φ : Formula α) ... (checker :
  EmptinessChecker (SysState × BAState) := nestedDFSChecker)`.

## Verification

- `lake build` to confirm the new definitions typecheck and `modelCheck`
  actually unifies against `nestedDFSWF`'s signature.
- Add a small example under `LTLLib/Examples/` (mirroring
  `BasicExample.lean`/`FairnessExample.lean`) instantiating `sysInit`/
  `sysSucc`/`sysLabel` for a tiny hand-written transition system and a small
  `φ`, checked against both a true and a false property, to confirm
  `modelCheck` produces `.empty`/`.nonEmpty` as expected — same spirit as
  `BuildPrint.lean`.
