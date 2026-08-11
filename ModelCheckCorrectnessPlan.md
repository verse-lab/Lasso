# Plan: `modelCheck` Correctness — connecting `Product`/`modelCheck` to real system traces

Status: **DONE (2026-08-11).** All three items implemented and merged:
`Sys.toSpec` (item 1), `Product.toSpec`/`run_decompose`/`run_combine`/
`acc_iff`/`gsp_correct1`/`gsp_correct2` (item 2), and `modelCheck_eq`/
`modelCheck_empty_unsat`/`modelCheck_nonEmpty_sat` (item 3) — plus §5's
`AcceptingCycle.toValidLasso` generalization. `lake build` clean, 0 `sorry`,
1004 jobs. `modelCheck`'s result is now connected to real system traces
exactly as scoped below; `README.md`/`ROADMAP.md`/`ProductModelChecker.md`
updated accordingly. Implementation deviations from the design below,
found along the way, are recorded inline where they occurred (search
"Implementation-time" for each) plus a final summary in §10.

`ProbMC/` was out of scope for this document throughout (separate,
independent track — see `ROADMAP.md`).

## 0. Goal and exact scope

Three items, each re-verified against the Isabelle/HOL AFP source directly
(fetched fresh this session from the AFP GitHub mirror,
`github.com/isabelle-prover/mirror-afp-devel`, `thys/CAVA_Automata/*.thy` and
`thys/CAVA_LTL_Modelchecker/*.thy` — not from memory, and not from the
`browser_info` HTML pages quoted in earlier docs, which turned out to be too
large for the fetch tool to return past a certain point without truncation;
the raw `.thy` source is shorter and was fetched in full for every
definition/lemma quoted below):

1. **System run / system language** — CAVA's `sa.is_run`/`sa.accept`/`sa.lang`.
   Doesn't exist in this repo yet.
2. **Product-run decomposition + acceptance transfer** — CAVA's `prod_run`/
   `prod_acc`/`gsp_correct1`/`gsp_correct2`. Not ported.
3. **The top-level correctness theorem** — CAVA's `abs_model_check_correct`.
   Not proven. The Lean analogues will be named `modelCheck_empty_unsat`/
   `modelCheck_nonEmpty_sat`, mirroring `fullPipeline_empty_unsat`/
   `fullPipeline_nonEmpty_sat` (`Pipeline.lean`) both in name and in proof
   shape — `Pipeline.lean` is the direct template for item 3's wiring.

**Explicitly not in scope**: modeling Isabelle's `nres`/Refinement Framework
monadic layer (`ASSERT`/`SPEC`/`≤`-refinement). See §4 for why this is safe
to skip, with evidence from how every other phase of this port already
handled the same question.

## 1. Inventory: what's already built and needs zero new proof

The single biggest finding of this planning pass: almost all of the
*hard* graph-theoretic content item 2/3 would naively need is **already
proven, already fully generic (not BA-specific), and directly applicable to
`Product`'s graph with no modification.** This concentrates essentially all
new proof content into two places (§2 and the "combine" half of §3).

| Piece | File | Generic over? | Reusable for `Product` as-is? |
|---|---|---|---|
| `OASpec`, `isRun`/`runCompatible`/`isAcceptingRun`/`accepts` | `Acceptance.lean` | any `State`/`α`/`k` | ✅ yes — need a new `OASpec` *instance* (§2.2/§3), not new *machinery* |
| `ValidLasso`, `run`/`run_isRun`/`run_isAccepting`/`accepts_of_validLasso` | `Lasso.lean` | any `OASpec State α 1` | ✅ yes, verbatim — not BA-specific despite living next to BA code |
| `exists_acceptingCycle_of_run` (the pumping lemma) | `NestedDFS/NestedDFSTermination.lean:2033` | any `succs`/`isAccepting`/`initialStates`/`FiniteReach` | ✅ yes, verbatim — confirmed by reading its actual signature (§3.3), not BA-specific despite living in the nested-DFS file |
| `EmptinessChecker.nonEmpty_valid`/`empty_no_cycle` | `EmptinessCheck.lean` | any `State`, any algorithm | ✅ yes — `nestedDFSChecker` (the default) already refines it for `Product`'s state type with no extra work |
| `constructGBA_correct_weak`, `degeneralize_accepts_any`, `Formula.toNNF_correct_aux` | `LTLtoGBA/GraphComplete.lean`, `DegeneralBridge.lean`, `LTL/Semantics.lean` | any `ξ : OmegaWord α` | ✅ yes, unchanged — automaton-side correctness doesn't care whether a system is attached (README's "What's *not* a gap" bullet) |
| `AcceptingCycle.toValidLasso` | `OutputVerifyBA.lean:110` | ❌ currently hard-coded to `{ba : BA α}`/`ba.toSpec` | Needs generalizing to an arbitrary `OASpec State α 1` matching an `AcceptingCycle`'s own `succs`/`initialStates`/`isAccepting` — see §5. Its own docstring already says the proof is "pure repackaging, no new mathematical content," so this is low-risk, not new content. |

Net effect: item 3's proof, once items 1-2 exist, should read almost
identically to `fullPipeline_empty_unsat`/`fullPipeline_nonEmpty_sat`
already do — see §3.3/§3.4 for the side-by-side.

## 2. Item 1 — System run / system language

### 2.1 What CAVA does

`sa.is_run` is not a bespoke definition on the system side — it's inherited
from the *same* generic graph-run notion the automaton side also inherits,
via locale composition. `CAVA_Automata/Digraph.thy`:

```isabelle
locale graph_defs =
  fixes G :: "('v, 'more) graph_rec_scheme"
begin
  abbreviation "V ≡ g_V G"
  abbreviation "E ≡ g_E G"
  abbreviation "V0 ≡ g_V0 G"
  abbreviation "reachable ≡ E⇧* `` V0"
  abbreviation "succ v ≡ E `` {v}"

definition is_run
  where "is_run r ≡ r 0 ∈ V0 ∧ ipath E r"
```

`CAVA_Automata/Automata.thy`'s `sa` locale (`sa_rec` extends `graph_rec`
with just `sa_L`) then builds `accept`/`lang` directly on top of the
inherited `is_run`, composing with the system's own deterministic labeling
function:

```isabelle
locale sa =
  g?: graph G
  for G :: "('Q, 'L, 'more) sa_rec_scheme"
begin
  abbreviation L where "L ≡ sa_L G"

  definition "accept w ≡ ∃r. is_run r ∧ w = L o r"

  definition "lang ≡ Collect accept"
end
```

The key fact this confirms (already suspected, now verified against
source): **CAVA's `sa.is_run` has no notion of deadlock handling built in
at all — it's the literal, unweakened "infinite path" definition.** A state
with no outgoing edge simply cannot appear at any non-final position of any
`r` satisfying `is_run` (there is no `r(i+1)` with `(r i, r(i+1)) ∈ E`), so
such a state contributes nothing to `sa.lang` either way — CAVA's framework
has no way to express "getting stuck here should count as a violation"
*unless the client's own `g_E` already has a self-loop there before it's
ever handed to `sa_rec`*. This directly confirms (not just by inference, by
reading the actual definition) what `README.md`'s "Terminal states, and a
deliberate divergence from CAVA" section already asserts, and pins down
precisely *why* it's true: it's a structural consequence of `is_run`
requiring a literal infinite `ipath`, not a design choice CAVA states
anywhere as a precondition.

### 2.2 Design for this port

Rather than hand-write a new `SysRun`/`SysLang` pair, **reuse `OASpec`
at `k = 0`** — `OASpec`'s own docstring already says "When `k = 0`, every
run is vacuously accepting," which is exactly right: a plain Kripke
structure has no Büchi-style acceptance condition, so `isAcceptingRun` at
`k = 0` (`∀ i : Fin 0, ...`, vacuous — `Fin 0` is empty) collapses `accepts`
down to exactly `∃ σ, isRun σ ∧ runCompatible σ ξ` — **exactly** `sa.accept
w ≡ ∃r. is_run r ∧ w = L∘r`. This isn't a simplification *beyond* CAVA
either: CAVA's own `sa`/`igba` locales already share one `is_run` via
`graph_defs`, the same way `OASpec` is meant to be shared here — reusing it
at `k=0` is the CAVA-faithful reading of that shared structure, not a new
idea layered on top of it.

```lean
-- New file or a new section of Product.lean — TBD, see §6.

/-- Corresponds to CAVA's `sa_rec`/`sa` locale (`Automata.thy`) via the
`graph_defs`-shared `is_run` (`Digraph.thy`) — see §2 of
`ModelCheckCorrectnessPlan.md` for the full correspondence and why `k = 0`.

Deliberately over `Product.totalizeSucc sysSucc`, not the caller's raw
`sysSucc` — see `README.md`'s "Terminal states, and a deliberate divergence
from CAVA" and `ProductModelChecker.md`'s note on `totalizeSucc` under
"Not yet ported". -/
def Sys.toSpec {α : Type u} {SysState : Type v} [BEq α] [Hashable α]
    (sysSucc : SysState → Array SysState) (sysInit : List SysState)
    (sysLabel : SysState → Std.HashSet α) : OASpec SysState α 0 where
  trans s t := t ∈ Product.totalizeSucc sysSucc s
  initial s := s ∈ sysInit
  -- `sa_L` is a genuine deterministic function, not a many-valuations
  -- relation like the automaton side's `pos`/`neg` — see `canonicalLabel`'s
  -- own docstring in `Acceptance.lean` for why CAVA never needs a
  -- `canonicalLabel`-style construction on the system side: `iff`, not a
  -- one-directional containment check, is what recovers CAVA's `w = L∘r`.
  labelCompat s v := ∀ a, v a ↔ a ∈ sysLabel s
  acceptSet := Fin.elim0
```

`Sys.toSpec.accepts ξ` is then, definitionally (via `Fin.elim0`'s
vacuousness), exactly `sa.lang`'s membership predicate — no further
definition needed. **Fallback if this reuse turns out awkward in practice**
(e.g. if `Fin.elim0`-vacuity fights `isAcceptingRun`'s binder shape som
where a bespoke `k=0` case would be cleaner): hand-write `Sys.isRun`/
`Sys.accept`/`Sys.lang` directly mirroring `is_run`/`accept`/`lang` above,
verbatim — a strictly smaller, more mechanical fallback, not a different
design.

**Expected instance requirements**: none beyond what `Product.lean` already
needs (`[BEq α] [Hashable α]`) — no new `BEq SysState`/`Hashable SysState`
requirement, consistent with `FiniteReach`'s classless redesign
(`FiniteReachRedesign.md`) and with `Product.lean`'s current `variable`
line. Worth confirming during implementation, not assuming.

## 3. Item 2 — Product run decomposition + acceptance transfer

### 3.1 What CAVA does

All four lemmas live inside the `igba_sys_prod_precond` locale
(`CAVA_Automata/Automata.thy`), immediately after the `prod`/
`prod_finite_reachable` content `Product.lean`/`ProductModelChecker.md`
already ported:

```isabelle
locale igba_sys_prod_precond =
  igba: igba G + sa: sa S
  for G :: "('q,'l,'moreG) igba_rec_scheme"
  and S :: "('s,'l,'moreS) sa_rec_scheme"
begin
  definition "prod ≡ ⦇
    g_V = igba.V × sa.V,
    g_E = { ((q,s),(q',s')).
      igba.L q (sa.L s) ∧ (q,q') ∈ igba.E ∧ (s,s') ∈ sa.E },
    g_V0 = igba.V0 × sa.V0,
    igbg_num_acc = igba.num_acc,
    igbg_acc = (λ(q,s). if s∈sa.V then igba.acc q else {} ) ⦈"

  sublocale prod: igb_graph prod using prod_invar .

  lemma prod_run: "prod.is_run r ⟷
      igba.is_run (fst o r)
    ∧ sa.is_run (snd o r)
    ∧ (∀i. igba.L (fst (r i)) (sa.L (snd (r i))))"

  lemma prod_acc:
    assumes A: "range (snd o r) ⊆ sa.V"
    shows "prod.is_acc r ⟷ igba.is_acc (fst o r)"

  lemma gsp_correct1:
    assumes A: "prod.is_acc_run r"
    shows "sa.is_run (snd o r) ∧ (sa.L o snd o r ∈ igba.lang)"

  lemma gsp_correct2:
    assumes A: "sa.is_run r" "sa.L o r ∈ igba.lang"
    shows "∃r'. r = snd o r' ∧ prod.is_acc_run r'"
end
```

Two things worth flagging precisely, both confirmed by reading the literal
source (not inferred):

1. **`prod_acc` needs a side hypothesis, `range (snd∘r) ⊆ sa.V`** — every
   system-half state the run ever visits must lie in the system's
   (explicit) state set `sa.V`. `Product.isAccepting` (`Product.lean`)
   already dropped the analogous `s ∈ sa.V` guard from `igbg_acc` itself,
   with an explicit docstring reason: "meaningless for an open-world
   successor function... `nestedDFS`/`nestedDFSWF` never assume a `states`
   set for their generic `State` parameter either." Since our port has no
   `sa.V` at all (no explicit system state set, ever — `SysState` is an
   open-world type throughout), **the Lean `prod_acc` analogue should need
   no side hypothesis whatsoever** — a genuine simplification over CAVA's
   own lemma, not a gap, and consistent with a design decision this repo
   already made once for `Product.isAccepting` itself.
2. **`prod_run` is stated as one `↔`.** Recommend splitting into two
   one-directional Lean lemmas instead (`Product.run_decompose`,
   soundness-direction; `Product.run_combine`, completeness-direction) —
   each direction is consumed by a different one of `gsp_correct1`/
   `gsp_correct2` below and this repo's own style already prefers
   directional lemmas over `iff` where only one direction is ever used at
   a call site (e.g. `Product.reachable_imp` is already one-directional
   despite being "morally" half of a possible iff). The CAVA correspondence
   is still exactly `prod_run`, just split for Lean ergonomics — not a
   different mathematical claim.

### 3.2 Design for this port

New `OASpec (SysState × BAState) α 1` instance, mirroring `BA.toSpec`
exactly but over `Product`'s own successor/initial/accepting functions:

```lean
/-- Corresponds to instantiating `igba_sys_prod_precond.prod` as an
`OASpec`-shaped run/acceptance carrier — the Lean analogue of the `prod`
locale value itself, not just its `g_E`/`g_V0` fields `Product.getSuccessors`/
`Product.initialStates` already expose. -/
def Product.toSpec {α : Type u} {SysState : Type v} [BEq α] [Hashable α]
    (ba : BA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    OASpec (SysState × BAState) α 1 where
  trans p p' := p' ∈ Product.getSuccessors ba sysSucc sysLabel p
  initial p := p ∈ Product.initialStates ba sysInit
  labelCompat p v := ∀ a, v a ↔ a ∈ sysLabel p.1   -- unused by gsp_correct*
                                                     -- below, kept for
                                                     -- OASpec-shape parity
  acceptSet _ p := Product.isAccepting ba p
```

Four lemmas, direct port of §3.1's four (names chosen to match CAVA's for
traceability):

```lean
/-- Corresponds to `prod_run`'s "→" direction: a product run decomposes
into a BA run + a `Sys.toSpec` run that stay `compatible` at every step.
Proof: `∀n` version of `Product.reachable_imp`'s existing one-step
`hcompat`/`Array.mem_flatMap`/`Array.mem_map` case split, applied
pointwise via the run's own `trans` hypothesis at each `n`. -/
theorem Product.run_decompose (ba : BA α) (sysSucc) (sysLabel) (sysInit)
    {r : Nat → SysState × BAState}
    (hrun : (Product.toSpec ba sysSucc sysLabel sysInit).isRun r) :
    (ba.toSpec).isRun (Prod.snd ∘ r) ∧
    (Sys.toSpec sysSucc sysInit sysLabel).isRun (Prod.fst ∘ r) ∧
    ∀ n, ba.compatible (r n).2 (sysLabel (r n).1) := ...
    -- NB: (system, automaton) order here vs CAVA's (automaton, system) —
    -- same convention note `Product.lean`'s own docstring already carries.

/-- Corresponds to `prod_run`'s "←" direction (the "combine" half CAVA
folds into the same iff, split out here per §3.1's note 2): a BA run and a
`Sys.toSpec` run that agree at every step under `ba.compatible` combine
into a genuine product run. Needed by `gsp_correct2`. -/
theorem Product.run_combine (ba : BA α) (sysSucc) (sysLabel) (sysInit)
    {σ : Nat → BAState} {τ : Nat → SysState}
    (hba : (ba.toSpec).isRun σ) (hsys : (Sys.toSpec sysSucc sysInit sysLabel).isRun τ)
    (hcompat : ∀ n, ba.compatible (σ n) (sysLabel (τ n))) :
    (Product.toSpec ba sysSucc sysLabel sysInit).isRun (fun n => (τ n, σ n)) := ...

/-- Corresponds to `prod_acc` — no `range (snd∘r) ⊆ sa.V`-style side
hypothesis needed, per §3.1 note 1 (`Product.isAccepting` already dropped
CAVA's analogous guard). -/
theorem Product.acc_iff (ba : BA α) {r : Nat → SysState × BAState} (n : Nat) :
    Product.isAccepting ba (r n) = ba.isAccepting (r n).2 := rfl  -- likely
    -- this direction is definitional once toSpec/isAccepting line up;
    -- confirm during implementation rather than assuming `rfl` survives
    -- unfolding, but expect it to be near-trivial either way.

/-- Corresponds to `gsp_correct1`. Soundness direction — used directly by
`modelCheck_nonEmpty_sat` (§3.4). -/
theorem Product.gsp_correct1 (ba) (sysSucc) (sysLabel) (sysInit)
    {r : Nat → SysState × BAState}
    (hacc : (Product.toSpec ba sysSucc sysLabel sysInit).isRun r ∧
            (Product.toSpec ba sysSucc sysLabel sysInit).isAcceptingRun r) :
    (Sys.toSpec sysSucc sysInit sysLabel).isRun (Prod.fst ∘ r) ∧
    (ba.toSpec).accepts (fun n a => a ∈ sysLabel (r n).1) := ...

/-- Corresponds to `gsp_correct2`. Completeness direction — used directly
by `modelCheck_empty_unsat` (§3.4). -/
theorem Product.gsp_correct2 (ba) (sysSucc) (sysLabel) (sysInit)
    {τ : Nat → SysState}
    (hsys : (Sys.toSpec sysSucc sysInit sysLabel).isRun τ)
    (hlang : (ba.toSpec).accepts (fun n a => a ∈ sysLabel (τ n))) :
    ∃ r : Nat → SysState × BAState, τ = Prod.fst ∘ r ∧
      (Product.toSpec ba sysSucc sysLabel sysInit).isRun r ∧
      (Product.toSpec ba sysSucc sysLabel sysInit).isAcceptingRun r := ...
```

**Implementation-time addition (2026-08-11), not anticipated by the design
above**: both `gsp_correct1`/`gsp_correct2` need to move between
`BA.compatible`'s `Bool` computation (what `run_decompose`/`run_combine`
traffic in, since that's what `getSuccessors`'s runtime gate actually
computes) and `BA.toSpec.labelCompat`'s `Prop`-level `match` (what
`ba.toSpec.accepts`/`runCompatible` are stated in terms of). No existing
lemma in the codebase bridges these for an *externally supplied* valuation
like `sysLabel` — every current `labelCompat` proof
(`DegeneralBridge.lean`, `Pipeline.lean`) goes through `canonicalLabel_compat`
instead, which is specifically about a valuation *synthesized from the
automaton's own labeling*, not a real one handed in from outside. Needed,
and added, a small new private lemma:

```lean
private theorem Product.compatible_iff_labelCompat [LawfulBEq α] (ba : BA α)
    (s : BAState) (valuation : Std.HashSet α) :
    ba.compatible s valuation = true ↔ ba.toSpec.labelCompat s (fun a => a ∈ valuation)
```

proved by unfolding `BA.compatible`/`BA.getLabeling`/`BA.toSpec` and case-
splitting on `ba.labeling[s.gbaState]?`, using
`Std.HashSet.all_eq_true_iff_forall_mem`/`any_eq_false_iff_forall_mem`
(both `[LawfulBEq α]`-gated, hence the new instance requirement — harmless,
since `ModelCheck.lean`'s own `variable` block already carries
`[LawfulBEq α]` for unrelated reasons). Genuinely new content, not
mechanical repackaging of anything already in the codebase, but small
(~10 lines) and fully generic beyond `Product` — could in principle move to
`Acceptance.lean` next to `BA.toSpec` itself if a second call site for it
ever appears.

Proof technique for all four: ordinary induction/pointwise reasoning over
`Nat`, no well-founded recursion involved anywhere (`OASpec.isRun` etc. are
plain `Prop`s, not recursive `def`s) — this phase does **not** hit the
`.eq_def`/`.induct` well-founded-recursion fragility class that the
`FiniteReach`/`NestedDFSTermination` work hit (`FiniteReachRedesign.md` §5.2/
§8.6); no toy spike is warranted here for that reason (see §7). The case
splits themselves are a direct `∀n`-wrapped generalization of
`Product.reachable_imp`'s existing one-step proof, which is the concrete
evidence this is tractable, not just structurally plausible.

### 3.3 The pumping lemma is *already* fully generic — verified, not assumed

Read directly from `NestedDFS/NestedDFSTermination.lean:2033-2039`:

```lean
theorem exists_acceptingCycle_of_run
    {succs : State → Array State} {isAccepting : State → Bool}
    {initialStates : List State} (fr : FiniteReach initialStates succs)
    {σ : Nat → State} (hinit : σ 0 ∈ initialStates)
    (htrans : ∀ n, σ (n + 1) ∈ succs (σ n))
    (hacc : ∀ N, ∃ n ≥ N, isAccepting (σ n) = true) :
    ∃ _ac : AcceptingCycle initialStates succs isAccepting, True
```

No `State = BAState` anywhere in the signature. `Product.getSuccessors ba
sysSucc sysLabel`/`Product.isAccepting ba`/`Product.initialStates ba
sysInit`/`Product.finiteReach ba hbawf sysSucc sysLabel sysInit sysFR`
instantiate `succs`/`isAccepting`/`initialStates`/`fr` directly — **zero
new proof needed for the pumping-lemma step itself**, only for producing
the `σ`/`hinit`/`htrans`/`hacc` inputs it needs, which is exactly what
`Product.run_combine` (§3.2) supplies once `gsp_correct2`'s hypotheses are
in hand.

### 3.4 How item 3's proof actually reads, once items 1-2 exist

Side-by-side with `Pipeline.lean`'s existing two theorems, since this is
the direct template:

**`modelCheck_empty_unsat`** (mirrors `fullPipeline_empty_unsat`,
`Pipeline.lean`, itself the Lean shape of `abs_model_check_correct`'s `None
⇒ sa.lang sys ⊆ language_ltlc φ` case):

```lean
theorem modelCheck_empty_unsat (φ : Formula α) (sysInit) (sysSucc) (sysLabel)
    (sysFR : FiniteReach sysInit sysSucc) {n : Nat}
    (h : modelCheck (S := S) φ sysInit sysSucc sysLabel sysFR = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  intro τ hτ hviolate  -- by_contra-style: assume φ fails along τ
  -- 1. ¬φ.directSatisfies → (φ.toNNF false).satisfies, via
  --    Formula.toNNF_correct_aux (already exists, ProductModelChecker.md
  --    "already available" bullet) — no new semantic work.
  -- 2. constructGBA_correct_weak / degeneralize_accepts_any (mpr) give an
  --    accepting BA run σ compatible with (sysLabel ∘ τ), exactly as
  --    fullPipeline_empty_unsat's existing proof already does verbatim.
  -- 3. Product.run_combine (§3.2, NEW) combines τ + σ into a product run r.
  -- 4. exists_acceptingCycle_of_run (§3.3, REUSED) on Product's graph, fed
  --    from r's isRun/isAcceptingRun — gives a genuine AcceptingCycle.
  -- 5. EmptinessChecker.empty_no_cycle (REUSED) on h contradicts step 4.
  sorry -- implementation, not this plan

theorem modelCheck_nonEmpty_sat (φ : Formula α) (sysInit) (sysSucc) (sysLabel)
    (sysFR : FiniteReach sysInit sysSucc) {stem loop : List (SysState × BAState)}
    (h : modelCheck (S := S) φ sysInit sysSucc sysLabel sysFR = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  -- 1. EmptinessChecker.nonEmpty_valid (REUSED) gives an AcceptingCycle ac
  --    with ac.stem = stem, ac.cycle = loop.tail.
  -- 2. AcceptingCycle.toValidLasso, generalized per §5 (LOW-RISK NEW), plus
  --    ValidLasso.run/run_isRun/run_isAccepting (REUSED, already generic)
  --    give a genuine infinite product run r := ac.toValidLasso.run.
  -- 3. τ := Prod.fst ∘ r — a concrete witness, matching CAVA's literal
  --    `Some (Some r)` (not just an existence claim).
  -- 4. Product.gsp_correct1 (§3.2, NEW) gives τ.isRun and
  --    (ba.toSpec).accepts (sysLabel ∘ τ) directly — no canonicalLabel,
  --    no BA.WellFormed reasoning needed at all here (see callout below).
  -- 5. constructGBA_correct_weak / degeneralize_accepts_any (mpr direction
  --    on the *negated* formula) + Formula.toNNF_correct_aux turn "BA for
  --    ¬φ accepts (sysLabel∘τ)" into "¬ φ.directSatisfies (sysLabel∘τ)".
  sorry -- implementation, not this plan
```

**Callout, worth having in the plan explicitly since it's a genuine
simplification relative to `Pipeline.lean`'s own proof of
`fullPipeline_nonEmpty_sat`**: that proof needs `canonicalLabel`/
`canonicalLabel_compat`/`AcceptingCycle.run_states_mem`/`BA.WellFormed`
because it has *no real system* to draw a label from — it has to
manufacture a valuation consistent with the BA state's own pos/neg
constraints (see `canonicalLabel`'s docstring in `Acceptance.lean`, which
already names this exact contrast with CAVA's `sa_L`). `modelCheck`'s proof
does not need any of that machinery: `Product.getSuccessors`'s own
`compatible` gate *is* the per-step compatibility fact (built into every
product run by construction, surfaced directly by `Product.gsp_correct1`),
and the label itself is the caller's real `sysLabel`, not a synthesized
one. Net: item 3's `.nonEmpty` proof should be *shorter* than
`fullPipeline_nonEmpty_sat`'s, not longer, once §2/§3.2 exist.

## 4. Design decision: skip the `nres`/Refinement-Framework layer

CAVA's abstract layer is entirely `nres`-monadic (`ASSERT`/`SPEC`/`do {}`,
refined via `≤`) — `find_ce_spec`, `inter_spec`, `abs_model_check` are all
stated this way, with `dflt_inter_refine : RETURN dflt_inter ≤ inter_spec S
G` (`CAVA_LTL_Modelchecker/CAVA_Impl.thy`, locale `cava_inter_impl_loc`)
proving the *concrete* on-the-fly product refines the *abstract* spec as a
genuinely separate obligation from `abs_model_check_correct` itself.

This Lean port has never modeled that layer, at any phase, for any piece —
confirmed by grep (`nres`/`ASSERT`/`SPEC` appear nowhere in `LTLLib/`).
Every existing correctness theorem (`constructGBA_correct_weak`,
`degeneralize_accepts_any`, `nestedDFSWF_nonEmpty_valid`/`_empty_no_cycle`,
`fullPipeline_nonEmpty_sat`/`_empty_unsat`) is proven directly about the
concrete, executable Lean `def`, with no separate abstract-spec-plus-
refinement step — the "spec" and the "implementation" are the same object,
and the correctness theorem is the refinement proof, collapsed into one.
`EmptinessChecker` (`EmptinessCheck.lean`) already plays the role of
`find_ce_spec` as an *algebraic* interface (a structure with proof
obligations), not a monadic one — deliberately, per its own docstring
("Corresponds to CAVA's `find_ce_spec`... packages that same contract as an
explicit interface").

Item 3 continues this pattern exactly: `modelCheck_empty_unsat`/
`modelCheck_nonEmpty_sat` are proven directly about `modelCheck` (the
concrete `def`), the same way `fullPipeline_empty_unsat`/
`fullPipeline_nonEmpty_sat` are proven directly about `fullPipeline`. There
is no separate "prove `Product`/`ModelCheck` refines an abstract
`inter_spec`/`abs_model_check` spec" step planned, and none is needed —
`dflt_inter_refine`'s role (bridging concrete implementation to abstract
spec) is simply not a step this port has ever had, at any layer, because
the "spec" was never separated from the implementation to begin with.

## 5. `AcceptingCycle.toValidLasso` generalization

Currently (`OutputVerifyBA.lean:110`) hard-coded to `{ba : BA α}`/
`ba.toSpec`/`ba.getSuccessors`/`ba.initialStates`/`ba.isAccepting`. Its own
docstring: "pure repackaging, no new mathematical content (mirrors CAVA's
`lasso_of_prpl`)" — i.e. it's already known to be content-free beyond field
renaming.

**Update (2026-08-11): re-checked against `CAVA_Automata/Lasso.thy`
directly — generalizing is the recommended path, not just an option.**
CAVA never has a "BA version" and a "product version" of this at all:
`is_lasso`/`run_of_lasso`/`lasso_accepted` are defined *inside* the
`graph`/`gb_graph`/`b_graph`/`igb_graph` locale hierarchy (parameterized
over an abstract graph type), and `lasso_of_prpl` itself is a bare,
ungrouped polymorphic definition outside any locale. The product graph
(`igba_sys_prod_precond.prod`, §3.1) is declared via `sublocale prod:
igb_graph prod using prod_invar .` — i.e. asserted to *be* another
`igb_graph` instance — so it inherits `is_lasso`/`run_of_lasso`/
`lasso_accepted` automatically, via Isabelle's locale mechanism, with zero
new proof anywhere. This repo's own `Lasso.lean` (`ValidLasso`, `lassoRun`,
`run_isRun`/`run_isAccepting`) already mirrors that genericity fully — it's
`OASpec State α k`-generic, not BA-specific. `AcceptingCycle.toValidLasso`
being hard-coded to `BA` is therefore the divergence from CAVA (an artifact
of `fullPipeline` being its only caller when it was written), not a
faithful port of anything CAVA actually does twice. Generalize it:

```lean
def AcceptingCycle.toValidLasso {State : Type u} {α : Type v}
    {succs : State → Array State} {initialStates : List State}
    {isAccepting : State → Bool} {A : OASpec State α 1}
    (htrans : ∀ s t, t ∈ succs s ↔ A.trans s t)
    (hinit : ∀ s, s ∈ initialStates ↔ A.initial s)
    (hacc : ∀ s, isAccepting s = true ↔ A.acceptSet ⟨0, by omega⟩ s)
    (ac : AcceptingCycle initialStates succs isAccepting) :
    ValidLasso A ac.stem ac.cycle := ...
```

then reprove today's `BA`-specific version as a one-line corollary
(`htrans`/`hinit`/`hacc` all `Iff.rfl` or near-`rfl` for `ba.toSpec`), and
add the `Product.toSpec` corollary the same way. **Fallback, only if this
turns out awkward mid-implementation**: a second, fully independent
`AcceptingCycle.toValidLasso`-shaped lemma specific to `Product.toSpec`
(copy-pasting `OutputVerifyBA.lean:110-121`'s ~12 lines with `ba` replaced
by the `Product` fields) — strictly smaller, lower-risk, but not the
preferred path given the CAVA correspondence above.

## 6. File-by-file plan

| File | Change | Size | Risk |
|---|---|---|---|
| `EmptinessCheck.lean` or new `Sys.lean` | `Sys.toSpec` (§2.2) | small | low |
| `Product.lean` | `Product.toSpec`, `run_decompose`, `run_combine`, `acc_iff`, `gsp_correct1`, `gsp_correct2` (§3.2) | medium | low-medium — mechanical but genuinely new content, the dominant cost of this whole phase |
| `OutputVerifyBA.lean` | generalize `AcceptingCycle.toValidLasso` (§5), or add a `Product`-specific twin | small | low |
| `ModelCheck.lean` | `modelCheck_empty_unsat`, `modelCheck_nonEmpty_sat` (§3.4) | small-medium (mostly wiring, per §3.4's callout likely *shorter* than `Pipeline.lean`'s analogues) | low, contingent on §3.2 landing cleanly |
| `NestedDFS/NestedDFSTermination.lean`, `LTLtoGBA/GraphComplete.lean`, `DegeneralBridge.lean`, `LTL/Semantics.lean` | none — reused as-is (§1) | — | — |

No file in the already-closed `fullPipeline` chain needs to change;
nothing here touches well-founded recursion, `FiniteReach`'s internals, or
`totalizeSucc` itself (already correct and untouched by this phase — only
*used*, via `Sys.toSpec`'s `trans`).

## 7. Risk assessment

- **No well-founded-recursion fragility class** (§3.2's closing paragraph):
  everything new here is either a plain `structure`/`def` (`Sys.toSpec`,
  `Product.toSpec`) or an ordinary `∀n`-indexed induction (`run_decompose`/
  `run_combine`/`gsp_correct1`/`gsp_correct2`). The `.eq_def`/`.induct`
  fragility that forced a mandatory toy spike before touching
  `NestedDFSTermination.lean` (`FiniteReachRedesign.md` §8.6) does not apply
  here — **no toy spike gate is being proposed for this phase.**
- **Dominant cost, honestly**: §3.2's four lemmas. CAVA's own versions are
  short (a handful of lines each, `simp`/`auto`-closed in Isabelle per their
  compactness), but Lean's `Array.flatMap`/`Array.map`-based
  `Product.getSuccessors` needs the same kind of explicit
  `Array.mem_flatMap`/`Array.mem_map` unfolding `Product.reachable_imp`
  already does today — expect each of the four to be a genuine, if
  mechanical, proof, not a one-liner. Estimate: comparable in total size to
  `Product.lean`'s existing proof content (`reachable_imp`+`finiteReach`+
  the `totalizeSucc` additions), i.e. a few hundred lines, not a few
  thousand — smaller than `DegeneralBridge.lean`, let alone
  `NestedDFSTermination.lean`.
- **Item 3 risk is contingent, not independent**: once §3.2 lands, §3.4's
  wiring is close to a transcription of `Pipeline.lean`'s existing two
  theorems (confirmed side-by-side above), so its risk is mostly inherited
  from §3.2, not separate.

## 8. Execution order

1. `Sys.toSpec` (§2.2) — small, no dependencies, do first.
2. `Product.toSpec` + `run_decompose`/`run_combine`/`acc_iff` (§3.2, first
   half) — depends on §2.2.
3. `gsp_correct1`/`gsp_correct2` (§3.2, second half) — depends on step 2 and
   on `exists_acceptingCycle_of_run` (§3.3, already exists, just needs
   instantiating).
4. `AcceptingCycle.toValidLasso` generalization or twin (§5) — independent
   of steps 1-3, can be done any time before step 5.
5. `modelCheck_nonEmpty_sat` (§3.4) — depends on 1-4.
6. `modelCheck_empty_unsat` (§3.4) — depends on 1-3 only (doesn't need §5).

Steps 5-6 can be swapped or parallelized once 1-4 are done; there's no
dependency between them.

## 9. References

- `sa`/`graph_defs`/`is_run`/`accept`/`lang`: `CAVA_Automata/Digraph.thy`
  (`graph_defs`, `is_run`), `CAVA_Automata/Automata.thy` (`sa` locale).
- `igba_sys_prod_precond`, `prod`, `prod_finite_reachable`, `prod_run`,
  `prod_acc`, `gsp_correct1`, `gsp_correct2`: `CAVA_Automata/Automata.thy`.
- `find_ce_spec`, `abs_model_check`, `abs_model_check_correct`,
  `inter_spec`: `CAVA_LTL_Modelchecker/CAVA_Abstract.thy`.
- `cava_inter_impl_loc`, `dflt_inter_refine`, the executable on-the-fly
  `g_E`: `CAVA_LTL_Modelchecker/CAVA_Impl.thy`.
- All quoted verbatim this session from
  `raw.githubusercontent.com/isabelle-prover/mirror-afp-devel/master/thys/...`
  — the AFP GitHub mirror, same primary-source discipline
  `ProductModelChecker.md`/`ProofPlan.md` already used (their own
  `browser_info` HTML citations point at the same underlying source, just a
  different rendering).
- This repo's reused machinery: `Acceptance.lean` (`OASpec`), `Lasso.lean`
  (`ValidLasso`), `NestedDFS/NestedDFSTermination.lean:2033`
  (`exists_acceptingCycle_of_run`), `EmptinessCheck.lean`
  (`EmptinessChecker`), `Pipeline.lean` (proof-shape template),
  `OutputVerifyBA.lean` (`AcceptingCycle.toValidLasso`),
  `Product.lean` (`reachable_imp`, `totalizeSucc` — proof-technique
  templates for §3.2).

## 10. Implementation summary (2026-08-11)

All six execution-order steps landed in that order, each built and verified
(`lake env lean` on the touched file, then a full `lake build`) before
moving to the next, with a fresh CAVA re-fetch before each step's
implementation. Deviations from the design above, beyond the two already
recorded inline (`Product.compatible_iff_labelCompat` in §3.2, the
`toValidLasso` generalization upgrade in §5):

- **`checker` generalized, not fixed to `nestedDFSChecker`**: §3.4's
  sketch wrote `modelCheck (S := S) φ ...` without a `checker` argument
  (implicitly the default). The actual `modelCheck_empty_unsat`/
  `modelCheck_nonEmpty_sat` take `checker : EmptinessChecker (SysState ×
  BAState)` as an explicit parameter and are proven for *any* checker
  satisfying the contract — matching `ProductModelChecker.md`'s "keeping
  the correctness proof algorithm-agnostic" design note and CAVA's own
  `abs_model_check_correct` (proven once against `find_ce_spec`, not tied
  to `find_ce_impl`/nested DFS). Costs nothing extra: `EmptinessChecker.
  nonEmpty_valid`/`empty_no_cycle` were already stated this generally.
- **New `modelCheck_eq` unfolding lemma added** (`ModelCheck.lean`,
  mirroring `Pipeline.lean`'s `fullPipeline_eq`) — not mentioned in §3.4's
  sketch but needed for the same reason `fullPipeline_eq` is: `rw`-ing past
  the `createGraph`/`degeneralize` scaffolding without re-deriving
  `createGraph_term`'s totality inline in both theorems. `split` needed an
  extra `dsimp only` first here, unlike `fullPipeline_eq`'s proof — `modelCheck`
  wraps its `match` in an outer `let negNNF := ...` that `fullPipeline`
  doesn't have, and `split` can't see through the `let` unaided.
- **`Formula.toNNF_correct_neg` added to `LTL/Semantics.lean`** — a one-line
  public wrapper exposing `toNNF_correct_aux`'s already-proven negative-
  polarity half (previously `private`, hence unreachable from
  `ModelCheck.lean` despite `ProductModelChecker.md`'s "already available"
  bullet assuming it was). Purely additive: no existing theorem, proof, or
  call site in the already-closed `fullPipeline` chain changed.
- **`ModelCheck.lean` needed a new `import LTLLib.OutputVerifyBA`** for
  `AcceptingCycle.toValidLassoProduct` — not flagged in §6's file-by-file
  table, a plain oversight there (the table listed `ModelCheck.lean`'s
  *content* changes correctly, just not this dependency edge).
- **Three `omit [...] in` annotations added** (`modelCheck_eq`,
  `modelCheck_empty_unsat`, `modelCheck_nonEmpty_sat`) for section
  variables genuinely unused by each (`modelCheck_eq` needs none of
  `[LawfulHashable SysState] [LawfulBEq α] [LawfulHashable α] [DecidableEq
  α]`; the other two need all but `[LawfulHashable SysState]`) — per
  `.claude/CLAUDE.md`'s "avoid `omit ... in` warnings" instruction, read as
  "use the mechanism Lean itself suggests to resolve them cleanly," the
  reading already applied earlier in this same phase (`Product.lean`'s
  `reachable_imp`, where the fix was instead to delete the unused variables
  file-wide since nothing else in that file needed them — not an option
  here, since `modelCheck` itself and the other two theorems *do* need
  these instances).
- No toy spike was needed anywhere in this phase, confirming §7's
  prediction — every new proof was ordinary `Nat`-indexed induction or
  structure unfolding, never well-founded recursion.
