# LTLLib

A standalone Lean 4 library for LTL (Linear Temporal Logic) model-checking infrastructure. Provides the full, formally verified pipeline from LTL formulas to Büchi automata, plus a verified nested-DFS emptiness/liveness check, composed end-to-end into a total, sound-and-complete LTL satisfiability decision procedure.

The core algorithm (LTL-to-GBA via Gerth et al.) is ported from the verified Isabelle/HOL formalization in [LTL_to_GBA](https://www.isa-afp.org/entries/LTL_to_GBA.html), part of the CAVA model checking framework. Every definition includes comments referencing its counterpart there.

## Proof status

**~13,525 lines, 0 `sorry`, 0 errors** across all 24 source files (`lake build`, 759 jobs). Every top-level correctness theorem is unconditional — no admitted hypotheses, no `GraphComplete`-style assumptions, no side conditions beyond the formula `φ` itself.

The top-level result:

```lean
theorem fullPipeline_empty_unsat (φ : NNF α) {n : Nat}
    (h : fullPipeline φ = .empty n) :
    ∀ ξ : OmegaWord α, ¬ NNF.satisfies ξ φ

theorem fullPipeline_nonEmpty_sat (φ : NNF α) {stem loop : List BAState}
    (h : fullPipeline φ = .nonEmpty stem loop) :
    ∃ ξ : OmegaWord α, NNF.satisfies ξ φ
```

`fullPipeline` (`LTLLib/Pipeline.lean`) is a genuine, computable `def` — not an axiom, not `noncomputable`, not gated behind an unfinished proof. Run it on any `φ`, and whichever branch it returns comes with a machine-checked correctness guarantee.

| Correctness link in the chain | Theorem | File |
|---|---|---|
| NNF compilation preserves semantics | `toNNF_correct` | `LTL/Semantics.lean` |
| `expand`/`createGraph` terminate on every input | `createGraph_term` | `LTLtoGBA/ExpandTermination.lean` |
| Graph expansion satisfies its structural invariants | `createGraph_spec` | `LTLtoGBA/Invariants.lean` |
| Expansion graph is exhaustive (drives completeness) | `createGraph_weakGraphComplete` | `LTLtoGBA/GraphComplete.lean` |
| Computational GBA accepts exactly the models of `φ` | `constructGBA_correct_weak` | `LTLtoGBA/GraphComplete.lean` |
| `constructGBA`'s output is well-formed | `constructGBA_wellFormed` | `LTLtoGBA/Bridge.lean` |
| GBA degeneralization preserves language, any `numAcceptSets` | `degeneralize_accepts_any` | `DegeneralBridge.lean` |
| `innerDFS`/`outerDFSLoop`/`nestedDFS` are total, well-founded | `nestedDFSWF` | `NestedDFSTermination.lean` |
| `nestedDFSWF` soundness (`.nonEmpty` → genuine accepting cycle) | `nestedDFSWF_nonEmpty_valid` | `NestedDFSTermination.lean` |
| `nestedDFSWF` completeness (`.empty` → no accepting cycle) | `nestedDFSWF_empty_no_cycle` | `NestedDFSTermination.lean` |
| Accepting run ⟹ accepting cycle exists (pumping lemma) | `exists_acceptingCycle_of_run` | `NestedDFSTermination.lean` |
| Everything composed into one satisfiability decision procedure | `fullPipeline_empty_unsat` / `fullPipeline_nonEmpty_sat` | `Pipeline.lean` |

See `ProofPlan.md` for the full, session-by-session history of how each piece was ported from the Isabelle sources, including every place the Lean port had to diverge from CAVA and why. `ROADMAP.md` gives a short current-status snapshot.

## Algorithm pipeline

```
LTL formula φ  (Formula α, user-facing syntax)
    │
    ▼  toNNF                     ✓ proved correct (toNNF_correct)
φ (in NNF)     (NNF α, internal IR — the type every stage below consumes)
    │
    ▼  createGraph                ✓ totality proved (createGraph_term); ExpandSpec proved (createGraph_spec)
Node graph (ExpandState)
    │
    ▼  constructGBA               ✓ accepts ξ ↔ ξ ⊨ φ, unconditional (constructGBA_correct_weak)
Generalized Büchi Automaton (GBA)
    │
    ▼  GBA.degeneralize            ✓ accepts ξ ↔ GBA accepts ξ, unconditional, any k (degeneralize_accepts_any)
Standard Büchi Automaton (BA)
    │
    ▼  nestedDFSWF                 ✓ total, sound + complete (nestedDFSWF_empty_no_cycle / _nonEmpty_valid)
EmptinessResult: empty exploredStates | nonEmpty stem loop
```

`fullPipeline` (`Pipeline.lean`) chains all four arrows above into one function and re-derives the end-to-end satisfiability guarantee shown at the top of this file. This is a **satisfiability decision procedure** for `φ` in isolation — it does not intersect `φ`'s automaton with a system model. See "Using this library with an external model checker" below if that's what you need.

## File organization

```
LTLLib/
  LTL.lean                       -- Re-exports LTL/Syntax.lean and Semantics.lean
  LTL/
    Syntax.lean                  -- Formula (user-facing) + NNF (internal IR) + toNNF
    Semantics.lean                -- LTL/NNF denotational semantics via Lentil TLA
    Subformulas.lean              -- Subformula closure and Until-subformula extraction
    Fairness.lean                 -- Weak/strong fairness combinators encoded as LTL
  GBA.lean                        -- Generalized Büchi Automaton type + WellFormed predicate
  BA.lean                         -- Standard Büchi Automaton type + GBA degeneralization + BA.WellFormed
  Acceptance.lean                 -- Proof-level automata specs, degeneralization correctness, canonicalLabel
  DegeneralBridge.lean            -- Bridge: computational BA ↔ proof-level degeneralization (any numAcceptSets)
  LTLtoGBA/
    FSet.lean                     -- Abstract finite set typeclass (HashSet/TreeSet instances)
    Node.lean                     -- GBANode record for graph construction
    Expand.lean                   -- Gerth et al. expand/createGraph algorithm
    ExpandTermination.lean        -- Totality of expand/createGraph (well-founded, expand_ord measure)
    Construction.lean             -- GBA construction from expanded node graph
    Invariants.lean                -- Structural invariants of the expand algorithm
    Soundness.lean                 -- Soundness: GBA accepts ξ → ξ ⊨ φ
    Completeness.lean              -- Completeness: ξ ⊨ φ → GBA accepts ξ (modulo GraphComplete)
    Bridge.lean                    -- Bridge: computational GBA ↔ abstract automaton; constructGBA_wellFormed
    GraphComplete.lean              -- GraphComplete proved from createGraph; unconditional end-to-end GBA theorem
  NestedDFS.lean                  -- Reference (partial def) nested DFS emptiness check (CVWY algorithm)
  NestedDFSCorrectness.lean       -- Fuel-based nestedDFS soundness + completeness (both directions)
  NestedDFSTermination.lean       -- Total nestedDFSWF; FiniteReach; pumping lemma; fuel bridges
  Lasso.lean                      -- Abstract lasso theory (ValidLasso, lassoRun)
  OutputVerify.lean                -- Bridge: nestedDFS/AcceptingCycle output → ValidLasso → accepting run
  Pipeline.lean                    -- fullPipeline: the composed, total, verified decision procedure
```

### Module descriptions

**`LTL.lean`** — Re-exports `LTL/Syntax.lean` and `LTL/Semantics.lean`. Import this to get both formula types and their semantics.

**`LTL/Syntax.lean`** — Defines both formula types and the conversion between them:
- `NNF α` — Internal NNF (Negative Normal Form) IR where negation only appears at the atomic level (`prop`/`nprop`). Corresponds to `'a ltlr` / `'a frml` in the CAVA LTL framework. This is the representation every downstream stage consumes.
- `Formula α` — User-facing syntax with the full set of standard operators. Corresponds to `'a ltln`.
- `Formula.toNNF` — NNF compilation with a `pos : Bool` polarity parameter. Corresponds to `ltln_to_ltlr`.

**`LTL/Subformulas.lean`** — Computes the subformula closure (`subformulas`) and extracts Until-subformulas (`untilSubformulas`). Corresponds to `subfrmlsr`/`until_frmlsr`. Used both for acceptance-set construction and (via `Finset.powerset`) `expand`'s termination measure.

**`LTL/Semantics.lean`** — Denotational semantics for NNF and Formula, built on the Lentil TLA library. `NNF.toPred`, `NNF.satisfies`, `Formula.directSatisfies`, `NNF.neg_correct`, `Formula.toNNF_correct`, `tla_release`.

**`LTL/Fairness.lean`** — Weak fairness (justice) and strong fairness (compassion) encoded as standard LTL formulas.

**`GBA.lean`** — The `GBA α` structure (states, initial states, successor map, positive/negative-proposition labeling, `k` acceptance sets) and `GBA.WellFormed` (initial/successor states stay within `states`). Corresponds to `create_gba_from_nodes`'s output.

**`BA.lean`** — The `BA α` structure (single acceptance set) and `GBA.degeneralize`, the standard `k`-counter construction (Baier & Katoen, §4.3.3), states `BAState = (gbaState, acceptIdx)`. Also `BA.WellFormed`.

**`Acceptance.lean`** — Proof-level `OASpec` (unified GBA/BA spec, `k` acceptance sets), `OASpec.degeneralize`, `degeneralize_correct` (proof-level language equivalence), `GBA.toSpec`/`BA.toSpec` bridges, and `canonicalLabel`/`canonicalLabel_compat` (a deterministic per-state valuation built from a `labeling` map — see "canonical labeling" below).

**`DegeneralBridge.lean`** — `degeneralize_bridge`/`degeneralize_wellFormed`/`degeneralize_getSuccessors_mem` etc. for `numAcceptSets > 0`, their `_zero` twins for `numAcceptSets = 0` (a real, common case — any formula with no Until-subformula — that has no valid `hk : numAcceptSets > 0`), and the unifying `degeneralize_wellFormed_any`/`degeneralize_accepts_any` combining both into one theorem, unconditional over `numAcceptSets`. `degeneralize_canonicalLabel_compat` transports `canonicalLabel` compatibility from GBA to BA level for free (labeling is literally unchanged by degeneralization).

**`LTLtoGBA/FSet.lean`** — Abstract finite-set typeclass `FSet α S`, instances for `Std.HashSet`/`Std.TreeSet`.

**`LTLtoGBA/Node.lean`** — `GBANode α S` record used during graph construction. Corresponds to `'a node`.

**`LTLtoGBA/Expand.lean`** — The core Gerth et al. algorithm. `expand` (via `partial_fixpoint`) decomposes formulas into a node graph; `createGraph` is the entry point. Corresponds to `expand_body`/`expand`/`create_graph`.

**`LTLtoGBA/ExpandTermination.lean`** — `expand_term`: totality of `expand`, proved by well-founded induction on CAVA's own `expand_ord` measure (signature-set growth, then weighted-syntactic-size shrink), ported directly rather than via a fuel-indexed mirror (Lean's `expand.eq_def` suffices). `createGraph_term` assembles this at the concrete initial node.

**`LTLtoGBA/Construction.lean`** — Assembles a `GBA` from the expanded node graph (`buildStates`, `buildSuccessors`, `buildAcceptSets`, `buildLabeling`, `buildInitialStates`). Corresponds to `create_gba_from_nodes`/`build_succ`/`build_F`/`pn_map`.

**`LTLtoGBA/Invariants.lean`** — `ExpandSpec` (11 structural properties), `createGraph_spec`, proved via `expand.partial_correctness`.

**`LTLtoGBA/Soundness.lean`** — `expandOASpec_soundness`: abstract GBA accepts ξ → ξ ⊨ φ.

**`LTLtoGBA/Completeness.lean`** — `expandOASpec_completeness`: ξ ⊨ φ → abstract GBA accepts ξ, given the (here still assumed) `GraphComplete` hypothesis — the unconditional version lives in `GraphComplete.lean`.

**`LTLtoGBA/Bridge.lean`** — `constructGBA_iff_expandOASpec` (computational GBA ↔ abstract automaton), `constructGBA_wellFormed`, and `constructGBA_canonicalLabel_compat`.

**`LTLtoGBA/GraphComplete.lean`** — Proves `GraphComplete`/`WeakGraphComplete` *from* `createGraph` itself (no longer an assumption), giving the fully unconditional `constructGBA_correct_weak : (constructGBA φ st).toSpec.accepts ξ ↔ ξ ⊨ φ`.

**`NestedDFS.lean`** — The reference Courcoubetis-Vardi-Wolper-Yannakakis (CVWY) nested DFS emptiness check, as two `partial def`s (`innerDFS`/`outerDFSLoop`) kept as a readable specification layer — the verified, total entry point is `nestedDFSWF` (`NestedDFSTermination.lean`), not this file directly.

**`NestedDFSCorrectness.lean`** — Fuel-indexed proof device (`innerDFS_fuel`/`outerDFSLoop_fuel`/`nestedDFS_fuel`) proving both directions unconditionally: `.empty` → no accepting cycle (`nestedDFS_fuel_empty_no_cycle`), `.nonEmpty` → genuine `AcceptingCycle` witness (`nestedDFS_fuel_nonEmpty_valid`).

**`NestedDFSTermination.lean`** — Converts `innerDFS`/`outerDFSLoop` off `partial` (`innerDFSWF`/`innerDFSCore`, `outerDFSLoopWF`, independent well-founded recursions, not mutual — matching CAVA's own blue/red DFS structure), bridges them to the fuel-based definitions so `NestedDFSCorrectness.lean`'s proofs transfer for free, and wires up the total `nestedDFSWF`. Also: `FiniteReach` (the `fb_graph`-analogue finiteness witness), `BA.finiteReach`/`BA.WellFormed`-packaging, and the pumping lemma `exists_acceptingCycle_of_run` (CAVA's `accepted_lasso`: an accepting run over a finite reachable set yields an `AcceptingCycle`, via a finite pigeonhole).

**`Lasso.lean`** — `lassoRun`, `ValidLasso`, `run_isRun`/`run_isAccepting`/`accepts_of_validLasso`. The Lean port of CAVA's `run_of_lasso`/`lasso_accepted`.

**`OutputVerify.lean`** — `AcceptingCycle.toValidLasso` (repackaging, mirrors CAVA's `lasso_of_prpl`) and the membership lemmas (`stem_states_mem`/`cycle_states_mem`/`run_states_mem`) needed to invoke `canonicalLabel` compatibility along the derived run.

**`Pipeline.lean`** — `fullPipeline`, chaining every stage above into one total function, plus `fullPipeline_empty_unsat`/`fullPipeline_nonEmpty_sat`.

## Using this library

There are two distinct ways to use this library, depending on what you already have.

### As a standalone LTL satisfiability checker

If you just want to know whether an LTL formula is satisfiable (and get a witness trace if so), call `fullPipeline` directly — see the top of this file. No other setup needed; `createGraph_term` guarantees it's defined for every formula.

### As a component inside your own model checker

If you already have a model checker with its own state-space exploration and liveness/cycle-detection machinery, you don't need `fullPipeline`/`nestedDFSWF` at all — those are *this* library's own emptiness check, redundant with yours. What you want instead is just the automaton-construction half, to build the product yourself:

```lean
-- 1. φ : NNF α — your LTL property (or its negation, depending on your convention)
obtain ⟨st, hcg, _⟩ := createGraph_term (S := S) φ   -- always succeeds

-- 2. Build the automaton
let gba := constructGBA φ st            -- GBA α: states, initialStates, successors, labeling, acceptSets
let ba  := gba.degeneralize             -- BA α, if your product/cycle-check wants single-acceptance-set Büchi
                                         -- (skip this step and use `gba` directly if yours handles k acceptance sets)

-- 3. Correctness, fully unconditional — no side hypotheses beyond hcg
have hwf   : gba.WellFormed := constructGBA_wellFormed hcg
have hbawf : ba.WellFormed  := degeneralize_wellFormed_any gba hwf
have hcorr : ∀ ξ, ba.toSpec.accepts ξ ↔ NNF.satisfies ξ φ := fun ξ =>
  (degeneralize_accepts_any gba hwf ξ).trans (constructGBA_correct_weak hcg ξ)
```

`gba`/`ba` are plain `Std.HashMap`/`Std.HashSet`-backed data (not proof terms) — read `states`/`successors`/`labeling`/`acceptSets`/`acceptingStates` directly to drive your own product construction against your system's explored states. `labeling : HashMap Nat (HashSet α × HashSet α)` gives each automaton state's (positive, negative) atom requirements; a system state is compatible with an automaton state exactly when its valuation satisfies both (see `OASpec.labelCompat`, `Acceptance.lean`, for the precise relation — it's the same shape CAVA's own `gba_L` uses). `hwf`/`hbawf` additionally guarantee every successor reference resolves to a real state, which a correct product construction typically needs.

**What this does *not* give you**, and structurally can't: a proof that *your* product construction correctly represents *your* system's traces. That step (CAVA calls it `inter_spec`) depends entirely on your system's own state representation, which lives outside this project — see `ProofPlan.md`'s "Track B" section for the full discussion of this boundary. If your model checker and product construction are trustworthy on their own terms, gluing them to `ba`/`gba` above gives you a genuinely verified automaton at the point where they meet; whether the full assembled pipeline is end-to-end formally verified depends on whether that gluing is itself checked, which is necessarily a separate piece of work specific to your system model.

## Isabelle correspondence

Each definition includes comments referencing its counterpart in the Isabelle/HOL formalization (`LTL_to_GBA.thy`, `LTL_to_GBA_impl.thy`, `CAVA_Automata/*.thy`, `DFS_Framework/*.thy`, and the wider CAVA LTL model-checking framework). `ProofPlan.md` documents, phase by phase, exactly which CAVA lemma each Lean theorem ports, and every place the port had to diverge from CAVA's own strategy (and why).
