# LTLLib

A standalone Lean 4 library for LTL (Linear Temporal Logic) model checking infrastructure. Provides the full pipeline from LTL formulas to Generalized/Standard Büchi Automata construction, and nested DFS emptiness checking.

The core algorithm (LTL-to-GBA via Gerth et al.) is ported from the verified Isabelle/HOL formalization in [LTL_to_GBA](https://www.isa-afp.org/entries/LTL_to_GBA.html), part of the CAVA model checking framework.

## Proof Status

**~5805 lines, 0 sorry.** The following correctness theorems are proved:

| Theorem | Statement | File |
|---------|-----------|------|
| `toNNF_correct` | NNF compilation preserves semantics | `LTL/Semantics.lean` |
| `createGraph_spec` | Graph expansion satisfies structural invariants | `LTLtoGBA/Invariants.lean` |
| `expandOASpec_soundness` | Abstract GBA accepts ξ → ξ ⊨ φ | `LTLtoGBA/Soundness.lean` |
| `expandOASpec_completeness` | ξ ⊨ φ → abstract GBA accepts ξ (modulo `GraphComplete`) | `LTLtoGBA/Completeness.lean` |
| `constructGBA_iff_expandOASpec` | Computational GBA ↔ abstract GBA | `LTLtoGBA/Bridge.lean` |
| `degeneralize_correct` | Proof-level degeneralization preserves language | `Acceptance.lean` |
| `degeneralize_bridge` | Computational BA ↔ proof-level degeneralization | `DegeneralBridge.lean` |
| `ba_hasAcceptingRun_of_lasso` | Valid lasso → BA has accepting run | `OutputVerify.lean` |
| `ba_hasAcceptingRun_of_ndfs_output` | nestedDFS output → BA has accepting run | `OutputVerify.lean` |

**Remaining for end-to-end**: Nested DFS completeness (`empty → no accepting run`, Phase 5b) and optionally `GraphComplete` (Phase 4.3).

## File Organization

```
LTLLib/
  LTL.lean                    -- Re-exports LTL/Syntax.lean and Semantics.lean
  LTL/
    Syntax.lean                -- Formula (user-facing) + NNF (internal IR) + toNNF
    Semantics.lean             -- LTL/NNF denotational semantics via Lentil TLA
    Subformulas.lean           -- Subformula closure and Until-subformula extraction
    Fairness.lean              -- Weak/strong fairness combinators encoded as LTL
  GBA.lean                     -- Generalized Büchi Automaton type + WellFormed predicate
  BA.lean                      -- Standard Büchi Automaton type + GBA degeneralization
  Acceptance.lean              -- Proof-level automata specs + degeneralization correctness
  DegeneralBridge.lean         -- Bridge: computational BA ↔ proof-level degeneralization
  LTLtoGBA/
    FSet.lean                  -- Abstract finite set typeclass (HashSet/TreeSet instances)
    Node.lean                  -- GBANode record for graph construction
    Expand.lean                -- Gerth et al. expand/createGraph algorithm
    Construction.lean          -- GBA construction from expanded node graph
    Invariants.lean            -- Structural invariants of the expand algorithm
    Soundness.lean             -- Soundness: GBA accepts ξ → ξ ⊨ φ
    Completeness.lean          -- Completeness: ξ ⊨ φ → GBA accepts ξ (modulo GraphComplete)
    Bridge.lean                -- Bridge: computational GBA ↔ abstract automaton
  NestedDFS.lean               -- Generic nested DFS emptiness check (CVWY algorithm)
  Lasso.lean                   -- Abstract lasso theory (ValidLasso, lassoRun)
  OutputVerify.lean            -- Bridge: nestedDFS output → ValidLasso → accepting run
```

### Module Descriptions

**`LTL.lean`** — Re-exports `LTL/Syntax.lean` and `LTL/Semantics.lean`. Import this to get both formula types and their semantics.

**`LTL/Syntax.lean`** — Defines both formula types and the conversion between them:
- `NNF α` — Internal NNF (Negative Normal Form) IR where negation only appears at the atomic level (`prop`/`nprop`). Provides `neg`, `eventually`, `always`, `implies`. Corresponds to `'a ltlr` / `'a frml` in the CAVA LTL framework. This is the representation consumed by the GBA pipeline.
- `Formula α` — User-facing syntax with the full set of standard operators: `not`, `implies`, `iff`, `eventually`, `always`, etc. Corresponds to `'a ltln` in the CAVA framework.
- `Formula.toNNF` — NNF compilation with a `pos : Bool` polarity parameter. Pushes negation to atoms, desugars derived operators. Corresponds to `ltln_to_ltlr`.

**`LTL/Subformulas.lean`** — Computes the subformula closure (`subformulas`) and extracts Until-subformulas as pairs (`untilSubformulas`). Corresponds to `subfrmlsr` and `until_frmlsr` in the CAVA framework. Used for defining acceptance conditions (one set per Until-subformula).

**`LTL/Semantics.lean`** — Denotational semantics for NNF and Formula types, built on the Lentil TLA library. Defines `NNF.toPred`, `NNF.satisfies`, `Formula.directSatisfies`, and proves `NNF.neg_correct` (negation correctness) and `Formula.toNNF_correct` (NNF compilation correctness). Also defines `tla_release` (the release temporal operator).

**`LTL/Fairness.lean`** — Encodes weak fairness (justice) and strong fairness (compassion) as standard LTL formulas: `weakFairness enabled taken = □◇(¬enabled ∨ taken)` and `strongFairness enabled taken = □(□¬enabled ∨ ◇taken)`. Also provides combinators for conjunctions of fairness constraints and checking properties under fairness assumptions.

**`Acceptance.lean`** — Proof-level automaton specification `OASpec` (unified for GBA/BA with k acceptance sets). Includes `OASpec.degeneralize` (counter-cycling construction), the sorry-free `degeneralize_correct` theorem proving language equivalence, and `GBA.toSpec`/`BA.toSpec` bridges from computational to proof-level automata.

**`DegeneralBridge.lean`** — Proves that the computational `BA` produced by `GBA.degeneralize` and the proof-level `OASpec.degeneralize` accept the same ω-words. Key theorem: `degeneralize_bridge`. Uses double-fold HashMap reasoning (outer over states, inner over acceptance counter values).

**`GBA.lean`** — The `GBA α` structure representing a Generalized Büchi Automaton with states, initial states, successor map, labeling (positive/negative propositions per state), and multiple acceptance sets. Includes `GBA.WellFormed` predicate. Corresponds to `create_gba_from_nodes` output in `LTL_to_GBA.thy`.

**`BA.lean`** — The `BA α` structure for a standard (single acceptance set) Büchi Automaton, and `GBA.degeneralize` which converts a GBA to a BA. States become `BAState = (gbaState, acceptIdx)` pairs. Accepting states are `{(q, 0) | q ∈ F_0}`. Standard construction from Baier & Katoen, Section 4.3.3.

**`LTLtoGBA/FSet.lean`** — Abstract finite set typeclass `FSet α S` with operations (`empty`, `insert`, `contains`, `foldl`, `all`, `toList`) and correctness laws. Instances for `Std.HashSet` and `Std.TreeSet`. Allows swapping set implementations without changing algorithms or proofs.

**`LTLtoGBA/Node.lean`** — The `GBANode α S` record used during graph construction, parametrized by an abstract set type `S` (via `FSet`). Fields: `name` (unique ID), `incoming` (predecessor nodes), `new` (formulas to expand), `old` (expanded formulas), `next` (next-state obligations). Corresponds to `'a node` in `LTL_to_GBA.thy`.

**`LTLtoGBA/Expand.lean`** — The core Gerth et al. algorithm. `expand` is a recursive worklist procedure that decomposes LTL formulas into a graph of nodes. `createGraph` is the entry point. Corresponds to `expand_body` / `expand` / `create_graph` in `LTL_to_GBA.thy`.

**`LTLtoGBA/Construction.lean`** — Assembles a `GBA` from the expanded node graph: builds successor map from incoming edges, acceptance sets from Until-subformulas, and labeling from atomic propositions. Corresponds to `create_gba_from_nodes`, `build_succ`, `build_F`, and `pn_map` in `LTL_to_GBA.thy` / `LTL_to_GBA_impl.thy`.

**`LTLtoGBA/Invariants.lean`** — Structural invariants of the expand algorithm, proved via `partial_correctness` induction. Defines `ExpandSpec` with 11 properties (literal consistency, no false, propagation rules for and/or/next/until/release, successor inheritance, initial formula containment). Main theorem: `createGraph_spec` proves `createGraph φ = some st → ExpandSpec φ st`.

**`LTLtoGBA/Soundness.lean`** — Soundness of the abstract GBA: `expandOASpec_soundness` proves that if the abstract automaton accepts ξ, then ξ ⊨ φ. Core lemma `old_implies_satisfied` (L4_8) by structural induction. Also defines `expandOASpec` (abstract automaton bypassing HashMap reasoning).

**`LTLtoGBA/Completeness.lean`** — Completeness of the abstract GBA: `expandOASpec_completeness` proves that if ξ ⊨ φ (and `GraphComplete` holds), then the abstract automaton accepts ξ. The `GraphComplete` hypothesis is not yet proved from `createGraph`.

**`LTLtoGBA/Bridge.lean`** — Proves `constructGBA_iff_expandOASpec`: the computational `GBA` (built by `constructGBA` using HashMaps) and the abstract `expandOASpec` accept the same words. Reasoning about `HashMap.fold` in `buildSuccessors`/`buildAcceptSets`/`buildLabeling`/`buildInitialStates`.

**`NestedDFS.lean`** — Generic Courcoubetis-Vardi-Wolper-Yannakakis (CVWY) nested DFS algorithm for detecting accepting cycles. Parameterized by state type, successor function, and accepting predicate. Returns either `empty` (property holds) or `nonEmpty stem loop` (lasso-shaped counterexample). Uses explicit stack for the outer DFS and recursive inner DFS with the `innerFinished` optimization.

**`Lasso.lean`** — Abstract lasso theory for Büchi automata. Defines `lassoRun` (infinite run from stem + cycle lists), `ValidLasso` (structure capturing validity conditions: initial state, transition chains, overlap, cycle back-edge, acceptance). Proves `run_isRun` (valid transitions), `run_isAccepting` (infinitely often accepting), and `accepts_of_validLasso`. Modular arithmetic reasoning handles cycle wrapping.

**`OutputVerify.lean`** — Bridges computational nestedDFS output to the abstract `ValidLasso` theory. `ba_hasAcceptingRun_of_lasso` takes `Array.contains`/`BA.isAccepting` checks and constructs a `ValidLasso` for `BA.toSpec`. `ba_hasAcceptingRun_of_ndfs_output` handles the raw nestedDFS output format where `loop = [seed, ...seed]` and the actual cycle is `loop.tail`.

## Algorithm Pipeline

```
LTL formula φ  (Formula α, user-facing syntax)
    │
    ▼  toNNF                     ✓ proved correct
φ (in NNF)     (NNF α, internal IR)
    │
    ▼  neg
¬φ (in NNF)
    │
    ▼  createGraph                ✓ ExpandSpec proved
Node graph (ExpandState)
    │
    ▼  constructGBA               ✓ bridge proved (↔ expandOASpec)
Generalized Büchi Automaton (GBA)
    │
    ▼  degeneralize               ✓ bridge proved (↔ OASpec.degeneralize)
Standard Büchi Automaton (BA)
    │
    ▼  nestedDFS (on product with system)
EmptinessResult: empty | nonEmpty stem loop
```

## Isabelle Correspondence

Each definition includes comments referencing its counterpart in the Isabelle/HOL formalization (`LTL_to_GBA.thy`, `LTL_to_GBA_impl.thy`, and the CAVA LTL framework).
