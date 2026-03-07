# LTLLib

A standalone Lean 4 library for LTL (Linear Temporal Logic) model checking infrastructure. Provides the full pipeline from LTL formulas to Generalized/Standard Büchi Automata construction, and nested DFS emptiness checking.

The core algorithm (LTL-to-GBA via Gerth et al.) is ported from the verified Isabelle/HOL formalization in [LTL_to_GBA](https://www.isa-afp.org/entries/LTL_to_GBA.html), part of the CAVA model checking framework.

## File Organization

```
LTLLib/
  LTL.lean                    -- Re-exports LTL/Syntax.lean and Semantics.lean
  LTL/
    Syntax.lean                -- Formula (user-facing) + NNF (internal IR) + toNNF
    Semantics.lean             -- LTL/NNF denotational semantics via Lentil TLA
    Subformulas.lean           -- Subformula closure and Until-subformula extraction
    Fairness.lean              -- Weak/strong fairness combinators encoded as LTL
  GBA.lean                     -- Generalized Büchi Automaton type definition
  BA.lean                      -- Standard Büchi Automaton type + GBA degeneralization
  Acceptance.lean              -- Proof-level automata specs + degeneralization correctness
  LTLtoGBA/
    FSet.lean                  -- Abstract finite set typeclass (HashSet/TreeSet instances)
    Node.lean                  -- GBANode record for graph construction
    Expand.lean                -- Gerth et al. expand/createGraph algorithm
    Construction.lean          -- GBA construction from expanded node graph
    Invariants.lean            -- Structural invariants of the expand algorithm
  NestedDFS.lean               -- Generic nested DFS emptiness check (CVWY algorithm)
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

**`Acceptance.lean`** — Proof-level automaton specifications (`GBASpec`, `BASpec`) with `isRun`, `isAcceptingRun`, `accepts` definitions. Includes `GBASpec.degeneralize` (counter-cycling construction) and the sorry-free `degeneralize_correct` theorem proving language equivalence between GBA and BA.

**`GBA.lean`** — The `GBA α` structure representing a Generalized Büchi Automaton with states, initial states, successor map, labeling (positive/negative propositions per state), and multiple acceptance sets. Corresponds to `create_gba_from_nodes` output in `LTL_to_GBA.thy`.

**`BA.lean`** — The `BA α` structure for a standard (single acceptance set) Büchi Automaton, and `GBA.degeneralize` which converts a GBA to a BA. States become `(gbaState, acceptIdx)` pairs. Accepting states are those with `acceptIdx = 0`. Standard construction from Baier & Katoen, Section 4.3.3.

**`LTLtoGBA/FSet.lean`** — Abstract finite set typeclass `FSet α S` with operations (`empty`, `insert`, `contains`, `foldl`, `all`, `toList`) and correctness laws. Instances for `Std.HashSet` and `Std.TreeSet`. Allows swapping set implementations without changing algorithms or proofs.

**`LTLtoGBA/Node.lean`** — The `GBANode α S` record used during graph construction, parametrized by an abstract set type `S` (via `FSet`). Fields: `name` (unique ID), `incoming` (predecessor nodes), `new` (formulas to expand), `old` (expanded formulas), `next` (next-state obligations). Corresponds to `'a node` in `LTL_to_GBA.thy`.

**`LTLtoGBA/Expand.lean`** — The core Gerth et al. algorithm. `expand` is a recursive worklist procedure that decomposes LTL formulas into a graph of nodes. `createGraph` is the entry point. Corresponds to `expand_body` / `expand` / `create_graph` in `LTL_to_GBA.thy`.

**`LTLtoGBA/Construction.lean`** — Assembles a `GBA` from the expanded node graph: builds successor map from incoming edges, acceptance sets from Until-subformulas, and labeling from atomic propositions. Corresponds to `create_gba_from_nodes`, `build_succ`, `build_F`, and `pn_map` in `LTL_to_GBA.thy` / `LTL_to_GBA_impl.thy`.

**`LTLtoGBA/Invariants.lean`** — Structural invariants of the expand algorithm, proved via `partial_correctness` induction. Defines `ExpandSpec` with 9 properties (literal consistency, no false, propagation rules for and/or/next/until/release, successor inheritance, initial formula containment). Main theorem: `createGraph_spec` proves `createGraph φ = some st → ExpandSpec φ st`.

**`NestedDFS.lean`** — Generic Courcoubetis-Vardi-Wolper-Yannakakis (CVWY) nested DFS algorithm for detecting accepting cycles. Parameterized by state type, successor function, and accepting predicate. Returns either `empty` (property holds) or `nonEmpty stem loop` (lasso-shaped counterexample). Uses explicit stack for the outer DFS and recursive inner DFS with the `innerFinished` optimization.

## Algorithm Pipeline

```
LTL formula φ  (Formula α, user-facing syntax)
    │
    ▼  toNNF
φ (in NNF)     (NNF α, internal IR)
    │
    ▼  neg
¬φ (in NNF)
    │
    ▼  createGraph (Gerth et al. expand)
Node graph (ExpandState)
    │
    ▼  constructGBA
Generalized Büchi Automaton (GBA)
    │
    ▼  degeneralize
Standard Büchi Automaton (BA)
    │
    ▼  nestedDFS (on product with system)
EmptinessResult: empty | nonEmpty stem loop
```

## Isabelle Correspondence

Each definition includes comments referencing its counterpart in the Isabelle/HOL formalization (`LTL_to_GBA.thy`, `LTL_to_GBA_impl.thy`, and the CAVA LTL framework).
