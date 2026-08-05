# Roadmap: Verified LTL Model Checking in Lean 4

**Status (2026-07-27): all phases below are DONE.** `LTLLib/` is 0 `sorry`,
0 warnings-from-this-project's-own-code, ~14,114 lines, 759 build jobs. The
top-level result is `fullPipeline` (`LTLLib/Pipeline.lean`): a total,
computable LTL satisfiability decision procedure with two unconditional
correctness theorems (`fullPipeline_empty_unsat`/`fullPipeline_nonEmpty_sat`).
See `README.md` for the proof-status table and usage guide, and
`ProofPlan.md` for the full session-by-session porting history (CAVA
correspondence, every divergence and why, every gotcha hit along the way).
This file is now a short orientation snapshot, not the detailed log —
`ProofPlan.md` is the actively-maintained one.

Beyond Track B, the nested-DFS emptiness check also now includes the
**Schwoon-Esparza outer-DFS back-edge shortcut** (`outerDFSLoop`/
`outerDFSLoop_fuel`/`outerDFSLoopWF` all detect an accepting cycle directly
on a back-edge to/from an accepting state, without launching the inner DFS)
— a performance optimization ported from CAVA's `se_back_edge`, fully
proven with no new hypotheses on the completeness direction. See
`NestedDFSPlan.md`'s "Schwoon-Esparza back-edge optimization" section for
the full port write-up.

It also includes the **Holzmann-Peled-Yannakakis inner-DFS shortcut**
(`innerDFS`/`innerDFS_fuel`/`innerDFSCore` all stop as soon as they reach
*any* state on the outer DFS's current call stack, not only the literal
seed) — the other of CAVA's two nested-DFS optimizations, ported from
`Nested_DFS.thy`'s `cyan`/`run_red_dfs` stop predicate. See
`NestedDFSPlan.md`'s "Holzmann-Peled-Yannakakis inner-DFS shortcut" section
for the full port write-up, including the CAVA source analysis done before
implementing.

## The pipeline

```
LTL formula φ
    │  toNNF                      ✅ toNNF_correct
NNF formula ψ
    │  createGraph                 ✅ totality: createGraph_term · invariants: createGraph_spec
ExpandState (node graph)
    │  constructGBA                 ✅ constructGBA_correct_weak (unconditional)
GBA (generalized Büchi automaton)
    │  GBA.degeneralize              ✅ degeneralize_accepts_any (unconditional, any numAcceptSets)
BA (standard Büchi automaton)
    │  nestedDFSWF                    ✅ nestedDFSWF_empty_no_cycle / _nonEmpty_valid (total, sound + complete)
EmptinessResult: "unsatisfiable" or "satisfiable, with witness"
```

`fullPipeline` composes all five arrows into one function and one pair of
top-level theorems (`Pipeline.lean`).

## Phase status

| Phase | Description | Status | Key file(s) |
|-------|-------------|--------|--------------|
| 1 | Semantic foundations | ✅ DONE | `LTL/Semantics.lean` |
| D | Degeneralization correctness (proof level) | ✅ DONE | `Acceptance.lean` |
| FSet | Abstract finite-set interface | ✅ DONE | `LTLtoGBA/FSet.lean` |
| 3 | Structural invariants of `expand` | ✅ DONE | `LTLtoGBA/Invariants.lean` |
| 4.1 | Soundness (GBA accepts → satisfies) | ✅ DONE | `LTLtoGBA/Soundness.lean` |
| 4.2 | Completeness (satisfies → GBA accepts), conditional | ✅ DONE | `LTLtoGBA/Completeness.lean` |
| 4.3 | `GraphComplete` proved unconditionally from `createGraph` | ✅ DONE | `LTLtoGBA/GraphComplete.lean` |
| — | `constructGBA` bridge (computational ↔ abstract) | ✅ DONE | `LTLtoGBA/Bridge.lean` |
| — | `degeneralize` bridge (computational ↔ proof-level) | ✅ DONE | `DegeneralBridge.lean` |
| 2 | Termination: `expand`, `innerDFS`, `outerDFSLoop`, `nestedDFS` | ✅ DONE | `LTLtoGBA/ExpandTermination.lean`, `NestedDFS/NestedDFSTermination.lean` |
| 5b | Nested DFS completeness (`.empty` → no accepting cycle) | ✅ DONE | `NestedDFS/NestedDFSCorrectness.lean` |
| 5c | Nested DFS soundness (`.nonEmpty` → genuine witness) | ✅ DONE | `NestedDFS/NestedDFSCorrectness.lean` |
| 6 | End-to-end GBA-level theorem | ✅ DONE | `LTLtoGBA/GraphComplete.lean` |
| Track B | Genuinely runnable end-to-end pipeline | ✅ DONE | `Pipeline.lean` |

Track B additionally needed two pieces found only once the earlier phases
were assembled together — both closed, not deferred:
- **`numAcceptSets = 0`**: every `numAcceptSets > 0`-gated `degeneralize_*`
  lemma has a `_zero` twin plus a unifying `_any` wrapper
  (`DegeneralBridge.lean`), since any formula with no Until-subformula hits
  this case.
- **The pumping lemma** (`exists_acceptingCycle_of_run`,
  `NestedDFS/NestedDFSTermination.lean`): CAVA's own `accepted_lasso`, connecting
  "some accepting run exists" (word-level) to "an accepting cycle exists"
  (graph-level) — needed because CAVA needs this too, one layer out from
  its own nested-DFS theorem (`ndfs_find_ce`'s refinement proof invokes it
  explicitly).

## Known non-goals (deliberately out of scope)

- **System-intersection / product construction** (CAVA's `inter_spec`):
  this library checks LTL satisfiability directly; it does not intersect a
  formula's automaton with a system/Kripke-structure model. If you have
  your own model checker and want to build that product yourself, see
  README.md's "Using this library" section — the automaton-construction
  half (`constructGBA`/`GBA.degeneralize`, with unconditional correctness)
  is fully usable standalone for exactly that.
- **`ProbMC/`**: a separate probabilistic-model-checking library in this
  same repository/`lakefile.toml`, entirely independent of `LTLLib/` and
  untouched by the work summarized here. It has its own open `sorry` (the
  finite-horizon Bellman principle, `ProbMC/ProbStateRefinement.lean`) —
  out of scope for this file.

## File-by-file line counts

See `README.md`'s "File organization" section for descriptions; run
`find LTLLib -name "*.lean" | xargs wc -l` for current counts (they drift
as the library evolves — the total was 13,525 lines across 24 files as of
this writing).
