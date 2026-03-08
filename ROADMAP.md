# Roadmap: Verified Liveness Model Checking in Lean 4

## The Full Pipeline

```
LTL formula φ
    │
    ▼  (toNNF)                    ✅ proved correct (toNNF_correct)
NNF formula ψ
    │
    ▼  (createGraph)              ✅ ExpandSpec proved (createGraph_spec)
ExpandState (node graph)
    │
    ▼  (constructGBA)             computational, bridge NOT yet proved
GBA (generalized Büchi automaton)
    │
    ▼  (degeneralize)             ✅ proof-level proved (degeneralize_correct)
BA (standard Büchi automaton)         computational bridge NOT yet proved
    │
    ▼  (nestedDFS / emptiness)    correctness NOT yet proved
"property holds" or "counterexample"
```

### Proof-level parallel track (abstract automaton)

```
createGraph φ = some st
    ↓ createGraph_spec            ✅ gives ExpandSpec φ st.toNodes
ExpandSpec φ st.toNodes
    ↓ expandOASpec                abstract automaton from NodeData predicates
OASpec (NodeData α) α k
    ↓ expandOASpec_soundness      ✅ accepts ξ → ξ ⊨ φ
    ↓ expandOASpec_completeness   ✅ ξ ⊨ φ → accepts ξ (needs GraphComplete)
    ↓ expandOASpec_correct        ✅ accepts ξ ↔ ξ ⊨ φ (needs GraphComplete)
```

---

## Current Status

| Phase | Description | Status | File(s) |
|-------|-------------|--------|---------|
| Phase 1 | Semantic Foundations | **DONE** | `Semantics.lean` |
| Phase D | Degeneralization Correctness | **DONE** | `Acceptance.lean` |
| FSet | Abstract Finite Set Interface | **DONE** | `FSet.lean` |
| Phase 3 | Structural Invariants (ExpandSpec) | **DONE** | `Invariants.lean` |
| Phase 4.1 | Soundness (L4_8, L4_9) | **DONE** | `Soundness.lean` |
| Phase 4.2 | Completeness (L4_10) | **DONE** (modulo GraphComplete) | `Completeness.lean` |
| Phase 4.3 | GraphComplete from createGraph | Not started | — |
| Phase 5 | Nested DFS Correctness | Not started | — |
| Phase 6 | End-to-end pipeline | Not started | — |
| Phase 2 | Termination | Not started (not blocking) | — |

**Codebase: ~4234 lines, 0 sorry**

---

## Critical Path: End-to-end Proof Certificate

To go from "LTL formula" to "verified model checking result", we need a chain
of correctness theorems connecting each pipeline stage. There are two paths:

### Path A: Soundness-only (certifies "property holds")

**Goal**: If `nestedDFS` returns `empty`, then every ξ satisfies φ.

This requires only the **soundness** direction at each stage — no `GraphComplete`
needed. This is the pragmatic path to a useful proof certificate.

```
nestedDFS returns empty
    → (Nested DFS soundness) no accepting run in BA
    → (degeneralize bridge) no accepting run in computational GBA
    → (constructGBA bridge) no accepting run in expandOASpec
    → (expandOASpec_soundness) no ξ satisfies ¬φ       ← ALREADY PROVED
    → (toNNF_correct) all ξ satisfy φ                   ← ALREADY PROVED
```

| Step | What's needed | Difficulty | Status |
|------|--------------|------------|--------|
| 1. constructGBA bridge | `constructGBA` refines `expandOASpec` | Medium | Not started |
| 2. degeneralize bridge | Computational `GBA.degeneralize` refines `OASpec.degeneralize` | Medium | Not started |
| 3. Nested DFS soundness | `empty → ¬∃ accepting cycle` | Medium | Not started |
| 4. expandOASpec_soundness | accepts ξ → ξ ⊨ φ | — | **DONE** |
| 5. toNNF_correct | directSatisfies ↔ NNF.satisfies ∘ toNNF | — | **DONE** |
| 6. Executable entry point | `main` function | Easy | Not started |

This path certifies "property holds" but cannot certify counterexamples.

### Path B: Full biconditional (certifies both directions)

**Goal**: `nestedDFS` returns `empty` ↔ all ξ satisfy φ.

Everything from Path A, plus the completeness direction:

| Additional step | What's needed | Difficulty | Status |
|-----------------|--------------|------------|--------|
| GraphComplete | `createGraph` produces all satisfiable types | **Hard** | Not started |
| Nested DFS completeness | `¬∃ accepting cycle → empty` | Medium | Not started |
| Bridges (reverse) | Abstract automaton refines computational one | Medium | Not started |

### Recommended execution order

1. **constructGBA bridge** — unblocks connecting expandOASpec results to the real GBA
2. **degeneralize bridge** — connects computational GBA to computational BA
3. **Nested DFS soundness** — the final link for Path A
4. **Executable entry point** — `main` function running the pipeline
5. (Optional) GraphComplete + nested DFS completeness for Path B

---

## Bridge Details

The bridges connect computational structures (HashMap-based `GBA`, `BA`) to
abstract proof-level structures (`OASpec`, `expandOASpec`).

### constructGBA bridge

Show that `(constructGBA φ st).toSpec` and `expandOASpec φ st.toNodes φ.untilSubformulas`
accept the same words. Requires reasoning about `HashMap.fold` in `buildSuccessors`,
`buildAcceptSets`, `buildLabeling`, `buildInitialStates` — showing they faithfully
encode the `NodeData` predicates. Tedious but not conceptually hard.

### degeneralize bridge

Show that `GBA.degeneralize` (computational, in `BA.lean`) implements
`OASpec.degeneralize` (proof-level, in `Acceptance.lean`). Requires showing the
counter logic matches. Should be straightforward since both follow the same algorithm.

---

## Phase Details

### Phase 1: Semantic Foundations  ✅ DONE

**File**: `LTLLib/LTL/Semantics.lean` (~152 lines, 0 sorry)

- `OmegaWord`, `tla_release`, `NNF.toPred`, `NNF.satisfies`
- `NNF.neg_correct`, `Formula.toNNF_correct`, `Formula.directSatisfies_eq_satisfies`

### Phase D: Degeneralization Correctness  ✅ DONE

**File**: `LTLLib/Acceptance.lean` (~348 lines, 0 sorry)

- `OASpec` (unified automaton spec with k acceptance sets)
- `degeneralize_correct`: degeneralized BA accepts ↔ GBA accepts
- Helper lemmas: `counter_stays_at`, `counter_advances_from`, `counter_reaches_zero`

### FSet: Abstract Finite Set Interface  ✅ DONE

**File**: `LTLLib/LTLtoGBA/FSet.lean` (~167 lines, 0 sorry)

- Typeclass with 6 operations + 6 laws
- Instances for `Std.HashSet` and `Std.TreeSet`

### Phase 3: Structural Invariants  ✅ DONE

**File**: `LTLLib/LTLtoGBA/Invariants.lean` (~1795 lines, 0 sorry)

- `ExpandSpec` — 11 invariant properties (literal_consistent, no_false, and/or/next/
  until/release propagation, old_subformula, next_subformula, successor_old, initial_old)
- `createGraph_spec`: `createGraph φ = some st → ExpandSpec φ st.toNodes`
- Uses `expand.partial_correctness` (no termination proof needed)

### Phase 4.1: Soundness  ✅ DONE

**File**: `LTLLib/LTLtoGBA/Soundness.lean` (~369 lines, 0 sorry)

- `old_implies_satisfied` (L4_8): ψ ∈ old(σ n) → ξ.drop(n) ⊨ ψ
- `soundness` (L4_9): valid accepting run → ξ ⊨ φ
- `expandOASpec`: abstract automaton from NodeData predicates (bypasses constructGBA)
- `expandOASpec_soundness`: expandOASpec accepts ξ → ξ ⊨ φ
- `untilSubformulas_complete` / `untilSubformulas_index`

### Phase 4.2: Completeness  ✅ DONE (modulo GraphComplete)

**File**: `LTLLib/LTLtoGBA/Completeness.lean` (~164 lines, 0 sorry)

- `GraphComplete`: for any ξ ⊨ φ, ∃ run σ with old(σ n) = {ψ | subformula ∧ satisfied}
- `expandOASpec_completeness`: GraphComplete + ξ ⊨ φ → expandOASpec accepts ξ
- `expandOASpec_correct`: accepts ξ ↔ ξ ⊨ φ (combining soundness + completeness)

### Phase 5: Emptiness Check Correctness — NOT STARTED

Three layers following CAVA's architecture:

**Layer 1: Graph theory** — basic directed graph notions (finite/infinite paths,
reachability, SCCs). May reuse from cslib (`LTS.MTr`, `LTS.ωTr`).

**Layer 2: Lasso characterization** — accepting run exists iff a "lasso" (stem + cycle)
exists. This is the key mathematical bridge.

**Layer 3: Algorithm correctness** — prove `nestedDFS` correctly decides lasso existence.

Options:
- **Nested DFS verification** — prove CVWY algorithm correct (~500-1000 lines)
- **Output verification** — trust the algorithm, verify its output (pragmatic middle ground)
- **SCC-based** — Tarjan/Gabow, equivalent effort

### Phase 2: Termination — NOT STARTED (not blocking)

Remove `partial`/`partial_fixpoint` from `expand`, `innerDFS`, `outerDFSLoop`.
Not required for correctness proofs (using `partial_correctness` induction instead).

---

## File Summary

| File | Phase | Status | Lines | Sorry |
|------|-------|--------|-------|-------|
| `LTLLib/LTL/Syntax.lean` | 1 | **DONE** | ~213 | 0 |
| `LTLLib/LTL/Subformulas.lean` | 1 | **DONE** | ~73 | 0 |
| `LTLLib/LTL/Fairness.lean` | 1 | **DONE** | ~67 | 0 |
| `LTLLib/LTL/Semantics.lean` | 1 | **DONE** | ~152 | 0 |
| `LTLLib/Acceptance.lean` | 1+D | **DONE** | ~348 | 0 |
| `LTLLib/LTLtoGBA/FSet.lean` | FSet | **DONE** | ~167 | 0 |
| `LTLLib/LTLtoGBA/Node.lean` | FSet | **DONE** | ~69 | 0 |
| `LTLLib/LTLtoGBA/Expand.lean` | — | **DONE** (partial_fixpoint) | ~247 | 0 |
| `LTLLib/LTLtoGBA/Construction.lean` | FSet | **DONE** | ~119 | 0 |
| `LTLLib/LTLtoGBA/Invariants.lean` | 3 | **DONE** | ~1795 | 0 |
| `LTLLib/LTLtoGBA/Soundness.lean` | 4.1 | **DONE** | ~369 | 0 |
| `LTLLib/LTLtoGBA/Completeness.lean` | 4.2 | **DONE** | ~164 | 0 |
| `LTLLib/GBA.lean` | — | **DONE** | ~89 | 0 |
| `LTLLib/BA.lean` | — | **DONE** | ~140 | 0 |
| `LTLLib/NestedDFS.lean` | — | **DONE** (partial) | ~175 | 0 |

**Total: ~4234 lines, 0 sorry**

---

## Available Libraries

| Library | What it provides | Usefulness |
|---------|-----------------|------------|
| **Lentil** | TLA semantics, temporal operators | ✅ Core (Phase 1, 4) |
| **cslib** | `NA.Buchi`, `NA.Run`, `LTS.CanReach`, `LTS.MTr` | ✅ Useful (Phase 5 Layer 1) |
| **Mathlib** | `Quiver.Path`, general math | 🟡 Some use (Phase 5) |
| **CAVA (Isabelle)** | Reference architecture for Phases D, 5 | 📖 Reference only |
