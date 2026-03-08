# LTLLib Proof Porting Plan

This document outlines the plan for porting correctness proofs from the Isabelle/HOL [LTL_to_GBA](https://www.isa-afp.org/entries/LTL_to_GBA.html) formalization to Lean 4.

## Current state

- Phases 1 (Semantics), D (Degeneralization), 3 (Invariants), 4.1 (Soundness), 4.2 (Completeness) are **DONE** — all sorry-free
- **constructGBA bridge** completed — computational GBA ↔ abstract automaton (Bridge.lean, ~777 lines)
- **degeneralize bridge** completed — computational BA ↔ proof-level degeneralization (DegeneralBridge.lean, ~429 lines)
- **FSet abstraction** completed — abstract finite set typeclass with HashSet/TreeSet instances
- **2** `partial` functions remain: `innerDFS` and `outerDFSLoop` (NestedDFS.lean)
- `expand` uses `partial_fixpoint` (provides equational rewriting + `partial_correctness` induction)
- **0** `sorry`, **0** warnings, **~5476 lines**

## What the Isabelle formalization proves

The top-level correctness theorem is **language equivalence**:

```isabelle
theorem create_name_gba_correct:
  "create_name_gba φ ≤ SPEC(λ𝔄. gba 𝔄 ∧ finite (g_V 𝔄) ∧
    (∀ξ. gba.accept 𝔄 ξ ↔ ξ ⊨ᵣ φ))"
```

The generated GBA accepts exactly the ω-words satisfying the LTL formula. This decomposes into:

- **Soundness (L4_9)**: If the GBA has an accepting run labeled by ξ, then `ξ ⊨ φ`. ✅ DONE
- **Completeness (L4_10)**: If `ξ ⊨ φ`, then there exists an accepting run of the GBA labeled by ξ. ✅ DONE (modulo GraphComplete)
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

### Phase 3: Structural invariants ✅ DONE

**File**: `LTLLib/LTLtoGBA/Invariants.lean` (~1795 lines, 0 sorry)

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

---

## Remaining proof phases

### Phase 4.3: GraphComplete from createGraph — NOT STARTED

**Goal**: Prove `GraphComplete φ st.toNodes` from `createGraph φ = some st`.

Requires showing the expand algorithm is exhaustive: for every satisfiable
"type" (consistent set of subformulas), the algorithm generates a matching node.

**Difficulty**: High. Requires reasoning about the branching structure of expand.

### Phase 5: Nested DFS Correctness — NOT STARTED

**Goal**: Prove that `nestedDFS` correctly decides emptiness.

**What's needed**:
1. Specification of what "accepting cycle" means
2. Soundness: `nonEmpty stem loop → stem ++ loop^ω is an accepting run`
3. Completeness: `empty → no accepting run exists`

### Phase 6: End-to-end Pipeline — NOT STARTED

**Goal**: Connect all pieces into a single theorem. Only Phase 5 is needed for the
soundness-only path (Path A). Phase 4.3 additionally needed for full biconditional.

### Phase 2: Termination — NOT STARTED (not blocking)

Remove `partial`/`partial_fixpoint` from `expand`, `innerDFS`, `outerDFSLoop`.

---

## Key challenges vs. Isabelle

1. **No refinement framework**: Isabelle's `REC`/`RECT_rule` provides well-founded recursion in a monadic setting. In Lean, we use `partial_fixpoint` + `partial_correctness` induction.

2. **Automation gap**: Isabelle's `auto`/`force`/`blast` vs Lean's `simp`/`omega`/`grind`. Set membership and HashMap fold reasoning required more manual work.

3. **Bridge proofs**: The Isabelle formalization uses refinement to connect abstract specs to implementations. In Lean, we proved explicit bridge theorems (`Bridge.lean`, `DegeneralBridge.lean`) with ~1200 lines of HashMap/HashSet fold reasoning.

4. **Proof size**: The Isabelle formalization is ~3200 lines. Our Lean port is ~5476 lines (larger due to explicit bridge proofs and less automation for set-theoretic reasoning).
