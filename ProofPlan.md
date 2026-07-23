# LTLLib Proof Porting Plan

This document outlines the plan for porting correctness proofs from the Isabelle/HOL [LTL_to_GBA](https://www.isa-afp.org/entries/LTL_to_GBA.html) formalization to Lean 4.

## Current state

- Phases 1 (Semantics), D (Degeneralization), 4.1 (Soundness), 4.2 (Completeness) are **DONE** — sorry-free
- Phase 3 (Invariants) is essentially done but has **1 remaining sorry** in a helper lemma (`mergeIncoming_incoming`, Invariants.lean:1215) needed for `HashSet.union` membership reasoning
- **constructGBA bridge** completed — computational GBA ↔ abstract automaton (Bridge.lean, ~777 lines)
- **degeneralize bridge** completed — computational BA ↔ proof-level degeneralization (DegeneralBridge.lean, ~429 lines)
- **FSet abstraction** completed — abstract finite set typeclass with HashSet/TreeSet instances
- **2** `partial` functions remain: `innerDFS` and `outerDFSLoop` (NestedDFS.lean)
- `expand` uses `partial_fixpoint` (provides equational rewriting + `partial_correctness` induction)
- Phase 4.3 (GraphComplete) and Phase 5 (Nested DFS completeness) are **in progress**, not "not started" — see below
- **4** `sorry` total (Invariants.lean:1215; GraphComplete.lean:975; NestedDFSCorrectness.lean:640,671), **0** warnings, **~7674 lines**

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

### Phase 3: Structural invariants — ESSENTIALLY DONE (1 sorry)

**File**: `LTLLib/LTLtoGBA/Invariants.lean` (~1803 lines), **1 sorry remains**:
- `mergeIncoming_incoming` (line 1215): needs a `HashSet.union`/`insertMany` membership
  characterization to finish a case split

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

### Phase 4.3: GraphComplete from createGraph — IN PROGRESS

**Goal**: Prove `GraphComplete φ st.toNodes` from `createGraph φ = some st`.

Requires showing the expand algorithm is exhaustive: for every satisfiable
"type" (consistent set of subformulas), the algorithm generates a matching node.

**File**: `LTLLib/LTLtoGBA/GraphComplete.lean` (~1229 lines), **1 sorry remains**:
- `expand_exist_aux` is now **fully DONE** (ported directly from Isabelle's
  `expand_prop_exist`, LTL_to_GBA.thy) — `ff`, deterministic (`and`/`next`), and the
  nondet (`or`/`until`/`release`) cases are all sorry-free.
  - Two quirks worth noting for anyone touching this file again:
    1. The compiled `if`/`matches` chain in `expand`'s body doesn't `split` cleanly
       one-branch-per-case — each `split at h_result` call can surface a spurious dead
       branch first (hypothesis literally `false = true`, an artifact of how the nested
       pattern match is compiled) before reaching the real branch; dismissed with
       `exact absurd h (by decide)`.
    2. `until` cannot be used as a bare `cases ... with | until μ η => ...` alternative
       name — some dependency (likely Mathlib/Aesop) registers it as a reserved token,
       giving a confusing "unexpected token" error. Escape it with guillemets:
       `| «until» μ η => ...`.
  - The nondet case mirrors Isabelle's case 8: case-split on whether ξ satisfies a
    per-operator selector formula (`until`/`or` select on the right operand, `release`
    selects on the left), then either use the first recursive call's result directly
    (selector false) or thread through both sequential recursive calls via
    `NodesPreservedInc` (selector true). Passing `ExpandAssmExist`/`ExpandRsltExistProp`
    across the second call's renamed node (`name := nm1`) is NOT accepted by `apply`/
    `exact` via defeq even though only `.name` differs — every field (`new_sat`,
    `old_sat`, etc.) must be manually re-projected into a fresh anonymous-constructor
    value, matching the style already used elsewhere in this file for the `tt`/literal
    cases.
- `expand_all` (Theorem 3): every semantically-valid finished node has a
  semantically-valid successor node — currently a bare `sorry`, needed to drive the
  recursive completeness argument. Isabelle's `expand_prop_all` proof invokes
  `expand_prop_exist` as a black box in its base case; now that `expand_exist_aux` is
  done, this is unblocked.

**Difficulty**: High. Requires reasoning about the branching structure of expand.

### Phase 5: Nested DFS Correctness — IN PROGRESS (Phase 5a done)

**Goal**: Prove that `nestedDFS` correctly decides emptiness.

**Phase 5a (output verification) — DONE**:
- `LTLLib/Lasso.lean` (~232 lines): Abstract lasso theory — `ValidLasso` structure, `lassoRun` construction, proofs that valid lassos yield accepting runs
- `LTLLib/OutputVerify.lean` (~97 lines): Bridge from computational checks to `ValidLasso`, connecting nestedDFS output format to the abstract theory

**Phase 5b (emptiness completeness) — IN PROGRESS**:

**File**: `LTLLib/NestedDFSCorrectness.lean` (~673 lines), **2 sorries remain**:
- `outerDFSLoop_fuel_empty_no_cycle` (line 640): the CVWY/Schwoon-Esparza post-order
  argument — among accepting states on a hypothetical cycle, the one with latest
  outer-DFS finish time would see the full cycle during inner DFS, contradiction
- `nestedDFS_fuel_empty_no_cycle` (line 671): top-level theorem composing the above
  across the whole fuel-based traversal — `empty` result ⇒ no accepting cycle exists

**Why this matters**: this is the direction that makes a "no counterexample found"
(PASS) result trustworthy, as opposed to Phase 5a which only certifies that a
reported counterexample is real.

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

4. **Proof size**: The Isabelle formalization is ~3200 lines. Our Lean port is ~7346 lines (larger due to explicit bridge proofs and less automation for set-theoretic reasoning).
