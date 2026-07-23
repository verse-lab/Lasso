# LTLLib Proof Porting Plan

This document outlines the plan for porting correctness proofs from the Isabelle/HOL [LTL_to_GBA](https://www.isa-afp.org/entries/LTL_to_GBA.html) formalization to Lean 4.

## Current state

- Phases 1 (Semantics), D (Degeneralization), 4.1 (Soundness), 4.2 (Completeness) are **DONE** — sorry-free
- **Phase 4.3 (GraphComplete) is now fully DONE** — `GraphComplete.lean` is entirely sorry-free, and
  `expandOASpec_completeness_weak` is a **fully unconditional completeness theorem** (no longer
  gated behind an assumed `GraphComplete`/`WeakGraphComplete` hypothesis)
- Phase 3 (Invariants) is essentially done but has **1 remaining sorry** in a helper lemma (`mergeIncoming_incoming`, Invariants.lean:1215) needed for `HashSet.union` membership reasoning
- **constructGBA bridge** completed — computational GBA ↔ abstract automaton (Bridge.lean, ~777 lines)
- **degeneralize bridge** completed — computational BA ↔ proof-level degeneralization (DegeneralBridge.lean, ~429 lines)
- **FSet abstraction** completed — abstract finite set typeclass with HashSet/TreeSet instances
- **2** `partial` functions remain: `innerDFS` and `outerDFSLoop` (NestedDFS.lean)
- `expand` uses `partial_fixpoint` (provides equational rewriting + `partial_correctness` induction)
- Phase 5 (Nested DFS completeness) is **in progress** — see below
- **3** `sorry` total (Invariants.lean:1215; NestedDFSCorrectness.lean:640,671), **0** warnings, **~8058 lines**

## What the Isabelle formalization proves

The top-level correctness theorem is **language equivalence**:

```isabelle
theorem create_name_gba_correct:
  "create_name_gba φ ≤ SPEC(λ𝔄. gba 𝔄 ∧ finite (g_V 𝔄) ∧
    (∀ξ. gba.accept 𝔄 ξ ↔ ξ ⊨ᵣ φ))"
```

The generated GBA accepts exactly the ω-words satisfying the LTL formula. This decomposes into:

- **Soundness (L4_9)**: If the GBA has an accepting run labeled by ξ, then `ξ ⊨ φ`. ✅ DONE
- **Completeness (L4_10)**: If `ξ ⊨ φ`, then there exists an accepting run of the GBA labeled by ξ. ✅ DONE, unconditionally (`expandOASpec_completeness_weak`)
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

### Phase 4.3: GraphComplete from createGraph ✅ DONE

**Goal**: Prove `GraphComplete φ st.toNodes` from `createGraph φ = some st` — i.e. show
the expand algorithm is exhaustive: for every satisfiable "type" (consistent set of
subformulas), the algorithm generates a matching node.

**File**: `LTLLib/LTLtoGBA/GraphComplete.lean` (~1613 lines, 0 sorry). Ends in
`expandOASpec_completeness_weak`: a fully unconditional completeness theorem (uses
`WeakGraphComplete`, a slightly weaker but sufficient variant of `GraphComplete` that
doesn't need the `old ↔` reverse direction — see `Completeness.lean` vs this file's
`expandOASpec_completeness_weak`/`expandOASpec_completeness`).

- `expand_exist_aux` (Theorem 1, ports Isabelle's `expand_prop_exist`): if all formulas
  in a node are satisfied by ξ, the output contains a finished node also satisfying ξ.
- `expand_all` (Theorem 3, ports Isabelle's `expand_prop_all`): every semantically-valid
  finished node has a semantically-valid successor at `ξ.drop 1`. This is the theorem
  that actually drives graph completeness, and it needed a structurally different proof
  strategy from Theorem 1 — see below.

**Quirks worth knowing before touching this file again**:
1. The compiled `if`/`matches` chain in `expand`'s body doesn't `split` cleanly
   one-branch-per-case — each `split at h_result` call can surface a spurious dead
   branch first (hypothesis literally `false = true`, an artifact of how the nested
   pattern match is compiled) before reaching the real branch; dismissed with
   `exact absurd h (by decide)`. Once a hypothesis like `h_nottt : node.new.head! = tt →
   False` is already in scope from an *outer* level, a fresh `split` at a *deeper* level
   can also land on a genuinely-live "wrong branch" goal (not a compiler artifact) whose
   only closing move is `exact absurd <the-outer-equation> h` — don't reach for
   `by decide` reflexively; check whether the branch is truly dead first.
2. `until` cannot be used as a bare `cases ... with | until μ η => ...` alternative
   name — some dependency (likely Mathlib/Aesop) registers it as a reserved token,
   giving a confusing "unexpected token" error. Escape it with guillemets:
   `| «until» μ η => ...`.
3. Passing `ExpandAssmExist`/`ExpandRsltExistProp`/`ExpandAssmExist` values across a
   record that differs *only* in one field (e.g. a renamed node, `name := nm1`) is NOT
   accepted by `apply`/`exact` via defeq, even though the structure in question never
   inspects that field. Every field must be manually re-projected into a fresh
   anonymous-constructor value (`⟨h.new_sat, h.old_sat, ...⟩`) — bare term reuse fails
   with a confusing "Application type mismatch" pointing at an unrelated hypothesis.
4. **`expand_all`'s proof needed a genuinely different trick from `expand_exist_aux`**:
   `expand.partial_correctness`'s induction only ever hands you an `expand_ih`-typed
   equation for recursive sub-calls (a bound placeholder standing in for "the recursive
   call"), which cannot be fed to already-proven lemmas about the *real* `expand`
   (`expand_exist`, `expand_nodesPreservedInc`, `expand_key_eq_name`) — those need a
   genuine `expand node st = some r`. Isabelle sidesteps this because its refinement
   framework hands every recursive step an explicit `f x ≤ expand x` monotonicity fact
   (`f_sup`) it can compose via `order_trans`; Lean's `partial_fixpoint`-generated
   induction doesn't expose an equivalent. The fix: bundle `expand node st = some r`
   itself as an extra conjunct in the induction's own motive (alongside the desired
   property), proven generically by mirroring `h_result`'s own case split. Once that's
   available via `ih`, the already-proven external lemmas can be invoked freely on
   recursive sub-calls, exactly like Isabelle's `order_trans` composition.
5. `expand_key_eq_name` (new lemma, key-equals-`.name` structural invariant) was needed
   because `expand_all`'s hypothesis was changed from `h_name_ident` (injectivity of
   `.name` among stored nodes) to the stronger, purely structural `h_key_eq : ∀ k n,
   st.nodes[k]? = some n → n.name = k` — the former isn't preserved by insertion without
   knowing a fresh key doesn't collide with some *other* key's stored `.name`, which is
   exactly what `h_key_eq` (trivial to establish, since every insertion in `Expand.lean`
   uses `<value>.name` as the key) gives for free.

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

**Goal**: Connect all pieces into a single theorem. Phase 4.3 is now done, so only
Phase 5 (nested DFS emptiness completeness) still blocks the full biconditional.

### Phase 2: Termination — NOT STARTED (not blocking)

Remove `partial`/`partial_fixpoint` from `expand`, `innerDFS`, `outerDFSLoop`.

---

## Key challenges vs. Isabelle

1. **No refinement framework**: Isabelle's `REC`/`RECT_rule` provides well-founded recursion in a monadic setting. In Lean, we use `partial_fixpoint` + `partial_correctness` induction.

2. **Automation gap**: Isabelle's `auto`/`force`/`blast` vs Lean's `simp`/`omega`/`grind`. Set membership and HashMap fold reasoning required more manual work.

3. **Bridge proofs**: The Isabelle formalization uses refinement to connect abstract specs to implementations. In Lean, we proved explicit bridge theorems (`Bridge.lean`, `DegeneralBridge.lean`) with ~1200 lines of HashMap/HashSet fold reasoning.

4. **Proof size**: The Isabelle formalization is ~3200 lines. Our Lean port is ~8058 lines (larger due to explicit bridge proofs and less automation for set-theoretic reasoning).

5. **No exposed monotonicity fact for recursive calls**: Isabelle's refinement framework
   hands every recursive step an explicit `f x ≤ expand x` fact (`f_sup`) usable via
   `order_trans` to compose already-proven lemmas about `expand` at a recursive call site.
   Lean's `partial_fixpoint`-generated `expand.partial_correctness` only ever gives an
   `expand_ih`-typed equation, with no equivalent bridge back to the real `expand`. The
   workaround (used in `expand_all`, see Phase 4.3 above): bundle `expand node st = some r`
   itself into the induction's motive as an extra conjunct, proven alongside the actual
   property — then it's available via `ih` wherever an external `expand`-based lemma is
   needed on a recursive sub-call.
