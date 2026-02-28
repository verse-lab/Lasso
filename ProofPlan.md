# LTLLib Proof Porting Plan

This document outlines a plan for porting the correctness proofs from the Isabelle/HOL [LTL_to_GBA](https://www.isa-afp.org/entries/LTL_to_GBA.html) formalization to Lean 4.

## Current state

- Phase 1 (Semantics) and Phase D (Degeneralization) are **DONE** — all sorry-free
- **3** `partial` functions remain: `expand` (Expand.lean), `innerDFS` and `outerDFSLoop` (NestedDFS.lean)
- **0** `sorry`
- Completed: `tla_release`, `NNF.toPred`, `NNF.satisfies`, `NNF.neg_correct`, `Formula.toNNF_correct`, `GBASpec`, `BASpec`, `degeneralize_correct`

## What the Isabelle formalization proves

The top-level correctness theorem is **language equivalence**:

```isabelle
theorem create_name_gba_correct:
  "create_name_gba φ ≤ SPEC(λ𝔄. gba 𝔄 ∧ finite (g_V 𝔄) ∧
    (∀ξ. gba.accept 𝔄 ξ ↔ ξ ⊨ᵣ φ))"
```

The generated GBA accepts exactly the ω-words satisfying the LTL formula. This decomposes into:

- **Soundness (L4_9)**: If the GBA has an accepting run labeled by ξ, then `ξ ⊨ φ`.
- **Completeness (L4_10)**: If `ξ ⊨ φ`, then there exists an accepting run of the GBA labeled by ξ.
- **Termination**: `expand` always terminates (well-founded recursion).
- **Finiteness**: The generated state space is finite.

### Key intermediate results

| Isabelle reference | Statement |
|--------------------|-----------|
| `expand_ord_wf` | The termination order for `expand` is well-founded |
| `expand_all_subfrmls_propag` | All formulas in new/old/next stay within the subformula closure |
| `expand_*_propag` (~15 lemmas) | One per NNF constructor — propagation of semantic properties through expand |
| L4_6 | Initial states contain the input formula: `q ∈ V₀ → φ ∈ old(q)` |
| L4_8 | Core semantic correspondence: if `ψ ∈ old(σ(0))` and σ is an accepting run labeled by ξ, then `ξ ⊨ ψ` |
| L4_2a–c | Properties of Until/Release along accepting runs |
| Degeneralization | BA accepts iff GBA accepts (standard construction) |

### Isabelle dependencies

The formalization imports:
- **LTL semantics** from Stefan Merz's AFP formalization (`LTL.LTL`)
- **Automata theory** from CAVA (`CAVA_Automata.Automata`) — GBA/BA acceptance definitions
- **Refinement framework** (`CAVA_Base.CAVA_Base`) — nondeterministic monad, `RECT_rule` for well-founded recursion

The refinement framework is used pervasively: `expand` is defined using `REC` (well-founded recursion in the nres monad), and properties are proved via `RECT_rule`. **There is no Lean equivalent** — proofs would need to be restructured around direct well-founded induction.

---

## Proof porting phases

### Phase 1: Semantic foundations ✅ DONE

Define the denotational semantics needed to even *state* the correctness theorems. No dependency on other phases.

**LTL satisfaction** — `NNF.satisfies : (Nat → Set α) → NNF α → Prop`:

```
ξ ⊨ prop(a)     ↔  a ∈ ξ(0)
ξ ⊨ nprop(a)    ↔  a ∉ ξ(0)
ξ ⊨ φ ∧ ψ       ↔  ξ ⊨ φ ∧ ξ ⊨ ψ
ξ ⊨ φ ∨ ψ       ↔  ξ ⊨ φ ∨ ξ ⊨ ψ
ξ ⊨ X φ         ↔  (ξ ∘ (· + 1)) ⊨ φ
ξ ⊨ φ U ψ       ↔  ∃ j, suffix(j, ξ) ⊨ ψ ∧ ∀ i < j, suffix(i, ξ) ⊨ φ
ξ ⊨ φ R ψ       ↔  ∀ j, suffix(j, ξ) ⊨ ψ ∨ ∃ i < j, suffix(i, ξ) ⊨ φ
```

**Formula satisfaction** — `Formula.satisfies` on the user-facing type, plus:
- `theorem toNNF_correct : Formula.satisfies ξ φ ↔ NNF.satisfies ξ (φ.toNNF true)`

**Automata acceptance**:
- `GBA.Run`: an infinite path `σ : Nat → State` compatible with labeling
- `GBA.isAcceptingRun`: run visits every acceptance set infinitely often
- `GBA.accepts ξ`: there exists an accepting run labeled by ξ
- Same for `BA`, plus: `theorem degeneralize_correct : ba.accepts ξ ↔ gba.accepts ξ` ✅

**Key consideration**: ω-words are `Nat → Set α` (or `Nat → α → Prop`). Lean's `Set` is `α → Prop`, so this is `Nat → α → Prop`. The `suffix` operation is `fun j ξ i => ξ (i + j)`.

### Phase 2: Termination

Remove `partial` from the three functions. Independent of Phase 1.

**`expand` termination** — the Isabelle measure is:

```
expand_ord φ = inv_image
  (finite_psupset (old_next_limit φ) ×lex less_than)
  (λ(n, ns). (old_next_pair ` ns, size_set (new n)))
```

In words: the pair `(set of (old, next) pairs across all finished nodes, size of new-formulas in current node)` decreases lexicographically. The first component can only grow finitely (bounded by `𝒫(subformulas(φ)) × 𝒫(subformulas(φ))`), and the second component decreases on each expansion step.

Steps:
1. Prove `subformulas φ` is finite (structural induction)
2. Prove all formulas in new/old/next are subformulas of the input
3. Define the well-founded measure in Lean (`WellFoundedRelation` or `termination_by`)
4. Show the measure decreases on each recursive call of `expand`

This is the hardest part of Phase 2. The Isabelle proof uses ~200 lines for the termination argument.

**`innerDFS` / `outerDFSLoop` termination** — these are simpler DFS traversals. Termination follows from the visited-set growing monotonically on a finite state space. However, the state space is only finite if the input automaton is finite (which follows from Phase 2's expand termination + subformula finiteness). For a standalone termination proof, we'd need to take finiteness as a precondition.

### Phase 3: Structural invariants

Depends on Phase 2 (needs non-partial `expand` to do induction on).

The ~15 **propagation lemmas** show that expand preserves semantic properties. Each has the form: "if property P holds before expanding formula φ, then P holds after." One lemma per NNF constructor:

- `expand_false_propag`: ⊥ ∈ old(q) → q is discarded
- `expand_and_propag`: (φ ∧ ψ) ∈ old(q) → φ ∈ old(q) ∧ ψ ∈ old(q)
- `expand_or_propag`: (φ ∨ ψ) ∈ old(q) → φ ∈ old(q) ∨ ψ ∈ old(q)
- `expand_next_propag`: (X φ) ∈ old(q) → φ ∈ next(q)
- `expand_until_propag`: (φ U ψ) ∈ old(q) → (φ U ψ) ∈ next(q) ∨ ψ ∈ old(q)
- `expand_release_propag`: similar for Release
- etc.

Plus the global invariant: all formulas in any node's new/old/next are subformulas of the input formula.

### Phase 4: Main correctness theorems

Depends on Phases 1–3.

**Soundness (L4_8 → L4_9)**: By structural induction on ψ. Given an accepting run σ of the GBA labeled by ξ, and ψ ∈ old(σ(0)), show `ξ ⊨ ψ`. Uses:
- Propagation lemmas (Phase 3) to know what's in old/next of each node
- The acceptance condition for Until-subformulas
- L4_2a–c for temporal operators along runs

**Completeness (L4_10)**: Construct a witness run `auto_run` that maps each position to a compatible node. Show this run is accepting. Uses:
- For each position i and formula in old(σ(i)), the truth of the formula at suffix(i, ξ) determines which successor to choose
- The key insight: `auto_run` picks nodes greedily based on which formulas are true at each step

**Degeneralization correctness**: Show `BA.accepts ξ ↔ GBA.accepts ξ` for the standard (q, counter) construction. Relatively straightforward — the counter cycles through acceptance sets.

---

## Dependency graph

```
Phase 1 (Semantics)          Phase 2 (Termination)
        │                            │
        │                            │
        └──────────┬─────────────────┘
                   │
           Phase 3 (Invariants)
                   │
           Phase 4 (Soundness + Completeness)
```

## Key challenges vs. Isabelle

1. **No refinement framework**: Isabelle's `REC`/`RECT_rule` provides well-founded recursion in a monadic setting with built-in termination reasoning. In Lean, we'd use `WellFounded.fix` or `termination_by` with explicit decreasing proofs.

2. **Automation gap**: Isabelle's `auto`/`force`/`blast` tactics handle set-theoretic reasoning automatically. Lean's `simp`/`omega`/`aesop` cover different ground. Set membership, subset, and finiteness proofs may require more manual work.

3. **Infinite objects**: Isabelle has `'a word = nat ⇒ 'a` for ω-words with a mature library. Lean has no standard ω-word library — we'd define `def OmegaWord (α : Type) := Nat → α` and build basic infrastructure (suffix, prefix, etc.).

4. **Proof size**: The Isabelle formalization is ~3200 lines of proof in `LTL_to_GBA.thy` plus ~1000 lines in the implementation refinement file. A Lean port would likely be comparable or larger due to less automation for set-theoretic reasoning.

## Estimated effort

| Phase | Isabelle lines | Estimated Lean effort |
|-------|---------------|----------------------|
| ~~Phase 1: Semantics~~ | ~~~200~~ | ✅ DONE |
| Phase 2: Termination | ~400 | Hard — restructure from refinement framework to direct WF induction |
| Phase 3: Invariants | ~1000 | Medium-Hard — mechanical but tedious, ~15 propagation lemmas |
| Phase 4: Main theorems | ~1800 | Hard — soundness induction + completeness witness construction |
