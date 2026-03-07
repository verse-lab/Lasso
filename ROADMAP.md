# Roadmap: Verified Liveness Model Checking in Lean 4

## The Full Pipeline

```
LTL formula φ
    │
    ▼  (toNNF)
NNF formula ψ
    │
    ▼  (constructGBA)          Phase 3-4: prove this correct
GBA (generalized Buchi automaton)
    │
    ▼  (degeneralize)          Phase D: ✅ proved correct
BA (standard Buchi automaton)
    │
    ▼  (nestedDFS / emptiness) Phase E: prove this correct
"property holds" or "counterexample"
```

## What We're Proving

### Core theorem (Phases 1-4): GBA construction correctness

```
∀ ξ, (constructGBA φ).toSpec.Accepts ξ ↔ NNF.satisfies ξ φ
```

This is the Isabelle LTL_to_GBA formalization. It says: the GBA constructed
from an NNF formula accepts exactly the ω-words satisfying that formula.

### Extended theorem (Phase D + E): Full pipeline correctness

```
nestedDFS returns .empty ↔ ∀ ξ, ¬ Formula.satisfies ξ φ
```

This requires additionally:
- Degeneralization correctness (GBA → BA preserves language)
- Emptiness check correctness (nestedDFS correctly decides BA emptiness)

---

## Phase 1: Semantic Foundations  ✅ DONE

**Status**: All sorry-free. Builds cleanly.

| Item | Status |
|------|--------|
| `tla_release`, `NNF.toPred`, `NNF.satisfies` | ✅ |
| `NNF.neg_correct` | ✅ |
| `Formula.toNNF_correct` | ✅ |
| `GBASpec`, `BASpec`, `GBASpec.Accepts` | ✅ |
| `degeneralize_correct` | ✅ (completed in Phase D) |

## Phase 3: Structural Invariants  ✅ DONE

**Status**: All sorry-free (~1795 lines in `Invariants.lean`).

Proved using `partial_correctness` induction on `expand` — does NOT require
termination proofs (Phase 2). The `partial_fixpoint` definition provides
equational rewrite rules and a `partial_correctness` theorem.

9 invariant properties bundled in `ExpandSpec`, including propagation lemmas
for all NNF constructors, literal consistency, successor inheritance, and
initial formula containment. Main theorem: `createGraph_spec`.

Also completed: **FSet abstraction** — abstract finite set typeclass (`FSet.lean`)
with `Std.HashSet` and `Std.TreeSet` instances, applied throughout Node/Expand/
Construction/Invariants.

## Phase 2: Termination

Remove `partial` from `expand`, `innerDFS`, `outerDFSLoop`.

| Item | Approach |
|------|----------|
| `expand` termination | Lexicographic: (possible signatures − current signatures, node.new.length) |
| `innerDFS` termination | `|reachable| − |innerVisited|` |
| `outerDFSLoop` termination | Lexicographic on (outerVisited size, stack, remaining successors) |

**Note**: Phase 3 was completed WITHOUT expand termination, using `partial_correctness`
induction. Phase 4 may also be achievable without termination proofs.
`innerDFS` and `outerDFSLoop` termination is only needed for Phase E.

## Phase 4: GBA Correctness

**Soundness** (L4_8, L4_9): If the GBA accepts ξ, then ξ satisfies the formula.
- Core argument: structural induction on NNF subformulas
- Until case uses Buchi acceptance to prevent indefinite postponement

**Completeness** (L4_10): If ξ satisfies the formula, construct a GBA run.
- Uses Classical.choice to pick compatible successor nodes at each step

---

## Phase D: Degeneralization Correctness  ✅ DONE

```
∀ ξ, A.degeneralize.Accepts ξ ↔ A.Accepts ξ
```

**Status**: Sorry-free. Uses counter-cycling argument following CAVA's `Automata.thy`.

Helper lemmas proved: `counterStep_not_accept_gen`, `counterStep_accept_gen`,
`counter_stays_at`, `counter_advances_from`, `counter_reaches_zero`,
`counter_advance_to_next`.

Main proofs: `degeneralize_forward` (chains `counter_advance_to_next` by induction
on acceptance set index) and `degeneralize_backward` (uses `counter_reaches_zero` +
`Nat.find` + `counter_stays_zero`).

---

## Phase E: Emptiness Check Correctness

This is the most substantial new work beyond the Isabelle LTL_to_GBA scope.
Following CAVA's architecture, this decomposes into three layers:

### Layer 1: Graph theory foundation

Define basic directed graph notions (or reuse from cslib/Mathlib):

| Concept | cslib availability | Mathlib availability |
|---------|-------------------|---------------------|
| Finite path | `LTS.MTr` | `Quiver.Path` |
| Infinite path | `LTS.ωTr` | — |
| Reachability | `LTS.CanReach` | `Quiver.Reachable` (undirected only in SimpleGraph) |
| SCC | — | `Quiver.StronglyConnectedComponent` |
| Cycle through a set | — | — |

### Layer 2: Lasso characterization (following CAVA's Lasso.thy)

**The key mathematical bridge**: an accepting run exists iff a "lasso" exists.

```
structure Lasso (State : Type) where
  stem : List State           -- finite path from initial state to cycle entry
  cycle : List State           -- non-empty cycle

def Lasso.toRun : Lasso State → exec State   -- stem ++ cycle^ω

-- Core theorems:
theorem lasso_implies_accepting : is_lasso L → is_acc_run (L.toRun)
theorem accepting_implies_lasso : [finite reachability] → is_acc_run r → ∃ L, is_lasso L
```

This reduces "does the automaton accept any word?" to "does a lasso exist?",
which is a finite graph property (reachable cycle intersecting all acceptance sets).

### Layer 3: Algorithm correctness

Prove that the nested DFS (or an alternative algorithm) correctly decides
whether a lasso exists. This is where the algorithm meets the math.

**Option A: Nested DFS** (current implementation)
- Prove: nestedDFS returns .nonEmpty iff a lasso exists
- Requires: DFS properties (parenthesis theorem, white-path theorem)
- Reference: Lammich & Neumann, "A Framework for Verified Depth-First Algorithms"
- **No Lean 4 DFS framework exists** — would need to build from scratch

**Option B: SCC-based** (Tarjan/Gabow)
- Prove: Tarjan/Gabow correctly computes SCCs
- Then: check if any reachable SCC contains an accepting state
- Reference: "Formal Proofs of Tarjan's SCC Algorithm" (ITP 2019)
- **No verified SCC algorithm exists in Lean 4**

**Option C: Simple reachability** (pragmatic)
- Don't verify the specific algorithm
- Just prove the lasso characterization (Layer 2)
- Trust the algorithm implementation (partial correctness only)
- Can verify the algorithm's OUTPUT (if it returns a lasso, check it)

### Recommended approach

Option A or B requires significant new infrastructure (~500-1000 lines).
Option C is pragmatic but loses full verification.

A middle ground: verify the lasso characterization + a simple BFS/DFS
reachability checker (much simpler than full nested DFS correctness).

---

## Dependency Graph

```
Phase 1 (Semantics) ✅ ─────────────────────┐
                                             ▼
Phase 3 (Invariants) ✅ ──────────────► Phase 4 (GBA Correctness)
                                              │
Phase D (Degeneralization) ✅ ◄──────────────┘  (independent)
         │
         ▼
Phase 2 (Termination of DFS) ──► Phase E (Emptiness Correctness)
```

Phase 3 was completed using `partial_correctness` (no termination needed).
Phase 4 depends on Phases 1 + 3 (both done).
Phase 2 (termination) is independent — nice to have but not blocking.

---

## Available Libraries

| Library | What it provides | Usefulness |
|---------|-----------------|------------|
| **Lentil** | TLA semantics, temporal operators | ✅ Core (Phase 1, 4) |
| **cslib** | `NA.Buchi`, `NA.Run`, `LTS.CanReach`, `LTS.MTr` | ✅ Useful (Phase E Layer 1) |
| **Mathlib** | `Quiver.Path`, `Quiver.SCC`, general math | 🟡 Some use (Phase E) |
| **CAVA (Isabelle)** | Reference architecture for Phases D, E | 📖 Reference only |

---

## Estimated Effort

| Phase | Lines (est.) | Difficulty |
|-------|-------------|------------|
| ~~Phase 1 (semantics)~~ | ~~150-200~~ | ✅ DONE |
| ~~Phase D (degeneralization proof)~~ | ~~150-200~~ | ✅ DONE |
| ~~Phase 3 (invariants + FSet)~~ | ~~500~~ ~1800 actual | ✅ DONE |
| Phase 2 (expand termination) | ~200 | Hard |
| Phase 2 (DFS termination) | ~100 | Medium |
| Phase 4 (soundness + completeness) | ~800 | Hard |
| Phase E Layer 2 (lasso characterization) | ~300 | Medium |
| Phase E Layer 3 (algorithm correctness) | 500-1000 | Very Hard |
