# Plan: Degeneralization Correctness Proof (Phase D) — ✅ DONE

## Status

**COMPLETED.** Both sorry's filled. Builds cleanly with 0 sorry, 0 warnings.
This remains accurate — `Acceptance.lean`'s `degeneralize_correct` hasn't
changed since. (2026-07-27 note: the whole LTL-to-GBA-to-emptiness pipeline
this was one early piece of is now fully done end-to-end — see
`README.md`/`ProofPlan.md`. The **"Previous Plan (for reference)" section
below this one is pre-implementation planning from before any of Phases
2-4 were actually built**, and is now substantially wrong as a description
of the codebase — type names (`GBA.Spec`/`BA.Spec`), file names
(`SubformulaFinite.lean`, `Correctness.lean`), and theorem names
(`gba_correct`) it mentions don't match what was actually built (`OASpec`,
`Invariants.lean`/`GraphComplete.lean`/`Pipeline.lean`,
`constructGBA_correct_weak`/`fullPipeline_*`). Kept only for historical
interest in how the plan evolved; treat `ProofPlan.md` as authoritative for
anything below this line.)

The actual proof followed the "simpler alternative" approach (CAVA's `degen_run_find_acc_aux`)
rather than the `Frequently` API approach. Used `Nat.find` from `Mathlib.Order.Nat`.

## Original Context

Phase 1 is mostly complete: `Semantics.lean` is sorry-free, `Acceptance.lean` has all
definitions (`GBASpec`, `BASpec`, `GBASpec.degeneralize`, `counterStep`, `mkCounter`) and
3 helper lemmas (`counterStep_zero_not_accept`, `counterStep_zero_accept`, `counter_stays_zero`).
Two `sorry`s remain in `degeneralize_correct` (lines 210, 253 of `Acceptance.lean`).

This plan fills in both sorry's, following the proof structure from CAVA's `Automata.thy`
(lines 976-1252).

## File to modify

`LTLLib/Acceptance.lean`

## Proof architecture (following CAVA)

CAVA decomposes the proof into 6 intermediate lemmas. We port the same structure:

### Helper lemmas to add (before the two main theorems)

**1. `counterStep_at_c` — Counter behavior at arbitrary value c**

Generalization of `counterStep_zero_not_accept`/`counterStep_zero_accept`:
- If `acceptSet c (σ n)`: counter advances from c to `(c+1) % (max 1 k)`
- If `¬ acceptSet c (σ n)`: counter stays at c
- When `k > 0` and `c : Fin (max 1 k)`, `c.val < k`, so `c.val % k = c.val`

**2. `counter_stays_at` — Counter stays at value c until F_c is visited**

Generalization of `counter_stays_zero` to arbitrary counter value c (not just 0).
Proof: induction on `m`, same structure as `counter_stays_zero`.

**3. `counter_first_visit` — At the first visit to F_c, counter is still c**

Given `mkCounter σ n = c` and `hacc : ∀ k, ∃ j, acceptSet c (σ (k+j))`,
use `Nat.find` to get the smallest `j` with `acceptSet c (σ (n+j))`.
By `counter_stays_at`, counter is still c at position `n+j`.
So counter advances to `(c+1) % (max 1 k)` at position `n+j+1`.

This corresponds to CAVA's `degen_acc_run_complete_aux1` (using LEAST).

**4. `counter_advances_from` — Counter eventually advances past c**

Given `mkCounter σ n = c` and all acceptance sets visited i.o.,
∃ m > n such that `mkCounter σ m = ⟨(c.val + 1) % (max 1 k), _⟩`.

Direct corollary of `counter_first_visit`.

**5. `counter_reaches_zero` — Counter eventually reaches 0 from any value**

Given all acceptance sets visited i.o., for any n:
∃ m ≥ n such that `mkCounter σ m = ⟨0, _⟩`.

Proof: well-founded induction on `max 1 k - c.val` (distance to 0).
- If c = 0: immediate (m = n).
- If c > 0: by `counter_advances_from`, counter reaches `(c+1) % (max 1 k)`.
  If this is 0, done. Otherwise distance decreased, apply IH.

This corresponds to CAVA's `degen_acc_run_complete_aux2`.

### Filling sorry 1: `degeneralize_backward` (GBA accepts → BA accepts)

**Goal**: Show `∀ n, ∃ j, accepting (σ_ba (n + j))` where accepting = counter 0 ∧ F_0.

Proof (for `k > 0` case):
1. Use `counter_reaches_zero` to find `m ≥ n` with `mkCounter σ m = ⟨0, _⟩`
2. At counter 0, use `counter_stays_zero` + `Nat.find` (same as existing `counter_stays_zero` logic):
   since F_0 is visited i.o., find first visit to F_0 at position `m + j₀`.
   Counter is still 0 at that point. So counter = 0 ∧ F_0 visited.

### Filling sorry 2: `degeneralize_forward` (BA accepts → GBA accepts)

**Goal**: Show `∀ i : Fin k, ∀ n, ∃ j, acceptSet i (σ_gba (n + j))`.

Proof for each `i`:
- For `i = 0`: directly from BA acceptance (counter = 0 ∧ F_0 visited i.o.)
- For `i > 0`: by contradiction using `not_frequently` from Mathlib.
  If F_i is visited only finitely often (i.e., `∀ᶠ n in atTop, ¬ acceptSet i (σ n)`),
  then from some point N onward, F_i is never visited.
  The counter can never advance past i after N.
  So the counter never returns to 0 after N.
  But BA acceptance says counter = 0 ∧ F_0 infinitely often. Contradiction.

  Key Mathlib lemma: `not_frequently : (¬∃ᶠ x in f, p x) ↔ ∀ᶠ x in f, ¬p x`
  and `frequently_atTop : (∃ᶠ n in atTop, p n) ↔ ∀ a, ∃ b ≥ a, p b`.

  We'll need a helper `counter_stuck_at` showing: if F_c is never visited after N
  and counter(N) ≤ c, then counter stays ≤ c forever. This means counter never
  reaches 0 again (since c > 0 blocks it from cycling).

  Alternatively (simpler): direct argument without `Frequently` API.
  Since BA acceptance gives infinitely many positions with counter = 0 ∧ F_0,
  pick two consecutive such positions m₁ < m₂. Between m₁ and m₂:
  - At m₁: counter = 0, F_0 visited → counter advances to 1
  - Counter must go 1 → 2 → ... → k-1 → 0 to return to 0 at m₂
  - When counter goes from i to i+1, F_i is visited at that step
  - So F_i is visited between m₁ and m₂, which is ≥ n (if we choose m₁ ≥ n)

  This is CAVA's `degen_run_find_acc_aux` approach and avoids the contradiction argument.

### Reusable infrastructure

| What | Source | How used |
|------|--------|----------|
| `Nat.find` / `Nat.find_spec` / `Nat.find_min` | Lean core | Find first visit to acceptance set |
| `frequently_atTop` | Mathlib `Order.Filter.AtTopBot.Basic` | Equivalence between our `∀ k, ∃ j` and `∃ᶠ` |
| `not_frequently` | Mathlib `Order.Filter.Basic` | Forward direction contradiction |
| `counterStep`, `mkCounter` | Already defined | Counter construction |
| `counter_stays_zero` | Already proved | Backward direction at counter 0 |
| `counterStep_zero_not_accept/accept` | Already proved | Counter behavior at 0 |
| CAVA `degen_acc_run_complete_aux1/aux2` | Reference only | Proof structure |

## Implementation order

1. Add `import Mathlib.Order.Filter.AtTopBot.Basic` to Acceptance.lean
2. Add generalized helper lemmas (items 1-5 above)
3. Fill in `degeneralize_backward` sorry
4. Fill in `degeneralize_forward` sorry
5. Verify: `lake build LTLLib.Acceptance` — no sorry warnings

## Verification

```
lake build LTLLib.Acceptance 2>&1 | grep -E "sorry|error"
# Expected: no output (no sorry, no errors)

lake build 2>&1 | tail -5
# Expected: "Build completed successfully"
```

---

# Previous Plan (for reference)

## Phase 1: Semantic Foundations

No dependency on other phases. Establishes the definitions needed to **state** correctness theorems.

### 1.1 Add Lentil as a Lake dependency

**Modify**: `lakefile.toml`

Add Lentil via local path (both repos use Lean v4.25.2). This transitively brings in `aesop`.

### 1.2 Define release operator and NNF denotation

**New file**: `LTLLib/LTL/Semantics.lean`

**Definitions:**
- `tla_release (p q : TLA.pred α) : TLA.pred α` — `fun σ => ∀ j, (q (σ.drop j)) ∨ ∃ i < j, (p (σ.drop i))`
- `NNF.toPred : NNF α → TLA.pred (α → Prop)` — denotation mapping NNF syntax to Lentil predicates:
  - `.tt → tla_true`, `.ff → tla_false`
  - `.prop a → state_pred (fun v => v a)`, `.nprop a → state_pred (fun v => ¬ v a)`
  - `.and/.or → tla_and/tla_or`, `.next → later`, `.until → tla_until`, `.release → tla_release`
- `NNF.satisfies (ξ : TLA.exec (α → Prop)) (φ : NNF α) : Prop := (φ.toPred) ξ`

**Theorems about release** (needed for neg_correct and later phases):
- `release_dual : tla_release p q = tla_not (tla_until (tla_not p) (tla_not q))` — unfold + `push_neg` + classical
- `not_release : tla_not (tla_release p q) = tla_until (tla_not p) (tla_not q)` — corollary
- `release_unroll : tla_release p q = tla_and q (tla_or p (later (tla_release p q)))` — expansion law
- `always_as_release : always p = tla_release tla_false p` — simplification

**Key theorems:**
- `NNF.neg_correct : NNF.satisfies ξ φ.neg ↔ ¬ NNF.satisfies ξ φ` — structural induction on φ (9 cases); uses `release_dual` for until/release cases
- `NNF.satisfies_drop_drop` — leverages Lentil's `exec.drop_drop`

### 1.3 Define Formula-level semantics and prove toNNF correctness

**Still in**: `LTLLib/LTL/Semantics.lean`

**Definitions:**
- `Formula.directSatisfies : TLA.exec (α → Prop) → Formula α → Prop` — independent recursive semantics on the user-facing type (13 cases, one per constructor)
- `Formula.satisfies ξ φ := NNF.satisfies ξ (φ.toNNF true)` — NNF-based definition

**Key theorem:**
- `toNNF_correct : Formula.directSatisfies ξ φ ↔ NNF.satisfies ξ (φ.toNNF true)`
  - Proof: generalized mutual induction with polarity parameter:
    - `toNNF_pos`: `directSatisfies ξ φ ↔ satisfies ξ (φ.toNNF true)`
    - `toNNF_neg`: `¬ directSatisfies ξ φ ↔ satisfies ξ (φ.toNNF false)`
  - 13 constructor cases × 2 polarities; uses `neg_correct`, classical `imp_iff_not_or` (from Lentil's lifted lemmas)

### 1.4 Define proof-level automata acceptance

**New file**: `LTLLib/Acceptance.lean`

**Definitions:**
- `GBA.Spec State α` — proof-level GBA: `trans`, `initial`, `labelCompat`, `numAcceptSets`, `acceptSet` (all as predicates/relations)
- `GBA.Spec.IsRun` — `initial (σ 0) ∧ ∀ k, trans (σ k) (σ (k+1))`
- `GBA.Spec.RunCompatible` — `∀ k, labelCompat (σ k) (ξ k)`
- `GBA.Spec.IsAcceptingRun` — Büchi condition via Lentil: `∀ idx, σ |=tla= □ ◇ (state_pred (acceptSet idx))`
- `GBA.Spec.Accepts ξ` — `∃ σ, IsRun σ ∧ RunCompatible σ ξ ∧ IsAcceptingRun σ`
- `BA.Spec State α` — proof-level BA with single `accepting` predicate
- `BA.Spec.Accepts` — analogous, with `σ |=tla= □ ◇ (state_pred accepting)`
- `GBA.toSpec : GBA α → GBA.Spec Nat α` — bridge from computational `GBA` to proof-level spec

**Key theorem:**
- `degeneralize_correct : (ba_spec).Accepts ξ ↔ (gba_spec).Accepts ξ` — standard counter-cycling argument

### 1.5 Update imports

**Modify**: `LTLLib.lean`, `LTLLib/LTL.lean` — add imports for `Semantics.lean` and `Acceptance.lean`

### Lentil theorems leveraged in Phase 1

- `exec.drop_drop` — suffix composition
- `not_always`, `not_eventually` — release duality proofs
- Lifted classical logic: `TLA.not_and`, `TLA.implies_to_or`, `Decidable.not_not`
- `tla_unfold_simp` tactic — unfolding TLA definitions

---

## Phase 2: Termination

Independent of Phase 1. Removes `partial` from the three functions.

### 2.1 Subformula finiteness

**New file**: `LTLLib/LTL/SubformulaFinite.lean`

- `NNF.size` — syntax tree node count
- Prove `subformulas φ` is finite (structural induction)
- Prove `new1`/`next1`/`new2` only produce subformulas of the input

### 2.2 `expand` termination

**Modify**: `LTLLib/LTLtoGBA/Expand.lean`

- Replace `partial` with `termination_by` using lexicographic measure:
  1. `|possible_signatures| - |current_signatures|` (finite powerset of subformula closure, grows strictly when no duplicate found)
  2. `node.new.length` (decreases on each formula processing step)
- ~200 lines of decreasing proofs (hardest item in Phase 2)

### 2.3 `innerDFS` / `outerDFSLoop` termination

**Modify**: `LTLLib/NestedDFS/NestedDFSRef.lean`

- Add finiteness precondition (bounded reachable state set)
- `innerDFS`: measure is `|reachable| - |innerVisited|`
- `outerDFSLoop`: lexicographic `(|reachable| - |outerVisited|, stack depth, remaining successors)`

---

## Phase 3: Structural Invariants

**Depends on Phase 2** (needs non-partial `expand` for well-founded induction).

### 3.1 Propagation lemmas

**New file**: `LTLLib/LTLtoGBA/Invariants.lean`

~15 lemmas, each proved by well-founded induction on expand, matching algorithm cases:

| Lemma | Statement |
|-------|-----------|
| `expand_false_propag` | `ff ∉ old(q)` for any finished node `q` |
| `expand_contradiction_propag` | `prop(a) ∈ old(q) → nprop(a) ∉ old(q)` |
| `expand_and_propag` | `and(p,q) ∈ old(n) → p ∈ old(n) ∧ q ∈ old(n)` |
| `expand_or_propag` | `or(p,q) ∈ old(n) → p ∈ old(n) ∨ q ∈ old(n)` |
| `expand_next_propag` | `next(p) ∈ old(n) → p ∈ next(n)` |
| `expand_until_propag` | `until(p,q) ∈ old(n) → q ∈ old(n) ∨ (p ∈ old(n) ∧ until(p,q) ∈ next(n))` |
| `expand_release_propag` | `release(p,q) ∈ old(n) → (p ∈ old(n) ∧ q ∈ old(n)) ∨ (q ∈ old(n) ∧ release(p,q) ∈ next(n))` |
| `expand_all_subfrmls` | All formulas in new/old/next are subformulas of input |

### 3.2 Initial state property (L4_6)

- `initial_state_contains_formula : expandInit ∈ incoming(q) → φ ∈ old(q)`

### 3.3 Successor structure

- Next-set of predecessor becomes part of old-set of successor (from `createGraph` logic)

---

## Phase 4: Main Correctness Theorems

**Depends on Phases 1 + 3.**

### 4.1 Soundness

**New file**: `LTLLib/LTLtoGBA/Soundness.lean`

- **L4_2a–c**: Properties of Until/Release along accepting runs
- **L4_8** (core): `ψ ∈ old(σ(0)) → σ accepting run labeled by ξ → NNF.satisfies ξ ψ`
  - Structural induction on `ψ`; until case uses Büchi acceptance to prevent indefinite postponement
  - Leverages Lentil's `until_induction` for structuring the temporal argument
- **L4_9** (soundness): Combines L4_8 + L4_6

### 4.2 Completeness

**New file**: `LTLLib/LTLtoGBA/Completeness.lean`

- **L4_10**: `NNF.satisfies ξ φ → gba_spec.Accepts ξ`
  - Construct witness run `auto_run : Nat → State` using `Classical.choice`
  - At each step, pick successor node whose `old` set is compatible with `ξ.drop k`
  - Prove run is accepting: until-subformulas eventually get satisfied

### 4.3 Top-level theorem

**New file**: `LTLLib/LTLtoGBA/Correctness.lean`

```
theorem gba_correct (φ : NNF α) :
    ∀ ξ, (constructGBA φ).toSpec.Accepts ξ ↔ NNF.satisfies ξ φ

theorem ltl_to_gba_correct (φ : Formula α) :
    ∀ ξ, (constructGBA (φ.toNNF true)).toSpec.Accepts ξ ↔ Formula.directSatisfies ξ φ
```

---

## File Summary

| File | Phase | Status |
|------|-------|--------|
| `lakefile.toml` | 1 | Modify (add Lentil dep) |
| `LTLLib/LTL/Semantics.lean` | 1 | **New** — tla_release, NNF.toPred, satisfies, neg_correct, toNNF_correct |
| `LTLLib/Acceptance.lean` | 1 | **New** — GBA.Spec, BA.Spec, acceptance, degeneralize_correct |
| `LTLLib/LTL/SubformulaFinite.lean` | 2 | **New** — NNF.size, finiteness |
| `LTLLib/LTLtoGBA/Expand.lean` | 2 | Modify (remove partial) |
| `LTLLib/NestedDFS/NestedDFSRef.lean` | 2 | Modify (remove partial) |
| `LTLLib/LTLtoGBA/Invariants.lean` | 3 | **New** — propagation lemmas, L4_6 |
| `LTLLib/LTLtoGBA/Soundness.lean` | 4 | **New** — L4_8, L4_9 |
| `LTLLib/LTLtoGBA/Completeness.lean` | 4 | **New** — L4_10, auto_run |
| `LTLLib/LTLtoGBA/Correctness.lean` | 4 | **New** — top-level theorems |
| `LTLLib.lean`, `LTLLib/LTL.lean` | 1 | Modify (imports) |

## Verification

After each phase:
- `lake build` must succeed with no errors
- No `sorry` should remain in completed phases
- Phase 1: `#check @NNF.neg_correct`, `#check @toNNF_correct`, `#check @degeneralize_correct`
- Phase 2: No `partial` functions remain; `#check @expand` shows clean type
- Phase 3: `#check @expand_until_propag` etc.
- Phase 4: `#check @gba_correct` — the top-level theorem
