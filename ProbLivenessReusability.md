# Reusability Analysis: CSLib / Mathlib / LTLLib / Prob

This document maps the automata, transition system, and measure-theoretic
definitions across the four layers of this project, identifies where they
overlap, and records design decisions for the probabilistic liveness
formalization.

---

## The Four Layers

### Layer 1: Lentil (temporal semantics foundation)

```
exec σ := ℕ → σ          -- infinite sequences
pred σ := exec σ → Prop   -- temporal predicates
OmegaWord α := exec (α → Prop)  -- ω-words
□, ◇, ◯, 𝑈, 𝑅           -- temporal operators
```

**Used by**: existing LTLLib (Semantics, Soundness, Completeness).
**No automata, no measure theory, no transitions.**

### Layer 2: Existing LTLLib (two-tier: computational + proof-level)

**Computational tier** (HashMap-based, for execution):

| Definition | File | Purpose |
|-----------|------|---------|
| `GBA α` | `GBA.lean` | Generalized Büchi: states/successors/labeling/acceptSets as HashMaps |
| `BA α`, `BAState` | `BA.lean` | Standard Büchi: degeneralized from GBA |
| `nestedDFS` | `NestedDFS.lean` | CVWY emptiness check on BA |

**Proof tier** (predicate-based, for reasoning):

| Definition | File | Purpose |
|-----------|------|---------|
| `OASpec State α k` | `Acceptance.lean` | Abstract spec: trans/initial/labelCompat/acceptSet as `Prop` |
| `OASpec.isRun`, `.accepts` | `Acceptance.lean` | Run validity and acceptance (nondeterministic: `∃ σ, ...`) |
| `OASpec.degeneralize` | `Acceptance.lean` | k acceptance sets → 1 |
| `GBA.toSpec`, `BA.toSpec` | `Acceptance.lean` | Bridges computational → proof tier |
| `expandOASpec` | `Soundness.lean` | Abstract automaton from node expansion |
| `ValidLasso`, `lassoRun` | `Lasso.lean` | Lasso witness for non-emptiness |

**Imports**: Lentil (for `exec`, temporal operators), `Mathlib.Order.Nat` (minor).
**Does NOT import CSLib.** Despite CSLib being a lakefile dependency, no LTLLib
file imports any `Cslib.*` module.

### Layer 3: CSLib (automata + LTS library)

| Definition | File | Type |
|-----------|------|------|
| `FLTS State Label` | `Semantics/FLTS/Basic.lean` | `tr : State → Label → State` (deterministic) |
| `LTS State Label` | `Semantics/LTS/Basic.lean` | `Tr : State → Label → State → Prop` (nondeterministic) |
| `DA State Symbol` | `Automata/DA/Basic.lean` | FLTS + `start`, with `DA.run` |
| `DA.Buchi`, `DA.Muller` | `Automata/DA/Basic.lean` | Büchi: `∃ᶠ k in atTop, run xs k ∈ accept` |
| `NA State Symbol` | `Automata/NA/Basic.lean` | Nondeterministic automaton |
| `NA.Buchi`, `NA.Muller` | `Automata/NA/Basic.lean` | Nondeterministic acceptance |
| `ωSequence α` | `Data/OmegaSequence/Defs.lean` | Wrapped `ℕ → α` with `FunLike` |
| `ωSequence.infOcc` | `Data/OmegaSequence/InfOcc.lean` | `{x \| ∃ᶠ k in atTop, xs k = x}` |
| `LTS.MTr` | `Semantics/LTS/Basic.lean` | Multistep transitions (finite traces) |
| `LTS.CanReach` | `Semantics/LTS/Basic.lean` | `∃ μs, MTr s1 μs s2` |
| `LTS.generatedBy` | `Semantics/LTS/Basic.lean` | Restrict to reachable states |
| `DA.prod` | `Automata/DA/Prod.lean` | Product of two DAs with `prod_mtr_eq` |
| `FLTS.prod` | `Semantics/FLTS/Prod.lean` | Product of two FLTSs |

**Available in LTLLib's dependency tree but never imported by any LTLLib file.**

### Layer 4: New ProbMC/ code (measure-theoretic)

| Definition | File | Type |
|-----------|------|------|
| `DTMC S` | `ProbMC/DTMC.lean` | `Kernel S S` with `IsMarkovKernel` |
| `DTMC.pathMeasure` | `ProbMC/DTMC.lean` | Probability measure on `ℕ → S` via Ionescu-Tulcea |
| `DTMC.nStep` | `ProbMC/DTMC.lean` | `κ^n` (Chapman-Kolmogorov) |
| `DetOmegaAut Q Alph` | `ProbMC/OmegaRegularMeasurable.lean` | `init + trans` (deterministic) |
| `DetOmegaAut.run` | `ProbMC/OmegaRegularMeasurable.lean` | `(ℕ → Alph) → ℕ → Q` |
| `measurableSet_buchiAcceptSet` | `ProbMC/OmegaRegularMeasurable.lean` | Büchi acceptance is G_δ |
| `measurableSet_rabinAcceptSet` | `ProbMC/OmegaRegularMeasurable.lean` | Rabin acceptance is measurable |

**Imports**: Mathlib (kernels, measure theory, Ionescu-Tulcea).
**Does NOT import CSLib or existing LTLLib.**

---

## Structural Overlaps

### DetOmegaAut (Layer 4) ≈ DA (Layer 3)

These are structurally identical modulo the sequence wrapper:

| | `DetOmegaAut Q Alph` (Layer 4) | `DA State Symbol` (Layer 3) |
|--|--|--|
| Init state | `init : Q` | `start : State` |
| Transition | `trans : Q → Alph → Q` | `tr : State → Symbol → State` (via `FLTS`) |
| Run at step n | `run : (ℕ → Alph) → ℕ → Q` | `run : ωSequence Symbol → ωSequence State` |
| Sequence type | raw `ℕ → α` | `ωSequence α` (wrapped `ℕ → α`) |
| Acceptance | `buchiAcceptSet` (set-theoretic) | `DA.Buchi` instance (`∃ᶠ` filter) |
| Measurability | `measurableSet_buchiAcceptSet` | (none) |

The `ωSequence` vs raw `ℕ → α` difference matters because Mathlib's
`MeasurableSpace.pi` works on raw `ℕ → α`. Using CSLib's `DA` directly would
require unwrapping through `ωSequence.get` at every measurability proof.

### OASpec (Layer 2) vs DetOmegaAut (Layer 4)

| | `OASpec State α k` (Layer 2) | `DetOmegaAut Q Alph` (Layer 4) |
|--|--|--|
| Determinism | Nondeterministic (`∃ σ, ...`) | Deterministic (unique run) |
| Transitions | `trans : State → State → Prop` | `trans : Q → Alph → Q` |
| Labels | `labelCompat : State → (α → Prop) → Prop` | Implicit in alphabet `Alph` |
| Acceptance | k acceptance sets, `∀ i : Fin k, visit Fᵢ i.o.` | Single set F, visit i.o. / Rabin pairs |
| Purpose | Correctness proofs (LTL ↔ automaton) | Measurability proofs (Borel structure) |

These serve fundamentally different roles. `OASpec` is for proving the LTL
translation correct; `DetOmegaAut` is for proving the probability is well-defined.

### exec (Layer 1) = path space (Layer 4)

Definitionally equal: `exec S = ℕ → S` and `DTMC.pathMeasure` produces a measure
on `ℕ → S`. No bridging code needed.

### LTS.CanReach (Layer 3) — unique, no overlap

CSLib's `LTS.CanReach` is the only reachability definition available. Neither
LTLLib nor Mathlib defines graph reachability on transition systems. This is
needed for SCC/BSCC in Phase P3.

---

## Connection Points for the End-to-End Theorem

The target theorem:

```
For DTMC D with labeling L and LTL formula φ:
  D.pathMeasure μ₀ {π | NNF.satisfies (L ∘ π) (toNNF φ)} =
    Pr_{D⊗A}(reach accepting BSCC)
```

This requires the following chain of connections:

```
Layer 1 (Lentil)              Layer 2 (existing LTLLib)
  NNF.satisfies ξ φ  ←————→    OASpec.accepts ξ
                                [existing: expandOASpec_correct]
         ↕                              ↕
         ?                     determinization gap
         ↕                     (Safra / LDBA / axiom)
                                        ↕
Layer 4 (Prob)                Layer 3 (CSLib)
  DetOmegaAut.run     ←·····→    DA.run
  DTMC.pathMeasure               DA.prod
  measurableSet_*                LTS.CanReach → BSCC (to define)
```

### Gap 1: Determinization (Layer 2 → Layer 4)

The existing pipeline produces a nondeterministic BA for ¬φ. Quantitative
probabilistic verification requires a deterministic Rabin automaton (DRA).
This is the **hardest gap** — Safra's construction is complex.

**Options**:
- (a) **Axiomatize**: assume a correct DRA is given as input (pragmatic)
- (b) **Qualitative only**: for Pr=1 checking, no determinization needed;
  use BSCC analysis on the product with NBA directly [BK08, §10.3.3]
- (c) **LDBA**: formalize limit-deterministic Büchi automata [SEJK16]

### Gap 2: ωSequence wrapper (Layer 3 ↔ Layer 4)

CSLib's `DA` uses `ωSequence α`; Prob uses raw `ℕ → α`.
Bridging: `ωSequence.get : ωSequence α → (ℕ → α)` and the `Coe (ℕ → α) (ωSequence α)` instance.
This is mechanical but adds noise to every lemma that crosses the boundary.

### Gap 3: BSCC definition (not in any layer)

Define using CSLib's `LTS.CanReach`:
```lean
def MutuallyReachable (lts : LTS State Label) (s1 s2 : State) : Prop :=
  lts.CanReach s1 s2 ∧ lts.CanReach s2 s1

def IsBSCC (lts : LTS State Label) (B : Set State) : Prop :=
  B.Nonempty ∧
  (∀ s1 ∈ B, ∀ s2 ∈ B, MutuallyReachable lts s1 s2) ∧
  (∀ s ∈ B, ∀ s', lts.CanReach s s' → s' ∈ B)
```

### Gap 4: Labeling bridge (Layer 1 ↔ Layer 4)

Given `L : S → (α → Prop)`, the map `trace π n := L (π n)` converts a state
path `π : ℕ → S` to an ω-word `trace π : ℕ → (α → Prop) = OmegaWord α`.
Then `NNF.satisfies (trace π) φ` is the satisfaction predicate on paths.
This map is measurable when `L` is measurable (composition of measurable
functions).

---

## Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Use CSLib's `DA` for Phase P2? | **No** | `ωSequence` friction with Mathlib's `MeasurableSpace.pi`; measurability proofs need raw `ℕ → α` throughout |
| Use CSLib's `DA.prod` for Phase P3? | **Probably not** | Product of `DetOmegaAut` is a 5-line definition; avoids `ωSequence` unwrapping |
| Use CSLib's `LTS.CanReach` for Phase P3? | **Yes** | Reachability is label-agnostic; convert DTMC to `LTS` for SCC/BSCC. No `ωSequence` friction. |
| Bridge to LTLLib's `OASpec`? | **Defer** | The determinization gap is the hardest part. Axiomatize the DRA for now. |
| Connect `exec` ↔ path space? | **Free** | Definitionally `ℕ → α`. Labeling function bridges state paths to ω-words. |
| Use CSLib's `infOcc`? | **Optional** | Our `buchiAcceptSet` is set-theoretic (`⋂_n ⋃_k`); CSLib's uses filters (`∃ᶠ`). Both work; ours is more direct for measurability. Could prove equivalence if needed. |

---

## What Each Layer Contributes to the Final Result

| Layer | Contribution | Status |
|-------|-------------|--------|
| **Lentil** | `NNF.satisfies` — ground truth for "ξ ⊨ φ" | Existing |
| **LTLLib** | `expandOASpec_correct` — OASpec accepts ξ ↔ ξ ⊨ φ | Existing |
| **LTLLib** | `constructGBA_correct` — computational GBA ↔ abstract spec | Existing (modulo GraphComplete) |
| **CSLib** | `LTS.CanReach` — reachability for BSCC definition | Available, to be used in Phase P3 |
| **Mathlib** | `Kernel`, `IsMarkovKernel`, `trajMeasure` — DTMC path measure | Available, used in Phase P1 |
| **Mathlib** | `MeasurableSpace.pi`, `MeasurableSet.iInter/iUnion` — measurability | Available, used in Phase P2 |
| **Prob (new)** | `DTMC.pathMeasure` — probability on infinite paths | Phase P1 ✅ |
| **Prob (new)** | `measurableSet_buchiAcceptSet` — ω-regular sets are Borel | Phase P2 ✅ |
| **Prob (new)** | Product DTMC ⊗ DRA, BSCC reduction | Phase P3 (planned) |
| **Prob (new)** | Pr=1 ↔ fair paths | Phase P5 (planned) |
| **??? (gap)** | BA → DRA determinization | Not planned (axiomatize) |
