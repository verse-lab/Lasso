# Ultimate Goal: Verified Probabilistic Liveness for Distributed Protocols

## Vision

Prove properties like "protocol X terminates in expected O(1) rounds" by combining:

1. **TPTL** (Timed Propositional Temporal Logic) — express time-bounded liveness
2. **Simple probabilistic transition system** — protocol model with `prob` as state variable
3. **Trace-level probability reasoning** — Pr(traces satisfying a TPTL property) = value
4. **Refinement theorems** — connecting each layer

## Target Protocols

| Protocol | Property | Reference |
|----------|----------|-----------|
| Ben-Or consensus | E[rounds] = O(2^{2n}) | [Ben83], [AT12] |
| VABA (Abraham et al.) | E[time] = O(1), E[comm] = O(n²) | [Abraham-Malkhi-Spiegelman 2018] |
| DAG-Rider (Keidar et al.) | E[rounds] = O(1) | [Keidar-Kokoris-Kogias-Naor-Spiegelman 2021] |

## Architecture

```
TPTL formula: □ x.(start_epoch → ◇ y.(decided ∧ y ≤ x + K))
    ↓ [TPTL semantics: timed trace satisfaction]
Set of timed traces: {(σ,τ) | (σ,τ) ⊨ φ}
    ↓ [measurability: extends Phase P2 to timed traces]
Measurable event in path space
    ↓ [prob-as-state-variable refinement]
PMF computation: ∑ prob over traces satisfying φ ≥ p
    ↓ [Borel-Cantelli / expectation computation]
E[rounds to termination] ≤ 1/p
```

## What Exists

| Component | File(s) | Status |
|-----------|---------|--------|
| DTMC definition + path measure | `ProbMC/DTMC.lean` | Done, sorry-free |
| MDP definition + strategies | `ProbMC/MDP.lean` | Done, sorry-free |
| ω-regular measurability | `ProbMC/OmegaRegularMeasurable.lean` | Done, sorry-free |
| Independent epochs (Borel-Cantelli) | `ProbMC/IndependentEpochs.lean` | Done, sorry-free |
| FiniteMDP (PMF-based MDP) | `ProbMC/FiniteMDP.lean` | Done, sorry-free |
| N-step distribution | `ProbMC/ProbStateRefinement.lean` | Definitions done |
| PMF → pathMeasure refinement | `ProbMC/ProbStateRefinement.lean` | 1 sorry |
| TPTL semantics (freeze quantifier) | `leantla/Lentil/Basic.lean` (external) | Formalized, needs porting |
| `leads_to_within` operator | `leantla/Lentil/Basic.lean:267` (external) | Formalized, needs porting |

## What's Missing (TODOs)

### Layer 1: Expected Value Bounds

The existing `almostSurelyForAll_of_epoch_bound` gives Pr = 1 (almost-sure termination).
For "expected O(1) rounds" we need **E[T] ≤ C** where T is the termination round.

**Key insight**: if each epoch succeeds independently with probability ≥ p, then
Pr(T > k) ≤ (1 - p)^k, so E[T] ≤ ∑ₖ (1-p)^k = 1/p.

- [ ] **TODO E1**: Define `terminationRound` or stopping time for a path
- [ ] **TODO E2**: Prove `Pr(T > k) ≤ (1 - p)^k` from epoch bound + independence
- [ ] **TODO E3**: Prove `E[T] ≤ 1/p` via geometric series summation of tail probabilities
- [ ] **TODO E4** (optional): Generalize to non-uniform epoch success probabilities

**Difficulty**: Medium. Mostly real-analysis (geometric series) + connecting to existing
epoch machinery. No new measure theory.

**File**: `ProbMC/ExpectedTermination.lean`

### Layer 2: PMF ↔ pathMeasure Refinement

The `probLowerBoundForAll_of_nStep_bound` theorem (sorry in `ProbStateRefinement.lean`)
bridges PMF-level arithmetic to MDP path measure bounds. This is the technical core.

- [ ] **TODO R1**: Prove `trajMeasure` of cylinder `{ξ | ξ N ∈ Good}` equals iterated
  kernel composition (uniform-state-space specialization of Ionescu-Tulcea)
- [ ] **TODO R2**: Connect iterated kernel composition to `nStepDist` (PMF.bind iteration)
  for `FiniteMDP`
- [ ] **TODO R3**: Close the sorry in `probLowerBoundForAll_of_nStep_bound`
- [ ] **TODO R4** (optional): Formalize the "prob as state variable" accumulator
  interpretation (`trace_prob_product_eq_nStepDist`)

**Difficulty**: R1 is hard (Ionescu-Tulcea API plumbing, type coercions between
`∀ i : Iic n, S` and `Fin (n+1) → S`). R2–R4 are medium once R1 is done.

**Key Mathlib APIs**:
- `trajContent_cylinder` — evaluates `trajContent` on cylinder sets via `partialTraj`
- `partialTraj_succ_of_le` — recursive decomposition
- `map_partialTraj_succ_self` — pushforward to next coordinate equals `κ n`
- `Kernel.ofFunOfCountable` — any function becomes a kernel for countable types

**File**: `ProbMC/ProbStateRefinement.lean`

### Layer 3: TPTL Integration

Port TPTL from leantla and connect to the probability framework.

- [ ] **TODO T1**: Port TPTL syntax and semantics from `leantla/Lentil/Basic.lean` to
  LTLLib (or make leantla a dependency)
- [ ] **TODO T2**: Port `leads_to_within` (timed bounded liveness) operator
- [ ] **TODO T3**: Prove measurability of TPTL properties for discrete time
  (extends Phase P2; for discrete T = ℕ, freeze quantifier just binds to current
  index, so TPTL properties reduce to ω-regular with bounded lookahead)
- [ ] **TODO T4**: Connect TPTL satisfaction to cylinder events:
  show `{ξ | (ξ, id) ⊨ leads_to_within φ ψ K}` is a countable intersection of
  cylinder events, hence measurable and amenable to PMF computation

**Difficulty**: T1–T2 are porting work. T3 is easy (discrete time makes everything
measurable). T4 is medium.

**File**: `ProbMC/TPTL.lean` or integrate into existing LTLLib TPTL

### Layer 4: Protocol Models

Model specific protocols as `FiniteMDP` and prove the epoch bounds.

- [ ] **TODO P1**: Model Ben-Or consensus as `FiniteMDP` (simplest target)
  - State: (process values, round counter, phase)
  - Actions: adversary scheduling decisions
  - PMF step: coin tosses with weight 1/2
- [ ] **TODO P2**: Prove Ben-Or epoch bound: Pr(lucky epoch) ≥ 2^{-2n}
- [ ] **TODO P3**: Instantiate `almostSurelyForAll_of_epoch_bound` → Pr(termination) = 1
- [ ] **TODO P4**: Instantiate E[T] ≤ 2^{2n} via TODO E3
- [ ] **TODO P5**: Model VABA as `FiniteMDP` (harder: 4-stage broadcast, leader election,
  view changes)
- [ ] **TODO P6**: Prove VABA view success probability ≥ 2/3 (the key probabilistic lemma)
- [ ] **TODO P7**: Instantiate E[views] ≤ 3/2, hence E[time] = O(1)

**Difficulty**: P1–P4 are the critical path (Ben-Or). P5–P7 are ambitious stretch goals.

**Files**: `ProbMC/BenOr/Model.lean`, `ProbMC/BenOr/Termination.lean`, etc.

## Critical Path

```
Current state
    │
    ├─ R1–R3: Close the refinement sorry          ← HARD, enables everything
    │
    ├─ E1–E3: Expected value bound theorem         ← MEDIUM, independent of R1
    │
    ├─ T1–T2: Port TPTL from leantla               ← PORTING, independent
    │
    ▼
P1–P2: Ben-Or model + epoch bound                  ← needs R3
    │
    ├─ P3: Pr(termination) = 1                      ← needs P2, already have theorem
    │
    └─ P4: E[T] ≤ 2^{2n}                           ← needs P2 + E3
         │
         ▼
    T3–T4: TPTL measurability + connection          ← needs T1, R3
         │
         ▼
    TPTL-stated result:
    "Pr(□ x.(epoch_start → ◇ y.(decided ∧ y ≤ x + 2^{2n}))) = 1"
```

Three workstreams can proceed in parallel:
1. **Refinement** (R1–R3): the hard Mathlib plumbing
2. **Expected value** (E1–E3): independent real-analysis work
3. **TPTL porting** (T1–T2): independent porting work

All three converge at P1–P4 (Ben-Or instantiation).

## Feasibility Summary

| Goal | Feasibility | Bottleneck |
|------|-------------|------------|
| Pr(Ben-Or terminates) = 1 | High | R1–R3 (refinement sorry) |
| E[Ben-Or rounds] ≤ 2^{2n} | High | E1–E3 + R1–R3 |
| TPTL-stated Ben-Or liveness | High | T1–T4 + above |
| Pr(VABA terminates) = 1 | Medium | Protocol modeling complexity (P5) |
| E[VABA time] = O(1) | Medium | P5–P7, epoch success probability proof |
| E[DAG-Rider rounds] = O(1) | Medium | Similar to VABA |

The framework is architecturally sound. The main risks are:
- R1 (Ionescu-Tulcea plumbing) being harder than expected
- Protocol modeling (P1, P5) being tedious regardless of framework
- TPTL porting from broken leantla requiring repairs

No fundamental obstacles. The "prob as state variable" idea avoids defining new
transition system types, and the expected value bound is a natural extension
of the existing Borel-Cantelli infrastructure.
