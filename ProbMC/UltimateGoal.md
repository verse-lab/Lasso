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
| N-step distribution (non-adaptive + adaptive) | `ProbMC/ProbStateRefinement.lean` | Done, sorry-free |
| PMF → pathMeasure refinement (adaptive) | `ProbMC/ProbStateRefinement.lean` | 1 sorry (Bellman) |
| FiniteDTMC (PMF DTMC + marginal = kernel power) | `ProbMC/Refinement/FiniteDTMC.lean` | Done, sorry-free |
| Action-independent MDP refinement | `ProbMC/Refinement/ActionIndep.lean` | Done, sorry-free |
| Geometric tail bound | `ProbMC/ExpectedTermination.lean` | Done, sorry-free |
| Expected stopping time ≤ 1/p | `ProbMC/ExpectedTermination.lean` | Done, sorry-free |
| MDP expected epoch bound | `ProbMC/ExpectedTermination.lean` | Done, sorry-free |
| TPTL semantics (freeze quantifier) | `leantla/Lentil/Basic.lean` (external) | Formalized, needs porting |
| `leads_to_within` operator | `leantla/Lentil/Basic.lean:267` (external) | Formalized, needs porting |

## What's Missing (TODOs)

### Layer 1: Expected Value Bounds ✅ DONE

The existing `almostSurelyForAll_of_epoch_bound` gives Pr = 1 (almost-sure termination).
For "expected O(1) rounds" we need **E[T] ≤ C** where T is the termination round.

**Key insight**: if each epoch succeeds independently with probability ≥ p, then
Pr(T > k) ≤ (1 - p)^k, so E[T] ≤ ∑ₖ (1-p)^k = 1/p.

- [x] **E1**: Geometric tail bound (`Pr(T > k) ≤ (1 - p)^k`)
- [x] **E2**: Expected stopping time ≤ 1/p
- [x] **E3**: MDP expected epoch bound (quantified over all strategies)
- [ ] **TODO E4** (optional): Generalize to non-uniform epoch success probabilities

**File**: `ProbMC/ExpectedTermination.lean` (sorry-free)

### Layer 2: PMF ↔ pathMeasure Refinement

Two approaches, depending on adversary model:

**Option A: Action-independent (non-adaptive adversary)** ✅ DONE, sorry-free

For protocols where coin flips don't depend on the adversary's scheduling
(`∀ s a₁ a₂, step s a₁ = step s a₂`), e.g., Ben-Or, VABA, DAG-Rider.
All strategies produce the same path measure, so a PMF bound on the
underlying DTMC directly gives `probLowerBoundForAll` for the MDP.

- [x] **R1**: Prove `trajMeasure` marginal at step N = kernel^N ∘ₘ μ₀
  (`pathMeasure_marginal_eq_nStep` in `Refinement/FiniteDTMC.lean`)
- [x] **R2**: Connect kernel power to `nStepDist` (PMF.bind iteration)
  (`nStepDist_eq_toDTMC_nStep` in `Refinement/FiniteDTMC.lean`)
- [x] **R3**: Sorry-free `probLowerBoundForAll` for action-independent MDPs
  (`probLowerBoundForAll_of_stepIndep_dtmc` in `Refinement/ActionIndep.lean`)

**Files**: `ProbMC/Refinement/FiniteDTMC.lean`, `ProbMC/Refinement/ActionIndep.lean`

**Option B: Adaptive adversary** ⚠ 1 sorry (Bellman principle)

For MDPs where the adversary's action choice affects transition probabilities.
Requires the finite-horizon Bellman principle to show that the worst-case over
Markovian strategies lower-bounds any history-dependent strategy.

- [x] **R1**: (same as above, already proved)
- [x] **R2**: (same as above, already proved)
- [ ] **TODO R3'**: Prove Bellman principle `pathMeasure_ge_iInf_nStepDistAdaptive`

**File**: `ProbMC/ProbStateRefinement.lean`

- [ ] **TODO R4** (optional): Formalize the "prob as state variable" accumulator
  interpretation (`trace_prob_product_eq_nStepDist`)

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
Current state (refinement done for action-independent case!)
    │
    ├─ E1–E3: Expected value bound theorem         ← DONE (ExpectedTermination.lean)
    │
    ├─ T1–T2: Port TPTL from leantla               ← PORTING, independent
    │
    ▼
P1–P2: Ben-Or model + epoch bound                  ← next major task
    │
    ├─ P3: Pr(termination) = 1                      ← needs P2, already have theorem
    │
    └─ P4: E[T] ≤ 2^{2n}                           ← needs P2, already have theorem
         │
         ▼
    T3–T4: TPTL measurability + connection          ← needs T1
         │
         ▼
    TPTL-stated result:
    "Pr(□ x.(epoch_start → ◇ y.(decided ∧ y ≤ x + 2^{2n}))) = 1"
```

The refinement layer (R1–R3) is **no longer a blocker** for action-independent
protocols like Ben-Or. The remaining workstreams:
1. **Protocol modeling** (P1–P2): model Ben-Or as `FiniteMDP`, prove epoch bound
2. **TPTL porting** (T1–T2): independent porting work

## Feasibility Summary

| Goal | Feasibility | Bottleneck |
|------|-------------|------------|
| Pr(Ben-Or terminates) = 1 | High | P1–P2 (protocol modeling + epoch bound) |
| E[Ben-Or rounds] ≤ 2^{2n} | High | P1–P2 (E1–E3 already done) |
| TPTL-stated Ben-Or liveness | High | T1–T4 + above |
| Pr(VABA terminates) = 1 | Medium | Protocol modeling complexity (P5) |
| E[VABA time] = O(1) | Medium | P5–P7, epoch success probability proof |
| E[DAG-Rider rounds] = O(1) | Medium | Similar to VABA |

The framework is architecturally sound. The refinement layer is complete for
action-independent protocols (sorry-free). The main remaining risks are:
- Protocol modeling (P1, P5) being tedious regardless of framework
- TPTL porting from broken leantla requiring repairs

No fundamental obstacles. For protocols with action-dependent transitions
(where the adversary's choice affects probabilities), proving the Bellman
principle (R3' in `ProbStateRefinement.lean`) would be needed.
