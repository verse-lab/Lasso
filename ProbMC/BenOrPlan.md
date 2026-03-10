# Plan: Verified Probabilistic Liveness for Ben-Or's Consensus Algorithm

## Goal

Formally verify that Ben-Or's randomized consensus algorithm [Ben-Or 1983]
terminates with probability 1 under a strong adversary with `f < n/2` crash
failures. Specifically:

- **Per-epoch bound**: Pr(all correct processes decide in epoch r) >= 2^{-2n}
- **Almost-sure termination**: Pr(eventually all decide) = 1

Based on the correctness proof by Aguilera & Toueg (Distrib. Comput., 2012).

---

## Architecture: Three-Layer Pipeline

```
Layer 1: Veil DSL (user writes protocol)
    |  coin_toss compiled specially
    v
Layer 2: MDP (compiled artifact)
    |  fix adversary strategy -> Markov chain
    v
Layer 3: Probabilistic reasoning (user proves bounds)
```

### Layer 1: Veil DSL Extensions

Two new primitives alongside `pick`:

```lean
-- Fair coin toss (Bernoulli(1/2))
let b <- coin_toss Bool

-- Uniform random choice over finite type
let v <- uniform_random (Fin k)

-- General: sample from a named distribution
let x <- sample (PMF.bernoulli p hp)
```

**Key rule**: `pick` = adversary chooses (forall-quantified), `coin_toss`/`sample`
= nature chooses (measured).

Ben-Or in this DSL:

```lean
veil module BenOr (node : Type) [ByzNodeSet node nset] where
  param n : Nat
  param f : Nat

  individual estimate : node -> Fin 2
  individual round : node -> Nat
  individual decided : node -> Option (Fin 2)
  relation report_msg : node -> node -> Nat -> Fin 2 -> Bool
  relation proposal_msg : node -> node -> Nat -> PropValue -> Bool

  action report_phase (p : node) := do
    require not_crashed p
    let k := round p
    for q in node do
      report_msg p q k (estimate p) := true
    let received <- pick (Finset node)   -- adversary chooses which n-f arrive
    require received.card >= n - f
    ...

  action decide_or_update (p : node) := do
    ...
    if received_f_plus_1_same v then
      decided p := some v
    else if received_any_value v then
      estimate p := v
    else
      let b <- coin_toss Bool              -- probabilistic primitive
      estimate p := b
```

### Layer 2: Compilation Target -- MDP

Veil currently compiles to `RelationalTransitionSystem rho sigma l`. With
probabilistic primitives, it compiles to an MDP:

```lean
/-- A Markov Decision Process: nondeterministic choices (adversary)
    compose with probabilistic transitions (coins). -/
structure MDP (sigma : Type*) [MeasurableSpace sigma] where
  /-- Initial states (nondeterministic). -/
  init : Set sigma
  /-- Available adversary actions in each state. -/
  Act : Type*
  /-- Enabled actions per state. -/
  enabled : sigma -> Set Act
  /-- Transition kernel: given state and adversary action,
      a probability distribution on next states. -/
  step : sigma -> Act -> PMF sigma    -- PMF for finite state; Kernel for general
```

Compilation rules:
- Each `pick x` becomes part of `Act` (adversary's choice space)
- Each `coin_toss` / `sample` becomes part of the kernel in `step`
- Deterministic updates stay deterministic (Dirac measure)

For finite-state protocols (Ben-Or with fixed `n`), `PMF sigma` suffices and
all measurability is automatic.

Compilation correctness theorem:

```lean
theorem compile_correct (spec : VeilModule) :
    forall adv_strategy, forall coin_sequence,
      spec.reaches s <-> (compile spec).reaches s
```

### Layer 3: User-Facing Probabilistic Reasoning

**Fixing an adversary yields a Markov chain:**

```lean
noncomputable def MDP.underStrategy (M : MDP sigma) (pi : Strategy sigma M.Act) :
    DTMC sigma := ...

-- Probabilistic properties: quantify over all adversary strategies
def MDP.almostSurelyForAll (M : MDP sigma) (P : (Nat -> sigma) -> Prop) : Prop :=
  forall pi : Strategy sigma M.Act,
    (M.underStrategy pi).pathMeasure mu0 {path | P path} = 1

def MDP.probLowerBoundForAll (M : MDP sigma) (P : (Nat -> sigma) -> Prop)
    (p : ENNReal) : Prop :=
  forall pi : Strategy sigma M.Act,
    (M.underStrategy pi).pathMeasure mu0 {path | P path} >= p
```

**User's proof sketch for Ben-Or:**

```lean
-- Step 1: Per-epoch bound
theorem lucky_epoch_prob (r : Nat) :
    BenOr.mdp.probLowerBoundForAll
      (fun path => allDecideInEpoch path r)
      (2^{-1} ^ (2 * n)) := by
  intro pi                          -- fix arbitrary adversary
  -- coins in epoch r are independent of adversary's past choices
  -- at most 2n coins per epoch, each fair
  -- if all match FavorableToss, everyone decides (from safety proof!)
  ...

-- Step 2: Almost-sure termination
theorem benor_terminates :
    BenOr.mdp.almostSurelyForAll
      (fun path => exists t, forall p, not_crashed path p -> decided path t p) := by
  apply MDP.almostSure_of_independent_epochs
  . exact lucky_epoch_prob
  . exact epochs_independent
  . exact ENNReal.tsum_geometric_diverges ...
```

---

## Reusable Probability Lemma Library

Common patterns across randomized distributed protocols:

```lean
-- "If independent events each have probability >= p > 0,
--  then some event occurs with probability 1"
theorem MDP.almostSure_of_independent_epochs (M : MDP sigma)
    (P : Nat -> (Nat -> sigma) -> Prop) (p : ENNReal) (hp : 0 < p)
    (hbound : forall r, M.probLowerBoundForAll (P r) p)
    (hindep : EpochsIndependent M P) :
    M.almostSurelyForAll (fun path => exists r, P r path)

-- "Coin tosses within an action are independent of adversary history"
theorem coin_independent_of_history ...

-- "At most k coins per epoch -> Pr(all favorable) >= 2^{-k}"
theorem all_coins_favorable_prob (k : Nat) :
    Pr(forall i < k, coin i = favorable i) >= 2^{-1} ^ k
```

---

## What Existing Infrastructure Contributes

| Component | Role |
|-----------|------|
| **Veil** (DSL + SMT) | Protocol modeling, safety proofs (agreement, validity) |
| **ProbMC.DTMC** | `MDP.underStrategy` produces a DTMC; path measure via Ionescu-Tulcea |
| **ProbMC.DetOmegaAut** | Not directly used (Ben-Or is not automata-theoretic) |
| **Mathlib** (measure theory) | Product measures, independence, Borel-Cantelli |
| **Lentil** (temporal logic) | Stating LTL properties on traces (optional) |

---

## Technical Considerations

### Finite vs. Infinite State

For Ben-Or with fixed `n`, the state space is finite, so `PMF` works and all
measurability is automatic. This covers most distributed protocols. Supporting
infinite state would need `Kernel` and explicit measurability proofs.

### Coin Independence Across Steps

The crucial invariant: coins tossed at step `t` are independent of the
adversary's choices up to step `t` (even though the adversary sees past coins).
Formally, the adversary's strategy is measurable w.r.t. the filtration
generated by past states and coins, but future coins are independent.
Mathlib has filtrations and conditional independence.

### The "Lucky Epoch" Pattern is General

Many randomized distributed algorithms use the same structure:
"with probability >= p, one round/epoch succeeds regardless of adversary;
independent rounds -> Pr=1." This includes:
- Randomized consensus (Ben-Or, Bracha)
- Randomized leader election
- Randomized Byzantine agreement

The `independent_epoch_termination` lemma covers them all.

### Veil Extension Feasibility

Adding `coin_toss` to Veil's DSL extends the existing `NonDetT` monad
interpretation. Veil already distinguishes demonic/angelic nondeterminism --
adding a third mode ("probabilistic") fits the existing architecture.

---

## Work Breakdown

| Component | Effort | Notes |
|-----------|--------|-------|
| DSL primitives (`coin_toss`, `sample`) | ~1 week | Extends Veil's elaboration |
| MDP compilation from Veil spec | 2-3 weeks | New compilation target |
| `MDP.underStrategy -> DTMC` bridge | 1-2 weeks | Connects to ProbMC.DTMC |
| Reusable probability lemma library | 2-3 weeks | Independent epochs, Borel-Cantelli |
| Ben-Or case study (model + proof) | 2-3 weeks | Safety (Veil SMT) + prob termination |
| **Total** | **~8-12 weeks** | First proof-assistant-verified probabilistic liveness for a distributed protocol |

---

## Proof Structure for Ben-Or (from Aguilera-Toueg 2012)

### Safety (Layer 1, Veil SMT)

- **Lemma 1**: Impossible for a process to propose 0 and another to propose 1
  in the same round (majority counting).
- **Lemma 2**: If some process decides `v` in round `k >= 1`, then `v` is
  `(k+1)`-locked.
- **Lemma 3**: If `v` is `k`-locked for `k >= 1`, every process reaching
  line 12 in round `k` decides `v`.
- **Corollary 2** (Uniform agreement): All decisions agree.
- **Corollary 3** (Uniform validity): Decision is some process's initial value.

### Probabilistic Termination (Layers 2-3, ProbMC + Mathlib)

- **Lemma 4**: Every correct process starts every round.
- **Definition**: Epoch `r` = rounds `(2r, 2r+1)`. FavorableToss function
  determines the "right" coin outcome for each toss in the epoch.
- **Lemma 6**: If epoch `r` is lucky (all coins match FavorableToss), some
  value becomes `(2r+1)`-locked or `(2r+2)`-locked.
- **Lemma 7**: Pr(some epoch is lucky) = 1.
  - Each epoch has <= 2n coin tosses -> Pr(lucky) >= 2^{-2n}
  - Epochs use disjoint coins -> independent
  - Borel-Cantelli (or direct: product of (1 - 2^{-2n}) -> 0)
- **Lemma 8**: Pr(all correct processes decide) = 1.

### Expected Rounds

From the proof: expected number of rounds for termination is O(2^{2n}).

---

## References

- [Ben-Or 1983] M. Ben-Or, "Another advantage of free choice: completely
  asynchronous agreement protocols," PODC 1983, pp. 27-30.
- [AT12] M.K. Aguilera & S. Toueg, "The correctness proof of Ben-Or's
  randomized consensus algorithm," Distrib. Comput. 25:371-381, 2012.
- [BK08] C. Baier & J.-P. Katoen, Principles of Model Checking, MIT Press, 2008.
- [Var85] M.Y. Vardi, "Automatic Verification of Probabilistic Concurrent
  Finite-State Programs," FOCS 1985.
