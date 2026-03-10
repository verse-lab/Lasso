# Probability as a State Variable: Design Notes

## The Idea

Model probabilistic transitions in a plain nondeterministic transition system
by adding a `prob : ℝ≥0` field to the state. Every time a probabilistic choice
is made (e.g., coin toss), the `prob` field is multiplied by the branch weight.
Adversarial choices leave `prob` unchanged.

```
State = (actual_state, prob : ℝ≥0)

-- adversarial choice (pick): probability unchanged
(s, p) → (s', p)

-- probabilistic choice (coin toss, weight w): multiply
(s, p) → (s₁, p * w₁)    -- heads
(s, p) → (s₂, p * w₂)    -- tails, w₁ + w₂ = 1
```

The system is just a regular nondeterministic transition system — no new
`step : Kernel (S × Act) S` definition needed. A `coin_toss` is syntactic
sugar for a nondeterministic `pick` that also multiplies `prob` by the
branch weight.

## Key Invariant

At every probabilistic branching point, the weights of all branches sum to 1.
This distinguishes "genuine" adversarial nondeterminism (no weight constraint)
from "probabilistic" nondeterminism (weights must sum to 1).

## Refinement Statement

For finite executions of n steps:

```
∀ trace of length n,
  trace.final.prob = ∏ᵢ, MDP.step(sᵢ, aᵢ)({sᵢ₊₁})
```

For reachability:

```
∑ (traces reaching target in n steps), trace.final.prob
  = MDP.pathMeasure(reach target by step n)
```

The `MDP` is a *derived* object extracted from the transition system, never
defined by hand. The refinement theorem is the bridge to measure theory.

## Why This Suits Ben-Or

For the epoch argument, we only reason about finite prefixes (one epoch = two
rounds). The proof structure becomes:

1. Sum of `prob` over all traces where the epoch succeeds ≥ 2⁻²ⁿ
2. This is arithmetic on a finite nondeterministic system — no measure theory
3. Refinement theorem lifts it to `MDP.probLowerBoundForAll`
4. `almostSurelyForAll_of_epoch_bound` (already proved) finishes it

The user never touches measure theory directly.

## Veil Integration

- Veil's `RelationalTransitionSystem` is a relation `S → S → Prop`
- The probabilistic version is the same, with `prob` as a state variable
- `pick` = adversarial (no weight), `coin_toss` = nondeterministic + multiply weight
- No changes to Veil's core; `prob` is just another state variable
- The weight-sum-to-1 invariant is a proof obligation at definition time

## Prior Art Survey

We searched for existing formalizations using this approach. **None found** that
do exactly this in a proof assistant. Related work:

### Closest

- **Tarzia (TLA+ course paper)**: Mentions using a probability variable multiplied
  by transition weights. But this was for model-*checking* (computing probabilities
  via state exploration), not formal *verification* (proving theorems).
  [Paper](https://stevetarzia.com/papers/Tarzia_495_paper.pdf)

- **Probabilistic symbolic execution** (Geldenhuys et al., ISSTA 2012): Path
  probabilities computed as products of branch weights — same math, but applied
  to program analysis, not transition system formalization.

### Standard approach (different from ours)

- **Hölzl (Isabelle/HOL, JAR 2017)**: DTMCs as `S → PMF S`, MDPs as `S → Set (PMF S)`.
  Coalgebraic trace space construction. Proper measure-theoretic definitions.
  [Paper](https://www.cs.vu.nl/~jhl890/pub/hoelzl2017mdp.pdf),
  [AFP entry](https://www.isa-afp.org/entries/Markov_Models.html)

- **Affeldt's Monae (Coq)**: Hierarchy of monadic effects (nondeterminism, state,
  probability). Uses the geometrically convex monad — algebraically elegant but
  a proper probabilistic monad, not a weight accumulator.
  [GitHub](https://github.com/affeldt-aist/monae),
  [Paper](https://arxiv.org/abs/2003.09993)

### Taxonomy of probabilistic transition systems

- **Van Glabbeek, Smolka, Steffen & Tofts (LICS 1990)**: Three models:
  - *Reactive*: `S × Act → Dist(S)` — our MDP definition
  - *Generative*: `S → Dist(Act × S)` — jointly draw action + next state
  - *Stratified*: `S → Dist(Act × Dist(S))` — two-level choice
  Our "probability as state variable" approach sidesteps this taxonomy entirely
  by encoding probability in the state rather than in the transition structure.
  [Paper](https://cgi.cse.unsw.edu.au/~rvg/pub/prob90.pdf)

- **Segala-Lynch (1995)**: `T ⊆ S × Act × Dist(S)` — nondeterministic choice
  *between* distributions. More expressive than reactive, harder measure-theoretically.
  [Slides](http://fais.jsiam.org/doc/20070523-Segala.pdf)

### Blog / discussion

- **Andrew Helwer**: "You cannot model probability with nondeterminism" — but this
  is about semantic equivalence. Our approach doesn't claim equivalence; it defines
  a *refinement* connecting the two views.
  [Post](https://ahelwer.ca/post/2020-09-11-probabilistic-distsys/)

## Open Questions

1. **Infinite traces**: For liveness (not just finite reachability), need to show
   the product of weights along an infinite path converges to the correct measure.
   For the Ben-Or epoch argument this is not needed (finite-depth reasoning), but
   a full refinement theorem would require it.

2. **Marking probabilistic vs adversarial branches**: Need some annotation or
   convention to distinguish which nondeterministic branches carry probability
   weights. Options:
   - Convention: only `coin_toss` branches carry weights
   - Type-level: separate `prob_step` and `nondet_step` constructors
   - State-level: a flag in the state indicating "this branch was probabilistic"

3. **Multiple probabilistic choices in one step**: If a single transition involves
   multiple coin tosses, do they compose multiplicatively? Need to clarify the
   granularity of steps vs probabilistic choices.

4. **Novelty**: Since no proof assistant formalization exists for this approach,
   the refinement proof is uncharted territory. The simplicity is appealing but
   there are no prior examples to follow.
