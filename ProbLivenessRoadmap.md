# Roadmap: Probabilistic Liveness Formalization

## Goal

Formalize the theory connecting probabilistic systems (DTMCs/MDPs) to temporal
properties (LTL), culminating in: **Pr_s(φ) is well-defined and computable via
automata-theoretic product constructions.** Build on Lentil (temporal semantics)
and Mathlib (measure theory / Markov kernels).

---

## References

The formalization follows the mathematical development in these primary sources:

| Tag | Reference |
|-----|-----------|
| [BK08] | C. Baier & J.-P. Katoen, *Principles of Model Checking*, MIT Press, 2008. Chapters 10–10.3 cover DTMCs, cylinder sets, PCTL, and LTL model checking for probabilistic systems. |
| [CY95] | C. Courcoubetis & M. Yannakakis, "The Complexity of Probabilistic Verification," *JACM* 42(4):857–907, 1995. Establishes the automata-theoretic framework: product construction, BSCC reduction, complexity results. |
| [Var85] | M.Y. Vardi, "Automatic Verification of Probabilistic Concurrent Finite-State Programs," *FOCS* 1985, pp. 327–338. Foundational: defines trace probability spaces, proves measurability, establishes Pr=1 ↔ fair paths. |
| [VW86] | M.Y. Vardi & P. Wolper, "An Automata-Theoretic Approach to Automatic Program Verification," *LICS* 1986, pp. 332–344. LTL → Büchi automaton translation; every LTL formula defines an ω-regular language. |
| [HSP83] | S. Hart, M. Sharir & A. Pnueli, "Termination of Probabilistic Concurrent Programs," *TOPLAS* 5(3):356–380, 1983. Almost-sure convergence depends only on transition topology, not probability values. |
| [PZ93] | A. Pnueli & L.D. Zuck, "Probabilistic Verification," *Information and Computation* 103:1–29, 1993. Probabilistic choices can be replaced by nondeterministic choices under strong fairness. |
| [HJ94] | H. Hansson & B. Jonsson, "A Logic for Reasoning about Time and Reliability," *Formal Aspects of Computing* 6:512–535, 1994. Introduces PCTL; model checking algorithm polynomial in model, linear in formula. |
| [BdA95] | A. Bianco & L. de Alfaro, "Model Checking of Probabilistic and Nondeterministic Systems," *FSTTCS* 1995, LNCS 1026, pp. 499–513. Defines PCTL*; complexity: PSPACE for DTMCs, 2EXPTIME for MDPs. |
| [dA97] | L. de Alfaro, "Formal Verification of Probabilistic Systems," PhD thesis, Stanford, 1997. Detailed treatment of BSCC structure, reachability linear equations, and MDP end components. |
| [SEJK16] | S. Sickert, J. Esparza, S. Jaax & J. Křetínský, "Limit-Deterministic Büchi Automata for Linear Temporal Logic," *CAV* 2016, LNCS 9780, pp. 312–332. LDBAs replace DRAs for MDP model checking, avoiding Safra's construction. |
| [KSK76] | J.G. Kemeny, J.L. Snell & A.W. Knapp, *Denumerable Markov Chains*, 2nd ed., Springer, 1976. Standard reference for cylinder-set measure construction on countable-state Markov chains. |
| [Put94] | M.L. Puterman, *Markov Decision Processes: Discrete Stochastic Dynamic Programming*, Wiley, 1994. Standard MDP reference: schedulers, value iteration, policy optimality. |
| [HN12] | J. Hölzl & T. Nipkow, "Verifying pCTL Model Checking," *TACAS* 2012, LNCS 7214, pp. 347–361. Isabelle/HOL formalization of DTMC trace spaces and pCTL model checking correctness. |
| [AT12] | M.K. Aguilera & S. Toueg, "The correctness proof of Ben-Or's randomized consensus algorithm," *Distrib. Comput.* 25:371–381, 2012. First complete proof under strong adversary with f < n/2. |
| [Ben83] | M. Ben-Or, "Another advantage of free choice: completely asynchronous agreement protocols," *PODC* 1983, pp. 27–30. Original randomized consensus algorithm. |

---

## Mathlib Inventory (what we get for free)

| Component | Mathlib Location | Notes |
|-----------|-----------------|-------|
| Markov kernels | `Probability.Kernel.Defs` | `Kernel α β`, `IsMarkovKernel`, `∘ₖ`, `×ₖ` |
| Cylinder sets | `MeasureTheory.Constructions.Cylinders` | `cylinder`, `measurableCylinders`, π-system |
| Product σ-algebra | `MeasureTheory.Constructions.Cylinders` | `generateFrom_measurableCylinders` |
| Infinite product measure | `Probability.ProductMeasure` | `Measure.infinitePi` via Carathéodory |
| Ionescu-Tulcea | `Probability.Kernel.IonescuTulcea.Traj` | `traj`, `trajMeasure` — infinite kernel composition |
| Projective families | `MeasureTheory.Constructions.Projective` | `IsProjectiveMeasureFamily` |
| Invariant measures | `Probability.Kernel.Invariance` | `Kernel.Invariant`, `Kernel.IsReversible` |
| Irreducibility | `Probability.Kernel.Irreducible` | `Kernel.IsIrreducible` |
| Martingales | `Probability.Martingale.*` | `Supermartingale`, a.s. convergence |
| Probability measures | `MeasureTheory.Measure.Typeclasses.Probability` | `IsProbabilityMeasure` |
| Borel-Cantelli | `Probability.BorelCantelli` | `measure_limsup_eq_one` (2nd BC lemma) |
| Independence | `Probability.Independence.*` | `iIndepSet`, `iIndepFun` |

## CSLib Inventory (what we can reuse from CSLib)

CSLib (leanprover/cslib) provides automata theory and transition system
infrastructure that overlaps significantly with our Phase P2 and P3 needs.

| Component | CSLib Location | Type / Definition | Reuse Potential |
|-----------|---------------|-------------------|-----------------|
| **Det. Büchi automaton** | `Automata.DA.Buchi` | `DA.Buchi State Symbol` with `DA.run` and acceptance `∃ᶠ k in atTop, run xs k ∈ accept` | **High** — nearly identical to our `DetOmegaAut` + `buchiAcceptSet`. Could replace Phase P2's automaton definition. |
| **Det. Muller automaton** | `Automata.DA.Muller` | `DA.Muller State Symbol` with `(run xs).infOcc ∈ accept` | Medium — useful if we formalize Muller acceptance measurability |
| **Deterministic automaton** | `Automata.DA` | `DA State Symbol` extending `FLTS` with `start : State`; `DA.run : DA → ωSequence Symbol → ωSequence State` | **High** — has `run_zero`, `run_succ` matching our `DetOmegaAut` |
| **FLTS (functional LTS)** | `Semantics.FLTS.Basic` | `FLTS State Label` with `tr : State → Label → State` | **High** — deterministic transition function, same as our `DetOmegaAut.trans` |
| **FLTS product** | `Semantics.FLTS.Prod` | `FLTS.prod : FLTS S₁ L → FLTS S₂ L → FLTS (S₁ × S₂) L` | **High** — directly useful for Phase P3 product DTMC ⊗ DRA |
| **DA product** | `Automata.DA.Prod` | `DA.prod da1 da2 : DA (S₁ × S₂) Symbol` with `prod_mtr_eq` | **High** — product automaton with run decomposition theorem |
| **ω-sequences** | `Data.OmegaSequence.Defs` | `ωSequence α` (wrapper around `ℕ → α`) with `head`, `tail`, `drop`, `map` | Medium — our code uses raw `ℕ → α`; interconvertible via coercion |
| **Infinite occurrence** | `Data.OmegaSequence.InfOcc` | `infOcc : ωSequence α → Set α` = `{x \| ∃ᶠ k in atTop, xs k = x}` | Medium — characterizes states visited infinitely often |
| **LTS reachability** | `Semantics.LTS.Basic` | `LTS.CanReach s1 s2 := ∃ μs, MTr s1 μs s2` | **High** — foundation for defining SCCs/BSCCs in Phase P3 |
| **LTS generated by** | `Semantics.LTS.Basic` | `LTS.generatedBy s` — restricts LTS to reachable states | Medium — useful for restricting to reachable part of product |
| **Nondeterministic Büchi** | `Automata.NA.Buchi` | `NA.Buchi State Symbol` with `∃ ss, Run xs ss ∧ ∃ᶠ k in atTop, ss k ∈ accept` | Low — nondeterministic; less relevant for probability (need deterministic) |
| **NA product** | `Automata.NA.Prod` | `NA.iProd : (i : I) → NA (State i) Symbol → NA (Π i, State i) Symbol` | Low — indexed product of NAs, not directly needed |
| **Bisimulation** | `Semantics.LTS.Bisimulation` | `IsBisimulation r`, `Bisimilarity` | Low — not directly needed for probabilistic verification |
| **ω-languages** | `Languages.OmegaLanguage` | `ωLanguage α = Set (ωSequence α)`, `omegaPow`, `omegaLim` | Low — language-theoretic view; we work with measure-theoretic sets |

### Key Observations

1. **Phase P2 overlap**: CSLib's `DA.Buchi` is essentially our `DetOmegaAut` +
   Büchi acceptance. The main difference: CSLib uses `ωSequence` (wrapped `ℕ → α`)
   while we use raw `ℕ → α` (needed for Mathlib's `MeasurableSpace.pi`). The
   measurability proofs are new — CSLib has no measure theory.

2. **Phase P3 opportunity**: `DA.prod` and `FLTS.prod` give the product automaton
   for free. The product of a DA with a DRA can be built on top of this. The key
   missing piece is BSCC analysis — CSLib has `CanReach` but no SCC/BSCC definitions.

3. **No SCC/BSCC in CSLib**: There are no strongly connected component or bottom SCC
   definitions. These need to be built, likely using `LTS.CanReach` as the foundation:
   `SCC s1 s2 := CanReach s1 s2 ∧ CanReach s2 s1`,
   `BSCC B := (∀ s1 s2 ∈ B, SCC s1 s2) ∧ (∀ s ∈ B, ∀ s', CanReach s s' → s' ∈ B)`.

4. **`ωSequence` vs `ℕ → α`**: CSLib wraps sequences in a structure. For Mathlib
   integration (measurable spaces on `ℕ → S`), we need raw functions. The coercion
   `ωSequence α → (ℕ → α)` exists but adds friction. Consider keeping both views
   and bridging where needed.

## LTLLib Inventory (what we already have)

| Component | File | Reusable for prob? |
|-----------|------|--------------------|
| LTL syntax & NNF | `LTL/Syntax.lean` | Yes — formula type, subformulas |
| LTL semantics (trace-based) | `LTL/Semantics.lean` | Yes — `NNF.satisfies`, `NNF.toPred` |
| Büchi automata specs | `Acceptance.lean`, `GBA.lean`, `BA.lean` | Yes — `OASpec`, acceptance conditions |
| LTL→GBA soundness/completeness | `Soundness.lean`, `Completeness.lean` | Yes — `expandOASpec_correct` |
| Degeneralization | `Acceptance.lean`, `DegeneralBridge.lean` | Partially — acceptance set structure |

---

## Shared Foundation (P1, P2, B1) ✅ ALL DONE

These phases are shared by both downstream pipelines.

### Phase P1: DTMC as Markov Kernel ✅ DONE

**Justification**: The standard definition of a DTMC as a tuple (S, **P**, ι_init, AP, L)
appears in [BK08, Def. 10.1]. The measure-theoretic construction of the path space
via cylinder sets and Carathéodory extension is from [KSK76, Ch. 1–3] and
[BK08, §10.1]. The Ionescu-Tulcea theorem (used in our formalization via Mathlib's
`trajMeasure`) is the standard tool for constructing probability measures on
infinite product spaces from a sequence of transition kernels; it generalizes the
Kolmogorov extension for the Markov (non-product) case. See also [HN12] for the
analogous Isabelle/HOL formalization.

**File**: `ProbMC/DTMC.lean`

**What was formalized**:
- `DTMC S`: structure wrapping `Kernel S S` with `IsMarkovKernel`
- `itKernel`: Ionescu-Tulcea kernel (project last coordinate, apply transition)
- `pathMeasure μ₀`: probability measure on `ℕ → S` via `trajMeasure`
- `pathMeasureFrom s`: path measure from single state (Dirac)
- `nStep n`: n-step transition `κ^n` with Chapman-Kolmogorov (`nStep_add`)

### Phase P2: Measurability of ω-Regular Properties ✅ DONE

**Justification**: The measurability of ω-regular languages in the product
σ-algebra is established in [Var85, §3] and fully developed in [CY95, §2].
The key argument: for a deterministic Büchi automaton with accepting states F,
acceptance = "visit F infinitely often" = lim sup_{n} {run ∈ F at step n},
which is a G_δ set (countable intersection of open sets in the product topology).
Since the product σ-algebra on a countable product of discrete spaces equals the
Borel σ-algebra [BK08, §10.1.2], G_δ sets are measurable. For Rabin acceptance,
the condition is a Boolean combination of Büchi (inf. often) and co-Büchi
(fin. often) conditions, both measurable. This argument is spelled out in
[CY95, Lemma 2.1] and [BK08, Theorem 10.39].

**File**: `ProbMC/OmegaRegularMeasurable.lean`

**What was formalized**:
- `DetOmegaAut Q Alph`: deterministic ω-automaton (init + trans)
- `measurable_run_at`: run at step n is measurable (by induction on n)
- `measurableSet_buchiAcceptSet`: Büchi acceptance is G_δ = `⋂_n ⋃_k {run(n+k) ∈ F}`
- `measurableSet_finitelyOftenSet`: "visit F finitely often" is F_σ
- `measurableSet_rabinAcceptSet`: Rabin acceptance is measurable

### Phase B1: MDP Definition ✅ DONE

**File**: `ProbMC/MDP.lean`

- `MDP S Act`: structure with `step : Kernel (S × Act) S`
- `MemorylessStrategy`: stationary policy `S → Act`, yields DTMC via `resolveKernel`
- `Strategy`: history-dependent policy `(n : ℕ) → (∀ _ : Iic n, S) → Act`
  (for strong adversaries that see full history)
- `MDP.pathMeasure π μ₀`: path measure under any strategy via Ionescu-Tulcea
- `probLowerBoundForAll` / `almostSurelyForAll`: probability properties quantified
  over all adversary strategies

B1 generalizes P1: fixing a strategy in an MDP gives a DTMC. B1 is used by the
Ben-Or pipeline (B2–B6) and could also serve P6 (MDP extension) if pursued.

---

## Probabilistic Model Checking Pipeline (P3–P6)

Uses the shared foundation (P1, P2) to formalize the automata-theoretic approach
to probabilistic LTL model checking.

### Phase P3: Product Construction DTMC ⊗ DRA

**Justification**: The product construction is the central technique of the
automata-theoretic approach to probabilistic model checking, originating in
[Var85, §4] and formalized as the standard algorithm in [CY95, §3]. Given a
DTMC D and a DRA A_φ recognizing an LTL property φ, the product D ⊗ A_φ is
itself a DTMC [BK08, Def. 10.54]. The key reduction theorem — Pr_s(φ) equals
the probability of reaching an accepting BSCC in the product — is
[CY95, Theorem 3.1] and [BK08, Theorem 10.56]. The BSCC absorption lemma
(almost all infinite paths eventually stay in a BSCC) is from
[KSK76, Theorem 1.4.1] for the countable case and [BK08, Lemma 10.27] for the
finite case. de Alfaro's thesis [dA97, Ch. 3] gives the most detailed treatment,
including the construction for Rabin acceptance conditions specifically.

**File**: `ProbMC/ProductDTMC.lean`

**Definitions**:
- `DRA Q Alph`: deterministic Rabin automaton
- `DTMC.product (D : DTMC S) (A : DRA Q (Set ap))`: product DTMC on `S × Q`
- `BSCC`: bottom strongly connected component (graph-theoretic)
- `acceptingBSCC`: BSCC satisfying Rabin condition

**Key theorems**:
- `product_isMarkovKernel`: product kernel is Markov
- `product_pathMeasure_eq`: paths in product = paths in D paired with automaton run
- `pr_ltl_eq_pr_reach_accepting_bscc`:
  `Pr_D(φ) = Pr_{D⊗A}(reach accepting BSCC)` — [CY95, Thm 3.1], [BK08, Thm 10.56]

**Estimated difficulty**: Hard.

**Dependencies**: Phase P1, Phase P2, DRA definition.

---

### Phase P4: LTL Probabilistic Model Checking Correctness

**Justification**: The characterization of reachability probabilities as the
least fixpoint of a linear equation system is from [BK08, Theorem 10.19] and
[dA97, §3.2]. For a DTMC with states partitioned into target states (prob = 1),
states that cannot reach the target (prob = 0), and remaining states, the
reachability probabilities are the unique solution of x_s = Σ_{s'} P(s,s') · x_{s'}
subject to boundary conditions. This is [CY95, Proposition 4.1] and underpins
every practical probabilistic model checker (PRISM, Storm). The PCTL model
checking algorithm of [HJ94] and its Isabelle formalization [HN12] also rely on
this linear characterization.

**File**: `ProbMC/ProbModelCheck.lean`

**Key theorems**:
- `probLTL_eq_reachability`: reduces LTL probability to reachability in product
- `reachabilityProb_linear_system`: [BK08, Thm 10.19], [dA97, §3.2]
- `probLTL_welldefined`: `Pr_s(φ)` is well-defined

**Estimated difficulty**: Hard.

**Dependencies**: Phase P3.

---

### Phase P5: Qualitative Verification (Pr = 0 or 1)

**Justification**: The qualitative theory has two main results:

1. **BSCC 0/1 law**: Within an irreducible finite Markov chain (= a single BSCC),
   any tail event has probability 0 or 1. This is the Kolmogorov 0–1 law applied
   to the tail σ-algebra, specialized to finite chains. See [KSK76, §1.4] and
   [BK08, Corollary 10.30]. Consequence: `Pr_s(φ) = 1 ↔ every reachable BSCC
   in D ⊗ A_φ is accepting` [BK08, Theorem 10.55].

2. **Probabilistic ↔ fair nondeterministic**: Vardi's 1985 result [Var85, Theorem 1]
   established that `Pr(φ) = 1` iff every fair computation satisfies φ, where "fair"
   means every persistently enabled transition is taken infinitely often. This was
   formalized more precisely in [HSP83] (conditions depend only on topology) and
   [PZ93] (probabilistic choices ↔ nondeterministic + strong fairness).

**File**: `ProbMC/Qualitative.lean`

**Key theorems**:
- `pr_one_iff_all_bscc_accepting`: [BK08, Thm 10.55]
- `pr_one_iff_fair_paths`: [Var85, Thm 1], [PZ93]
- `pr_zero_or_one_for_bscc`: [KSK76, §1.4], [BK08, Cor 10.30]

**Estimated difficulty**: Medium.

**Dependencies**: Phase P3.

---

### Phase P6 (Optional): MDP Extension

**Justification**: The extension to MDPs follows [BdA95] for the logic PCTL* and
[CY95, §5] for the LTL case. The key concept is the **scheduler** (or adversary/policy),
first formalized in [Var85, §5] for the probabilistic setting. The quantities
Pr^max(φ) = sup_𝔖 Pr^𝔖(φ) and Pr^min(φ) = inf_𝔖 Pr^𝔖(φ) are well-defined
[BdA95, Thm 3.1]. **Maximal end components (MECs)** replace BSCCs: under any
scheduler, an MDP almost surely reaches a MEC [dA97, Theorem 3.1],
[BK08, Theorem 10.120]. For LTL properties, the product MDP ⊗ DRA reduces
verification to reachability in the product [CY95, §5], with complexity
2EXPTIME-complete [BdA95] due to Safra determinization. The LDBA approach
of [SEJK16] avoids determinization for the MDP case. The standard reference
for MDP theory (Bellman equations, value iteration, policy optimality) is [Put94].

**File**: `ProbMC/MDPExtension.lean`

**Key theorems**:
- `mdp_maxProb_attained_by_memoryless`: [Put94, Ch. 6], [BK08, Thm 10.100]
- `mdp_ltl_via_mec`: [CY95, §5], [dA97, §3.3]

**Estimated difficulty**: Very Hard. Consider deferring.

**Dependencies**: All of P1–P5.

---

### Suggested Execution Order

```
         Shared Foundation
┌──────────────────────────────────┐
│ P1 (DTMC) ✅   P2 (ω-reg) ✅    │
│         B1 (MDP) ✅              │
└──────┬───────────────┬───────────┘
       │               │
       ▼               ▼
  PMC Pipeline    Ben-Or Pipeline
┌──────────────┐ ┌─────────────────┐
│ P3 (Product) │ │ B2 (Epochs) ✅   │
│   │          │ │ B3 (Veil DSL)   │
│   ├→ P4      │ │ B4 (Compile)    │
│   └→ P5      │ │ B5 (Model)      │
│      └→ P6   │ │ B6 (Pr=1)       │
└──────────────┘ └─────────────────┘
```

**PMC minimum viable result**: P1 + P2 gives "Pr_s(φ) is well-defined."
**PMC core result**: + P3 gives "Pr_s(φ) = Pr(reach accepting BSCC in product)."
**PMC full result**: + P4–P5 gives both quantitative and qualitative model checking.
**Ben-Or result**: B1–B6 gives "Ben-Or terminates with probability 1."

---

## File Layout

```
ProbMC/
├── DTMC.lean                   (Phase P1) ✅
├── OmegaRegularMeasurable.lean (Phase P2) ✅
├── MDP.lean                    (Phase B1) ✅
├── IndependentEpochs.lean      (Phase B2) ✅
├── BenOrPlan.md                (detailed Ben-Or pipeline plan)
├── DRA.lean                    (Phase P3, not started)
├── ProductDTMC.lean            (Phase P3, not started)
├── BSCC.lean                   (Phase P3, not started)
├── ProbModelCheck.lean         (Phase P4, not started)
├── Qualitative.lean            (Phase P5, not started)
├── MDPExtension.lean           (Phase P6, not started)
└── BenOr/                      (Phase B5–B6, not started)
    ├── Model.lean              (protocol as MDP)
    ├── Safety.lean             (agreement, validity)
    └── Termination.lean        (probabilistic liveness)
```

---

## Risk Assessment

| Risk | Mitigation |
|------|-----------|
| Ionescu-Tulcea instantiation is painful | Start with finite S (Fintype), where `infinitePi` may suffice |
| Product topology ≠ product σ-algebra issues | For finite/countable S, they coincide; restrict to `Fintype S` initially |
| DRA definition missing from Mathlib | Define locally; keep minimal (Fintype states) |
| BSCC theory requires substantial graph theory | Leverage cslib's `LTS.CanReach`; or define BSCCs directly for finite graphs |
| Linear equation characterization is deep | Phase P4 can be deferred; P1+P2+P3 already gives the main reduction |
| MDP scheduler optimization is very hard | Phase P6 is explicitly optional |
| Veil DSL extension is complex (Ben-Or) | Bypass with manual MDP definition for Ben-Or |
| FavorableToss definition is intricate (Ben-Or) | Follow [AT12] proof structure closely |

---

## Connection to Existing LTLLib

The existing LTL→GBA→BA pipeline produces a Büchi automaton for ¬φ. For
probabilistic verification, we need:

1. **Determinize** the BA to a DRA (Safra's construction or LDBA approach)
   — This is algorithmically complex. For the formalization, we can:
   - (a) Assume a correct DRA is given (axiomatize the translation), or
   - (b) Use the existing BA directly for qualitative verification (Phase P5),
     since Pr=1 checking only needs graph-theoretic BSCC analysis [BK08, §10.3.3], or
   - (c) Formalize limit-deterministic Büchi automata (LDBA) following [SEJK16]

2. **Reuse `OASpec`** from `Acceptance.lean` as the abstract automaton interface
   for the product construction

3. **Reuse `NNF.satisfies`** from `Semantics.lean` as the ground truth for
   what "ξ ⊨ φ" means — the bridge theorem becomes:
   `Pr{ξ | NNF.satisfies ξ (toNNF φ)} = Pr(reach accepting BSCC in D ⊗ A_{¬φ})`

---

## Ben-Or Probabilistic Liveness Pipeline (B2–B6)

A second track, orthogonal to the general P3–P6 pipeline above, targeting the
first proof-assistant-verified probabilistic liveness proof for a distributed
protocol. Uses a three-layer pipeline: Veil DSL → MDP compilation → Borel-Cantelli.
Builds on the shared foundation (P1, P2, B1).

See `ProbMC/BenOrPlan.md` for the detailed design.

### Three-Layer Pipeline

```
Layer 1: Veil DSL (user writes protocol with coin_toss)
    │  coin_toss compiled specially; pick stays adversarial
    ▼
Layer 2: MDP (compiled artifact)
    │  fix adversary strategy → path measure via Ionescu-Tulcea
    ▼
Layer 3: Probabilistic reasoning (user proves bounds)
    │  independent epochs + Borel-Cantelli → Pr = 1
    ▼
Result: Ben-Or terminates with probability 1
```

### Phase B2: Independent Epochs Theorem ✅ DONE

**File**: `ProbMC/IndependentEpochs.lean`

- `ENNReal.tsum_eq_top_of_pos_lower_bound`: tsum divergence from uniform bound
- `almostSure_of_independent_events`: second Borel-Cantelli + limsup ⊆ union
- `MDP.almostSurelyForAll_of_epoch_bound`: if independent epoch events each have
  probability ≥ p > 0 under all strategies, their union has probability 1 under
  all strategies. This is the key reusable pattern for randomized protocol termination.

### Phase B3: Veil DSL Extension ⬜ NEXT

**Location**: Veil repo (`veil-dev-clean-3/`)

- Add `coin_toss` and `sample` primitives alongside `pick`
- `pick` = adversarial (∀-quantified); `coin_toss` = probabilistic (measured)
- Extend `NonDetT` monad with a third mode ("probabilistic")

**Estimated effort**: ~1 week.

### Phase B4: MDP Compilation from Veil Spec ⬜

- Compile Veil `RelationalTransitionSystem` + probabilistic annotations → `MDP`
- `pick` choices → `Act`; `coin_toss` choices → kernel in `step`
- Compilation correctness theorem

**Estimated effort**: 2–3 weeks. **Dependencies**: B3.

### Phase B5: Ben-Or Model + Safety ⬜

- Model Ben-Or in extended Veil DSL
- Safety proofs (agreement, validity) via Veil SMT [AT12, §5.1]
- Epoch structure: epoch r = rounds (2r, 2r+1)

**Estimated effort**: 2–3 weeks. **Dependencies**: B3, B4.

### Phase B6: Probabilistic Termination ⬜

- Define FavorableToss function (Fig. 2 of [AT12])
- Prove: lucky epoch → value locked (Lemma 6 of [AT12])
- Prove: ≤ 2n coins per epoch → Pr(lucky) ≥ 2^{-2n} (Lemma 7)
- Prove: disjoint coins → independent epochs
- Instantiate `MDP.almostSurelyForAll_of_epoch_bound` → Pr(termination) = 1

**Estimated effort**: 2–3 weeks. **Dependencies**: B2, B5.

### Alternative: bypass Veil

If Veil modification is deferred, define Ben-Or's state and transitions
as an `MDP` directly in ProbMC (bypassing the DSL), then prove probabilistic
termination against that hand-written model. Faster but less reusable.

---

## Current Status

### Completed ✅

| Phase | Section | File | Status |
|-------|---------|------|--------|
| P1: DTMC | Shared | `ProbMC/DTMC.lean` | Sorry-free |
| P2: ω-regular measurability | Shared | `ProbMC/OmegaRegularMeasurable.lean` | Sorry-free |
| B1: MDP definition | Shared | `ProbMC/MDP.lean` | Sorry-free |
| B2: Independent epochs | Ben-Or | `ProbMC/IndependentEpochs.lean` | Sorry-free |

### Next Steps ⬅

**PMC pipeline**: Phase P3 (Product DTMC ⊗ DRA) — hard, requires graph theory for BSCCs.

**Ben-Or pipeline**: Phase B3 (Veil DSL extension) — the enabling step for all
downstream Ben-Or work. Critical path: `B2 ✅ → B3 ⬜ → B4 ⬜ → B5 ⬜ → B6 ⬜`
