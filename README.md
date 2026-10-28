# LTLLib

A standalone Lean 4 library for LTL (Linear Temporal Logic) model checking. It provides the formally verified pipeline from an LTL formula to a transition-based generalized Büchi automaton (TGBA), an on-the-fly product against an external system, and SCC-based emptiness checks, composed end to end into total, machine-checked decision procedures: model checking a system against an LTL property under a fairness assumption, and standalone LTL satisfiability.

Only `LTLLib/TGBABased/` is used, and only it is described here. The state-based pipeline beside it is deprecated and kept for reference alone, see [Other routes](#other-routes).

The translation follows the ltl2ba and ltl3ba line of work, Gastin and Oddoux (CAV'01) [GO01] and Babiak, Křetínský, Řehák and Strejček (TACAS'12) [BKŘS12], with the formula and automaton simplifications of Somenzi and Bloem (CAV'00) [SB00]. The emptiness checks follow the SCC-based checks of Renault, Duret-Lutz, Kordon and Poitrenaud (LPAR-19) [RDKP13]. Fairness is decided by hoisting, Li, Song, Feng and Zhang (arXiv:1606.08116) [LSFZ16], together with the recursive fairness check of PAT, Sun, Liu, Dong and Pang (CAV'09) [SLDP09], and the prune of Emerson and Lei (1987) [EL87]. Each stage is implemented and proved in Lean directly from those papers, and every file records the references for the arguments it reuses.

## Contents

- [LTLLib](#ltllib)
  - [Contents](#contents)
  - [Building and testing](#building-and-testing)
  - [LTL to TGBA translation](#ltl-to-tgba-translation)
    - [Top-level results](#top-level-results)
    - [Correctness link in the chain](#correctness-link-in-the-chain)
    - [Algorithm pipeline](#algorithm-pipeline)
  - [Model checking](#model-checking)
    - [Top-level results](#top-level-results-1)
    - [Example usage](#example-usage)
    - [What the caller supplies](#what-the-caller-supplies)
    - [Correctness link in the chain](#correctness-link-in-the-chain-1)
    - [Algorithm pipeline](#algorithm-pipeline-1)
    - [Labelled steps and edge atoms](#labelled-steps-and-edge-atoms)
    - [Terminal states](#terminal-states)
  - [Satisfiability](#satisfiability)
    - [Top-level results](#top-level-results-2)
    - [Example usage](#example-usage-1)
    - [Algorithm pipeline](#algorithm-pipeline-2)
    - [Correctness link in the chain](#correctness-link-in-the-chain-2)
  - [Proof status](#proof-status)
  - [Other routes](#other-routes)
    - [Without fairness](#without-fairness)
    - [Other fairness routes](#other-fairness-routes)
    - [The deprecated state-based pipeline](#the-deprecated-state-based-pipeline)
  - [File organization](#file-organization)
    - [Module descriptions](#module-descriptions)

## Building and testing

Install [Elan](https://github.com/leanprover/elan) and use the toolchain pinned in
`lean-toolchain`. Full verification also requires Git and Python 3.9 or newer:

```sh
python3 scripts/verify.py
```

Use this command for full verification. It checks source coverage, then builds the main library,
tests, examples and retained historical proofs. By default it prints coverage and the final result,
build and test logs are shown on failure. Any coverage, compilation, test assertion or axiom-guard
failure, warning, or Lean panic produces a nonzero exit status, including panics replayed from
Lake's build cache. Add `--verbose` to stream all build and test output. A successful run reports:

```text
Source coverage: PASS (151/151 Lean files)
Building library and tests...
Library build: PASS
Tests, examples and historical proofs: PASS
Axiom checks: PASS
Warnings: 0; panics: 0
```

| Command | Scope |
|---|---|
| `lake build` | Main library and proofs imported by `LTLLib.lean` |
| `python3 scripts/verify.py` | Full verification of all Lean sources, tests, examples and historical proofs |
| `python3 scripts/verify.py --coverage-only` | Audit that every Lean source is reached by a build target, without compiling |

## LTL to TGBA translation

Compiles an LTL formula into a TGBA over its atoms, with the label and the acceptance marks on each transition rather than on each state. This is the shared core beneath both [Model checking](#model-checking), which translates whatever part of `¬φ` is not hoisted, and [Satisfiability](#satisfiability), which translates `φ` directly.

### Top-level results

```lean
theorem ltl3ba_accepts (φ : NNF α) {t : TGBA α} (h : ltl3ba φ = some t) (ξ : OmegaWord α) :
    t.toSpec.accepts ξ ↔ φ.satisfies ξ

theorem ltl3baFormula_accepts (φ : Formula α) {t : TGBA α} (h : ltl3baFormula φ = some t)
    (ξ : OmegaWord α) : t.toSpec.accepts ξ ↔ ¬ φ.satisfies ξ

theorem ltl3ba_isSome (φ : NNF α) : (ltl3ba φ).isSome
```

`ltl3ba_isSome` makes the translation total. `ltl3ba_wellFormed` and `ltl3ba_marks_lt` are the two structural facts the searches need: the automaton is well formed, and every mark on every transition indexes an acceptance set.

### Correctness link in the chain

| Correctness link | Theorem | File |
|---|---|---|
| The rewrite pass preserves every formula's language | `simplify_correct` | `LTLtoTGBA/Preprocess/Simplify.lean` |
| The VWAA of a formula accepts exactly its models | `ConcreteVWAA.build_correct` | `LTLtoTGBA/VWAA.lean` |
| Letterwise simulation carries acceptance across a reduction | `VWAA.acceptsFrom_congr` | `LTLtoTGBA/AbstractSpec/VWAAReduce.lean` |
| A TGBA meeting (S) and (C) accepts what its VWAA accepts | `vwaaToTgba_correct` (generalised [GO01] Theorem 2) | `LTLtoTGBA/AbstractSpec/VWAAToTGBA.lean` |
| The construction meets (S) and tight (C) | `canonicalTrans_soundTrans`, `canonicalTrans_completeTransTight` | `LTLtoTGBA/TGBAConstruct.lean` |
| The numbered output accepts what the VWAA accepts | `buildTGBA_build_accepts_iff` | `LTLtoTGBA/TGBAConstructCorrect.lean` |
| A posteriori simplification preserves the language | `simplifyTGBA_correct` | `LTLtoTGBA/TGBASimplify.lean` |
| The whole translator accepts exactly the models of `φ` | `ltl3ba_accepts` | `LTLtoTGBA/Pipeline.lean` |

### Algorithm pipeline

```
φ (in NNF)     (NNF α, internal IR — φ for satisfiability, the kept part of ¬φ for model checking)
    │
    ▼  simplify                   ✓ language preserved, one bottom-up pass (simplify_correct)
φ rewritten
    │
    ▼  ConcreteVWAA.build         ✓ accepts ξ ↔ ξ ⊨ φ (ConcreteVWAA.build_correct)
Very weak alternating co-Büchi automaton (VWAA), states as bitmasks over the subformula table
    │
    ▼  buildTGBA                  ✓ (S) and tight (C) of [GO01] Thm 2 (canonicalTrans_*)
TGBA, one transition per non-contradictory cube, marks on transitions
    │
    ▼  simplifyTGBA               ✓ language preserved (simplifyTGBA_correct)
TGBA, mark-erased, implied transitions and equivalent states merged, dead states pruned
```

## Model checking

Check an external system against an LTL property under a fairness assumption. The system is given as initial states, a successor function and a state-labeling function, with no bundled record type, which is what an on-the-fly checker needs. `modelCheckFair` negates the property, hoists every fairness conjunct out of it, translates only what is left, forms the product *on-the-fly*, and decides the hoisted conjuncts per strongly connected component, called **pruning**.

Hoisting is the point of the route. A fairness conjunct that reaches the translator becomes automaton states and acceptance marks that multiply the product, so each one is instead turned into acceptance marks and a region on the product, keeping the translation small. For example, a property that is itself a fairness, such as `□◇p → □◇q`, leaves the translator with `⊤`.

### Top-level results

```lean
theorem modelCheckFair_empty_unsat (φ : Formula α) (sysInit) (sysSucc) (sysLabel)
    (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {n : Nat}
    (h : modelCheckFair φ sysInit sysSucc sysLabel = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ

theorem modelCheckFair_nonEmpty_sat (φ : Formula α) (sysInit) (sysSucc) (sysLabel)
    (hstate : ∀ b ∈ branches …, ∀ ds ∈ …, ∀ d ∈ ds, LSys.StateOnly sysSucc sysLabel d.1.eval)
    {stem loop : List (SysState × Nat)}
    (h : modelCheckFair φ sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ ∧
      (∀ n, (lassoAt stem loop.tail n).map Prod.fst = some (ρ n).1)
```

If a counterexample exists, a concrete one is also reported in lasso form, so `stem` and `loop` are a trace of the system a user can read.

A front end should call `modelCheckFairRoutedOfStep`, which takes the system as one callback and picks the route itself:

```lean
theorem modelCheckFairRoutedOfStep_empty_unsat (φ) (sysInit) (sysStep) (edgeAtom : α → Bool)
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1)) {n : Nat}
    (h : modelCheckFairRoutedOfStep φ sysInit sysStep edgeAtom = .empty n) : …

theorem modelCheckFairRoutedOfStep_nonEmpty_sat (φ) (sysInit) (sysStep) (edgeAtom : α → Bool)
    (hsteps : ∀ s, ∀ st ∈ LSys.totalize (fun s => (sysStep s).1) s, ∀ a ∈ st.1, edgeAtom a = true)
    (sysFR : pruneApplicable edgeAtom φ = false →
      FiniteReach sysInit (LSys.targets fun s => (sysStep s).1))
    {stem loop : List (SysState × Nat)}
    (h : modelCheckFairRoutedOfStep φ sysInit sysStep edgeAtom = .nonEmpty stem loop) : …
```

`edgeAtom` marks the atoms a *step* may contribute. `pruneApplicable` then tests the regions each branch of the prune actually receives, and a property that puts one of those atoms inside a hoisted `◇□` falls back to crossing (see [Other fairness routes](#other-fairness-routes)), which latches such a region into the product instead. A system with no edge atoms passes `fun _ => false` and always takes the pruning approach. Both routes answer the same question.

In a real terms, a system may encode a "action taken" edge atom (like TLA+). Then, a fall back to crossing could happen if the the formula has strong fairness
as a property under an assumption (Assumption -> SF) instead of as an assumption (SF -> Property).
In most real-world applications like verifying distributed systems, a fall back should be **very** rare.
A system with no edge atoms cannot fall back.
See [Labelled steps and edge atoms](#labelled-steps-and-edge-atoms) for more details.

### Example usage

```lean
open LTLLib

/-- A token circulates round four positions, and may idle at `park`. -/
inductive Spot where
  | park | hold | carry | drop
deriving BEq, Hashable, Repr, Inhabited, DecidableEq

instance : LawfulBEq Spot where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

def succ : Spot → Array Spot
  | .park => #[.park, .hold]   -- idling here is what makes `□◇q` fail on its own
  | .hold => #[.carry]
  | .carry => #[.drop]
  | .drop => #[.park]

def label : Spot → Std.HashSet String
  | .hold => {"p"}             -- the token was picked up
  | .drop => {"q"}             -- the token was delivered
  | _ => ∅

def init : List Spot := [.park]

/-- `□◇p → □◇q`: delivered infinitely often whenever it is picked up infinitely often. -/
def prop : Formula String :=
  .implies (.always (.eventually (.atom "p"))) (.always (.eventually (.atom "q")))

#eval modelCheckFair prop init (LSys.unlabelled succ) label
-- .empty _   (the only way back to `hold` runs through `drop`)
```

`LSys.unlabelled` is how a system without edge atoms is passed, see [Labelled steps and edge atoms](#labelled-steps-and-edge-atoms). Both halves of `prop` are fairness formulas, so the whole implication is one, and so is its negation: the router hoists `□◇p` and `◇□¬q` alike and the translator receives `⊤`.

The runnable demos are in `LTLLibTests/Examples/`: `FairPropertyDemo.lean` is this token ring, including what each routing hands to the translator, `NestedFairnessDemo.lean` and `DeMorganSplitDemo.lean` work through properties whose hoisting is less obvious, and `LTLLibTests/TGBABased/ModelCheckCounterExample.lean` checks a reported counterexample against the system edge by edge.

### What the caller supplies

Nothing is needed to *run* a check. `modelCheckFair` takes no proof argument and cannot fail. The two obligations belong to the theorems:

- **`sysFR : FiniteReach sysInit (LSys.targets sysSucc)`**, that the system's reachable state set is finite, is what makes an `.empty` answer meaningful. It is a bare `Prop` existence certificate (`FinitePred (Reachable …)`), with no witness data needed. For a system finite by construction it is `FiniteReach.of_forall_mem l (fun s => …)`, and otherwise a concrete finite superset. `LSys.finiteReach_unlabelled` converts a certificate about a plain `succ` into one about `LSys.targets (LSys.unlabelled succ)`. The product's finiteness is derived.
- **The witness hypothesis** on the `.nonEmpty` side asks that every hoisted region be `LSys.StateOnly`, decidable from the source state alone. A caller going through `modelCheckFairRoutedOfStep` discharges it by supplying `edgeAtom` and `hsteps`, and `stateOnly_of_pruneApplicable` does the rest.

The prune needs no finiteness on the `.nonEmpty` side: it validates a reported lasso with `streettCheck_nonEmpty_valid`, which has no such hypothesis. That is why `modelCheckFairRoutedOfStep_nonEmpty_sat` owes `sysFR` *only if* the route falls back to the crossing, whose checker contract carries `FiniteReach` as a field.

### Correctness link in the chain

| Correctness link | Theorem | File |
|---|---|---|
| Negating `φ` preserves semantics | `Formula.toNNF_correct_neg` | `LTL/Semantics.lean` |
| Splitting at the top-level conjunctions preserves meaning | `NNF.satisfies_splitConj` | `LTL/Semantics.lean` |
| A fairness is closed under suffixes and prefixes ([LSFZ16] Def. 1) | `isPureEventuality_sound`, `isPurelyUniversal_sound` | `LTL/FairClass.lean` |
| Fair normal form of a fairness in `LTL(F, G)` ([LSFZ16] Thm 1) | `fnf_correct` | `LTL/FairNormalForm.lean` |
| The split into hoisted normal forms and kept conjuncts | `hoistFairness_correct` | `TGBABased/Fairness/FairRouter.lean` |
| Re-hoisting what the rewrite pass exposes | `rehoist_correct` | `TGBABased/Fairness/Rehoist.lean` |
| Splitting a mixed conjunct `ψ ∨ γ` on its sides | `mixedSplit_correct`, `branches_correct` | `TGBABased/Fairness/DisjunctiveHoist.lean` |
| The kept property's TGBA accepts exactly its models | `ltl3ba_accepts` | `TGBABased/LTLtoTGBA/Pipeline.lean` |
| Product run ↔ system run plus TGBA edge-run | `TGBAProduct.gsp_correct1` / `gsp_correct2` | `TGBABased/Product.lean` |
| A region cycle yields a run whose tail stays in the region | `exists_run_of_TRegionCycle` | `TGBABased/Fairness/FairProduct.lean` |
| Accepting SCC exists ↔ accepting cycle exists | `acceptingSCC_iff_acceptingCycle` | `TGBABased/AbstractSpec/SCCTheory.lean` |
| The flushed sets are the maximal SCCs of the reachable subgraph | `enumSCCs_sound` | `TGBABased/SCC/SCCEnumeration.lean` |
| The recursive check misses no fair SCC ([SLDP09], [EL87]) | `streettCheck_empty_no_fairSCC` | `TGBABased/SCC/StreettPrune.lean` |
| A reported stem and cycle is validated before it is reported | `streettCheck_nonEmpty_valid` | `TGBABased/SCC/StreettPrune.lean` |
| Accepting run ⟹ accepting cycle exists (pumping) | `exists_TAcceptingCycle_of_run` | `TGBABased/AbstractSpec/Pumping.lean` |
| Everything composed into system-level model checking | `modelCheckFair_empty_unsat` / `modelCheckFair_nonEmpty_sat` | `TGBABased/ModelCheck.lean` |

### Algorithm pipeline

```
LTL property φ  (Formula α)
    │
    ▼  negate + toNNF                 ✓ proved correct (Formula.toNNF_correct_neg)
¬φ (in NNF)
    │
    ▼  splitConj + hoistFairness      ✓ meaning preserved (hoistFairness_correct)
    │     a conjunct that is a fairness and flattens into LTL(F, G) becomes its fair
    │     normal form ⋁ᵢ (◇□lᵢ ∧ ⋀ⱼ □◇lᵢⱼ) and never reaches the translator (fnf_correct)
    ▼  rehoist                        ✓ meaning preserved (rehoist_correct)
    │     one simplify, splitConj, hoistFairness pass over what was kept
    ▼  mixedSplit + branches          ✓ meaning preserved (branches_correct)
    │     a kept `ψ ∨ γ` with a flattenable fairness γ is decided once per choice of side
kept property  +  hoisted options (per conjunct: a region ◇□l and marks □◇g)
    │
    ▼  ltl3ba on the kept property    ✓ accepts ξ ↔ ξ ⊨ the kept part (ltl3ba_accepts)
TGBA for the kept part
    │
    ▼  TGBAProduct.getSuccessors / initialStates / edgeMarks, on-the-fly, per labelled step
Product graph  (SysState × Nat)      ✓ product run ↔ system run (gsp_correct1/2)
    │
    ▼  streettCheckP                  ✓ validated witness, no fair SCC missed
    │     Tarjan's SCC enumeration, and per closing SCC the prune recursion: an SCC
    │     passes when every conjunct has an available option, and a failing conjunct
    │     sends the SCC back with that option's region conjoined [SLDP09, EL87].
EmptinessResult (SysState × Nat)
    .empty n            → sys ⊨ φ
    .nonEmpty stem loop → a real run of sys violating φ while satisfying the assumption,
                           reported as (system state, kept-automaton state) pairs
```

The first stage is the [LTL to TGBA translation](#ltl-to-tgba-translation) shared with satisfiability. The regions restrict *steps* rather than states, so a hoisted `◇□ψ` may mention an edge atom, and a prune step narrows a region instead of deleting states. The candidate therefore carries its conjoined options as a bitmask and the loop decreases on that bitmask, which is what makes termination independent of whether an edge prune removes any state.

### Labelled steps and edge atoms

An atom like `taken(a)`, meaning "the step being taken is an `a`-step", is not a predicate of any state. Encoding it as one costs a factor of the number of actions in reachable states. A system is therefore presented with the letters on its steps (`TGBABased/LabelledSys.lean`): a successor entry is an `LStep`, a pair of the atoms the step itself contributes and the target, and the letter read at a step is the source state's atoms together with the step's own. The product's state set stays `SysState × Nat`, so an edge atom costs no states at all.

A state-labelled caller passes `LSys.unlabelled sysSucc` and reads every statement back through `LSys.toSpec_isRun_ofRun`, `LSys.valuation_unlabelled` and `LSys.finiteReach_unlabelled`. A caller that computes a state's steps and its atoms together passes one `LSys.StepFn` to an `OfStep` entry point. The two forms are the same term.

### Terminal states

LTL and Büchi semantics are defined over *infinite* words, so every state needs at least one successor, and a terminal state is read as "the system stays there forever". A `sysSucc` that returns `#[]` for some reachable state would break that silently and the check would under-report, missing any counterexample whose violation only manifests by the system stalling there. 
This is fixed automatically by totalizing the system: a state with no outgoing steps gets a self-loop before the product is ever built, contributing the empty letter. Systems that are already total stay the same.

## Satisfiability

Decide whether an LTL formula is satisfiable, with a witness lasso if so, and with no external system.

### Top-level results

```lean
theorem tgbaPipeline_empty_unsat (φ : NNF α) {n : Nat} (h : tgbaPipeline φ = .empty n) :
    ∀ ξ : OmegaWord α, ¬ NNF.satisfies ξ φ

theorem tgbaPipeline_nonEmpty_sat (φ : NNF α) {stem loop : List Nat}
    (h : tgbaPipeline φ = .nonEmpty stem loop) :
    ∃ ξ : OmegaWord α, NNF.satisfies ξ φ
```

`tgbaPipeline` is a computable `def`, defined for every formula, with nothing for the caller to supply: the automaton's own finiteness certificate (`TGBA.finiteReach`) comes from its well-formedness.

### Example usage

```lean
open LTLLib

/-- `□◇a ∧ □◇¬a`: `a` holds infinitely often, and fails infinitely often. -/
def φ : Formula String :=
  .and (.always (.eventually (.atom "a"))) (.always (.eventually (.not (.atom "a"))))

#eval tgbaPipeline (φ.toNNF true)
-- .nonEmpty _ _   (satisfiable, the lists are a stem into a cycle of automaton states)
```

`φ.toNNF true` compiles the surface formula to the internal IR without negating it, which is the difference from model checking, where `toNNF false` is used so that the automaton accepts the violating words.

### Algorithm pipeline

```
LTL formula φ  (Formula α, user-facing syntax)
    │
    ▼  toNNF true                ✓ proved correct (Formula.toNNF_correct)
φ (in NNF)
    │
    ▼  ltl3ba                     ✓ accepts ξ ↔ ξ ⊨ φ (ltl3ba_accepts)
TGBA for φ
    │
    ▼  TGBA.consistentPart        ✓ language preserved (consistentPart_accepts)
TGBA without the transitions no valuation takes, so the graph alone decides the language
    │
    ▼  dijkstraCheck              ✓ validated witness, no accepting cycle missed
EmptinessResult Nat
    .empty n            → φ is unsatisfiable
    .nonEmpty stem loop → φ is satisfiable, witnessed by a lasso of automaton states
```

There is no degeneralization and no product here. The check reads only the graph, which is why the inconsistent transitions are dropped first: after that, every accepting cycle is read by some word (`accepts_of_consistentPart_cycle`).

### Correctness link in the chain

| Correctness link | Theorem | File |
|---|---|---|
| NNF compilation preserves semantics | `Formula.toNNF_correct` | `LTL/Semantics.lean` |
| The TGBA accepts exactly the models of `φ` | `ltl3ba_accepts` | `TGBABased/LTLtoTGBA/Pipeline.lean` |
| The translation always succeeds, well formed, marks in range | `ltl3ba_isSome`, `ltl3ba_wellFormed`, `ltl3ba_marks_lt` | `TGBABased/LTLtoTGBA/Pipeline.lean` |
| Dropping the transitions no valuation takes keeps the language | `TGBA.consistentPart_accepts` | `TGBA.lean` |
| An accepting cycle of the consistent part is read by some word | `TGBA.accepts_of_consistentPart_cycle` | `TGBA.lean` |
| An accepting run of a well-formed TGBA yields a lasso | `TGBA.exists_TAcceptingCycle_of_acceptingRun` | `TGBA.lean` |
| A well-formed TGBA is finite-reach | `TGBA.finiteReach` | `TGBA.lean` |
| Dijkstra's check is sound and complete against `TAcceptingCycle` | `dijkstraCheck_nonEmpty_valid`, `dijkstraCheck_empty_no_cycle` | `TGBABased/SCC/DijkstraSCC.lean` |
| Everything composed into one satisfiability decision procedure | `tgbaPipeline_empty_unsat` / `tgbaPipeline_nonEmpty_sat` | `TGBABased/Satisfiability.lean` |

## Proof status

Every top-level theorem is fully proven: no `sorry`, no admitted hypothesis, and no side condition beyond the system's finite reachability and, on the counterexample side, the witness obligation described in [What the caller supplies](#what-the-caller-supplies). Every decision procedure is a computable `def`.

`LTLLibTests/TGBABased/PipelineTheorems.lean` pins this down with `#guard_axioms`, which fails the build if any of the following depends on an axiom outside `propext`, `Classical.choice` and `Quot.sound`:

- `modelCheckFair_empty_unsat` / `modelCheckFair_nonEmpty_sat`, the default fairness route
- `tgbaPipeline_empty_unsat` / `tgbaPipeline_nonEmpty_sat`, satisfiability
- the same pair for each of the other routes: `modelCheckTGBA`, `modelCheckNDFS`, `modelCheckDijkstra`, `modelCheckFairDirect`, `modelCheckFairFNFCross`, `modelCheckFairFNFPrune`
- `dijkstraTChecker`, `exists_TAcceptingCycle_of_run`, and two proof-level tests applying the theorems to a concrete system

The same file also checks that the theorems are *usable*: both top-level pairs are applied to a concrete traffic light given only its `FiniteReach`.

## Other routes

`modelCheckFair`, reached through `modelCheckFairRoutedOfStep`, is the default and the fastest, and is the only route described above. The others are kept because they are measured against it, and each restates the same two theorems, so switching route changes no obligation on the caller.

### Without fairness

| Entry point | How it differs from `modelCheckFair` |
|---|---|
| `modelCheckDijkstra` | No fairness at all. The whole of `¬φ` goes to the translator and the product is searched by Dijkstra's SCC-based check. A fairness assumption written into `φ` becomes automaton states and marks. |
| `modelCheckNDFS` | No fairness, and the TGBA is degeneralized to a single-mark `TBA` before the product, because the transition-based nested DFS is sound only for one mark. The product is then `SysState × TBAState`, a factor of the mark count larger. |
| `modelCheckTGBAFair` | Dijkstra's check with propositional `□◇ψ` assumptions carried as extra marks on the product. It hoists nothing from the property itself. |

### Other fairness routes

| Entry point | How it differs from `modelCheckFair` |
|---|---|
| `modelCheckFairDirect` | Hoists only the conjuncts that are syntactically `□◇p` or `◇□p` over state predicates, and Boolean combinations of them, which is exactly what TLC's classifier, PAT's classifier and NuSMV's `JUSTICE`/`COMPASSION` recognise. The gap to the routes below measures, from inside this pipeline, what those tools leave on the table. It exists for the ablation study. |
| `modelCheckFairFNFCross` | Hoists every fairness conjunct through its fair normal form, then *crosses* the per-conjunct disjuncts and runs one latched Dijkstra check per combination, instead of deciding them per SCC. The region is latched into the product, so the state carries an extra `Bool`, and the number of checks is the product of the disjunct counts. This is also the fallback the router picks when a hoisted region mentions an edge atom. |
| `modelCheckFairFNFPrune` | The same hoisting, decided per SCC by the prune, but without disjunctive hoisting: a kept conjunct `ψ ∨ γ` whose `∨`-chain contains a flattenable fairness `γ` is left whole for the translator rather than split on its sides. |
| `modelCheckUnderFairness`, `modelCheckUnderFairnessPrune`, `modelCheckUnderFairnessFlat` | The split-level routes in `Fairness/FairRouter.lean` that the modes above are named after, hoisting without the `rehoist` pass. |

Each fairness route also has an `OfStep` form taking one `LSys.StepFn`, bridged to the two-function form by `rfl`.

### The deprecated state-based pipeline

The library still builds an older, state-based pipeline: `GBA.lean`, `BA.lean`, `DegeneralBridge.lean`, `LTLtoGBA/` (the Gerth et al. construction ported from the Isabelle/HOL [LTL_to_GBA](https://www.isa-afp.org/entries/LTL_to_GBA.html) entry of the CAVA framework), `NestedDFS/`, `Product.lean`, `ModelCheck.lean` and `Satisfiability.lean`, with `modelCheck` and `fullPipeline` as its entry points. It is **deprecated**. Acceptance there sits on states, the product is crossed against a degeneralized BA, and there is no fairness hoisting, no edge atom and no SCC-based search. It is retained only so its proofs keep compiling, a few of its files are still imported for shared definitions, and nothing in this document describes it. The examples in `LTLLibTests/Examples/` that call `modelCheck` or `fullPipeline` belong to it.

The shared foundation is not part of that deprecation: `LTL/` (syntax, semantics, the fairness class and the fair normal form), `AbstractSpec/` (reachability, the emptiness contract, graph paths), `Data/` and `Tactic/` are what `TGBABased/` is built on.

## File organization

```
LTLLib/
  Data/
    Nat.lean
    List.lean
    FinitePred.lean
    FinSet.lean
  Tactic/
    Set.lean
  LTL/
    Syntax.lean
    Subformulas.lean
    Propositional.lean
    Semantics.lean
    FairClass.lean
    FairNormalForm.lean
    Fairness.lean
  AbstractSpec/
    Acceptance.lean
    EmptinessCheck.lean
    GraphPaths.lean
    Lasso.lean
  TGBA.lean
  TGBABased/
    AbstractSpec/
      Acceptance.lean
      EmptinessCheck.lean
      Lasso.lean
      LassoCheck.lean
      Pumping.lean
      RegionLatch.lean
      SCCTheory.lean
      StreettSCC.lean
      StreettSCCRegion.lean
      StreettPruneSpec.lean
    LTLtoTGBA/
      AbstractSpec/
        VWAA.lean
        VWAARuns.lean
        VWAAReduce.lean
        LTLToVWAA.lean
        SetTGBA.lean
        VWAAToTGBA.lean
        VWAAToTGBAInstance.lean
      Preprocess/
        Rules.lean
        Implication.lean
        Simplify.lean
      SubformulaTable.lean
      Label.lean
      VWAA.lean
      TGBAConstruct.lean
      TGBAConstructCorrect.lean
      TGBASimplify.lean
      GBAToTGBA.lean
      Reachability.lean
      Pipeline.lean
    SCC/
      GenericDFS.lean
      LiveStack.lean
      SCCEnumeration.lean
      WitnessExtraction.lean
      TarjanSCC.lean
      DijkstraSCC.lean
      GabowSCC.lean
      StreettPrune.lean
      StreettPruneFast.lean
      StreettPruneFastP.lean
    Degeneralization/
      TAcceptance.lean
      TBA.lean
      TBAProduct.lean
      DegeneralBridge.lean
    NestedDFS/
      NestedDFST.lean
      NestedDFSTCorrectness.lean
      NestedDFSTTermination.lean
    Fairness/
      FairProduct.lean
      FairCheck.lean
      StreettOptsProduct.lean
      StreettRegionProduct.lean
      Rehoist.lean
      DisjunctiveHoist.lean
      FairRouter.lean
      FairPipeline.lean
    LabelledSys.lean
    Product.lean
    DijkstraCheck.lean
    NDFSCheck.lean
    Satisfiability.lean
    ModelCheck.lean
  GBA.lean, BA.lean, DegeneralBridge.lean, LTLtoGBA/, NestedDFS/,
  Product.lean, ModelCheck.lean, Satisfiability.lean   -- deprecated, see Other routes
LTLLibTests/
  GuardAxioms.lean
  ModuleSystem.lean
  HistoricalTheorems.lean
  TGBABased/         -- the tests of everything described above
  Examples/          -- worked usage examples, referenced above
```

### Module descriptions

**`TGBA.lean`** — The `TGBA α` structure, labels and marks on transitions, `toSpec`, the lasso bridge, the `FiniteReach` witness of a well-formed automaton, and `consistentPart`, the automaton without the transitions no valuation takes.

**`TGBABased/LabelledSys.lean`** — A system whose letters are carried by steps: `LStep`, `LSys.Edge`, `LSys.letter`, `LSys.targets`, `LSys.totalize`, `LSys.unlabelled`, the `StepFn` form, `LSys.StateOnly`, and the bridges that read a labelled statement back as a state-labelled one.

**`TGBABased/Product.lean`** — On-the-fly product of a labelled system and a TGBA, with the compatibility gate checked per (system step, automaton transition) pair, plus run decomposition and the lasso witness.

**`TGBABased/Fairness/FairProduct.lean`** — The product extended with one generalized Büchi mark per propositional fairness conjunct, and `fgRegion`, the region a propositional `◇□` part carves out.

**`TGBABased/Fairness/FairCheck.lean`** — Model checking against one fair-normal-form disjunct `◇□l ∧ ⋀ⱼ □◇lⱼ`, the `□◇` parts as marks and the `◇□` part as the latch's region, plus the system-level fail-fast.

**`TGBABased/Fairness/FairRouter.lean`** — The split of the negated property into hoisted normal forms and kept conjuncts, and the crossing and prune routes over that split.

**`TGBABased/Fairness/Rehoist.lean`** — `rehoist`: `hoistFairness` after a `simplify` and `splitConj` pre-pass on the kept conjuncts.

**`TGBABased/Fairness/DisjunctiveHoist.lean`** — Splitting a kept `ψ ∨ γ` with a flattenable fairness `γ` into one run per choice of side, and `branches`, which enumerates the combinations.

**`TGBABased/Fairness/FairPipeline.lean`** — The routes built on the split-level searches, including the default `modelCheckUnderFairnessDisjunctiveHoist`, and `pruneApplicable`, which chooses between the prune and the crossing.

**`TGBABased/Fairness/StreettOptsProduct.lean`** — The product's fused expansion with per-edge option bits, so the prune's scan needs no callback into the spec's region predicates.

**`TGBABased/Fairness/StreettRegionProduct.lean`** — The bridge showing the product already implements the region-indexed Streett interface, the two operators being the region-restricted graph and the marks carried by those same steps.

**`TGBABased/ModelCheck.lean`** — One entry point per search mode, each restating the soundness and completeness of the search it names, with `modelCheckFair` the default and `modelCheckFairRoutedOfStep` the one a front end calls.

**`TGBABased/DijkstraCheck.lean`** — `modelCheckTGBA`, a `TEmptinessChecker` run on the product, and `modelCheckTGBAFair`, the same under propositional `□◇` assumptions carried as marks.

**`TGBABased/NDFSCheck.lean`** — `modelCheckTBA`, the degeneralized product searched by the transition-based nested DFS.

**`TGBABased/Satisfiability.lean`** — `tgbaPipeline`, the satisfiability decision procedure, walking the automaton alone.

**`TGBABased/AbstractSpec/Acceptance.lean`** — `TOASpec`, the edge-indexed proof-level automaton, and the pushdown from the state-indexed `OASpec`.

**`TGBABased/AbstractSpec/EmptinessCheck.lean`** — `TAcceptingCycle` and the algorithm-agnostic `TEmptinessChecker` contract, with acceptance as a mark set per transition.

**`TGBABased/AbstractSpec/Lasso.lean`** — Transition-based lasso theory: a stem of edges into a cycle of edges covering every mark witnesses non-emptiness.

**`TGBABased/AbstractSpec/LassoCheck.lean`** — Deciding `TAcceptingCycle` on a concrete stem and cycle, so a reported witness is checked rather than trusted.

**`TGBABased/AbstractSpec/Pumping.lean`** — From an accepting run to a lasso, by cutting the run into rounds that each contain every mark and pigeonholing the round boundaries.

**`TGBABased/AbstractSpec/SCCTheory.lean`** — `AcceptingSCC` for transition-based acceptance, the equivalence with `TAcceptingCycle`, and the `SCCEnumerationSound` contract an enumeration owes a prune-based check.

**`TGBABased/AbstractSpec/RegionLatch.lean`** — The region latch: a static `◇□l` restriction checked with one call to an unmodified checker, by doubling the graph with a `Bool` and forcing the accepting cycle into the region.

**`TGBABased/AbstractSpec/StreettSCC.lean`** — What it means for an SCC to satisfy a hoisted fairness assumption, Streett acceptance stated on a strongly connected set.

**`TGBABased/AbstractSpec/StreettSCCRegion.lean`** — The same when the hoisted regions restrict steps rather than states, which is what parallel realizations of one product pair require.

**`TGBABased/AbstractSpec/StreettPruneSpec.lean`** — The recursive check of [SLDP09] as a specification, with the Emerson-Lei argument that it misses nothing.

**`TGBABased/SCC/GenericDFS.lean`** — Algorithm 1 of [RDKP13], the DFS skeleton parameterized by PUSH, POP, GET_STATUS and UPDATE that every SCC-based check refines, and the witness extraction they share.

**`TGBABased/SCC/LiveStack.lean`** — The live and dead bookkeeping shared by the SCC-based checks, with the status laws proved once.

**`TGBABased/SCC/SCCEnumeration.lean`** — That the sets POP flushes are the maximal SCCs of the reachable subgraph, for every lowlink-based refinement.

**`TGBABased/SCC/WitnessExtraction.lean`** — Rebuilding an explicit accepting cycle from a valid candidate by chained BFS, since a refinement's own stack is no witness.

**`TGBABased/SCC/TarjanSCC.lean`** — Tarjan's check (Algorithm 2 of [RDKP13]), reporting only at a closing POP so the hint is always a flushed maximal SCC.

**`TGBABased/SCC/DijkstraSCC.lean`** — Dijkstra's check (Algorithm 3 of [RDKP13]) with the live stack and the open SCC candidates, mark sets as bitmasks, and the `dijkstraTChecker` instance.

**`TGBABased/SCC/GabowSCC.lean`** — Gabow's check (Algorithm 4 of [RDKP13]). Not implemented, the file records the algorithm.

**`TGBABased/SCC/StreettPrune.lean`** — The recursive fairness check run on the SCCs a Tarjan search closes, one search plus a prune instead of a crossing, with the regions restricting steps and the candidate's conjoined options as the termination measure.

**`TGBABased/SCC/StreettPruneFast.lean`** — The same scan reading the option bits the expansion carried, instead of asking the spec's region predicates once per edge and option.

**`TGBABased/SCC/StreettPruneFastP.lean`** — The fast prune with the live position returned by `getStatus`, so a back edge costs one hash probe instead of two. Bridged to the proved driver by `streettCheckP_eq`.

**`TGBABased/Degeneralization/TAcceptance.lean`** — Abstract degeneralization of edge-indexed automata, the `k` marks collapsing into one via a counter.

**`TGBABased/Degeneralization/TBA.lean`** — The single-mark `TBA` and `TGBA.degeneralize`, acceptance staying on edges throughout.

**`TGBABased/Degeneralization/TBAProduct.lean`** — The product of a system with an already degeneralized `TBA`.

**`TGBABased/Degeneralization/DegeneralBridge.lean`** — Computational `TGBA.degeneralize` against the abstract `TOASpec.degeneralize`.

**`TGBABased/NestedDFS/NestedDFST.lean`**, **`NestedDFSTCorrectness.lean`**, **`NestedDFSTTermination.lean`** — The transition-based nested DFS: the fuel-indexed version, its soundness and completeness, and the executable well-founded `nestedDFSTWF` bridged to it.

**`TGBABased/LTLtoTGBA/Pipeline.lean`** — `ltl3ba`, the end-to-end translator, and `ltl3baFormula`, which translates the negation of a surface formula.

**`TGBABased/LTLtoTGBA/Preprocess/Rules.lean`** — Building blocks for the rewrite rules, including the chain walks that let one bottom-up pass reach the rules' normal form.

**`TGBABased/LTLtoTGBA/Preprocess/Implication.lean`** — Syntactic implication between NNF formulas, [SB00] §3's relation with the `X`-rules of [BKŘS12] §4.

**`TGBABased/LTLtoTGBA/Preprocess/Simplify.lean`** — The bottom-up rewrite pass: constant folding, absorption, the pure-eventuality and purely-universal rules, alternating-conjunct lifting and the shape rules.

**`TGBABased/LTLtoTGBA/SubformulaTable.lean`** — Every subformula indexed by a `Nat` id, so each VWAA and TGBA state is a canonically hashable set of ids.

**`TGBABased/LTLtoTGBA/Label.lean`** — Transition labels in disjunctive normal form, with cube conjunction, the sharp difference, implication by literal inclusion, and the export to one transition per cube.

**`TGBABased/LTLtoTGBA/VWAA.lean`** — The concrete VWAA of an NNF formula, target sets as bitmasks, each node's transitions reduced before its parent combines them, restricted to the reachable ids.

**`TGBABased/LTLtoTGBA/TGBAConstruct.lean`** — VWAA to TGBA on the fly: the transition product, the `T_f` marks, on-the-fly dominance, OR-merging, and the worklist exploration.

**`TGBABased/LTLtoTGBA/TGBAConstructCorrect.lean`** — That the numbered output accepts exactly what its VWAA accepts, through the `SetTGBA` the construction denotes.

**`TGBABased/LTLtoTGBA/TGBASimplify.lean`** — A posteriori simplification: mark erasure, implied-transition removal, state merging, and removal of dead and unreachable states, repeated to a fixed point.

**`TGBABased/LTLtoTGBA/GBAToTGBA.lean`** — GBA to TGBA, pushing each state's acceptance-set membership and label onto its outgoing transitions.

**`TGBABased/LTLtoTGBA/Reachability.lean`** — Well-founded DFS reachability over `Nat`-keyed adjacency, with the lexicographic measure the restriction passes use.

**`TGBABased/LTLtoTGBA/AbstractSpec/VWAA.lean`** — Very weak alternating co-Büchi automata over arbitrary states, with very weakness as a rank into `Nat`.

**`TGBABased/LTLtoTGBA/AbstractSpec/VWAARuns.lean`** — Generic run theory: every branch is eventually constant without any finiteness assumption, so co-Büchi acceptance reduces to no branch settling in a final state.

**`TGBABased/LTLtoTGBA/AbstractSpec/VWAAReduce.lean`** — One letterwise simulation theorem carrying acceptance across any transition change that meets a local per-letter condition, with the published optimisations as instances.

**`TGBABased/LTLtoTGBA/AbstractSpec/LTLToVWAA.lean`** — The abstract LTL to VWAA construction, stated directly in `Prop` and `FinSet`.

**`TGBABased/LTLtoTGBA/AbstractSpec/SetTGBA.lean`** — TGBAs whose states are finite sets of VWAA states, with the `T_f` condition and the product-transition predicate.

**`TGBABased/LTLtoTGBA/AbstractSpec/VWAAToTGBA.lean`** — Generalised [GO01] Theorem 2: a TGBA built from a VWAA accepts exactly what the VWAA accepts, given soundness (S) and completeness (C) at every reachable state.

**`TGBABased/LTLtoTGBA/AbstractSpec/VWAAToTGBAInstance.lean`** — Three instances of that condition: the plain product with `T_f` marks, on-the-fly dominance, and OR-merging.

**`LTL/Syntax.lean`** — `Formula α` (user-facing syntax) and `NNF α` (internal negation-normal-form IR), `Formula.toNNF` between them, and `NNF.splitConj`, which splits at the top-level conjunctions.

**`LTL/Subformulas.lean`** — Subformula closure, the generic fold, and Until-subformula extraction.

**`LTL/Propositional.lean`** — `BoolFormula`, the propositional fragment fairness assumptions are checked in, evaluated at a single state, with the embedding into `NNF` both ways.

**`LTL/Semantics.lean`** — Denotational semantics for `NNF` and `Formula`, built on the Lentil TLA library, with `Formula.toNNF_correct`, `toNNF_correct_neg` and `NNF.satisfies_splitConj`.

**`LTL/FairClass.lean`** — The syntactic recognisers for the fairness class of [LSFZ16] Definition 1, which is the conjunction of Etessami and Holzmann's pure eventuality and purely universal classes, and the classifier that routes a conjunct to a mechanism.

**`LTL/FairNormalForm.lean`** — The fair normal form of [LSFZ16] Theorem 1: every fairness in `LTL(F, G)` as a disjunction of `◇□l ∧ ⋀ⱼ □◇lⱼ` with propositional parts, pushed inward by a well-founded recursion.

**`LTL/Fairness.lean`** — Unconditional, weak (justice) and strong (compassion) fairness as LTL formulas, combinators over lists of them, and `BoolFormula.weakFairMark`, the propositional weak fairness carried as a single mark.

**`AbstractSpec/EmptinessCheck.lean`** — `EmptinessResult` and its renaming, `AcceptingCycle`, `Reachable` and `FiniteReach`, and the state-indexed `EmptinessChecker` contract.

**`AbstractSpec/Acceptance.lean`** — `OASpec`, the state-indexed proof-level automaton with `k` acceptance sets, and the abstract degeneralization.

**`AbstractSpec/GraphPaths.lean`** — Generic `succs`-graph reachability, paths through unblocked intermediates, and the conversions to and from their list witnesses.

**`AbstractSpec/Lasso.lean`** — Abstract state-based lasso theory.

**`Data/Nat.lean`**, **`Data/List.lean`** — `Nat` and `List` lemmas core Lean does not provide.

**`Data/FinitePred.lean`** — Finiteness of a predicate, witnessed by a list covering it, which is what `FiniteReach` is.

**`Data/FinSet.lean`** — Finite sets as predicates enumerated by a list, mirroring the `Finset` API without Mathlib.

**`Tactic/Set.lean`** — The `set` tactic, vendored.
