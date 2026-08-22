# LTLLib

A standalone Lean 4 library for LTL (Linear Temporal Logic) model-checking infrastructure. Provides the full, formally verified pipeline from LTL formulas to Büchi automata, plus a verified nested-DFS emptiness/liveness check, composed end-to-end into two total, machine-checked decision procedures: model checking a system against an LTL property, and standalone LTL satisfiability.

The core LTL-to-GBA algorithm (Gerth et al.) is ported from the verified Isabelle/HOL formalization in [LTL_to_GBA](https://www.isa-afp.org/entries/LTL_to_GBA.html), part of the CAVA model-checking framework.

## Contents

- [Model checking](#model-checking)
  - [Top-level results](#top-level-results)
  - [Example usage](#example-usage)
  - [Termination: `FiniteReach`](#termination-finitereach)
  - [Correctness link in the chain](#correctness-link-in-the-chain)
  - [Algorithm pipeline](#algorithm-pipeline)
  - [Terminal states](#terminal-states)
- [Satisfiability](#satisfiability)
  - [Top-level results](#top-level-results-1)
  - [Example usage](#example-usage-1)
  - [Algorithm pipeline](#algorithm-pipeline-1)
  - [Correctness link in the chain](#correctness-link-in-the-chain-1)
- [Proof status](#proof-status)
- [File organization](#file-organization)
  - [Module descriptions](#module-descriptions)

## Model checking

Check an external system (given as initial states, a successor function, and a state-labeling function — no bundled record type, exactly what an on-the-fly checker needs) against an LTL property. `modelCheck` negates the property, builds its automaton, forms the product against the system *on-the-fly*, and runs a verified emptiness check.

### Top-level results

```lean
theorem modelCheck_empty_unsat (φ : Formula α) (sysInit) (sysSucc) (sysLabel)
    (sysFR : FiniteReach sysInit sysSucc) (checker : EmptinessChecker (SysState × BAState))
    {n : Nat} (h : modelCheck (S := S) φ sysInit sysSucc sysLabel sysFR checker = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ

theorem modelCheck_nonEmpty_sat (φ : Formula α) (sysInit) (sysSucc) (sysLabel)
    (sysFR : FiniteReach sysInit sysSucc) (checker : EmptinessChecker (SysState × BAState))
    {stem loop : List (SysState × BAState)}
    (h : modelCheck (S := S) φ sysInit sysSucc sysLabel sysFR checker = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ
```

Both are proven for *any* `checker : EmptinessChecker`, not fixed to the default nested-DFS one.

### Example usage

```lean
open LTLLib

inductive Light where | red | green | yellow
deriving BEq, Hashable, Repr, Inhabited, DecidableEq, Fintype

def lightSucc : Light → Array Light
  | .red => #[.green] | .green => #[.yellow] | .yellow => #[.red]

def lightLabel : Light → Std.HashSet String
  | .green => {"green"} | _ => ∅

def lightInit : List Light := [.red]
abbrev S := Std.HashSet (NNF String)
def lightFR : FiniteReach lightInit lightSucc := Set.toFinite _

def ψ : Formula String := .always (.eventually (.atom "green"))

#eval modelCheck (S := S) ψ lightInit lightSucc lightLabel lightFR
-- .empty _  (the light does turn green infinitely often)
```

The full runnable file — `LawfulBEq`/`LawfulHashable`/`ToString` instances included — is `LTLLib/Examples/ModelCheckExample.lean`; `Examples/ModelCheckCounterExample.lean` shows the `.nonEmpty` (violation) side.

### Termination: `FiniteReach`

`modelCheck` needs one proof from the caller: `sysFR : FiniteReach sysInit sysSucc`, that the system's reachable state set is finite. It's a bare `Prop` existence certificate (`{s | Reachable sysInit sysSucc s}.Finite`) — no `HashSet` witness, no data touched at runtime. `Product.finiteReach` lifts it to the product graph automatically, so the caller never reasons about the product directly:
- system finite by construction (a `Fintype` state type): `Set.toFinite _`
- otherwise: exhibit a concrete finite superset and `Set.Finite.subset`

### Correctness link in the chain

| Correctness link | Theorem | File |
|---|---|---|
| Negating `φ` preserves semantics | `Formula.toNNF_correct_neg` | `LTL/Semantics.lean` |
| `¬φ`'s GBA accepts exactly `¬φ`'s models | `constructGBA_correct_weak` | `LTLtoGBA/GraphComplete.lean` |
| Degeneralized BA preserves language | `degeneralize_accepts_any` | `DegeneralBridge.lean` |
| Product run ↔ system run + BA-language witness | `Product.gsp_correct1` / `gsp_correct2` | `Product.lean` |
| Product accepting cycle → concrete accepting run | `AcceptingCycle.toValidLassoProduct` | `Product.lean` |
| Accepting run ⟹ accepting cycle exists (pumping) | `exists_acceptingCycle_of_run` | `NestedDFS/NestedDFSTermination.lean` |
| Emptiness check sound + complete vs. `AcceptingCycle` | `EmptinessChecker.nonEmpty_valid` / `.empty_no_cycle` | `AbstractSpec/EmptinessCheck.lean` |
| Everything composed into system-level model checking | `modelCheck_empty_unsat` / `modelCheck_nonEmpty_sat` | `ModelCheck.lean` |

### Algorithm pipeline

```
LTL property φ  (Formula α)
    │
    ▼  negate + toNNF                 ✓ proved correct (Formula.toNNF_correct_neg)
¬φ (in NNF)
    │
    ▼  createGraph → constructGBA → GBA.degeneralize   ✓ unconditional, same stages as satisfiability
BA for ¬φ
    │
    ▼  Product.getSuccessors / initialStates / isAccepting  ✓ product run ↔ system run (gsp_correct1/2)
Product graph  (SysState × BAState), built on-the-fly
    │
    ▼  checker.check   (nestedDFSWF by default)          ✓ sound + complete vs. AcceptingCycle
EmptinessResult (SysState × BAState)
    .empty n            → sys ⊨ φ
    .nonEmpty stem loop → a real run of sys violating φ, witnessed by
                           (system state, ¬φ-automaton state) pairs
```

If a different emptiness-check algorithm suits your system better than nested DFS, `modelCheck` takes an optional `checker : EmptinessChecker (SysState × BAState) := nestedDFSChecker` parameter — any instance works, with no other change to the call.

### Terminal states

LTL/Büchi semantics are defined over *infinite* words, so every state needs at least one successor; a terminal state is read as "the system stays there forever". A `sysSucc` that returns `#[]` for some reachable state breaks that silently — `modelCheck` just under-reports, missing any counterexample whose violation only manifests by the system stalling there.

`Product.getSuccessors` fixes this automatically via `Product.totalizeSucc`: any state with no outgoing edges gets a self-loop before the product is ever built. Systems that are already total pay nothing extra — `totalizeSucc` is a no-op on them. See `LTLLib/Examples/ModelCheckTerminalStateExample.lean` for a worked failure/fix example.

## Satisfiability

Decide whether an LTL formula is satisfiable, with a witness trace if so — no external system needed.

### Top-level results

```lean
theorem fullPipeline_empty_unsat (φ : NNF α) {n : Nat}
    (h : fullPipeline φ = .empty n) :
    ∀ ξ : OmegaWord α, ¬ NNF.satisfies ξ φ

theorem fullPipeline_nonEmpty_sat (φ : NNF α) {stem loop : List BAState}
    (h : fullPipeline φ = .nonEmpty stem loop) :
    ∃ ξ : OmegaWord α, NNF.satisfies ξ φ
```

`fullPipeline` is a genuine, computable `def`, defined for every formula (`createGraph_term` guarantees it) — no external setup needed.

### Example usage

```lean
open LTLLib

abbrev Prop' := String

/-- □◇a ∧ □◇¬a: a holds infinitely often, and fails infinitely often. -/
def φ : Formula Prop' :=
  .and (.always (.eventually (.atom "a"))) (.always (.eventually (.not (.atom "a"))))

#eval report φ
-- satisfiable
-- stem: {} → {} → {a} → {} → {a} → {a} → {}
-- loop: {} → {} → {a} → {} → {a} → {a} ⟲ (repeats forever)
```

`report` (`Examples/SatisfiabilityExample.lean`) calls `fullPipeline` for the verdict and, for `.nonEmpty`, renders the witness lasso's atoms at each step by looking them up in the same automaton's own labeling — see the file for `report`/`showRun` and the `.empty` (unsatisfiable) case.

### Algorithm pipeline

```
LTL formula φ  (Formula α, user-facing syntax)
    │
    ▼  toNNF                     ✓ proved correct (Formula.toNNF_correct)
φ (in NNF)     (NNF α, internal IR — the type every stage below consumes)
    │
    ▼  createGraph                ✓ totality proved (createGraph_term); ExpandSpec proved (createGraph_spec)
Node graph (ExpandState)
    │
    ▼  constructGBA               ✓ accepts ξ ↔ ξ ⊨ φ, unconditional (constructGBA_correct_weak)
Generalized Büchi Automaton (GBA)
    │
    ▼  GBA.degeneralize            ✓ accepts ξ ↔ GBA accepts ξ, unconditional, any k (degeneralize_accepts_any)
Standard Büchi Automaton (BA)
    │
    ▼  nestedDFSWF                 ✓ total, sound + complete (nestedDFSWF_empty_no_cycle / _nonEmpty_valid)
EmptinessResult: empty exploredStates | nonEmpty stem loop
```

### Correctness link in the chain

| Correctness link | Theorem | File |
|---|---|---|
| NNF compilation preserves semantics | `Formula.toNNF_correct` | `LTL/Semantics.lean` |
| `expand`/`createGraph` terminate on every input | `createGraph_term` | `LTLtoGBA/ExpandTermination.lean` |
| Graph expansion satisfies its structural invariants | `createGraph_spec` | `LTLtoGBA/Invariants.lean` |
| Expansion graph is exhaustive (drives completeness) | `createGraph_weakGraphComplete` | `LTLtoGBA/GraphComplete.lean` |
| Computational GBA accepts exactly the models of `φ` | `constructGBA_correct_weak` | `LTLtoGBA/GraphComplete.lean` |
| `constructGBA`'s output is well-formed | `constructGBA_wellFormed` | `LTLtoGBA/Bridge.lean` |
| GBA degeneralization preserves language, any `numAcceptSets` | `degeneralize_accepts_any` | `DegeneralBridge.lean` |
| `innerDFS`/`outerDFSLoop`/`nestedDFS` are total, well-founded | `nestedDFSWF` | `NestedDFS/NestedDFSTermination.lean` |
| `nestedDFSWF` soundness (`.nonEmpty` → genuine accepting cycle) | `nestedDFSWF_nonEmpty_valid` | `NestedDFS/NestedDFSTermination.lean` |
| `nestedDFSWF` completeness (`.empty` → no accepting cycle) | `nestedDFSWF_empty_no_cycle` | `NestedDFS/NestedDFSTermination.lean` |
| Accepting run ⟹ accepting cycle exists (pumping lemma) | `exists_acceptingCycle_of_run` | `NestedDFS/NestedDFSTermination.lean` |
| Everything composed into one satisfiability decision procedure | `fullPipeline_empty_unsat` / `fullPipeline_nonEmpty_sat` | `Satisfiability.lean` |

## Proof status

Every top-level theorem is fully proven: 0 `sorry`, 0 axioms, no admitted hypotheses, no side conditions beyond the formula (or system) itself. Both decision procedures are genuine, computable `def`s — not gated behind an axiom or an unfinished proof.

- `fullPipeline_empty_unsat` / `fullPipeline_nonEmpty_sat` — satisfiability (`Satisfiability.lean`)
- `modelCheck_empty_unsat` / `modelCheck_nonEmpty_sat` — model checking (`ModelCheck.lean`)

## File organization

```
LTLLib/
  LTL.lean
  LTL/
    Syntax.lean
    Semantics.lean
    Subformulas.lean
    Fairness.lean
  GBA.lean
  BA.lean
  AbstractSpec/
    Acceptance.lean
    EmptinessCheck.lean
    Lasso.lean
  DegeneralBridge.lean
  LTLtoGBA/
    FSet.lean
    Node.lean
    Expand.lean
    ExpandTermination.lean
    Construction.lean
    Invariants.lean
    Soundness.lean
    Completeness.lean
    Correctness.lean
    Bridge.lean
    GraphComplete.lean
  NestedDFS/
    NestedDFSCorrectness.lean
    NestedDFSTermination.lean
  Satisfiability.lean
  Product.lean
  ModelCheck.lean
  Examples/          -- worked usage examples, referenced above
```

### Module descriptions

**`LTL.lean`** — Re-exports `LTL/Syntax.lean` and `LTL/Semantics.lean`.

**`LTL/Syntax.lean`** — `Formula α` (user-facing syntax) and `NNF α` (internal negation-normal-form IR); `Formula.toNNF` compiles between them.

**`LTL/Subformulas.lean`** — Subformula closure and Until-subformula extraction; used for acceptance-set construction and `expand`'s termination measure.

**`LTL/Semantics.lean`** — Denotational semantics for `NNF`/`Formula`, built on the Lentil TLA library; `Formula.toNNF_correct`.

**`LTL/Fairness.lean`** — Weak/strong fairness (justice/compassion) encoded as LTL formulas.

**`GBA.lean`** — The `GBA α` structure and `GBA.WellFormed`.

**`BA.lean`** — The `BA α` structure, `GBA.degeneralize`, `BA.WellFormed`, and the `AcceptingCycle → ValidLasso` bridge for `BA.toSpec`.

**`AbstractSpec/Acceptance.lean`** — `OASpec` (unified GBA/BA proof-level spec), `OASpec.degeneralize`, `canonicalLabel`.

**`AbstractSpec/EmptinessCheck.lean`** — `EmptinessResult`, `AcceptingCycle`, `FiniteReach`, and the algorithm-agnostic `EmptinessChecker` contract.

**`AbstractSpec/Lasso.lean`** — `ValidLasso`/`lassoRun`: a stem+cycle witness constructs a genuine accepting run.

**`DegeneralBridge.lean`** — Bridges computational `GBA.degeneralize` to the abstract `OASpec.degeneralize`, for any number of acceptance sets.

**`LTLtoGBA/FSet.lean`** — Abstract finite-set typeclass, with `Std.HashSet`/`Std.TreeSet` instances.

**`LTLtoGBA/Node.lean`** — `GBANode`, the record used during graph construction.

**`LTLtoGBA/Expand.lean`** — The Gerth et al. `expand`/`createGraph` algorithm.

**`LTLtoGBA/ExpandTermination.lean`** — Totality of `expand`/`createGraph`.

**`LTLtoGBA/Construction.lean`** — Assembles a `GBA` from the expanded node graph.

**`LTLtoGBA/Invariants.lean`** — Structural invariants of the expand algorithm (`ExpandSpec`, `createGraph_spec`).

**`LTLtoGBA/Soundness.lean`** — GBA accepts `ξ` ⟹ `ξ ⊨ φ`.

**`LTLtoGBA/Completeness.lean`** — `ξ ⊨ φ` ⟹ GBA accepts `ξ`, given `GraphComplete`.

**`LTLtoGBA/Correctness.lean`** — Combines soundness + completeness into one iff, still under `GraphComplete`.

**`LTLtoGBA/Bridge.lean`** — Computational GBA ↔ abstract automaton; `constructGBA_wellFormed`.

**`LTLtoGBA/GraphComplete.lean`** — Proves `GraphComplete` from `createGraph` itself, giving the unconditional `constructGBA_correct_weak`.

**`NestedDFS/NestedDFSCorrectness.lean`** — Fuel-indexed nested DFS, proven sound and complete against `AcceptingCycle`.

**`NestedDFS/NestedDFSTermination.lean`** — The executable well-founded `nestedDFSWF`, bridged to the fuel version above; `nestedDFSChecker`; the pumping lemma `exists_acceptingCycle_of_run`.

**`Satisfiability.lean`** — `fullPipeline`, plus `fullPipeline_empty_unsat`/`fullPipeline_nonEmpty_sat`.

**`Product.lean`** — On-the-fly product between an external system and a `BA`, including terminal-state totalization and the `AcceptingCycle → ValidLasso` bridge for `Product.toSpec`.

**`ModelCheck.lean`** — `modelCheck`, plus `modelCheck_empty_unsat`/`modelCheck_nonEmpty_sat`.
