module

/-
  On-the-fly product of an external system and a `TGBA`. Both sides are transition-based: a `TGBA.Transition`
  carries its own label, and a system step carries its own letter (`LabelledSys.lean`), so the
  compatibility gate is checked per (system step, automaton transition) pair rather than once per source state.

  The product's state set is `SysState × Nat` either way — an edge atom such as `taken(a)` costs no states.
  See `EdgeLabels.md` for the design.

  Defines:
  - `initialStates`, `getSuccessors`, `realizations`, `edgeMarks`: the product graph and its marks
  - `toSpec`: the product as an abstract `TOASpec`
  - `edgeWitness`: a concrete product edge for every product step and every mark on it

  Proves:
  - `run_decompose`, `run_combine`: a product run splits into a TGBA edge-run and a system run, and back
  - `gsp_correct1`, `gsp_correct2`: the two directions of the product's own correctness
  - `exists_TAcceptingCycle_of_acceptingRun`: an accepting product run yields a lasso witness
  - `exists_run_of_TAcceptingCycle`: a lasso witness yields a system run, carrying a per-cycle predicate onto the run's
    tail and a per-state one onto infinitely many positions

  Sections:
  - Product construction
  - Realizations of a product step
  - Proof-level bridge
  - Product run decomposition + acceptance transfer
  - Edge witness
  - From an accepting run to a lasso
  - Lasso witness
-/
public import LTLLib.AbstractSpec.Reachability
public import LTLLib.TGBA
public import LTLLib.AbstractSpec.Pumping
public import LTLLib.LabelledSys

public section

namespace LTLLib

namespace TGBAProduct

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]

/-! ## Product construction -/

@[expose] def initialStates (tgba : TGBA α) (sysInit : List SysState) :
    List (SysState × Nat) :=
  sysInit.flatMap fun s => tgba.initialStates.toList.map fun q => (s, q)

/-- Does `valuation` satisfy `t`'s own positive/negative propositional constraint? -/
@[expose] def transCompatible (t : TGBA.Transition α) (valuation : Std.HashSet α) : Bool :=
  t.positiveProps.all valuation.contains && !t.negativeProps.any valuation.contains

/-- The product successors a given set of system steps out of `s` generates. Both the whole product and the
restriction an `FG` part carves out are this, differing only in which steps they are handed. -/
@[expose] def succsFrom (tgba : TGBA α) (q : Nat) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) : Array (SysState × Nat) :=
  let ts := tgba.getSuccessors q
  if steps.all (·.1.isEmpty) then
    -- PERF, and the reason this is not just `flatMap`. Every step reads the *same* letter here, namely
    -- `base`, so transition compatibility is a property of the transition alone and is tested once per
    -- transition instead of once per (step, transition). A state-labelled product is always in this
    -- branch, so it pays what it paid before edge atoms existed: `transCompatible` walks two `HashSet`s,
    -- and the outer loop had to move inside the step loop when the letter became a property of the step
    -- (`EdgeLabels.md` §12.10). The guard is one `isEmpty` per step and the branches agree.
    let ok := ts.filter fun t => transCompatible t base
    steps.flatMap fun st => ok.map fun t => (st.2, t.target)
  else
    steps.flatMap fun st =>
      let lbl := LSys.letter base st.1
      ts.filterMap fun t =>
        if transCompatible t lbl then some (st.2, t.target) else none

/-- From `(s, q)`, every system step out of `s` paired with every `q`-transition compatible with the letter
*that step* reads. The system step is chosen first because it is what fixes the letter; in a state-labelled
product the two loops are nested the other way round. -/
@[expose] def getSuccessors (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) :
    (SysState × Nat) → Array (SysState × Nat) :=
  fun (s, q) => succsFrom tgba q (sysLabel s) (LSys.totalize sysSucc s)

/-! ## Realizations of a product step

A product step `(s, q) → (s', q')` is realized by a pair: a system step `s → s'` and a `q → q'` transition
compatible with that step's letter. Parallel system steps make several pairs realize the same product step,
which is why the marks are collected over all of them and why `edgeWitness` has to name one. -/

/-- Every realization of a product step out of a source whose letter and steps are already in hand. -/
@[expose] def realizationsFrom [BEq SysState] [Hashable SysState] (tgba : TGBA α) (q : Nat) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) (p' : SysState × Nat) :
    Array (LStep α SysState × TGBA.Transition α) :=
  (steps.filter fun st => st.2 == p'.1).flatMap fun st =>
    -- PERF: the step's letter is loop-invariant in the transition scan, but `LSys.letter` *allocates*
    -- (`base.union L` whenever the step carries atoms of its own), so leaving it inside cost one
    -- `HashSet` per (step, transition) rather than per step. `EdgeLabels.md` §12.10 (b).
    let lbl := LSys.letter base st.1
    ((tgba.getSuccessors q).filter fun t =>
      t.target == p'.2 && transCompatible t lbl).map (st, ·)

/-- Every (system step, automaton transition) pair realizing the product step `p → p'`. -/
@[expose] def realizations [BEq SysState] [Hashable SysState] (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (p p' : SysState × Nat) :
    Array (LStep α SysState × TGBA.Transition α) :=
  realizationsFrom tgba p.2 (sysLabel p.1) (LSys.totalize sysSucc p.1) p'

theorem mem_realizationsFrom_iff [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (tgba : TGBA α)
    (q : Nat) (base : Std.HashSet α) (steps : Array (LStep α SysState)) (p' : SysState × Nat)
    (r : LStep α SysState × TGBA.Transition α) :
    r ∈ realizationsFrom tgba q base steps p' ↔
      (r.1 ∈ steps ∧ r.1.2 = p'.1) ∧
      (r.2 ∈ tgba.getSuccessors q ∧ r.2.target = p'.2 ∧
        transCompatible r.2 (LSys.letter base r.1.1) = true) := by
  simp only [realizationsFrom, Array.mem_flatMap, Array.mem_filter, Array.mem_map, Bool.and_eq_true,
    beq_iff_eq]
  constructor
  · rintro ⟨st, ⟨hst, hst2⟩, t, ⟨ht, htgt, hc⟩, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
    exact ⟨⟨hst, hst2⟩, ht, htgt, hc⟩
  · rintro ⟨⟨hst, hst2⟩, ht, htgt, hc⟩
    exact ⟨r.1, ⟨hst, hst2⟩, r.2, ⟨ht, htgt, hc⟩, rfl⟩

theorem mem_realizations_iff [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (p p' : SysState × Nat) (r : LStep α SysState × TGBA.Transition α) :
    r ∈ realizations tgba sysSucc sysLabel p p' ↔
      (r.1 ∈ LSys.totalize sysSucc p.1 ∧ r.1.2 = p'.1) ∧
      (r.2 ∈ tgba.getSuccessors p.2 ∧ r.2.target = p'.2 ∧
        transCompatible r.2 (LSys.letter (sysLabel p.1) r.1.1) = true) := by
  simp only [realizations, realizationsFrom, Array.mem_flatMap, Array.mem_filter, Array.mem_map,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨st, ⟨hst, hst2⟩, t, ⟨ht, htgt, hc⟩, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
    exact ⟨⟨hst, hst2⟩, ht, htgt, hc⟩
  · rintro ⟨⟨hst, hst2⟩, ht, htgt, hc⟩
    exact ⟨r.1, ⟨hst, hst2⟩, r.2, ⟨ht, htgt, hc⟩, rfl⟩

/-- The marks of every `q`-transition compatible with `base`, grouped by target.

Keyed by `t.target : Nat`, so building it costs no `SysState` comparisons. It is only meaningful when
every step out of the source reads `base` — i.e. no step carries a letter of its own — because only then
is transition compatibility independent of which step realizes an edge. `edgeMarksFrom` builds it exactly
under that guard. -/
def marksByTarget (tgba : TGBA α) (q : Nat) (base : Std.HashSet α) :
    Std.HashMap Nat (Std.HashSet Nat) :=
  (tgba.getSuccessors q).foldl (init := ∅) fun m t =>
    if transCompatible t base then
      m.insert t.target ((m.getD t.target (Std.HashSet.emptyWithCapacity 0)).union t.acceptMarks)
    else m

/-- `edgeMarksFrom` with the source's per-state work already in hand, in the `…From` style of §12.8.

`byTgt?` is `some table` exactly when every step reads `base`, and carries the grouped marks; `none`
selects the general path. Making the *decision* data rather than an `if` above `p'` is the §9 lesson: an
`if` there would be re-evaluated on every call, since Lean eta-expands to full arity.

PERF: in the `some` branch an edge's marks are a lookup on a `Nat` key. The general path had to ask
"which steps land on `p'.1`?" per successor, and that is a **deep `SysState` comparison** — `EdgeLabels.md`
§13.3 profiled it at 24.5 % of the Dijkstra route. Here the only state work left is the short-circuiting
`any` that decides whether the edge exists at all. -/
@[expose] def edgeMarksFromShared [BEq SysState] [Hashable SysState] (tgba : TGBA α) (q : Nat) (base : Std.HashSet α)
    (steps : Array (LStep α SysState))
    (byTgt? : Option (Std.HashMap Nat (Std.HashSet Nat) × Std.HashSet SysState))
    (p' : SysState × Nat) : Std.HashSet Nat :=
  match byTgt? with
  | some (byTgt, tgts) =>
    if tgts.contains p'.1 then
      byTgt.getD p'.2 (Std.HashSet.emptyWithCapacity 0)
    else Std.HashSet.emptyWithCapacity 0
  | none =>
    (realizationsFrom tgba q base steps p').foldl
      (init := Std.HashSet.emptyWithCapacity 0) fun acc r => acc.union r.2.acceptMarks

/-- The targets of a source's steps, as a set. One hash per step to build, one per lookup, replacing the
`steps.any (· .2 == p'.1)` scan that cost a **deep `SysState` comparison** per step per successor —
`EdgeLabels.md` §13.3 profiled that at 24.5 % of the Dijkstra route. -/
def stepTargets [BEq SysState] [Hashable SysState]
    (steps : Array (LStep α SysState)) : Std.HashSet SysState :=
  steps.foldl (init := ∅) fun acc st => acc.insert st.2

/-- The grouped table and the source's step targets, or `none` when some step carries its own letter. -/
@[expose] def marksTable [BEq SysState] [Hashable SysState] (tgba : TGBA α) (q : Nat) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) :
    Option (Std.HashMap Nat (Std.HashSet Nat) × Std.HashSet SysState) :=
  if steps.all (·.1.isEmpty) then some (marksByTarget tgba q base, stepTargets steps) else none

/-- The grouped table alone, which is all a *generating* expansion needs. A successor `succsFrom` produced
has a step target by construction, so the membership half of `marksTable` — `stepTargets`, one hash per
step to build and one hash plus one deep state equality per successor to consult — answers a question
whose answer is known. On a model whose states are cheap to produce and expensive to compare that test
was 14 % of the default route and three quarters of a crossing row (`EdgeLabels.md` §13.23). -/
@[expose] def marksTableGen (tgba : TGBA α) (q : Nat) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) : Option (Std.HashMap Nat (Std.HashSet Nat)) :=
  if steps.all (·.1.isEmpty) then some (marksByTarget tgba q base) else none

/-- `edgeMarksFromShared` for a successor the source's own steps generated: the `some` branch is the
`Nat`-keyed lookup and nothing else. It agrees with `edgeMarksFrom` on every such successor
(`genMarksFromShared_eq`), which is what the fused expansions' coherence rests on; the spec form keeps
its guard, since it has to be total on an arbitrary `p'`. -/
@[expose] def genMarksFromShared [BEq SysState] [Hashable SysState] (tgba : TGBA α) (q : Nat) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) (byTgt? : Option (Std.HashMap Nat (Std.HashSet Nat)))
    (p' : SysState × Nat) : Std.HashSet Nat :=
  match byTgt? with
  | some byTgt => byTgt.getD p'.2 (Std.HashSet.emptyWithCapacity 0)
  | none =>
    (realizationsFrom tgba q base steps p').foldl
      (init := Std.HashSet.emptyWithCapacity 0) fun acc r => acc.union r.2.acceptMarks

/-- Marks on a product edge `(s, q) → (s', q')`: the union over every realization of the step. Unioning
across realizations over-approximates a single step; it is sound because TGBA acceptance asks for each mark
infinitely often and `edgeWitness.markEdge` names a realization carrying the mark, so pumping the cycle
realizes them one at a time. A *region* may not be over-approximated this way — see `EdgeLabels.md` §6.3. -/
@[expose] def edgeMarksFrom [BEq SysState] [Hashable SysState] (tgba : TGBA α) (q : Nat) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) (p' : SysState × Nat) : Std.HashSet Nat :=
  edgeMarksFromShared tgba q base steps (marksTable tgba q base steps) p'

-- PERF: `edgeMarks` is the *spec* form, one edge at a time; the search does not call it. `expand` above is
-- what the search walks with, fusing this and `getSuccessors` so a caller's per-source cost is paid once per
-- product state. Do not try to make this one cache its own per-source work by returning a closure: Lean
-- eta-expands a function-returning definition into its full arity, so `edgeMarks tgba sysSucc sysLabel p` is
-- a partial application whose body never runs. That was measured. `expand` returns a pair of arrays, which
-- is not a function and so is saturated at `p`. See `EdgeLabels.md` §9.
@[expose] def edgeMarks [BEq SysState] [Hashable SysState] (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (p : SysState × Nat) :
    (SysState × Nat) → Std.HashSet Nat :=
  let base := sysLabel p.1
  let steps := LSys.totalize sysSucc p.1
  fun p' => edgeMarksFrom tgba p.2 base steps p'

/-- Successors of a product state together with the marks of each, from one pass over the source. The
result type is a *pair of arrays*, not a function, so the compiler cannot eta-expand it: the body runs once
per call and `sysLabel`/`sysSucc` are entered once per product state. -/
@[expose] def expand [BEq SysState] [Hashable SysState] (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (p : SysState × Nat) :
    Array (SysState × Nat) × Array (Std.HashSet Nat) × Array Nat :=
  let base := sysLabel p.1
  let steps := LSys.totalize sysSucc p.1
  let byTgt? := marksTableGen tgba p.2 base steps
  let out := succsFrom tgba p.2 base steps
  -- option bits are empty here: this is the *unrestricted* expansion, used by the routes with no
  -- hoisted conjuncts. `expandWithOpts` below is what the Streett scan gets. §13.17
  -- The marks come from `genMarksFromShared`, not `edgeMarksFromShared`: every `p'` in `out` was generated
  -- from a step, so the spec form's membership guard is not consulted. Coherence is `expand_coherent`,
  -- below `contains_stepTargets`, which is the lemma it needs. §13.23
  (out, out.map fun p' => genMarksFromShared tgba p.2 base steps byTgt? p', #[])

/-! ## The restriction an `FG` part carves out

`◇□ψ` confines the accepting cycle to the steps whose *letter* satisfies ψ. That is a subgraph, not a set of
states: two parallel steps out of the same state can differ on ψ once a letter belongs to the step. The
latch (`AbstractSpec/RegionLatch.lean`) therefore takes this graph, and `keptSuccs_sub` is what lets it
project back. See `EdgeLabels.md` §6. -/

/-- The steps out of `s` whose letter satisfies `keep`. The totalizing self-loop is filtered too: a
deadlocked state's stutter reads the state's own atoms, so it survives exactly when `keep` holds there. A
`keep` that ignores the step's own atoms keeps all of a state's steps or none, which is the state region the
latch used to take. -/
@[expose] def keptStepsFrom (base : Std.HashSet α) (steps : Array (LStep α SysState))
    (keep : Std.HashSet α → Bool) : Array (LStep α SysState) :=
  steps.filter fun st => keep (LSys.letter base st.1)

/-- The steps out of `s` whose letter satisfies `keep`.

PERF: every caller that already holds the source's label and steps uses `keptStepsFrom` instead, so that
`sysLabel` and `sysSucc` are entered once per *source* rather than once per use. Spelling this one out as
`succsFrom … (sysLabel p.1) (keptSteps … p.1)` — which is what it was — enters `sysLabel` twice, once for
the letter base and once inside `keptSteps`. On the Veil side each entry is a `tr` call. -/
@[expose] def keptSteps (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) (s : SysState) :
    Array (LStep α SysState) :=
  keptStepsFrom (sysLabel s) (LSys.totalize sysSucc s) keep

theorem mem_keptSteps {sysSucc : SysState → Array (LStep α SysState)}
    {sysLabel : SysState → Std.HashSet α} {keep : Std.HashSet α → Bool} {s : SysState}
    {st : LStep α SysState} :
    st ∈ keptSteps sysSucc sysLabel keep s ↔
      st ∈ LSys.totalize sysSucc s ∧ keep (LSys.letter (sysLabel s) st.1) = true := by
  simp [keptSteps, keptStepsFrom, Array.mem_filter]

/-- The restricted product from a source whose label and steps are already in hand. The fairness
expansions build one of these per conjunct, so sharing `base` and `steps` across them is what keeps those
at one `sysLabel`/`sysSucc` per product state rather than one per conjunct. -/
@[expose] def keptSuccsFrom (tgba : TGBA α) (q : Nat) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) (keep : Std.HashSet α → Bool) : Array (SysState × Nat) :=
  succsFrom tgba q base (keptStepsFrom base steps keep)

/-- The product restricted to those steps. -/
@[expose] def keptSuccs (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) :
    (SysState × Nat) → Array (SysState × Nat) :=
  fun p => keptSuccsFrom tgba p.2 (sysLabel p.1) (LSys.totalize sysSucc p.1) keep

/-- `keptSuccs` in its pre-sharing spelling. The definition now threads the source's label and steps so
that each is entered once; this restores the old shape for the unfolding proofs below. -/
theorem keptSuccs_eq (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) (p : SysState × Nat) :
    keptSuccs tgba sysSucc sysLabel keep p
      = succsFrom tgba p.2 (sysLabel p.1) (keptSteps sysSucc sysLabel keep p.1) := rfl

/-- Marks of the restricted product: only the restricted steps may realize them. -/
@[expose] def keptEdgeMarks [BEq SysState] [Hashable SysState] (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) :
    (SysState × Nat) → (SysState × Nat) → Std.HashSet Nat :=
  -- left pointwise on purpose: a `let` before `fun p'` would be re-entered per call anyway (§9's
  -- eta-expansion) and buys nothing. The *fused* `keptExpand` is what the search actually calls, and
  -- that one shares its source work. Both go through `edgeMarksFrom`, which is what keeps
  -- `keptExpand_coherent` a `rfl` now that the grouped fast path is on this route too (§13.10).
  fun p p' => edgeMarksFrom tgba p.2 (sysLabel p.1) (keptSteps sysSucc sysLabel keep p.1) p'

/-- The fused expansion for the restricted product. -/
@[expose] def keptExpand [BEq SysState] [Hashable SysState] (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) (p : SysState × Nat) :
    Array (SysState × Nat) × Array (Std.HashSet Nat) × Array Nat :=
  let base := sysLabel p.1
  let kept := keptStepsFrom base (LSys.totalize sysSucc p.1) keep
  let byTgt? := marksTable tgba p.2 base kept
  let out := succsFrom tgba p.2 base kept
  (out, out.map fun p' => edgeMarksFromShared tgba p.2 base kept byTgt? p', #[])

theorem keptExpand_coherent [BEq SysState] [Hashable SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) :
    ExpandCoherent (keptSuccs tgba sysSucc sysLabel keep) (keptEdgeMarks tgba sysSucc sysLabel keep)
      (keptExpand tgba sysSucc sysLabel keep) := fun _ => rfl

/-! ## The same product, from one system callback

Each definition above applies `sysLabel s` and `sysSucc s` at the same `s`, so a two-callback system makes
its implementer compute `s` twice. These take `LSys.StepFn` — steps and atoms together — and are otherwise
the same expressions, which is why every bridge is `rfl` up to unfolding the pattern match on the product
state. Nothing above changes; the two-callback forms remain the ones every theorem is stated over, and a
fused caller reaches them through the bridges. `EdgeLabels.md` §15. -/

section OfStep

variable (tgba : TGBA α) (sysStep : LSys.StepFn α SysState)

@[expose] def getSuccessorsOfStep : (SysState × Nat) → Array (SysState × Nat) :=
  fun p => let r := sysStep p.1; succsFrom tgba p.2 r.2 (LSys.totalizeAt r.1 p.1)

@[expose] def keptStepsOfStep (keep : Std.HashSet α → Bool) (s : SysState) : Array (LStep α SysState) :=
  let r := sysStep s; keptStepsFrom r.2 (LSys.totalizeAt r.1 s) keep

@[expose] def keptSuccsOfStep (keep : Std.HashSet α → Bool) :
    (SysState × Nat) → Array (SysState × Nat) :=
  fun p => let r := sysStep p.1; keptSuccsFrom tgba p.2 r.2 (LSys.totalizeAt r.1 p.1) keep

variable [BEq SysState] [Hashable SysState]

@[expose] def edgeMarksOfStep (p : SysState × Nat) : (SysState × Nat) → Std.HashSet Nat :=
  let r := sysStep p.1
  fun p' => edgeMarksFrom tgba p.2 r.2 (LSys.totalizeAt r.1 p.1) p'

@[expose] def expandOfStep (p : SysState × Nat) :
    Array (SysState × Nat) × Array (Std.HashSet Nat) × Array Nat :=
  let r := sysStep p.1
  let base := r.2
  let steps := LSys.totalizeAt r.1 p.1
  let byTgt? := marksTableGen tgba p.2 base steps
  let out := succsFrom tgba p.2 base steps
  (out, out.map fun p' => genMarksFromShared tgba p.2 base steps byTgt? p', #[])

@[expose] def keptEdgeMarksOfStep (keep : Std.HashSet α → Bool) :
    (SysState × Nat) → (SysState × Nat) → Std.HashSet Nat :=
  fun p p' => edgeMarksFrom tgba p.2 (sysStep p.1).2 (keptStepsOfStep sysStep keep p.1) p'

@[expose] def keptExpandOfStep (keep : Std.HashSet α → Bool) (p : SysState × Nat) :
    Array (SysState × Nat) × Array (Std.HashSet Nat) × Array Nat :=
  let r := sysStep p.1
  let base := r.2
  let kept := keptStepsFrom base (LSys.totalizeAt r.1 p.1) keep
  let byTgt? := marksTable tgba p.2 base kept
  let out := succsFrom tgba p.2 base kept
  (out, out.map fun p' => edgeMarksFromShared tgba p.2 base kept byTgt? p', #[])

end OfStep

section OfStepEq

variable (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
  (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool)

theorem getSuccessorsOfStep_eq :
    getSuccessorsOfStep tgba (fun s => (sysSucc s, sysLabel s)) = getSuccessors tgba sysSucc sysLabel := by
  funext p; obtain ⟨s, q⟩ := p; rfl

theorem keptStepsOfStep_eq :
    keptStepsOfStep (fun s => (sysSucc s, sysLabel s)) keep = keptSteps sysSucc sysLabel keep := rfl

theorem keptSuccsOfStep_eq :
    keptSuccsOfStep tgba (fun s => (sysSucc s, sysLabel s)) keep = keptSuccs tgba sysSucc sysLabel keep := rfl

variable [BEq SysState] [Hashable SysState]

theorem edgeMarksOfStep_eq :
    edgeMarksOfStep tgba (fun s => (sysSucc s, sysLabel s)) = edgeMarks tgba sysSucc sysLabel := rfl

theorem expandOfStep_eq :
    expandOfStep tgba (fun s => (sysSucc s, sysLabel s)) = expand tgba sysSucc sysLabel := rfl

theorem keptEdgeMarksOfStep_eq :
    keptEdgeMarksOfStep tgba (fun s => (sysSucc s, sysLabel s)) keep
      = keptEdgeMarks tgba sysSucc sysLabel keep := rfl

theorem keptExpandOfStep_eq :
    keptExpandOfStep tgba (fun s => (sysSucc s, sysLabel s)) keep = keptExpand tgba sysSucc sysLabel keep := rfl

end OfStepEq

/-! Generic forms, at an arbitrary `sysStep` rather than at a literal pair. These are what a `rw` inside
a definition needs, since `rw` matches syntactically and a route's callback is an opaque variable. They
hold for the same reason: `fun s => ((f s).1, (f s).2)` is `f`. -/

section OfStepEqGen

variable (tgba : TGBA α) (sysStep : LSys.StepFn α SysState) (keep : Std.HashSet α → Bool)

theorem getSuccessorsOfStep_eq' :
    getSuccessorsOfStep tgba sysStep
      = getSuccessors tgba (fun s => (sysStep s).1) (fun s => (sysStep s).2) :=
  getSuccessorsOfStep_eq tgba _ _

theorem keptStepsOfStep_eq' :
    keptStepsOfStep sysStep keep
      = keptSteps (fun s => (sysStep s).1) (fun s => (sysStep s).2) keep := rfl

theorem keptSuccsOfStep_eq' :
    keptSuccsOfStep tgba sysStep keep
      = keptSuccs tgba (fun s => (sysStep s).1) (fun s => (sysStep s).2) keep := rfl

variable [BEq SysState] [Hashable SysState]

theorem edgeMarksOfStep_eq' :
    edgeMarksOfStep tgba sysStep
      = edgeMarks tgba (fun s => (sysStep s).1) (fun s => (sysStep s).2) := rfl

theorem expandOfStep_eq' :
    expandOfStep tgba sysStep
      = expand tgba (fun s => (sysStep s).1) (fun s => (sysStep s).2) := rfl

theorem keptEdgeMarksOfStep_eq' :
    keptEdgeMarksOfStep tgba sysStep keep
      = keptEdgeMarks tgba (fun s => (sysStep s).1) (fun s => (sysStep s).2) keep := rfl

theorem keptExpandOfStep_eq' :
    keptExpandOfStep tgba sysStep keep
      = keptExpand tgba (fun s => (sysStep s).1) (fun s => (sysStep s).2) keep := rfl

end OfStepEqGen


theorem succsFrom_mem_iff (tgba : TGBA α) (q : Nat) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) (p' : SysState × Nat) :
    p' ∈ succsFrom tgba q base steps ↔
      ∃ st ∈ steps, ∃ t ∈ tgba.getSuccessors q,
        transCompatible t (LSys.letter base st.1) = true ∧ st.2 = p'.1 ∧ t.target = p'.2 := by
  obtain ⟨s', q'⟩ := p'
  unfold succsFrom
  dsimp only
  split
  · -- the shared-letter branch: `LSys.letter base st.1 = base` for every step, by the guard
    next hall =>
      have hbase : ∀ st ∈ steps, LSys.letter base st.1 = base := fun st hst => by
        rw [LSys.letter, if_pos (by simpa using Array.all_eq_true'.mp hall st hst)]
      simp only [Array.mem_flatMap, Array.mem_map, Array.mem_filter]
      constructor
      · rintro ⟨st, hst, t, ⟨ht, hc⟩, heq⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
        exact ⟨st, hst, t, ht, by rw [hbase st hst]; exact hc, rfl, rfl⟩
      · rintro ⟨st, hst, t, ht, hc, rfl, rfl⟩
        rw [hbase st hst] at hc
        exact ⟨st, hst, t, ⟨ht, hc⟩, rfl⟩
  · simp only [Array.mem_flatMap, Array.mem_filterMap]
    constructor
    · rintro ⟨st, hst, t, ht, hopt⟩
      by_cases hc : transCompatible t (LSys.letter base st.1) = true
      · rw [if_pos hc] at hopt
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp (Option.some.inj hopt)
        exact ⟨st, hst, t, ht, hc, rfl, rfl⟩
      · rw [if_neg hc] at hopt; exact absurd hopt (by simp)
    · rintro ⟨st, hst, t, ht, hc, rfl, rfl⟩
      exact ⟨st, hst, t, ht, by rw [if_pos hc]⟩

/-! ## Proof-level bridge -/

abbrev Edge (SysState : Type v) (α : Type u) [BEq α] [Hashable α] :=
  SysState × LStep α SysState × TGBA.Edge α

/-- Convert the computational product to an abstract `TOASpec`. -/
@[expose] def toSpec (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    TOASpec (SysState × Nat) (Edge SysState α) α tgba.numAcceptSets where
  src e := (e.1, e.2.2.1)
  dst e := (e.2.1.2, e.2.2.2.target)
  valid e := e.2.2.2 ∈ tgba.getSuccessors e.2.2.1 ∧
    transCompatible e.2.2.2 (LSys.letter (sysLabel e.1) e.2.1.1) = true ∧
    e.2.1 ∈ LSys.totalize sysSucc e.1
  initial p := p ∈ initialStates tgba sysInit
  labelCompat e v := ∀ a, v a ↔ a ∈ LSys.letter (sysLabel e.1) e.2.1.1
  acceptMark i e := e.2.2.2.acceptMarks.contains i.val

/-- Stand-in for the `find?`-missed branches below, never actually selected. -/
private def junkTransition (q : Nat) : TGBA.Transition α :=
  { target := q, positiveProps := Std.HashSet.emptyWithCapacity 0,
    negativeProps := Std.HashSet.emptyWithCapacity 0,
    acceptMarks := Std.HashSet.emptyWithCapacity 0 }

/-! ## Product run decomposition + acceptance transfer -/

/-- A product step is exactly a system step out of `p.1` paired with an automaton transition compatible with
that step's letter. -/
theorem getSuccessors_mem_iff (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) {p p' : SysState × Nat} :
    p' ∈ getSuccessors tgba sysSucc sysLabel p ↔
      ∃ st ∈ LSys.totalize sysSucc p.1, ∃ t ∈ tgba.getSuccessors p.2,
        transCompatible t (LSys.letter (sysLabel p.1) st.1) = true ∧ st.2 = p'.1 ∧ t.target = p'.2 := by
  obtain ⟨s, q⟩ := p
  exact succsFrom_mem_iff tgba q (sysLabel s) (LSys.totalize sysSucc s) p'

private theorem reachable_imp (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    ∀ {p : SysState × Nat},
      Reachable (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel) p →
      Reachable sysInit (totalizeSucc (LSys.targets sysSucc)) p.1 ∧
        Reachable tgba.initialStates.toList tgba.succStates p.2 := by
  intro p h
  induction h with
  | base hi =>
    simp only [initialStates, List.mem_flatMap, List.mem_map] at hi
    obtain ⟨s, hs_mem, q, hq_mem, heq⟩ := hi
    subst heq
    exact ⟨.base hs_mem, .base hq_mem⟩
  | step hprev hmem ih =>
    rename_i prev cur
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨st, hst, t, ht, -, hst2, htgt⟩ := (getSuccessors_mem_iff tgba sysSucc sysLabel).mp hmem
    refine ⟨.step ih1 ?_, .step ih2 (htgt ▸ Array.mem_map.mpr ⟨t, ht, rfl⟩)⟩
    rw [← LSys.targets_totalize]
    exact hst2 ▸ Array.mem_map.mpr ⟨st, hst, rfl⟩

/-- The product's own `FiniteReach` witness, from the caller's system-side one and `TGBA.WellFormed`. -/
theorem finiteReach (tgba : TGBA α) (htwf : tgba.WellFormed)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState) (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) :
    FiniteReach (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel) :=
  ((finiteReach_totalizeSucc sysInit (LSys.targets sysSucc) sysFR).prod
      (tgba.finiteReach htwf)).subset
    (fun _ hp => reachable_imp tgba sysSucc sysLabel sysInit hp)

/-- A product run splits into a TGBA edge-run and an `LSys.toSpec` run that stay compatible at every step. -/
theorem run_decompose (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : Lentil.exec (Edge SysState α)} (hrun : (toSpec tgba sysSucc sysLabel sysInit).isRun σ) :
    tgba.toSpec.isRun (fun n => (σ n).2.2) ∧
    (LSys.toSpec sysSucc sysInit sysLabel).isRun (fun n => ((σ n).1, (σ n).2.1)) ∧
    ∀ n, transCompatible (σ n).2.2.2 (LSys.letter (sysLabel (σ n).1) (σ n).2.1.1) = true := by
  obtain ⟨hinit, hstep⟩ := hrun
  simp only [toSpec, initialStates, List.mem_flatMap, List.mem_map] at hinit
  obtain ⟨s, hs_mem, q, hq_mem, heq⟩ := hinit
  obtain ⟨hs0, hq0⟩ := Prod.mk.injEq .. |>.mp heq
  refine ⟨⟨?_, fun n => ⟨(hstep n).1.1, ?_⟩⟩, ⟨?_, fun n => ⟨(hstep n).1.2.2, ?_⟩⟩,
    fun n => (hstep n).1.2.1⟩
  · show tgba.isInitial (σ 0).2.2.1 = true
    rw [← hq0]
    exact Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hq_mem)
  · exact congrArg Prod.snd (hstep n).2
  · show (σ 0).1 ∈ sysInit
    rw [← hs0]; exact hs_mem
  · exact congrArg Prod.fst (hstep n).2

/-- A TGBA edge-run and a labelled system run that agree step by step combine into a genuine product run. -/
theorem run_combine (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : Lentil.exec (TGBA.Edge α)} {ρ : Lentil.exec (LSys.Edge α SysState)}
    (htgba : tgba.toSpec.isRun σ) (hsys : (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ)
    (hcompat : ∀ n, transCompatible (σ n).2 (LSys.letter (sysLabel (ρ n).1) (ρ n).2.1) = true) :
    (toSpec tgba sysSucc sysLabel sysInit).isRun (fun n => ((ρ n).1, (ρ n).2, σ n)) := by
  obtain ⟨htgba_init, htgba_step⟩ := htgba
  obtain ⟨hsys_init, hsys_step⟩ := hsys
  refine ⟨?_, fun n => ⟨⟨(htgba_step n).1, hcompat n, (hsys_step n).1⟩, ?_⟩⟩
  · show ((ρ 0).1, (σ 0).1) ∈ initialStates tgba sysInit
    simp only [initialStates, List.mem_flatMap, List.mem_map]
    exact ⟨(ρ 0).1, hsys_init, (σ 0).1,
      Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr htgba_init), rfl⟩
  · have h1 : (ρ n).2.2 = (ρ (n + 1)).1 := (hsys_step n).2
    have h2 : (σ n).2.target = (σ (n + 1)).1 := (htgba_step n).2
    show ((ρ n).2.2, (σ n).2.target) = ((ρ (n + 1)).1, (σ (n + 1)).1)
    rw [h1, h2]

private theorem transCompatible_iff_labelCompat [LawfulBEq α] (tgba : TGBA α)
    (e : TGBA.Edge α) (valuation : Std.HashSet α) :
    transCompatible e.2 valuation = true ↔ tgba.toSpec.labelCompat e (fun a => a ∈ valuation) := by
  unfold transCompatible TGBA.toSpec
  simp only [Bool.and_eq_true, Bool.not_eq_true', Std.HashSet.all_eq_true_iff_forall_mem,
    Std.HashSet.any_eq_false_iff_forall_mem, Std.HashSet.mem_iff_contains, Bool.not_eq_true]

/-- An accepting product run decomposes into a labelled system run and a TGBA-language membership witness for
the letters that run reads. -/
theorem gsp_correct1 [LawfulBEq α] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState) {σ : Lentil.exec (Edge SysState α)}
    (hacc : (toSpec tgba sysSucc sysLabel sysInit).isRun σ ∧
            (toSpec tgba sysSucc sysLabel sysInit).isAcceptingRun σ) :
    (LSys.toSpec sysSucc sysInit sysLabel).isRun (fun n => ((σ n).1, (σ n).2.1)) ∧
    tgba.toSpec.accepts (LSys.valuation sysLabel (fun n => ((σ n).1, (σ n).2.1))) := by
  obtain ⟨hrun, hacc⟩ := hacc
  obtain ⟨htgbarun, hsysrun, hcompat⟩ := run_decompose tgba sysSucc sysLabel sysInit hrun
  exact ⟨hsysrun, fun n => (σ n).2.2, htgbarun,
    fun n => (transCompatible_iff_labelCompat tgba (σ n).2.2
      (LSys.letter (sysLabel (σ n).1) (σ n).2.1.1)).mp (hcompat n),
    hacc⟩

/-- A genuine labelled system run whose letters lie in the TGBA's language lifts to an accepting product run
projecting back down to it. -/
theorem gsp_correct2 [LawfulBEq α] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState) {ρ : Lentil.exec (LSys.Edge α SysState)}
    (hsys : (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ)
    (hlang : tgba.toSpec.accepts (LSys.valuation sysLabel ρ)) :
    ∃ σ : Lentil.exec (Edge SysState α), ρ = (fun n => ((σ n).1, (σ n).2.1)) ∧
      (toSpec tgba sysSucc sysLabel sysInit).isRun σ ∧
      (toSpec tgba sysSucc sysLabel sysInit).isAcceptingRun σ := by
  obtain ⟨σ, hrun, hcompat, hacc⟩ := hlang
  exact ⟨fun n => ((ρ n).1, (ρ n).2, σ n), rfl,
    run_combine tgba sysSucc sysLabel sysInit hrun hsys
      (fun n => (transCompatible_iff_labelCompat tgba (σ n)
        (LSys.letter (sysLabel (ρ n).1) (ρ n).2.1)).mpr (hcompat n)),
    hacc⟩

/-! ## Edge witness -/

private theorem foldl_union_contains {β : Type w} (m : Nat) (f : β → Std.HashSet Nat) :
    ∀ (l : List β) (init : Std.HashSet Nat),
      (l.foldl (fun acc b => acc.union (f b)) init).contains m ↔
        init.contains m ∨ ∃ b ∈ l, (f b).contains m := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro init
    rw [List.foldl_cons, ih, Std.HashSet.union_eq, Std.HashSet.contains_union]
    simp only [Bool.or_eq_true, List.mem_cons]
    constructor
    · rintro ((h1 | h2) | ⟨b, hb, hbm⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨a, Or.inl rfl, h2⟩
      · exact Or.inr ⟨b, Or.inr hb, hbm⟩
    · rintro (h | ⟨b, rfl | hb, hbm⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr hbm)
      · exact Or.inr ⟨b, hb, hbm⟩

/-! ### Membership through the grouped fast path

`edgeMarksFrom` has two shapes, so its characterization needs both. The `none` branch is the plain fold
over `realizationsFrom`. The `some` branch answers from two hash lookups instead of a per-successor scan,
and that is sound only when the hash agrees with `==` — which is why everything below carries
`LawfulHashable SysState`. That instance is not proof bookkeeping: it is the precondition the optimization
actually runs on. See `EdgeLabels.md` §13.6. -/

/-- The grouped table's entry for a key, characterized. Stated over the fold's accumulator so that the
induction has something to move on. -/
private theorem foldl_marksByTarget_contains (base : Std.HashSet α) (k m : Nat) :
    ∀ (l : List (TGBA.Transition α)) (init : Std.HashMap Nat (Std.HashSet Nat)),
      ((l.foldl (fun mp t =>
            if transCompatible t base then
              mp.insert t.target
                ((mp.getD t.target (Std.HashSet.emptyWithCapacity 0)).union t.acceptMarks)
            else mp) init).getD k (Std.HashSet.emptyWithCapacity 0)).contains m ↔
        (init.getD k (Std.HashSet.emptyWithCapacity 0)).contains m ∨
          ∃ t ∈ l, t.target = k ∧ transCompatible t base = true ∧ t.acceptMarks.contains m := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro init
    rw [List.foldl_cons, ih]
    simp only [List.mem_cons]
    by_cases hc : transCompatible a base = true
    · by_cases hk : a.target = k
      · subst hk
        rw [if_pos hc, Std.HashMap.getD_insert, if_pos (beq_self_eq_true a.target),
          Std.HashSet.union_eq, Std.HashSet.contains_union]
        simp only [Bool.or_eq_true]
        constructor
        · rintro ((h | h) | ⟨t, ht, h⟩)
          · exact Or.inl h
          · exact Or.inr ⟨a, Or.inl rfl, rfl, hc, h⟩
          · exact Or.inr ⟨t, Or.inr ht, h⟩
        · rintro (h | ⟨t, ht, htk, htc, htm⟩)
          · exact Or.inl (Or.inl h)
          · rcases ht with rfl | ht
            · exact Or.inl (Or.inr htm)
            · exact Or.inr ⟨t, ht, htk, htc, htm⟩
      · rw [if_pos hc, Std.HashMap.getD_insert, if_neg (by simpa using hk)]
        constructor
        · rintro (h | ⟨t, ht, h⟩)
          · exact Or.inl h
          · exact Or.inr ⟨t, Or.inr ht, h⟩
        · rintro (h | ⟨t, ht, htk, htc, htm⟩)
          · exact Or.inl h
          · rcases ht with rfl | ht
            · exact absurd htk hk
            · exact Or.inr ⟨t, ht, htk, htc, htm⟩
    · rw [if_neg hc]
      constructor
      · rintro (h | ⟨t, ht, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨t, Or.inr ht, h⟩
      · rintro (h | ⟨t, ht, htk, htc, htm⟩)
        · exact Or.inl h
        · rcases ht with rfl | ht
          · exact absurd htc hc
          · exact Or.inr ⟨t, ht, htk, htc, htm⟩

/-- A mark sits under key `k` of the grouped table exactly when a `base`-compatible `q`-transition to `k`
carries it. -/
theorem contains_marksByTarget (tgba : TGBA α) (q : Nat)
    (base : Std.HashSet α) (k m : Nat) :
    ((marksByTarget tgba q base).getD k (Std.HashSet.emptyWithCapacity 0)).contains m ↔
      ∃ t ∈ tgba.getSuccessors q,
        t.target = k ∧ transCompatible t base = true ∧ t.acceptMarks.contains m := by
  rw [marksByTarget, ← Array.foldl_toList, foldl_marksByTarget_contains]
  simp only [Std.HashMap.getD_empty, Std.HashSet.contains_emptyWithCapacity, Bool.false_eq_true,
    false_or, ← Array.mem_def]

/-- The hashed step-target guard, characterized. This is the lemma the whole optimization rests on: it is
where `LawfulHashable SysState` is consumed, replacing the deep `SysState` comparison the scan used to do
per step per successor. -/
private theorem foldl_stepTargets_contains [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
    [LawfulHashable SysState] (s : SysState) :
    ∀ (l : List (LStep α SysState)) (init : Std.HashSet SysState),
      (l.foldl (fun acc st => acc.insert st.2) init).contains s ↔
        init.contains s ∨ ∃ st ∈ l, st.2 = s := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro init
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert]
    simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨st, hst, h⟩)
      · exact Or.inr ⟨a, Or.inl rfl, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨st, Or.inr hst, h⟩
    · rintro (h | ⟨st, hst, h⟩)
      · exact Or.inl (Or.inr h)
      · rcases hst with rfl | hst
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨st, hst, h⟩

theorem contains_stepTargets [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
    [LawfulHashable SysState] (steps : Array (LStep α SysState)) (s : SysState) :
    (stepTargets steps).contains s ↔ ∃ st ∈ steps, st.2 = s := by
  rw [stepTargets, ← Array.foldl_toList, foldl_stepTargets_contains]
  simp only [Std.HashSet.contains_empty, Bool.false_eq_true, false_or, ← Array.mem_def]

/-- The generating lookup agrees with the spec's guarded one on every successor the source generated. The
guard is `stepTargets`' membership, which takes lawful hashing to read, and this is the one place a
wired route reads it — as a proof obligation, not as a hash per successor. §13.23 -/
theorem genMarksFromShared_eq [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
    [LawfulHashable SysState] (tgba : TGBA α) (q : Nat) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) {p' : SysState × Nat}
    (hp' : p' ∈ succsFrom tgba q base steps) :
    genMarksFromShared tgba q base steps (marksTableGen tgba q base steps) p'
      = edgeMarksFrom tgba q base steps p' := by
  obtain ⟨st, hst, -, -, -, h1, -⟩ := (succsFrom_mem_iff tgba q base steps p').mp hp'
  rw [edgeMarksFrom, marksTable, marksTableGen]
  by_cases hall : steps.all (·.1.isEmpty) = true
  · rw [if_pos hall, if_pos hall]
    show _ = (if (stepTargets steps).contains p'.1 then _ else _)
    rw [if_pos ((contains_stepTargets steps p'.1).mpr ⟨st, hst, h1⟩)]
    rfl
  · rw [if_neg hall, if_neg hall]
    rfl

/-- `expand` is the fused form of `getSuccessors` and `edgeMarks`: one call per product state. The
successors are definitionally the same; the marks agree on every generated successor by
`genMarksFromShared_eq`, which is why this is a map-congruence over members rather than `rfl` (§13.23). -/
theorem expand_coherent [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [LawfulHashable SysState]
    (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α) :
    ExpandCoherent (getSuccessors tgba sysSucc sysLabel) (edgeMarks tgba sysSucc sysLabel)
      (expand tgba sysSucc sysLabel) := by
  intro p
  refine Prod.ext rfl ?_
  exact Array.map_congr_left fun p' hp' => genMarksFromShared_eq tgba p.2 _ _ hp'

/-- The marks of a product edge, whichever shape `edgeMarksFrom` took. Both branches compute the union of
the accept marks over the edge's realizations; the grouped one just gets there without comparing states. -/
theorem contains_edgeMarksFrom_iff [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
    [LawfulHashable SysState] (tgba : TGBA α) (q : Nat) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) (p' : SysState × Nat) (m : Nat) :
    (edgeMarksFrom tgba q base steps p').contains m ↔
      ∃ r ∈ realizationsFrom tgba q base steps p', r.2.acceptMarks.contains m := by
  rw [edgeMarksFrom, marksTable]
  by_cases hall : steps.all (·.1.isEmpty) = true
  · rw [if_pos hall]
    show (if (stepTargets steps).contains p'.1 then
        (marksByTarget tgba q base).getD p'.2 (Std.HashSet.emptyWithCapacity 0)
      else Std.HashSet.emptyWithCapacity 0).contains m ↔ _
    -- under the guard every step reads `base`, so compatibility no longer depends on the step
    have hbase : ∀ st ∈ steps, LSys.letter base st.1 = base := fun st hst => by
      rw [LSys.letter, if_pos (by simpa using Array.all_eq_true'.mp hall st hst)]
    have hR : (∃ r ∈ realizationsFrom tgba q base steps p', r.2.acceptMarks.contains m) ↔
        (∃ st ∈ steps, st.2 = p'.1) ∧
          (∃ t ∈ tgba.getSuccessors q,
            t.target = p'.2 ∧ transCompatible t base = true ∧ t.acceptMarks.contains m) := by
      constructor
      · rintro ⟨r, hr, hrm⟩
        obtain ⟨⟨hst, hst2⟩, ht, htgt, hc⟩ :=
          (mem_realizationsFrom_iff tgba q base steps p' r).mp hr
        rw [hbase r.1 hst] at hc
        exact ⟨⟨r.1, hst, hst2⟩, r.2, ht, htgt, hc, hrm⟩
      · rintro ⟨⟨st, hst, hst2⟩, t, ht, htgt, hc, hm⟩
        refine ⟨(st, t), (mem_realizationsFrom_iff tgba q base steps p' (st, t)).mpr ?_, hm⟩
        exact ⟨⟨hst, hst2⟩, ht, htgt, by rw [hbase st hst]; exact hc⟩
    rw [hR]
    by_cases hg : (stepTargets steps).contains p'.1 = true
    · rw [if_pos hg, contains_marksByTarget]
      exact (and_iff_right ((contains_stepTargets steps p'.1).mp hg)).symm
    · rw [if_neg hg, Std.HashSet.contains_emptyWithCapacity]
      simp only [Bool.false_eq_true, false_iff, not_and]
      exact fun h1 => absurd ((contains_stepTargets steps p'.1).mpr h1) hg
  · rw [if_neg hall]
    simp only [edgeMarksFromShared]
    rw [← Array.foldl_toList,
      foldl_union_contains m (fun r : LStep α SysState × TGBA.Transition α => r.2.acceptMarks),
      Std.HashSet.contains_emptyWithCapacity]
    simp only [Bool.false_eq_true, false_or, ← Array.mem_def]

/-- A product edge's marks are exactly those of the transitions of its realizations. -/
theorem mem_edgeMarks_iff [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
    [LawfulHashable SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (p p' : SysState × Nat) (m : Nat) :
    (edgeMarks tgba sysSucc sysLabel p p').contains m ↔
      ∃ r ∈ realizations tgba sysSucc sysLabel p p', r.2.acceptMarks.contains m :=
  contains_edgeMarksFrom_iff tgba p.2 (sysLabel p.1) (LSys.totalize sysSucc p.1) p' m

/-- The restricted edge's marks, characterized. `keptEdgeMarks` differs from `edgeMarks` only in which
`steps` array it is handed, so this is `contains_edgeMarksFrom_iff` at `keptSteps`. Every lemma below
that used to unfold the old `foldl` body goes through this instead. -/
theorem contains_keptEdgeMarks_iff [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
    [LawfulHashable SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) (p p' : SysState × Nat) (m : Nat) :
    (keptEdgeMarks tgba sysSucc sysLabel keep p p').contains m ↔
      ∃ r ∈ realizationsFrom tgba p.2 (sysLabel p.1) (keptSteps sysSucc sysLabel keep p.1) p',
        r.2.acceptMarks.contains m :=
  contains_edgeMarksFrom_iff tgba p.2 (sysLabel p.1) (keptSteps sysSucc sysLabel keep p.1) p' m

/-- A product edge's marks are exactly some automaton transition's, so any per-transition bound transfers. -/
theorem edgeMarks_lt [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
    [LawfulHashable SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (hbound : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets)
    (p p' : SysState × Nat) (m : Nat) (hm : m ∈ edgeMarks tgba sysSucc sysLabel p p') :
    m < tgba.numAcceptSets := by
  obtain ⟨r, hr, hrm⟩ :=
    (mem_edgeMarks_iff tgba sysSucc sysLabel p p' m).mp (Std.HashSet.mem_iff_contains.mp hm)
  obtain ⟨-, ht, -, -⟩ := (mem_realizations_iff tgba sysSucc sysLabel p p' r).mp hr
  exact hbound _ _ ht m (Std.HashSet.mem_iff_contains.mpr hrm)

/-- A restricted product step is a product step: the latch's stem copy can follow it. -/
theorem keptSuccs_sub (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) (p q : SysState × Nat)
    (h : q ∈ keptSuccs tgba sysSucc sysLabel keep p) : q ∈ getSuccessors tgba sysSucc sysLabel p := by
  obtain ⟨st, hst, t, ht, hc, h1, h2⟩ := (succsFrom_mem_iff _ _ _ _ _).mp h
  exact (getSuccessors_mem_iff tgba sysSucc sysLabel).mpr
    ⟨st, (mem_keptSteps.mp hst).1, t, ht, hc, h1, h2⟩

/-! ### Antitonicity in the restriction (§6.5)

The prune conjoins one option's region into a candidate at a time, so it needs the restricted product to be
antitone in `keep`: strengthening the predicate keeps fewer steps, hence fewer successors and fewer marks.
Together with `keptSteps_top` these generalize the `_sub` lemmas above, which are the special case
`keep := fun _ => true`; `_sub` keeps its own proof only because it is stated earlier in the file. -/

theorem keptSteps_mono {sysSucc : SysState → Array (LStep α SysState)}
    {sysLabel : SysState → Std.HashSet α} {keep keep' : Std.HashSet α → Bool}
    (hle : ∀ l, keep' l = true → keep l = true) (s : SysState) {st : LStep α SysState}
    (h : st ∈ keptSteps sysSucc sysLabel keep' s) : st ∈ keptSteps sysSucc sysLabel keep s :=
  mem_keptSteps.mpr ⟨(mem_keptSteps.mp h).1, hle _ (mem_keptSteps.mp h).2⟩

theorem keptSuccs_mono (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) {keep keep' : Std.HashSet α → Bool}
    (hle : ∀ l, keep' l = true → keep l = true) (p q : SysState × Nat)
    (h : q ∈ keptSuccs tgba sysSucc sysLabel keep' p) : q ∈ keptSuccs tgba sysSucc sysLabel keep p := by
  obtain ⟨st, hst, t, ht, hc, h1, h2⟩ := (succsFrom_mem_iff _ _ _ _ _).mp h
  exact (succsFrom_mem_iff _ _ _ _ _).mpr ⟨st, keptSteps_mono hle p.1 hst, t, ht, hc, h1, h2⟩

theorem keptEdgeMarks_mono [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
    [LawfulHashable SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    {keep keep' : Std.HashSet α → Bool} (hle : ∀ l, keep' l = true → keep l = true)
    (p p' : SysState × Nat) (m : Nat)
    (h : m ∈ keptEdgeMarks tgba sysSucc sysLabel keep' p p') :
    m ∈ keptEdgeMarks tgba sysSucc sysLabel keep p p' := by
  obtain ⟨r, hr, hrm⟩ :=
    (contains_keptEdgeMarks_iff tgba sysSucc sysLabel keep' p p' m).mp
      (Std.HashSet.mem_iff_contains.mp h)
  obtain ⟨⟨hst, hst2⟩, ht, htgt, hc⟩ :=
    (mem_realizationsFrom_iff tgba p.2 (sysLabel p.1) _ p' r).mp hr
  refine Std.HashSet.mem_iff_contains.mpr
    ((contains_keptEdgeMarks_iff tgba sysSucc sysLabel keep p p' m).mpr ⟨r, ?_, hrm⟩)
  exact (mem_realizationsFrom_iff _ _ _ _ _ _).mpr
    ⟨⟨keptSteps_mono hle p.1 hst, hst2⟩, ht, htgt, hc⟩

/-- A restricted product edge carries every mark of every realization that survives the restriction. The
`mpr` half of `mem_edgeMarks_iff` for the restricted marks, which is all a caller building an `RRun` needs:
it hands over the realization the run actually takes. -/
theorem mem_keptEdgeMarks_of_realization [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
    [LawfulHashable SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) (p p' : SysState × Nat)
    (r : LStep α SysState × TGBA.Transition α)
    (hr : r ∈ realizationsFrom tgba p.2 (sysLabel p.1) (keptSteps sysSucc sysLabel keep p.1) p')
    {m : Nat} (hm : m ∈ r.2.acceptMarks) :
    m ∈ keptEdgeMarks tgba sysSucc sysLabel keep p p' :=
  Std.HashSet.mem_iff_contains.mpr
    ((contains_keptEdgeMarks_iff tgba sysSucc sysLabel keep p p' m).mpr
      ⟨r, hr, Std.HashSet.mem_iff_contains.mp hm⟩)

/-- At the top predicate nothing is cut, so the restricted product is the product. -/
theorem keptSteps_top (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (s : SysState) :
    keptSteps sysSucc sysLabel (fun _ => true) s = LSys.totalize sysSucc s := by
  apply Array.ext'
  rw [keptSteps, keptStepsFrom, Array.toList_filter, List.filter_eq_self]
  intro st _
  rfl

theorem keptSuccs_top (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (p : SysState × Nat) :
    keptSuccs tgba sysSucc sysLabel (fun _ => true) p = getSuccessors tgba sysSucc sysLabel p := by
  rw [keptSuccs_eq, keptSteps_top]; rfl

/-- At the top region nothing is cut, so a restricted edge carries exactly the marks of the product edge.

Stated pointwise on marks rather than as an equality of `Std.HashSet Nat`.

§13.7 had to weaken this: back then `keptEdgeMarks` folded a union per realization while `edgeMarks`
answered from the grouped table, and the two agreed on membership but not on representation. Since
§13.10 both sides are `edgeMarksFrom` at arguments `keptSteps_top` proves *equal*, so the value equality
is recoverable. It is left pointwise because that is all `RStreettSpec.Compat.marks_top` uses, and
strengthening it back would mean re-threading that law through its implementors for no gain. -/
theorem keptEdgeMarks_top [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
    [LawfulHashable SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (p p' : SysState × Nat) (m : Nat) :
    m ∈ keptEdgeMarks tgba sysSucc sysLabel (fun _ => true) p p' ↔
      m ∈ edgeMarks tgba sysSucc sysLabel p p' := by
  simp only [Std.HashSet.mem_iff_contains, contains_keptEdgeMarks_iff, mem_edgeMarks_iff,
    realizations, keptSteps_top]

/-! ### The state-labelled special case

For an unlabelled system every step reads exactly the source state's label, so the letter restriction
`keep` degenerates to a predicate on the source state. When it holds at `s`, *no* step out of `s` is cut
and the restricted product coincides with the product there. This is what makes the edge-aware latch a
conservative generalisation of the old state-region latch. -/

theorem keptSteps_unlabelled (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) (s : SysState)
    (hk : keep (sysLabel s) = true) :
    keptSteps (LSys.unlabelled sysSucc) sysLabel keep s
      = LSys.totalize (LSys.unlabelled sysSucc) s := by
  apply Array.ext'
  rw [keptSteps, keptStepsFrom, Array.toList_filter, List.filter_eq_self]
  intro st hst
  rw [LSys.letter_eq_empty_of_unlabelled (by simpa using hst), LSys.letter_empty]
  exact hk

/-- For a system with no edge atoms, a restriction is decided by the source state's label alone, so two
restrictions agreeing there keep the same steps. -/
theorem keptSteps_unlabelled_congr (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (keep keep' : Std.HashSet α → Bool) (s : SysState)
    (h : keep (sysLabel s) = keep' (sysLabel s)) :
    keptSteps (LSys.unlabelled sysSucc) sysLabel keep s
      = keptSteps (LSys.unlabelled sysSucc) sysLabel keep' s := by
  apply Array.ext'
  rw [keptSteps, keptSteps, keptStepsFrom, keptStepsFrom, Array.toList_filter,
    Array.toList_filter]
  refine List.filter_congr fun st hst => ?_
  rw [LSys.letter_eq_empty_of_unlabelled (by simpa using hst), LSys.letter_empty, h]

theorem keptSuccs_unlabelled_congr (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (keep keep' : Std.HashSet α → Bool) (p : SysState × Nat)
    (h : keep (sysLabel p.1) = keep' (sysLabel p.1)) :
    keptSuccs tgba (LSys.unlabelled sysSucc) sysLabel keep p
      = keptSuccs tgba (LSys.unlabelled sysSucc) sysLabel keep' p := by
  rw [keptSuccs_eq, keptSuccs_eq, keptSteps_unlabelled_congr sysSucc sysLabel keep keep' p.1 h]

theorem keptSuccs_unlabelled (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) (p : SysState × Nat)
    (hk : keep (sysLabel p.1) = true) :
    keptSuccs tgba (LSys.unlabelled sysSucc) sysLabel keep p
      = getSuccessors tgba (LSys.unlabelled sysSucc) sysLabel p := by
  rw [keptSuccs_eq, keptSteps_unlabelled _ _ _ _ hk]; rfl

/-- Pointwise on marks, for the same reason as `keptEdgeMarks_top`. -/
theorem keptEdgeMarks_unlabelled [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
    [LawfulHashable SysState] (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) (p p' : SysState × Nat)
    (m : Nat) (hk : keep (sysLabel p.1) = true) :
    m ∈ keptEdgeMarks tgba (LSys.unlabelled sysSucc) sysLabel keep p p' ↔
      m ∈ edgeMarks tgba (LSys.unlabelled sysSucc) sysLabel p p' := by
  simp only [Std.HashSet.mem_iff_contains, contains_keptEdgeMarks_iff, mem_edgeMarks_iff,
    realizations, keptSteps_unlabelled sysSucc sysLabel keep p.1 hk]

/-- Membership form of `keptSuccs_unlabelled`: cheaper to apply, since every implicit is fixed by `h`
rather than recovered from the goal. -/
theorem mem_keptSuccs_unlabelled (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) (p q : SysState × Nat)
    (hk : keep (sysLabel p.1) = true)
    (h : q ∈ getSuccessors tgba (LSys.unlabelled sysSucc) sysLabel p) :
    q ∈ keptSuccs tgba (LSys.unlabelled sysSucc) sysLabel keep p := by
  rw [keptSuccs_unlabelled tgba sysSucc sysLabel keep p hk]; exact h

/-- A restricted product edge's marks are a subset of the unrestricted edge's. -/
theorem keptEdgeMarks_sub [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
    [LawfulHashable SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) (p p' : SysState × Nat) (m : Nat)
    (h : m ∈ keptEdgeMarks tgba sysSucc sysLabel keep p p') :
    m ∈ edgeMarks tgba sysSucc sysLabel p p' := by
  obtain ⟨r, hr, hrm⟩ :=
    (contains_keptEdgeMarks_iff tgba sysSucc sysLabel keep p p' m).mp
      (Std.HashSet.mem_iff_contains.mp h)
  refine Std.HashSet.mem_iff_contains.mpr ((mem_edgeMarks_iff tgba sysSucc sysLabel p p' m).mpr
    ⟨r, ?_, hrm⟩)
  obtain ⟨⟨hst, hst2⟩, ht, htgt, hc⟩ :=
    (mem_realizationsFrom_iff tgba p.2 (sysLabel p.1) _ p' r).mp hr
  exact (mem_realizations_iff tgba sysSucc sysLabel p p' r).mpr
    ⟨⟨(mem_keptSteps.mp hst).1, hst2⟩, ht, htgt, hc⟩

/-- The product step `p → p'` has a realization exactly when it is a step at all. -/
theorem exists_realization_iff [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (p p' : SysState × Nat) :
    (∃ r, r ∈ realizations tgba sysSucc sysLabel p p') ↔
      p' ∈ getSuccessors tgba sysSucc sysLabel p := by
  rw [getSuccessors_mem_iff]
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨⟨hst, hst2⟩, ht, htgt, hc⟩ := (mem_realizations_iff tgba sysSucc sysLabel p p' r).mp hr
    exact ⟨r.1, hst, r.2, ht, hc, hst2, htgt⟩
  · rintro ⟨st, hst, t, ht, hc, hst2, htgt⟩
    exact ⟨(st, t), (mem_realizations_iff tgba sysSucc sysLabel p p' (st, t)).mpr
      ⟨⟨hst, hst2⟩, ht, htgt, hc⟩⟩

variable [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [LawfulHashable SysState]

/-- The realization the witness picks for a step, or for a step carrying a given mark. -/
private def pick (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (p p' : SysState × Nat)
    (extra : LStep α SysState × TGBA.Transition α → Bool) :
    LStep α SysState × TGBA.Transition α :=
  ((realizations tgba sysSucc sysLabel p p').find? extra).getD
    (((∅ : Std.HashSet α), p'.1), junkTransition p'.2)

omit [LawfulBEq SysState] [LawfulHashable SysState] in
private theorem pick_spec (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (p p' : SysState × Nat)
    (extra : LStep α SysState × TGBA.Transition α → Bool)
    (hex : ∃ r ∈ realizations tgba sysSucc sysLabel p p', extra r = true) :
    (pick tgba sysSucc sysLabel p p' extra) ∈ realizations tgba sysSucc sysLabel p p' ∧
      extra (pick tgba sysSucc sysLabel p p' extra) = true := by
  obtain ⟨r, hr, hextra⟩ := hex
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Array.find?_isSome.mpr ⟨r, hr, hextra⟩)
  rw [pick, ha, Option.getD_some]
  exact ⟨Array.mem_of_find?_eq_some ha, Array.find?_some ha⟩

/-- `pick` over the restricted step set. -/
private def pickKept (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) (p p' : SysState × Nat)
    (extra : LStep α SysState × TGBA.Transition α → Bool) :
    LStep α SysState × TGBA.Transition α :=
  ((realizationsFrom tgba p.2 (sysLabel p.1) (keptSteps sysSucc sysLabel keep p.1) p').find?
    extra).getD (((∅ : Std.HashSet α), p'.1), junkTransition p'.2)

omit [LawfulBEq SysState] [LawfulHashable SysState] in
private theorem pickKept_spec (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) (p p' : SysState × Nat)
    (extra : LStep α SysState × TGBA.Transition α → Bool)
    (hex : ∃ r ∈ realizationsFrom tgba p.2 (sysLabel p.1) (keptSteps sysSucc sysLabel keep p.1) p',
      extra r = true) :
    (pickKept tgba sysSucc sysLabel keep p p' extra) ∈
      realizationsFrom tgba p.2 (sysLabel p.1) (keptSteps sysSucc sysLabel keep p.1) p' ∧
      extra (pickKept tgba sysSucc sysLabel keep p p' extra) = true := by
  obtain ⟨r, hr, hextra⟩ := hex
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Array.find?_isSome.mpr ⟨r, hr, hextra⟩)
  rw [pickKept, ha, Option.getD_some]
  exact ⟨Array.mem_of_find?_eq_some ha, Array.find?_some ha⟩

/-- Realize any product step or `edgeMarks`-witnessed mark as a concrete product `Edge`, by picking a
realization of matching shape. -/
def edgeWitness (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    TEdgeWitness (toSpec tgba sysSucc sysLabel sysInit)
      (getSuccessors tgba sysSucc sysLabel) (edgeMarks tgba sysSucc sysLabel) where
  stepEdge p p' :=
    let r := pick tgba sysSucc sysLabel p p' (fun _ => true)
    (p.1, r.1, ⟨p.2, r.2⟩)
  stepEdge_spec := by
    intro p p' hp'
    obtain ⟨r, hr⟩ := (exists_realization_iff tgba sysSucc sysLabel p p').mpr hp'
    obtain ⟨hmem, -⟩ := pick_spec tgba sysSucc sysLabel p p' (fun _ => true) ⟨r, hr, rfl⟩
    obtain ⟨⟨hst, hst2⟩, ht, htgt, hc⟩ :=
      (mem_realizations_iff tgba sysSucc sysLabel p p' _).mp hmem
    exact ⟨⟨ht, hc, hst⟩, rfl, by simp only [toSpec, hst2, htgt]⟩
  markEdge p p' m :=
    let r := pick tgba sysSucc sysLabel p p' (fun r => r.2.acceptMarks.contains m)
    (p.1, r.1, ⟨p.2, r.2⟩)
  markEdge_spec := by
    intro p p' m _ _ hm
    obtain ⟨r, hr, hrm⟩ :=
      (mem_edgeMarks_iff tgba sysSucc sysLabel p p' m).mp (Std.HashSet.mem_iff_contains.mp hm)
    obtain ⟨hmem, hextra⟩ := pick_spec tgba sysSucc sysLabel p p'
      (fun r => r.2.acceptMarks.contains m) ⟨r, hr, hrm⟩
    obtain ⟨⟨hst, hst2⟩, ht, htgt, hc⟩ :=
      (mem_realizations_iff tgba sysSucc sysLabel p p' _).mp hmem
    exact ⟨⟨ht, hc, hst⟩, rfl, by simp only [toSpec, hst2, htgt], hextra⟩

omit [LawfulHashable SysState] in
/-- A restricted product step has a restricted realization. -/
theorem exists_keptRealization_iff (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) (p p' : SysState × Nat) :
    (∃ r, r ∈ realizationsFrom tgba p.2 (sysLabel p.1) (keptSteps sysSucc sysLabel keep p.1) p') ↔
      p' ∈ keptSuccs tgba sysSucc sysLabel keep p := by
  rw [keptSuccs_eq, succsFrom_mem_iff]
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨⟨hst, hst2⟩, ht, htgt, hc⟩ := (mem_realizationsFrom_iff _ _ _ _ _ _).mp hr
    exact ⟨r.1, hst, r.2, ht, hc, hst2, htgt⟩
  · rintro ⟨st, hst, t, ht, hc, hst2, htgt⟩
    exact ⟨(st, t), (mem_realizationsFrom_iff _ _ _ _ _ _).mpr ⟨⟨hst, hst2⟩, ht, htgt, hc⟩⟩

/-- A mark on a restricted product edge is carried by a restricted realization. -/
theorem exists_keptRealization_of_mark (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) (p p' : SysState × Nat) (m : Nat)
    (hm : m ∈ keptEdgeMarks tgba sysSucc sysLabel keep p p') :
    ∃ r ∈ realizationsFrom tgba p.2 (sysLabel p.1) (keptSteps sysSucc sysLabel keep p.1) p',
      r.2.acceptMarks.contains m := by
  exact (contains_keptEdgeMarks_iff tgba sysSucc sysLabel keep p p' m).mp
    (Std.HashSet.mem_iff_contains.mp hm)

set_option maxHeartbeats 1000000 in
/-- The edge witness for the *restricted* product: it realizes a step with a kept realization, so every
edge it emits reads a letter the restriction admits. It still targets the unrestricted `toSpec`, because
that is the spec the lasso lives in — only the graph and marks it draws from are restricted. -/
def keptEdgeWitness (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) (sysInit : List SysState) :
    TEdgeWitness (toSpec tgba sysSucc sysLabel sysInit) (keptSuccs tgba sysSucc sysLabel keep)
      (keptEdgeMarks tgba sysSucc sysLabel keep) where
  stepEdge p p' :=
    let r := pickKept tgba sysSucc sysLabel keep p p' (fun _ => true)
    (p.1, r.1, ⟨p.2, r.2⟩)
  stepEdge_spec := by
    intro p p' hp'
    obtain ⟨st, hst, t, ht, hc, h1, h2⟩ := (succsFrom_mem_iff _ _ _ _ _).mp hp'
    obtain ⟨hmem, -⟩ := pickKept_spec tgba sysSucc sysLabel keep p p' (fun _ => true)
      ⟨(st, t), (mem_realizationsFrom_iff _ _ _ _ _ _).mpr ⟨⟨hst, h1⟩, ht, h2, hc⟩, rfl⟩
    obtain ⟨⟨hst', hst2⟩, ht', htgt, hc'⟩ :=
      (mem_realizationsFrom_iff tgba p.2 (sysLabel p.1) _ p' _).mp hmem
    exact ⟨⟨ht', hc', (mem_keptSteps.mp hst').1⟩, rfl, by simp only [toSpec, hst2, htgt]⟩
  markEdge p p' m :=
    let r := pickKept tgba sysSucc sysLabel keep p p' (fun r => r.2.acceptMarks.contains m)
    (p.1, r.1, ⟨p.2, r.2⟩)
  markEdge_spec := by
    intro p p' m _ _ hm
    obtain ⟨r, hr, hrm⟩ :=
      (contains_keptEdgeMarks_iff tgba sysSucc sysLabel keep p p' m).mp
        (Std.HashSet.mem_iff_contains.mp hm)
    obtain ⟨hmem, hextra⟩ := pickKept_spec tgba sysSucc sysLabel keep p p'
      (fun r => r.2.acceptMarks.contains m) ⟨r, hr, hrm⟩
    obtain ⟨⟨hst', hst2⟩, ht', htgt, hc'⟩ :=
      (mem_realizationsFrom_iff tgba p.2 (sysLabel p.1) _ p' _).mp hmem
    exact ⟨⟨ht', hc', (mem_keptSteps.mp hst').1⟩, rfl, by simp only [toSpec, hst2, htgt], hextra⟩

omit [LawfulHashable SysState] in
/-- Every edge the restricted witness emits on a real restricted step reads a letter the restriction
admits. This is what `cycleE_forall` turns into `◇□` on the run. -/
private theorem keptEdgeWitness_letter (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool)
    (p p' : SysState × Nat)
    (extra : LStep α SysState × TGBA.Transition α → Bool)
    (hex : ∃ r ∈ realizationsFrom tgba p.2 (sysLabel p.1) (keptSteps sysSucc sysLabel keep p.1) p',
      extra r = true) :
    keep (LSys.letter (sysLabel p.1) (pickKept tgba sysSucc sysLabel keep p p' extra).1.1) = true := by
  obtain ⟨hmem, -⟩ := pickKept_spec tgba sysSucc sysLabel keep p p' extra hex
  obtain ⟨⟨hst, -⟩, -⟩ := (mem_realizationsFrom_iff tgba p.2 (sysLabel p.1) _ p' _).mp hmem
  exact (mem_keptSteps.mp hst).2

/-- `keptEdgeWitness_letter` at the `stepEdge` projection, with the source read off the *edge* rather
than off `p` — that is the shape `cycleE_forall`'s predicate produces. -/
theorem keptEdgeWitness_stepEdge_letter (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) (sysInit : List SysState)
    (p p' : SysState × Nat) (hp' : p' ∈ keptSuccs tgba sysSucc sysLabel keep p) :
    keep (LSys.letter
        (sysLabel ((keptEdgeWitness tgba sysSucc sysLabel keep sysInit).stepEdge p p').1)
        ((keptEdgeWitness tgba sysSucc sysLabel keep sysInit).stepEdge p p').2.1.1) = true := by
  rw [show ((keptEdgeWitness tgba sysSucc sysLabel keep sysInit).stepEdge p p').1 = p.1 from
    congrArg Prod.fst ((keptEdgeWitness tgba sysSucc sysLabel keep sysInit).stepEdge_spec hp').2.1]
  refine keptEdgeWitness_letter tgba sysSucc sysLabel keep p p' (fun _ => true) ?_
  obtain ⟨st, hst, t, ht, hc, h1, h2⟩ := (succsFrom_mem_iff _ _ _ _ _).mp hp'
  exact ⟨(st, t), (mem_realizationsFrom_iff _ _ _ _ _ _).mpr ⟨⟨hst, h1⟩, ht, h2, hc⟩, rfl⟩

/-- `keptEdgeWitness_letter` at the `markEdge` projection, in the same edge-relative shape. -/
theorem keptEdgeWitness_markEdge_letter (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) (sysInit : List SysState)
    (p p' : SysState × Nat) (hp' : p' ∈ keptSuccs tgba sysSucc sysLabel keep p) (m : Nat)
    (hlt : m < tgba.numAcceptSets) (hm : m ∈ keptEdgeMarks tgba sysSucc sysLabel keep p p') :
    keep (LSys.letter
        (sysLabel ((keptEdgeWitness tgba sysSucc sysLabel keep sysInit).markEdge p p' m).1)
        ((keptEdgeWitness tgba sysSucc sysLabel keep sysInit).markEdge p p' m).2.1.1) = true := by
  rw [show ((keptEdgeWitness tgba sysSucc sysLabel keep sysInit).markEdge p p' m).1 = p.1 from
    congrArg Prod.fst
      ((keptEdgeWitness tgba sysSucc sysLabel keep sysInit).markEdge_spec hlt hp' hm).2.1]
  exact keptEdgeWitness_letter tgba sysSucc sysLabel keep p p' _
    (exists_keptRealization_of_mark tgba sysSucc sysLabel keep p p' m hm)

attribute [irreducible] keptEdgeWitness

/-! ## From an accepting run to a lasso -/

/-- The product-state sequence an accepting product run walks starts initial, steps along `getSuccessors`, and
carries every mark infinitely often. -/
theorem acceptingRun_states (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : Lentil.exec (Edge SysState α)}
    (hrun : (toSpec tgba sysSucc sysLabel sysInit).isRun σ)
    (hacc : (toSpec tgba sysSucc sysLabel sysInit).isAcceptingRun σ) :
    ((σ 0).1, (σ 0).2.2.1) ∈ initialStates tgba sysInit ∧
    (∀ n, ((σ (n + 1)).1, (σ (n + 1)).2.2.1) ∈
      getSuccessors tgba sysSucc sysLabel ((σ n).1, (σ n).2.2.1)) ∧
    ∀ m, m < tgba.numAcceptSets → ∀ N, ∃ n ≥ N, m ∈ edgeMarks tgba sysSucc sysLabel
      ((σ n).1, (σ n).2.2.1) ((σ (n + 1)).1, (σ (n + 1)).2.2.1) := by
  obtain ⟨hinit, hstep⟩ := hrun
  refine ⟨hinit, fun n => ?_, fun m hm N => ?_⟩
  · obtain ⟨⟨ht, hc, hsys⟩, hlink⟩ := hstep n
    have h1 : (σ n).2.1.2 = (σ (n + 1)).1 := congrArg Prod.fst hlink
    have h2 : (σ n).2.2.2.target = (σ (n + 1)).2.2.1 := congrArg Prod.snd hlink
    exact (getSuccessors_mem_iff tgba sysSucc sysLabel).mpr
      ⟨(σ n).2.1, hsys, (σ n).2.2.2, ht, hc, h1, h2⟩
  · obtain ⟨j, hj⟩ := hacc ⟨m, hm⟩ N
    obtain ⟨⟨ht, hc, hsys⟩, hlink⟩ := hstep (N + j)
    have h1 : (σ (N + j)).2.1.2 = (σ (N + j + 1)).1 := congrArg Prod.fst hlink
    have h2 : (σ (N + j)).2.2.2.target = (σ (N + j + 1)).2.2.1 := congrArg Prod.snd hlink
    refine ⟨N + j, by omega, Std.HashSet.mem_iff_contains.mpr
      ((mem_edgeMarks_iff tgba sysSucc sysLabel _ _ m).mpr
        ⟨((σ (N + j)).2.1, (σ (N + j)).2.2.2), ?_, hj⟩)⟩
    exact (mem_realizations_iff tgba sysSucc sysLabel _ _ _).mpr ⟨⟨hsys, h1⟩, ht, h2, hc⟩

theorem exists_TAcceptingCycle_of_acceptingRun (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState)
    (fr : FiniteReach (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel))
    {σ : Lentil.exec (Edge SysState α)}
    (hrun : (toSpec tgba sysSucc sysLabel sysInit).isRun σ)
    (hacc : (toSpec tgba sysSucc sysLabel sysInit).isAcceptingRun σ) :
    ∃ _ac : TAcceptingCycle (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel)
      (edgeMarks tgba sysSucc sysLabel) tgba.numAcceptSets, True :=
  have h := acceptingRun_states tgba sysSucc sysLabel sysInit hrun hacc
  exists_TAcceptingCycle_of_run fr (σ := fun n => ((σ n).1, (σ n).2.2.1)) h.1 h.2.1 h.2.2

end TGBAProduct

/-! ## Lasso witness -/

/-- The `TGBAProduct.toSpec` specialization of `TAcceptingCycle.toTValidLassoOf`. -/
theorem TAcceptingCycle.toTValidLassoProduct {α : Type u} {SysState : Type v} [BEq α] [Hashable α]
    [BEq SysState] [Hashable SysState] [LawfulBEq SysState] {tgba : TGBA α}
    {sysSucc : SysState → Array (LStep α SysState)} {sysLabel : SysState → Std.HashSet α}
    {sysInit : List SysState}
    (ac : TAcceptingCycle (TGBAProduct.initialStates tgba sysInit)
      (TGBAProduct.getSuccessors tgba sysSucc sysLabel)
      (TGBAProduct.edgeMarks tgba sysSucc sysLabel) tgba.numAcceptSets) :
    TValidLasso (TGBAProduct.toSpec tgba sysSucc sysLabel sysInit)
      (stemEdges (TGBAProduct.edgeWitness tgba sysSucc sysLabel sysInit).stepEdge ac.stem)
      (ac.cycleE (TGBAProduct.edgeWitness tgba sysSucc sysLabel sysInit)) :=
  ac.toTValidLassoOf (TGBAProduct.edgeWitness tgba sysSucc sysLabel sysInit) (fun hs => hs)

namespace TGBAProduct

/-- The counterexample a product cycle describes: one labelled system run whose letters the automaton accepts.
A predicate holding at every cycle state holds past the stem, and one holding at some cycle state infinitely
often. -/
theorem exists_run_of_TAcceptingCycle {α : Type u} {SysState : Type v} [BEq α] [Hashable α]
    [LawfulBEq α] [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState)
    (ac : TAcceptingCycle (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel)
      (edgeMarks tgba sysSucc sysLabel) tgba.numAcceptSets) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      tgba.toSpec.accepts (LSys.valuation sysLabel ρ) ∧
      (∀ P : SysState → Prop, (∀ p ∈ ac.cycle, P p.1) → ∃ N, ∀ n, N ≤ n → P (ρ n).1) ∧
      (∀ P : SysState → Prop, (∃ p ∈ ac.cycle, P p.1) → ∀ n, ∃ j, P (ρ (n + j)).1) := by
  obtain ⟨hρrun, hlang⟩ := gsp_correct1 tgba sysSucc sysLabel sysInit
    ⟨ac.toTValidLassoProduct.run_isRun, ac.toTValidLassoProduct.run_isAccepting⟩
  refine ⟨fun n => ((ac.toTValidLassoProduct.run n).1, (ac.toTValidLassoProduct.run n).2.1),
    hρrun, hlang, fun P hP => ?_, fun P hP n => ?_⟩
  · refine ⟨(stemEdges (edgeWitness tgba sysSucc sysLabel sysInit).stepEdge ac.stem).length,
      fun n hn => ?_⟩
    obtain ⟨i, hi, hsrc⟩ := TValidLasso.run_src_mem_cycle
      (edgeWitness tgba sysSucc sysLabel sysInit) ac ac.toTValidLassoProduct n (by omega)
    have hPi := hP _ (List.getElem_mem hi)
    rw [← hsrc] at hPi
    exact hPi
  · obtain ⟨p, hp, hPp⟩ := hP
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
    obtain ⟨t, ht⟩ := TValidLasso.run_src_hits_cycle (edgeWitness tgba sysSucc sysLabel sysInit)
      ac ac.toTValidLassoProduct i hi n
    rw [← ht] at hPp
    exact ⟨t, hPp⟩

end TGBAProduct

end LTLLib
