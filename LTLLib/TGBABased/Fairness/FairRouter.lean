/-
  Model checking under fairness, with every fairness conjunct hoisted out of the property. The negated property
  `φ.toNNF false` is split at its conjunctions. A conjunct that is a fairness ([LSFZ16, Definition 1], `NNF.isFairness`)
  and flattens into `LTL(F, G)` contributes its fair normal form, which becomes marks and a region on the product and
  never reaches the translator. Every other conjunct is translated through `keptProperty`, exactly as without hoisting.

  `NNF.isFairness` is a sound but incomplete syntactic approximation of [LSFZ16, Definition 1]'s class, closed under
  negation, so a fairness property is hoisted alongside the assumption. A disjunction is hoisted whole or not at all. A
  fairness that does not flatten, such as `FG(a ∨ X(b U c))`, is kept, [LSFZ16, Theorem 4] would cover it.

  Routes, all translating with `ltl3ba`:
  - `modelCheckUnderFairness`: crosses the per-conjunct normal forms, one latched check per disjunct
  - `modelCheckUnderFairnessPrune`: decides the uncrossed conjuncts per SCC in one pass, without the latch
  - `modelCheckUnderFairnessFlat`: the prune with only flat fairness hoisted, the conjuncts TLC, PAT and NuSMV recognise

  Defines:
  - `checkDisjuncts`: the short-circuiting fold over the disjuncts of a fair normal form
  - `hoistConjunct`, `hoistFairness`: the split into hoisted normal forms and kept conjuncts
  - `isFlatLeaf`, `isFlatFairness`, `hoistFlat`: the split a state-predicate classifier makes
  - `keptProperty`: the kept conjuncts as one property, `⊤` when there are none
  - `hoistedOptions`, `streettRSpecOf`: the hoisted conjuncts as an `RStreettSpec`, whose regions select
    *steps* by the letter they read, so a hoisted `FG ψ` may mention an edge atom
  - `modelCheckCrossSplit`, `modelCheckPruneSplit`: the crossing and the prune with the split given

  Proves:
  - `hoistFairness_correct`, `hoistFlat_correct`: both splits preserve meaning
  - `modelCheckUnderFairness_empty_unsat`: (Soundness) an `.empty` result means every run of `sys` satisfies `φ`
  - `modelCheckUnderFairness_nonEmpty_sat`: (Completeness) a `.nonEmpty` result yields a run violating `φ`
  - the same two for `modelCheckUnderFairnessPrune`, `modelCheckUnderFairnessFlat`, `modelCheckCrossSplit` and `modelCheckPruneSplit`

  References:
  - [LSFZ16] Li, Song, Feng, Zhang. Verify LTL with Fairness Assumptions Efficiently. arXiv:1606.08116, 2016.

  Sections:
  - Folding over disjuncts
  - Splitting the negated property
  - Model checking under fairness
  - Soundness
  - Completeness
  - Routes
-/
import LTLLib.AbstractSpec.EmptinessCheck
import LTLLib.LTL.FairClass
import LTLLib.LTL.FairNormalForm
import LTLLib.LTL.Semantics
import LTLLib.LTL.Syntax
import LTLLib.Product
import LTLLib.TGBABased.AbstractSpec.EmptinessCheck
import LTLLib.TGBABased.DijkstraCheck
import LTLLib.TGBABased.Fairness.FairCheck
import LTLLib.TGBABased.Fairness.StreettOptsProduct
import LTLLib.TGBABased.Fairness.StreettRegionProduct
import LTLLib.TGBABased.LTLtoTGBA.Pipeline
import LTLLib.TGBABased.SCC.DijkstraSCC
import LTLLib.TGBABased.SCC.StreettPrune
import LTLLib.TGBABased.SCC.StreettPruneFastP

namespace LTLLib

/-! ## Folding over disjuncts -/

section Disjuncts

variable {α : Type u} {P : Type v}

/-- Check every disjunct, stopping at the first counterexample. The explored-state counts of an exhausted
run are summed. -/
def checkDisjuncts (f : NNF.FairDisjunct α → EmptinessResult P) :
    List (NNF.FairDisjunct α) → EmptinessResult P
  | [] => .empty 0
  | d :: ds =>
    match f d with
    | .nonEmpty stem loop => .nonEmpty stem loop
    | .empty n =>
      match checkDisjuncts f ds with
      | .nonEmpty stem loop => .nonEmpty stem loop
      | .empty m => .empty (n + m)

theorem checkDisjuncts_empty {f : NNF.FairDisjunct α → EmptinessResult P} :
    ∀ {ds : List (NNF.FairDisjunct α)} {n : Nat}, checkDisjuncts f ds = .empty n →
      ∀ d ∈ ds, ∃ m, f d = .empty m := by
  intro ds
  induction ds with
  | nil => simp
  | cons d ds ih =>
    intro n h e he
    rw [checkDisjuncts] at h
    split at h
    · simp at h
    · next n' hfd =>
      split at h
      · simp at h
      · next m hrec =>
        rcases List.mem_cons.mp he with rfl | hm
        · exact ⟨n', hfd⟩
        · exact ih hrec e hm

theorem checkDisjuncts_nonEmpty {f : NNF.FairDisjunct α → EmptinessResult P} :
    ∀ {ds : List (NNF.FairDisjunct α)} {stem loop : List P},
      checkDisjuncts f ds = .nonEmpty stem loop → ∃ d ∈ ds, f d = .nonEmpty stem loop := by
  intro ds
  induction ds with
  | nil => simp [checkDisjuncts]
  | cons d ds ih =>
    intro stem loop h
    rw [checkDisjuncts] at h
    split at h
    · next s l hfd =>
      cases h
      exact ⟨d, by simp, hfd⟩
    · next n' hfd =>
      split at h
      · next s l hrec =>
        cases h
        obtain ⟨e, he, hfe⟩ := ih hrec
        exact ⟨e, by simp [he], hfe⟩
      · simp at h

end Disjuncts

/-! ## Splitting the negated property -/

section Split

variable {α : Type u} [DecidableEq α]

/-- The fair normal form of one conjunct, `none` when it is not a fairness or does not flatten. -/
def hoistConjunct (c : NNF α) : Option (List (NNF.FairDisjunct α)) :=
  if c.isFairness then NNF.fnf c else none

/-- Split conjuncts into the normal forms that get hoisted onto the product, and the ones that stay in the
property. -/
def hoistFairness : List (NNF α) → List (List (NNF.FairDisjunct α)) × List (NNF α)
  | [] => ([], [])
  | c :: cs =>
    match hoistConjunct c, hoistFairness cs with
    | some ds, (dss, kept) => (ds :: dss, kept)
    | none, (dss, kept) => (dss, c :: kept)

/-- A hoisted conjunct is equivalent to the disjunction of its normal form. -/
theorem hoistConjunct_correct {c : NNF α} {ds : List (NNF.FairDisjunct α)}
    (h : hoistConjunct c = some ds) (ξ : OmegaWord α) :
    c.satisfies ξ ↔ ∃ d ∈ ds, NNF.FairDisjunct.holds ξ d := by
  rw [hoistConjunct] at h
  split at h
  · next hfair => exact NNF.fnf_correct hfair h ξ
  · exact absurd h (by simp)

/-- The split preserves meaning, the hoisted conjuncts through their normal forms and the kept ones directly. -/
theorem hoistFairness_correct (ξ : OmegaWord α) (cs : List (NNF α)) :
    (∀ c ∈ cs, c.satisfies ξ) ↔
      ((∀ ds ∈ (hoistFairness cs).1, ∃ d ∈ ds, NNF.FairDisjunct.holds ξ d) ∧
        ∀ c ∈ (hoistFairness cs).2, c.satisfies ξ) := by
  induction cs with
  | nil => simp [hoistFairness]
  | cons c cs ih =>
    rw [hoistFairness]
    split
    · next ds dss kept hc hrec =>
      rw [hrec] at ih
      simp only [List.forall_mem_cons, ih, hoistConjunct_correct hc ξ]
      grind
    · next dss kept hc hrec =>
      rw [hrec] at ih
      simp only [List.forall_mem_cons, ih]
      grind

/-- A leaf a state-predicate classifier recognises: `□◇p` or `◇□p` for a propositional `p`, or `□p`, `◇p`. -/
def isFlatLeaf (c : NNF α) : Bool :=
  (NNF.asFGPart c).isSome || (NNF.asGFPart c).isSome ||
    (match c with
      | .release φ ψ => φ.isBot && (NNF.asGFPart ψ).isSome
      | .until φ ψ => φ.isTop && (NNF.asFGPart ψ).isSome
      | _ => false)

/-- A Boolean combination of flat leaves, what TLC's `classifyExpr`, PAT's classifier and NuSMV's `JUSTICE` and
`COMPASSION` recognise as fairness. A nested condition such as `□◇(r ∧ ◇w)` is not flat. -/
def isFlatFairness : NNF α → Bool
  | .and a b => isFlatFairness a && isFlatFairness b
  | .or a b => isFlatFairness a && isFlatFairness b
  | c => isFlatLeaf c

/-- The split those classifiers make, only flat conjuncts hoisted and every other conjunct kept. -/
def hoistFlat (cs : List (NNF α)) : List (List (NNF.FairDisjunct α)) × List (NNF α) :=
  ((hoistFairness (cs.filter isFlatFairness)).1,
    (hoistFairness (cs.filter isFlatFairness)).2 ++ cs.filter fun c => !isFlatFairness c)

/-- The flat split preserves meaning. -/
theorem hoistFlat_correct (ξ : OmegaWord α) (cs : List (NNF α)) :
    (∀ c ∈ cs, c.satisfies ξ) ↔
      ((∀ ds ∈ (hoistFlat cs).1, ∃ d ∈ ds, NNF.FairDisjunct.holds ξ d) ∧ ∀ c ∈ (hoistFlat cs).2, c.satisfies ξ) := by
  unfold hoistFlat
  simp only [List.mem_append, or_imp, forall_and]
  rw [← and_assoc, ← hoistFairness_correct]
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_of_mem_filter hc), fun c hc => h c (List.mem_of_mem_filter hc)⟩
  · rintro ⟨h1, h2⟩ c hc
    by_cases hf : isFlatFairness c = true
    · exact h1 c (List.mem_filter.mpr ⟨hc, hf⟩)
    · exact h2 c (List.mem_filter.mpr ⟨hc, by simpa using hf⟩)

end Split

/-! ## Choosing between the prune and the crossing

The prune's witness contract asks that every hoisted region be `LSys.StateOnly` (`EdgeLabels.md` §12.4).
A caller does not check that semantically: it knows which atoms a *step* may contribute — in Veil, exactly
the `T(…)` indices — and checks that no region mentions one. That is a decidable test on the regions the
route actually hands the prune, which is the only reliable place to apply it: the routes hoist
differently, and disjunctive hoisting *adds* options after the first split (§12.6, step 6). -/

section Routing

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]

/-- No hoisted region mentions an atom that `edgeAtom` marks. Decidable, and exactly the premise of
`stateOnly_of_regionsAvoid`. -/
def regionsAvoid (edgeAtom : α → Bool) (dss : List (List (NNF.FairDisjunct α))) : Bool :=
  dss.all fun ds => ds.all fun d => d.1.atoms.all fun a => !edgeAtom a

/-- The syntactic discharge of the prune's hypothesis: if every atom a step can contribute is one
`edgeAtom` marks, and no region mentions such an atom, then every region is `StateOnly`. -/
theorem stateOnly_of_regionsAvoid [LawfulBEq α] [LawfulHashable α] {edgeAtom : α → Bool}
    {sysSucc : SysState → Array (LStep α SysState)} {sysLabel : SysState → Std.HashSet α}
    {dss : List (List (NNF.FairDisjunct α))}
    (hsteps : ∀ s, ∀ st ∈ LSys.totalize sysSucc s, ∀ a ∈ st.1, edgeAtom a = true)
    (h : regionsAvoid edgeAtom dss = true) :
    ∀ ds ∈ dss, ∀ d ∈ ds, LSys.StateOnly sysSucc sysLabel d.1.eval := by
  intro ds hds d hd
  refine LSys.stateOnly_of_neverStepAtom fun s st hst a ha hmem => ?_
  have havoid : (!edgeAtom a) = true :=
    List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h ds hds) d hd) a ha
  rw [hsteps s st hst a hmem] at havoid
  exact absurd havoid (by simp)

omit [BEq α] [Hashable α] in
/-- `regionsAvoid` on an append, which is the shape the re-hoisting routes need. -/
theorem regionsAvoid_append {edgeAtom : α → Bool} {dss ess : List (List (NNF.FairDisjunct α))} :
    regionsAvoid edgeAtom (dss ++ ess) = true ↔
      regionsAvoid edgeAtom dss = true ∧ regionsAvoid edgeAtom ess = true := by
  simp [regionsAvoid, List.all_eq_true]

end Routing

/-! ## Model checking under fairness

Both searches take the split given, `kept` being the property the translator receives and `dss` the hoisted conjuncts. -/

section Kept

variable {α : Type u}

/-- The kept conjuncts as one property, negated because the translator negates what it is given. -/
def keptProperty (cs : List (NNF α)) : Formula α := .not (Formula.conj (cs.map NNF.toFormula))

theorem directSatisfies_keptProperty (ξ : OmegaWord α) (cs : List (NNF α)) :
    (keptProperty cs).directSatisfies ξ ↔ ¬ ∀ c ∈ cs, c.satisfies ξ := by
  simp only [keptProperty, Formula.directSatisfies, Formula.directSatisfies_conj]
  refine not_congr ⟨fun h n hn => (NNF.directSatisfies_toFormula ξ n).mp (h _ (List.mem_map_of_mem hn)),
    fun h c hc => ?_⟩
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hc
  exact (NNF.directSatisfies_toFormula ξ n).mpr (h n hn)

end Kept

variable {α : Type u} {SysState : Type v} [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [Inhabited SysState]
  [BEq α] [Hashable α]

/-- The hoisted conjuncts as options, one entry per conjunct and one option per disjunct. -/
def hoistedOptions (dss : List (List (NNF.FairDisjunct α))) :
    Array (Array (StreettOption (Std.HashSet α))) :=
  dss.toArray.map fun ds => ds.toArray.map fun d =>
    { region := d.1.eval, marks := d.2.toArray.map (·.eval) }

/-- The hoisted conjuncts as an `RStreettSpec` over the product. The regions select *steps* by the letter
they read rather than states by their label, which is what lets a hoisted `FG ψ` mention an edge atom
(`EdgeLabels.md` §6.5). For the state-labelled systems this route is wired to, every step out of `s` reads
`sysLabel s` and the two readings coincide — that collapse is `TGBAProduct.acceptingRRun_lets_unlabelled`
and `TGBAProduct.region_of_mem_keptSuccs_unlabelled`. -/
def streettRSpecOf (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (dss : List (List (NNF.FairDisjunct α))) :
    RStreettSpec (SysState × Nat) (Std.HashSet α) :=
  TGBAProduct.streettRSpecOf tgba sysSucc sysLabel tgba.numAcceptSets (hoistedOptions dss)

omit [LawfulBEq SysState] [Inhabited SysState] in
@[simp] theorem streettRSpecOf_regionSuccs (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (dss : List (List (NNF.FairDisjunct α))) (r : Std.HashSet α → Bool) :
    (streettRSpecOf tgba sysSucc sysLabel dss).regionSuccs r
      = TGBAProduct.keptSuccs tgba sysSucc sysLabel r := rfl

omit [LawfulBEq SysState] [Inhabited SysState] in
@[simp] theorem streettRSpecOf_conjuncts (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (dss : List (List (NNF.FairDisjunct α))) :
    (streettRSpecOf tgba sysSucc sysLabel dss).conjuncts = hoistedOptions dss := rfl

/-- The prune with the split supplied rather than derived, `kept` going to the translator.

Reads a *labelled* system, but with an asymmetry between its two contracts that is the whole subject of
`EdgeLabels.md` §12, and worth stating here because it decides which routes may call this.

- `modelCheckPruneSplit_empty_unsat` needs **nothing**. The per-SCC test decides each conjunct's options
  independently, which *over-approximates* acceptance once regions select steps; so a verdict of `.empty`
  means the scan could not satisfy even the over-approximation, and a fortiori no run satisfies the real
  condition. Soundness is free.
- `modelCheckPruneSplit_nonEmpty_sat` needs every hoisted region to be `LSys.StateOnly`. Without it two
  conjuncts can be available through *different* realizations of the same edges and the reported
  counterexample need not exist — `Tests/PruneJointRegions.lean` is the worked case. Deciding jointness
  exactly is NP-hard (§12.1), so the hypothesis is the affordable answer rather than a stopgap, and the
  properties that violate it are routed to the crossing (§12.6). -/
def modelCheckPruneSplit (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) : EmptinessResult (SysState × Nat) :=
  match ltl3ba (kept.toNNF false) with
  | some tgba =>
    -- §13.20: the fast path. The DFS expands through `expandWithOpts`, whose payload carries each
    -- edge's option bits, and POP scans retained frames instead of calling `succs` and the spec's
    -- region predicates. `modelCheckPruneSplit_eq` below is the bridge to the proved `streettCheck`
    -- (§13.22), and every soundness theorem of this route goes through that one rewrite.
    let cs := CompiledSpec.of (streettRSpecOf tgba sysSucc sysLabel dss)
    -- §13.30: the position-carrying driver; `streettCheckP_eq` bridges it to `streettCheckF`.
    streettCheckP cs
      (TGBAProduct.getSuccessors tgba sysSucc sysLabel)
      (TGBAProduct.edgeMarks tgba sysSucc sysLabel)
      (TGBAProduct.expandWithOpts tgba sysSucc sysLabel cs)
      (TGBAProduct.keptExpandWithOpts tgba sysSucc sysLabel cs)
      (TGBAProduct.initialStates tgba sysInit)
  | none => .empty 0

/-! ## The same route, from one system callback

`modelCheckPruneSplitOfStep` is `modelCheckPruneSplit` with `LSys.StepFn` in place of the
`sysSucc`/`sysLabel` pair: the product's transitions out of a state are computed once, as a fact about
the type rather than a memo installed behind `@[implemented_by]`. The bridge is `rfl` — Lean's
definitional eta for structures makes `fun s => ((f s).1, (f s).2)` the same term as `f` — so every
soundness theorem below transfers by one rewrite and none of them is restated. `EdgeLabels.md` §15. -/

def streettRSpecOfStep (tgba : TGBA α) (sysStep : LSys.StepFn α SysState)
    (dss : List (List (NNF.FairDisjunct α))) : RStreettSpec (SysState × Nat) (Std.HashSet α) :=
  TGBAProduct.streettRSpecOfStep tgba sysStep tgba.numAcceptSets (hoistedOptions dss)

theorem streettRSpecOfStep_eq (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (dss : List (List (NNF.FairDisjunct α))) :
    streettRSpecOfStep tgba (fun s => (sysSucc s, sysLabel s)) dss
      = streettRSpecOf tgba sysSucc sysLabel dss := rfl

def modelCheckPruneSplitOfStep (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysStep : LSys.StepFn α SysState) :
    EmptinessResult (SysState × Nat) :=
  match ltl3ba (kept.toNNF false) with
  | some tgba =>
    let cs := CompiledSpec.of (streettRSpecOfStep tgba sysStep dss)
    streettCheckP cs
      (TGBAProduct.getSuccessorsOfStep tgba sysStep)
      (TGBAProduct.edgeMarksOfStep tgba sysStep)
      (TGBAProduct.expandWithOptsOfStep tgba sysStep cs)
      (TGBAProduct.keptExpandWithOptsOfStep tgba sysStep cs)
      (TGBAProduct.initialStates tgba sysInit)
  | none => .empty 0

theorem modelCheckPruneSplitOfStep_eq (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) :
    modelCheckPruneSplitOfStep kept dss sysInit (fun s => (sysSucc s, sysLabel s))
      = modelCheckPruneSplit kept dss sysInit sysSucc sysLabel := rfl

/-- The fast path computes what the proved route computes (§13.22). Nothing else in the tree unfolds
`modelCheckPruneSplit`, so every soundness theorem of the fair routes goes through this one rewrite.
`streettCheckF_eq` does the work; the product supplies `expandWithOpts`'s coherence (definitional) and
the fact that its payload is `edgeBits` edge by edge (`optBitsFor_eq`). -/
theorem modelCheckPruneSplit_eq [LawfulHashable SysState] (kept : Formula α)
    (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) {tgba : TGBA α} (htg : ltl3ba (kept.toNNF false) = some tgba) :
    modelCheckPruneSplit kept dss sysInit sysSucc sysLabel =
      streettCheck (CompiledSpec.of (streettRSpecOf tgba sysSucc sysLabel dss))
        (TGBAProduct.getSuccessors tgba sysSucc sysLabel)
        (TGBAProduct.edgeMarks tgba sysSucc sysLabel)
        (TGBAProduct.expand tgba sysSucc sysLabel)
        (TGBAProduct.initialStates tgba sysInit) := by
  unfold modelCheckPruneSplit
  rw [htg]
  refine (streettCheckP_eq _ _ _ _ _ _).trans ?_
  exact streettCheckF_eq (CompiledSpec.of (streettRSpecOf tgba sysSucc sysLabel dss))
    (CompiledSpec.of_wf _) _ _ _ _
    (TGBAProduct.expand_coherent tgba sysSucc sysLabel)
    (TGBAProduct.expandWithOpts_coherent tgba sysSucc sysLabel _)
    (TGBAProduct.expandWithOpts_bits tgba sysSucc sysLabel
      (CompiledSpec.of (streettRSpecOf tgba sysSucc sysLabel dss)) (CompiledSpec.of_wf _) (fun _ => rfl))
    _ (TGBAProduct.keptExpandWithOpts_coherent tgba sysSucc sysLabel _)
    (TGBAProduct.keptExpandWithOpts_bits tgba sysSucc sysLabel
      (CompiledSpec.of (streettRSpecOf tgba sysSucc sysLabel dss)) (CompiledSpec.of_wf _)
      (fun _ => rfl) (fun _ => rfl))
    _

variable [LawfulBEq α] [LawfulHashable α] [DecidableEq α]

/-- The crossing with the split supplied rather than derived, one latched check per disjunct of the crossed `dss`.

Reads a *labelled* system, so a hoisted `◇□ψ` or `□◇ψ` may mention an edge atom such as `taken(a)`: the
latch's region and its extra marks are both decided on the letter each step contributes
(`EdgeLabels.md` §6.5). A system with no edge atoms is passed as `LSys.unlabelled sysSucc`. -/
def modelCheckCrossSplit (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    (checker : TEmptinessChecker ((SysState × Nat) × Bool) := dijkstraTChecker)
    (sysChecker : TEmptinessChecker (SysState × Bool) := dijkstraTChecker) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  checkDisjuncts (fun d => modelCheckTGBADisjunctFast kept d.1 d.2 sysInit sysSucc sysLabel sysFR checker sysChecker)
    (NNF.crossAllDNF dss)

/-- `modelCheckCrossSplit` over one system callback. §15 -/
def modelCheckCrossSplitOfStep (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysStep : LSys.StepFn α SysState)
    (sysFR : FiniteReach sysInit (LSys.targets fun s => (sysStep s).1))
    (checker : TEmptinessChecker ((SysState × Nat) × Bool) := dijkstraTChecker)
    (sysChecker : TEmptinessChecker (SysState × Bool) := dijkstraTChecker) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  checkDisjuncts (fun d => modelCheckTGBADisjunctFastOfStep kept d.1 d.2 sysInit sysStep sysFR
    checker sysChecker) (NNF.crossAllDNF dss)

theorem modelCheckCrossSplitOfStep_eq (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool)) :
    modelCheckCrossSplitOfStep kept dss sysInit (fun s => (sysSucc s, sysLabel s)) sysFR checker
        sysChecker
      = modelCheckCrossSplit kept dss sysInit sysSucc sysLabel sysFR checker sysChecker := rfl

/-! ## Soundness -/

/-- Soundness of the crossing with the split given: an `.empty` result means every run satisfying the hoisted
conjuncts satisfies the kept property. -/
theorem modelCheckCrossSplit_empty_unsat (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool)) {n : Nat}
    (h : modelCheckCrossSplit kept dss sysInit sysSucc sysLabel sysFR checker sysChecker = .empty n)
    (ρ : Nat → LSys.Edge α SysState) (hρ : (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ)
    (hdss : ∀ ds ∈ dss, ∃ d ∈ ds, NNF.FairDisjunct.holds (LSys.valuation sysLabel ρ) d) :
    Formula.directSatisfies (LSys.valuation sysLabel ρ) kept := by
  obtain ⟨d, hd, hholds⟩ := (NNF.holds_crossAllDNF (LSys.valuation sysLabel ρ) _).mpr hdss
  obtain ⟨m, hm⟩ := checkDisjuncts_empty h d hd
  exact modelCheckTGBADisjunctFast_empty_unsat _ d.1 d.2 sysInit sysSucc sysLabel sysFR checker sysChecker hm ρ hρ
    hholds.1 hholds.2

/-- Soundness of the prune with the split given: an `.empty` result means every run satisfying the hoisted
conjuncts satisfies the kept property. -/
theorem modelCheckPruneSplit_empty_unsat [LawfulHashable SysState] (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc)) {n : Nat}
    (h : modelCheckPruneSplit kept dss sysInit sysSucc sysLabel = .empty n)
    (ρ : Nat → LSys.Edge α SysState) (hρ : (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ)
    (hdss : ∀ ds ∈ dss, ∃ d ∈ ds, NNF.FairDisjunct.holds (LSys.valuation sysLabel ρ) d) :
    Formula.directSatisfies (LSys.valuation sysLabel ρ) kept := by
  by_contra hviolate
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome (kept.toNNF false))
  rw [modelCheckPruneSplit_eq kept dss sysInit sysSucc sysLabel htg] at h
  obtain ⟨σ, hproj, hrun, hacc⟩ := TGBAProduct.gsp_correct2 _ sysSucc sysLabel sysInit hρ
    ((ltl3ba_accepts _ htg _).mpr ((Formula.toNNF_correct_neg _ kept).mp hviolate))
  subst hproj
  have hFR := TGBAProduct.finiteReach tgba (ltl3ba_wellFormed _ htg) sysSucc sysLabel sysInit sysFR
  have hcompat := TGBAProduct.streettRSpecOf_compat tgba sysSucc sysLabel
    tgba.numAcceptSets (hoistedOptions dss)
  refine streettCheck_empty_no_fairSCC _ _ _ hcompat _
    (TGBAProduct.expand_coherent tgba sysSucc sysLabel) _
    (fun p p' m hm => TGBAProduct.edgeMarks_lt tgba sysSucc sysLabel
      (ltl3ba_marks_lt _ htg) p p' m hm) hFR h
    (Nonempty.some (exists_RFairSCC_of_run hcompat hFR
      (TGBAProduct.acceptingRRun tgba sysSucc sysLabel sysInit
        tgba.numAcceptSets (hoistedOptions dss) hrun)
      (TGBAProduct.acceptingRRun_marks tgba sysSucc sysLabel sysInit
        tgba.numAcceptSets (hoistedOptions dss) hrun hacc (Nat.le_refl _)) ?_))
  -- No collapse is needed in this direction, and that is the point: the `RRun`'s letters *are* the ones
  -- the run reads, so the hypothesis transfers with nothing in between. `LSys.StateOnly` is required only
  -- by the witness direction, where separately available options have to be jointly available
  -- (`EdgeLabels.md` §12).
  intro c hc
  obtain ⟨ds, hds, rfl⟩ := Array.mem_map.mp hc
  obtain ⟨d, hd, hfg, hgf⟩ := hdss ds (by simpa using hds)
  refine ⟨_, Array.mem_map_of_mem (by simpa using hd), ?_, fun g hg K => ?_⟩
  · exact (TGBAProduct.eventuallyAlways_iff_indexed_letters d.1 _).mp hfg
  · obtain ⟨b, hb, rfl⟩ := Array.mem_map.mp hg
    obtain ⟨j, hj⟩ := (BoolFormula.satisfies_alwaysEventually _ b).mp (hgf b (by simpa using hb)) K
    exact ⟨K + j, by omega, (BoolFormula.eval_iff_holds b _).mpr hj⟩

/-! ## Completeness -/

/-- Completeness of the crossing with the split given: a reported witness is a run satisfying every hoisted
conjunct through one of its disjuncts and violating the kept property. -/
theorem modelCheckCrossSplit_nonEmpty_sat (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool))
    {stem loop : List ((SysState × Nat) × Bool)}
    (h : modelCheckCrossSplit kept dss sysInit sysSucc sysLabel sysFR checker sysChecker = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      (∀ ds ∈ dss, ∃ d ∈ ds, NNF.FairDisjunct.holds (LSys.valuation sysLabel ρ) d) ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) kept := by
  obtain ⟨d, hd, hcall⟩ := checkDisjuncts_nonEmpty h
  obtain ⟨ρ, hρ, hfg, hgf, hviol⟩ := modelCheckTGBADisjunctFast_nonEmpty_sat _ d.1 d.2
    sysInit sysSucc sysLabel sysFR checker sysChecker hcall
  exact ⟨ρ, hρ, (NNF.holds_crossAllDNF _ _).mp ⟨d, hd, hfg, hgf⟩, hviol⟩

set_option maxHeartbeats 1000000 in
/-- Completeness of the prune with the split given: a reported witness is a run satisfying every hoisted
conjunct through one of its options and violating the kept property.

**Unconditional** since `EdgeLabels.md` §14. It used to need `LSys.StateOnly` on every hoisted region,
because the per-SCC scan decides each conjunct's options *independently* and with step regions that is an
over-approximation: separately available options need not be jointly available. The scan still decides
them independently — it is the hot loop — but it no longer licenses a report. A candidate reads every
option *inside* the region its commitments denote, `streettPop` reports only once each conjunct's
selected option is one of those commitments, and `CompiledSpec.fairCycleOpts` re-checks the reported
cycle against that one region. So what comes back is `RStreettSpec.AvailableWith`, which is exactly the
run-level statement below, and the jointness that `StateOnly` used to supply is decided rather than
assumed. §12.1's NP-hardness is unaffected: it is paid by branching, and only over the conjuncts that
need it. -/
theorem modelCheckPruneSplit_nonEmpty_sat (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α)
    {stem loop : List (SysState × Nat)}
    (h : modelCheckPruneSplit kept dss sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      (∀ ds ∈ dss, ∃ d ∈ ds, NNF.FairDisjunct.holds (LSys.valuation sysLabel ρ) d) ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) kept := by
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome (kept.toNNF false))
  rw [modelCheckPruneSplit_eq kept dss sysInit sysSucc sysLabel htg] at h
  obtain ⟨bits, ac, -, hcyc, hfair⟩ := streettCheck_nonEmpty_valid _ (CompiledSpec.of_wf _) _ _ _ _ h
  set cs := (CompiledSpec.of (streettRSpecOf tgba sysSucc sysLabel dss)).atBits bits with hcs
  have hcsspec : cs.spec = streettRSpecOf tgba sysSucc sysLabel dss := rfl
  have hmono : cs.spec.Mono :=
    (TGBAProduct.streettRSpecOf_compat tgba sysSucc sysLabel _ _).toMono
  -- One option per conjunct, as the report-time validator reports them. The validator answers every
  -- conjunct at the *one* predicate `cs.restrict`, which entails each selected option's region because
  -- the report branch only fires on options the candidate had already committed — so what comes back is
  -- `AvailableWith`, not the per-option approximation. `EdgeLabels.md` §12.
  have hsel0 : ∀ ds ∈ dss, ∃ d, d ∈ ds ∧ LePred cs.restrict d.1.eval ∧
      (∀ e ∈ cycleEdges loop.tail,
        e.2 ∈ TGBAProduct.keptSuccs tgba sysSucc sysLabel cs.restrict e.1) ∧
      (∀ g ∈ d.2, ∃ e ∈ cycleEdges loop.tail,
        e.2 ∈ TGBAProduct.keptSuccs tgba sysSucc sysLabel
          (fun l => cs.restrict l && g.eval l) e.1) := by
    intro ds hds
    obtain ⟨i, hi, hci⟩ : ∃ i, ∃ _ : i < cs.spec.conjuncts.size,
        cs.spec.conjuncts[i]! = ds.toArray.map fun d =>
          ({ region := d.1.eval, marks := d.2.toArray.map (·.eval) } :
            StreettOption (Std.HashSet α)) := by
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hds
      have hj' : j < cs.spec.conjuncts.size := by
        show j < (hoistedOptions dss).size
        simpa [hoistedOptions] using hj
      refine ⟨j, hj', ?_⟩
      show (hoistedOptions dss)[j]! = _
      rw [getElem!_pos _ j (by simpa [hoistedOptions] using hj)]
      simp [hoistedOptions]
    obtain ⟨opt, hopt, hle, hregionE, hmarksE⟩ :=
      exists_option_of_fairCycleOpts (CompiledSpec.WF.atBits (CompiledSpec.of_wf _) bits) hmono hfair
        hi
    rw [hci] at hopt
    obtain ⟨d, hd, rfl⟩ := Array.mem_map.mp hopt
    simp only [hcsspec, streettRSpecOf_regionSuccs] at hregionE hmarksE
    refine ⟨d, by simpa using hd, hle, fun e he => hregionE e he, fun g hg => ?_⟩
    exact hmarksE g.eval (Array.mem_map_of_mem (by simpa using hg))
  choose sel hmem hle hR hM using hsel0
  -- the cycle lives in the restricted graph, stated once and not per conjunct
  have hedgeR : ∀ e ∈ cycleEdges loop.tail,
      e.2 ∈ TGBAProduct.keptSuccs tgba sysSucc sysLabel cs.restrict e.1 := by
    intro e he
    have := fairCycleOpts_edges hfair e he
    simpa using this
  have hedgeR' : ∀ e ∈ cycleEdges ac.cycle,
      e.2 ∈ TGBAProduct.keptSuccs tgba sysSucc sysLabel cs.restrict e.1 := by
    rw [hcyc]; exact hedgeR
  -- the region is the reporting candidate's own, and it entails every selected option's
  set selected : List (NNF.FairDisjunct α) := dss.attach.map (fun p => sel p.1 p.2) with hselected
  set r : Std.HashSet α → Bool := cs.restrict with hr
  set extra : List (BoolFormula α) := selected.flatMap (·.2) with hextra
  have hrle : ∀ d ∈ selected, ∀ l, r l = true → d.1.eval l = true := by
    intro d hd l hl
    obtain ⟨⟨ds, hds⟩, -, rfl⟩ := List.mem_map.mp hd
    exact hle ds hds l hl
  -- The reported cycle, read in the region-restricted graph with the selected marks.
  have rc : TRegionCycle (TGBAProduct.initialStates tgba sysInit)
      (TGBAProduct.getSuccessors tgba sysSucc sysLabel)
      (TGBAProduct.keptSuccs tgba sysSucc sysLabel r)
      (TGBAProduct.edgeMarksFair tgba sysSucc sysLabel extra)
      (TGBAProduct.keptEdgeMarksFair tgba sysSucc sysLabel r extra)
      (tgba.numAcceptSets + extra.length) := by
    refine
      { stem := ac.stem
        cycle := ac.cycle
        stem_nonempty := ac.stem_nonempty
        cycle_nonempty := ac.cycle_nonempty
        stem_head_initial := ac.stem_head_initial
        stem_chain := ac.stem_chain
        overlap := ac.overlap
        cycle_chain := ?_
        cycle_back := ?_
        cycle_covers_marks := ?_ }
    -- the cycle's edges: the validator answered them at `r` itself, so there is nothing to transfer
    · intro i hi
      have hmod : (i + 1) % ac.cycle.length = i + 1 := Nat.mod_eq_of_lt (by omega)
      have := hedgeR' _ (mem_cycleEdges_iff.mpr ⟨i, by omega, rfl⟩)
      rw [getElem!_pos ac.cycle i (by omega), hmod,
        getElem!_pos ac.cycle (i + 1) hi] at this
      exact this
    · have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)
      have hq : ac.cycle.length - 1 < ac.cycle.length := by have := ac.cycle_nonempty; omega
      have hmod : (ac.cycle.length - 1 + 1) % ac.cycle.length = 0 := by
        have h1 : ac.cycle.length - 1 + 1 = ac.cycle.length := by have := ac.cycle_nonempty; omega
        rw [h1]; exact Nat.mod_self _
      have := hedgeR' _ (mem_cycleEdges_iff.mpr ⟨ac.cycle.length - 1, hq, rfl⟩)
      rw [getElem!_pos ac.cycle _ hq, hmod,
        getElem!_pos ac.cycle 0 (by have := ac.cycle_nonempty; omega)] at this
      have he1 : ac.cycle[ac.cycle.length - 1] = ac.cycle.getLast hne := by
        rw [List.getLast_eq_getElem hne]
      have he2 : ac.cycle[0]'(by have := ac.cycle_nonempty; omega) = ac.cycle.head hne :=
        (List.head_eq_getElem hne).symm
      rw [he1, he2] at this
      exact this
    · intro m hm
      by_cases hlt : m < tgba.numAcceptSets
      · -- a property mark: the reported lasso was validated against `regionMarks r` in the first
        -- place (`buildResult`), so this is the same fact, not a transfer
        obtain ⟨i, hi, hmi⟩ := ac.cycle_covers_marks m hlt
        refine ⟨i, hi, Std.HashSet.mem_iff_contains.mpr ?_⟩
        simp only [TGBAProduct.keptEdgeMarksFair, Std.HashSet.union_eq,
          Std.HashSet.contains_union, Bool.or_eq_true]
        exact Or.inl (Std.HashSet.mem_iff_contains.mp hmi)
      · -- a selected option's mark: the witnessing realization reads a letter satisfying the option's
        -- region and the mark, and `r` a fortiori, so it survives `fairKeep r extra _`
        have hidx : m - tgba.numAcceptSets < extra.length := by omega
        have hgmem : extra[m - tgba.numAcceptSets] ∈ extra := List.getElem_mem hidx
        obtain ⟨d, hd, hgd⟩ := List.mem_flatMap.mp hgmem
        obtain ⟨⟨ds, hds⟩, -, rfl⟩ := List.mem_map.mp hd
        obtain ⟨e, he, hse⟩ := hM ds hds _ hgd
        obtain ⟨i, hi, rfl⟩ := mem_cycleEdges_iff.mp he
        -- move the witness onto `ac.cycle`; the goal cannot be rewritten the other way, since its
        -- length proof depends on the list
        rw [← hcyc] at hi hse
        have hmod : (i + 1) % ac.cycle.length < ac.cycle.length := Nat.mod_lt _ (by omega)
        rw [getElem!_pos ac.cycle i hi,
          getElem!_pos ac.cycle ((i + 1) % ac.cycle.length) hmod] at hse
        refine ⟨i, hi, Std.HashSet.mem_iff_contains.mpr ?_⟩
        simp only [TGBAProduct.keptEdgeMarksFair, Std.HashSet.union_eq,
          Std.HashSet.contains_union, Bool.or_eq_true]
        refine Or.inr (Std.HashSet.mem_iff_contains.mp
          ((TGBAProduct.mem_fairMarksEdge_iff tgba sysSucc sysLabel r tgba.numAcceptSets extra _ _ m).mpr
            ⟨m - tgba.numAcceptSets, hidx, by omega, Array.contains_iff_mem.mpr ?_⟩))
        -- the same realization, now read against `fairKeep r extra _`
        obtain ⟨st, hst, t, ht, hc, h1, h2⟩ := (TGBAProduct.succsFrom_mem_iff tgba _ _ _ _).mp hse
        obtain ⟨hst', hkeep⟩ := TGBAProduct.mem_keptSteps.mp hst
        refine (TGBAProduct.succsFrom_mem_iff tgba _ _ _ _).mpr
          ⟨st, TGBAProduct.mem_keptSteps.mpr ⟨hst', ?_⟩, t, ht, hc, h1, h2⟩
        have hgi : TGBAProduct.fairConj extra (m - tgba.numAcceptSets)
            = extra[m - tgba.numAcceptSets] :=
          (List.getElem_eq_getD (l := extra) (i := m - tgba.numAcceptSets) .ff).symm
        simp only [TGBAProduct.fairKeep, Bool.and_eq_true, hgi]
        -- the witness realization was found at `r ∧ g`, so it satisfies both halves at once — this is
        -- the jointness the validator now decides, where it used to be inferred from `StateOnly`
        exact ⟨(Bool.and_eq_true _ _).mp hkeep |>.1, (Bool.and_eq_true _ _).mp hkeep |>.2⟩
  obtain ⟨ρ, hρrun, hlang, hfairρ, hregionρ⟩ := TGBAProduct.exists_run_of_TRegionCycle tgba
    sysSucc sysLabel sysInit extra r (ltl3ba_marks_lt _ htg) rc
  refine ⟨ρ, hρrun, fun ds hds => ⟨sel ds hds, hmem ds hds, ?_, ?_⟩,
    fun hsat => (Formula.toNNF_correct_neg _ kept).mpr ((ltl3ba_accepts _ htg _).mp hlang) hsat⟩
  · -- the region: `◇□ r` on the run's letters, and `r` implies each selected option's region
    obtain ⟨N, hN⟩ := hregionρ
    refine (TGBAProduct.eventuallyAlways_iff_indexed_run (sel ds hds).1 sysLabel ρ).mpr ⟨N, fun n hn => ?_⟩
    exact hrle _ (List.mem_map.mpr ⟨⟨ds, hds⟩, List.mem_attach _ _, rfl⟩) _ (hN n hn)
  · -- each mark: it is one of `extra`, and the run reads it infinitely often
    intro b hb
    have hbe : b ∈ extra :=
      List.mem_flatMap.mpr ⟨sel ds hds, List.mem_map.mpr ⟨⟨ds, hds⟩, List.mem_attach _ _, rfl⟩, hb⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hbe
    refine (BoolFormula.satisfies_alwaysEventually _ _).mpr fun n => ?_
    obtain ⟨j, hj⟩ := hfairρ i hi n
    have hgi : TGBAProduct.fairConj extra i = extra[i] :=
      (List.getElem_eq_getD (l := extra) (i := i) .ff).symm
    rw [hgi] at hj
    exact ⟨j, (BoolFormula.eval_iff_holds _ _).mp hj⟩

/-! ## Routes -/

/-- Does `sys` satisfy `φ` on every run? The negated property is split at its conjunctions, every conjunct
that is a fairness becomes marks and a region on the product, and the rest go back to the translator. -/
def modelCheckUnderFairness (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    (checker : TEmptinessChecker ((SysState × Nat) × Bool) := dijkstraTChecker)
    (sysChecker : TEmptinessChecker (SysState × Bool) := dijkstraTChecker) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  let split := hoistFairness (φ.toNNF false).splitConj
  modelCheckCrossSplit (keptProperty split.2) split.1 sysInit sysSucc sysLabel sysFR checker sysChecker

/-- Does `sys` satisfy `φ` on every run? The negated property is split exactly as `modelCheckUnderFairness`
splits it, and the hoisted conjuncts are then decided per SCC instead of being crossed. -/
def modelCheckUnderFairnessPrune (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) : EmptinessResult (SysState × Nat) :=
  let split := hoistFairness (φ.toNNF false).splitConj
  modelCheckPruneSplit (keptProperty split.2) split.1 sysInit sysSucc sysLabel

/-- The prune with only flat fairness hoisted (`hoistFlat`), the conjuncts TLC, PAT and NuSMV recognise, and
everything else translated. -/
def modelCheckUnderFairnessFlat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) : EmptinessResult (SysState × Nat) :=
  let split := hoistFlat (φ.toNNF false).splitConj
  modelCheckPruneSplit (keptProperty split.2) split.1 sysInit sysSucc sysLabel

/-- `modelCheckUnderFairnessFlat` over one system callback. §15 -/
def modelCheckUnderFairnessFlatOfStep (φ : Formula α)
    (sysInit : List SysState) (sysStep : LSys.StepFn α SysState) :
    EmptinessResult (SysState × Nat) :=
  let split := hoistFlat (φ.toNNF false).splitConj
  modelCheckPruneSplitOfStep (keptProperty split.2) split.1 sysInit sysStep

theorem modelCheckUnderFairnessFlatOfStep_eq (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α) :
    modelCheckUnderFairnessFlatOfStep φ sysInit (fun s => (sysSucc s, sysLabel s))
      = modelCheckUnderFairnessFlat φ sysInit sysSucc sysLabel := rfl

/-- An `.empty` result means every run of `sys` satisfies `φ`. -/
theorem modelCheckUnderFairness_empty_unsat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool)) {n : Nat}
    (h : modelCheckUnderFairness φ sysInit sysSucc sysLabel sysFR checker sysChecker = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  intro ρ hρ
  by_contra hviol
  obtain ⟨hdss, hkept⟩ :=
    (hoistFairness_correct (LSys.valuation sysLabel ρ) (φ.toNNF false).splitConj).mp
      ((NNF.satisfies_splitConj _ _).mp ((Formula.toNNF_correct_neg _ φ).mp hviol))
  exact (directSatisfies_keptProperty _ _).mp
    (modelCheckCrossSplit_empty_unsat _ _ sysInit sysSucc sysLabel sysFR checker sysChecker h ρ hρ hdss) hkept

/-- A `.nonEmpty` result yields one run of `sys` that violates `φ`. -/
theorem modelCheckUnderFairness_nonEmpty_sat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool))
    {stem loop : List ((SysState × Nat) × Bool)}
    (h : modelCheckUnderFairness φ sysInit sysSucc sysLabel sysFR checker sysChecker = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  obtain ⟨ρ, hρ, hdss, hviol⟩ := modelCheckCrossSplit_nonEmpty_sat _ _ sysInit sysSucc sysLabel sysFR checker
    sysChecker h
  -- the violated goal is the kept conjuncts negated, so they all hold on this run
  have hkept := not_not.mp (fun hno => hviol ((directSatisfies_keptProperty _ _).mpr hno))
  exact ⟨ρ, hρ, (Formula.toNNF_correct_neg _ φ).mpr ((NNF.satisfies_splitConj _ _).mpr
    ((hoistFairness_correct _ (φ.toNNF false).splitConj).mpr ⟨hdss, hkept⟩))⟩

/-- Soundness of the prune route: an `.empty` result means every run of `sys` satisfies `φ`. -/
theorem modelCheckUnderFairnessPrune_empty_unsat [LawfulHashable SysState] (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    {n : Nat} (h : modelCheckUnderFairnessPrune φ sysInit sysSucc sysLabel = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  intro ρ hρ
  by_contra hviol
  obtain ⟨hdss, hkept⟩ :=
    (hoistFairness_correct (LSys.valuation sysLabel ρ) (φ.toNNF false).splitConj).mp
      ((NNF.satisfies_splitConj _ _).mp ((Formula.toNNF_correct_neg _ φ).mp hviol))
  exact (directSatisfies_keptProperty _ _).mp
    (modelCheckPruneSplit_empty_unsat _ _ sysInit sysSucc sysLabel sysFR h ρ hρ hdss) hkept

/-- Completeness of the prune route: a `.nonEmpty` result yields one run of `sys` that violates `φ`. -/
theorem modelCheckUnderFairnessPrune_nonEmpty_sat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α)
    {stem loop : List (SysState × Nat)}
    (h : modelCheckUnderFairnessPrune φ sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  obtain ⟨ρ, hρ, hdss, hviol⟩ :=
    modelCheckPruneSplit_nonEmpty_sat _ _ sysInit sysSucc sysLabel h
  -- the violated goal is the kept conjuncts negated, so they all hold on this run
  have hkept := not_not.mp (fun hno => hviol ((directSatisfies_keptProperty _ _).mpr hno))
  exact ⟨ρ, hρ, (Formula.toNNF_correct_neg _ φ).mpr ((NNF.satisfies_splitConj _ _).mpr
    ((hoistFairness_correct _ (φ.toNNF false).splitConj).mpr ⟨hdss, hkept⟩))⟩

/-- Soundness of the flat-fairness prune: an `.empty` result means every run of `sys` satisfies `φ`. -/
theorem modelCheckUnderFairnessFlat_empty_unsat [LawfulHashable SysState] (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit (LSys.targets sysSucc))
    {n : Nat} (h : modelCheckUnderFairnessFlat φ sysInit sysSucc sysLabel = .empty n) :
    ∀ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ →
      Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  intro ρ hρ
  by_contra hviol
  obtain ⟨hdss, hkept⟩ :=
    (hoistFlat_correct (LSys.valuation sysLabel ρ) (φ.toNNF false).splitConj).mp
      ((NNF.satisfies_splitConj _ _).mp ((Formula.toNNF_correct_neg _ φ).mp hviol))
  exact (directSatisfies_keptProperty _ _).mp
    (modelCheckPruneSplit_empty_unsat _ _ sysInit sysSucc sysLabel sysFR h ρ hρ hdss) hkept

/-- Completeness of the flat-fairness prune: a `.nonEmpty` result yields one run of `sys` that violates `φ`. -/
theorem modelCheckUnderFairnessFlat_nonEmpty_sat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α)
    {stem loop : List (SysState × Nat)}
    (h : modelCheckUnderFairnessFlat φ sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation sysLabel ρ) φ := by
  obtain ⟨ρ, hρ, hdss, hviol⟩ :=
    modelCheckPruneSplit_nonEmpty_sat _ _ sysInit sysSucc sysLabel h
  have hkept := not_not.mp (fun hno => hviol ((directSatisfies_keptProperty _ _).mpr hno))
  exact ⟨ρ, hρ, (Formula.toNNF_correct_neg _ φ).mpr ((NNF.satisfies_splitConj _ _).mpr
    ((hoistFlat_correct _ (φ.toNNF false).splitConj).mpr ⟨hdss, hkept⟩))⟩

end LTLLib
