/-
  The top-level entry point: model checking under a fairness assumption, with the assumption hoisted out of
  the property wherever it can be.

  The negated property `φ.toNNF false` is split at its conjunctions. A conjunct that is a fairness
  ([LSFZ16, Definition 1], `NNF.isFairness`) and flattens into `LTL(F, G)` contributes its fair normal form,
  which becomes marks and a region on the product and so never reaches the translator. Every other conjunct
  goes back to the translator through `keptProperty`. Crossing the per-conjunct normal forms gives one disjunct
  per combination, and the answer is the disjunction over them, so the checker runs once per disjunct and stops
  at the first counterexample. A disjunct whose region holds no cycle is rejected by `regionHasCycle` before
  the product is touched.

  What a user has to write, and what they do not. Write the property, `fair → φ` included, and nothing else.
  Every test here is syntactic, total and linear in the formula, so the routing is automatic. `NNF.isFairness`
  is Etessami and Holzmann's grammar, a sound but incomplete approximation of [LSFZ16, Definition 1]'s semantic
  class, so a `true` really is a fairness while a `false` may still be one written in an unrecognised shape.
  Nothing is lost either way: a conjunct that is not hoisted is translated exactly as it would have been
  without this file, so the worst case is the plain checker's behaviour and never a wrong answer.

  Splitting the negated property rather than the assumption is what lets the property be hoisted too. The class
  is closed under negation, `isPureEventuality` and `isPurelyUniversal` being exact duals under the NNF
  negation map, so a fairness property negates to a fairness and is hoisted alongside the assumption. When
  every conjunct is hoisted, nothing is kept and the translator is handed `⊤`, whose automaton is two states
  and no marks, so the product is the system with the region latch and little else.

  Only conjunction splits. `φ ∧ ψ` becomes two conjuncts, while `φ ∨ ψ` is one, hoisted whole when both sides
  are fairness and kept whole otherwise. Since it is the negation that is split, a conjunctive property
  `φ ∧ ψ` arrives as the disjunction `¬φ ∨ ¬ψ` and does not split, while a disjunctive property does. An
  assumption keeps its own polarity, so `fair₁ ∧ fair₂ → φ` splits into three conjuncts and hoists both halves.

  `NNF.classify` reports which of three things happened. `.notFairness` is not a fairness at all,
  `.fgFragment` is a fairness in `LTL(F, G)` and is hoisted, and `.temporal` is a fairness that does not
  flatten, `FG(a ∨ X(b U c))` being the witness, which [LSFZ16, Theorem 4] would cover and this does not.

  The split runs on the NNF rather than on the surface formula, so a conjunction written as `¬(¬φ ∨ ¬ψ)` splits
  too and a mixed assumption hidden under a negation still hoists what it can. Kept conjuncts return to the
  translator through `NNF.toFormula`, whose `toNNF true` is the identity, so it receives exactly what it would
  have received anyway.

  Two routes leave this file with the same answer. `modelCheckUnderFairness` crosses the per-conjunct normal
  forms and runs one latched check per disjunct. `modelCheckUnderFairnessPrune` leaves them uncrossed and
  decides them per SCC, so the product is not doubled by the latch and there is one pass rather than `2ⁿ`.
  Both stay available, since only measurement decides which wins on a given model.

  Defines:
  - `checkDisjuncts`: the short-circuiting fold over the disjuncts of a fair normal form
  - `hoistConjunct`, `hoistFairness`: splitting the negated property into hoisted normal forms and kept conjuncts
  - `keptProperty`: the kept conjuncts handed back to the translator, `⊤` when there are none
  - `modelCheckUnderFairness`: the entry point, crossing the disjuncts
  - `streettSpecOf`, `modelCheckPruneSplit`, `modelCheckUnderFairnessPrune`: the entry point that prunes SCCs
    instead of crossing, and the form of it that takes the split rather than deriving it
  - `modelCheckUnderFairness_empty_unsat`:  (Soundness)    an `.empty` result means every run of `sys` satisfies `φ`
  - `modelCheckUnderFairness_nonEmpty_sat`: (Completeness) a `.nonEmpty` result yields a run violating `φ`
  - `modelCheckPruneSplit_nonEmpty_sat`, `modelCheckUnderFairnessPrune_nonEmpty_sat`: the same completeness
    for the pruning route, whose witness is validated against the hoisted conjuncts before it is reported
  - `modelCheckPruneSplit_empty_unsat`, `modelCheckUnderFairnessPrune_empty_unsat`: the same soundness for the
    pruning route, resting on `streettCheck_empty_no_fairSCC`

  References:
  - [LSFZ16] Li, Song, Feng, Zhang. Verify LTL with Fairness Assumptions Efficiently. arXiv:1606.08116, 2016.

  Sections:
  - Folding over disjuncts
  - Splitting the negated property
  - Model checking under fairness
  - Soundness
  - Completeness
  - Pruning instead of crossing
-/
import LTLLib.AbstractSpec.EmptinessCheck
import LTLLib.LTL.FairClass
import LTLLib.LTL.FairNormalForm
import LTLLib.LTL.Semantics
import LTLLib.LTL.Syntax
import LTLLib.Product
import LTLLib.TGBABased.AbstractSpec.EmptinessCheck
import LTLLib.TGBABased.DijkstraCheck
import LTLLib.TGBABased.FairCheck
import LTLLib.TGBABased.SCC.DijkstraSCC
import LTLLib.TGBABased.SCC.StreettPrune

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

end Split

/-! ## Model checking under fairness -/

variable {α : Type u} {S : Type w} [FSet (NNF α) S]
  {SysState : Type v} [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [Inhabited SysState]
  [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α]

/-- The kept conjuncts as one property. The translator negates what it is given, so negating here hands it
back exactly the conjuncts, and an empty list leaves it the automaton for `⊤`. -/
def keptProperty (cs : List (NNF α)) : Formula α := .not (Formula.conj (cs.map NNF.toFormula))

omit [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α] in
theorem directSatisfies_keptProperty (ξ : OmegaWord α) (cs : List (NNF α)) :
    (keptProperty cs).directSatisfies ξ ↔ ¬ ∀ c ∈ cs, c.satisfies ξ := by
  simp only [keptProperty, Formula.directSatisfies, Formula.directSatisfies_conj]
  refine not_congr ⟨fun h n hn => (NNF.directSatisfies_toFormula ξ n).mp (h _ (List.mem_map_of_mem hn)),
    fun h c hc => ?_⟩
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hc
  exact (NNF.directSatisfies_toFormula ξ n).mpr (h n hn)

/-- Does `sys` satisfy `φ` on every run? The negated property is split at its conjunctions, every conjunct
that is a fairness becomes marks and a region on the product, and the rest go back to the translator. -/
def modelCheckUnderFairness (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool) := dijkstraTChecker)
    (sysChecker : TEmptinessChecker (SysState × Bool) := dijkstraTChecker) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  let split := hoistFairness (φ.toNNF false).splitConj
  checkDisjuncts
    (fun d => modelCheckTGBADisjunctFast (S := S) (keptProperty split.2) d.1 d.2
      sysInit sysSucc sysLabel sysFR checker sysChecker)
    (NNF.crossAllDNF split.1)

/-! ## Soundness -/

/-- An `.empty` result means every run of `sys` satisfies `φ`. -/
theorem modelCheckUnderFairness_empty_unsat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool)) {n : Nat}
    (h : modelCheckUnderFairness (S := S) φ sysInit sysSucc sysLabel sysFR checker sysChecker
      = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  intro τ hτ
  by_contra hviol
  obtain ⟨hdss, hkept⟩ :=
    (hoistFairness_correct (fun i a => a ∈ sysLabel (τ i)) (φ.toNNF false).splitConj).mp
      ((NNF.satisfies_splitConj _ _).mp ((Formula.toNNF_correct_neg _ φ).mp hviol))
  obtain ⟨d, hd, hholds⟩ :=
    (NNF.holds_crossAllDNF (fun i a => a ∈ sysLabel (τ i)) _).mpr hdss
  obtain ⟨m, hm⟩ := checkDisjuncts_empty h d hd
  exact (directSatisfies_keptProperty _ _).mp
    (modelCheckTGBADisjunctFast_empty_unsat (S := S) _ d.1 d.2 sysInit sysSucc sysLabel sysFR
      checker sysChecker hm τ hτ hholds.1 hholds.2) hkept

/-! ## Completeness -/

/-- A `.nonEmpty` result yields one run of `sys` that violates `φ`. -/
theorem modelCheckUnderFairness_nonEmpty_sat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool))
    {stem loop : List ((SysState × Nat) × Bool)}
    (h : modelCheckUnderFairness (S := S) φ sysInit sysSucc sysLabel sysFR checker sysChecker
      = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  obtain ⟨d, hd, hcall⟩ := checkDisjuncts_nonEmpty h
  obtain ⟨τ, hτ, hfg, hgf, hviol⟩ := modelCheckTGBADisjunctFast_nonEmpty_sat (S := S) _ d.1 d.2
    sysInit sysSucc sysLabel sysFR checker sysChecker hcall
  -- the violated goal is the kept conjuncts negated, so they all hold on this run
  have hkept := not_not.mp (fun hno => hviol ((directSatisfies_keptProperty _ _).mpr hno))
  refine ⟨τ, hτ, (Formula.toNNF_correct_neg _ φ).mpr ((NNF.satisfies_splitConj _ _).mpr
    ((hoistFairness_correct _ (φ.toNNF false).splitConj).mpr ⟨?_, hkept⟩))⟩
  exact (NNF.holds_crossAllDNF _ _).mp ⟨d, hd, hfg, hgf⟩

/-! ## Pruning instead of crossing

The same split, decided on the product's SCCs rather than by enumerating the crossing. A hoisted conjunct
becomes one entry of the `StreettSpec`, its disjuncts becoming that entry's options, and `StreettPrune.lean`
tests each SCC as Tarjan closes it. Nothing is crossed, so the exponent goes, and nothing is latched, so the
product loses the `Bool` factor `RegionLatch.lean` adds on the other route. -/

/-- The hoisted conjuncts as the SCC test sees them, one entry per conjunct and one option per disjunct.
Regions and marks are read off the system label, which is why the spec's `label` drops the automaton
component of a product state. -/
def streettSpecOf (numMarks : Nat) (sysLabel : SysState → Std.HashSet α)
    (dss : List (List (NNF.FairDisjunct α))) : StreettSpec (SysState × Nat) (Std.HashSet α) where
  numMarks := numMarks
  label := fun p => sysLabel p.1
  conjuncts := dss.toArray.map fun ds => ds.toArray.map fun d =>
    { region := d.1.eval, marks := d.2.toArray.map (·.eval) }

/-- The prune with the split supplied rather than derived. `kept` is the property the translator receives, in
the same convention `modelCheckTGBA` uses, and `dss` are the hoisted conjuncts. Holding a conjunct back from
`dss` and putting it into `kept` measures what translating it costs instead. -/
def modelCheckPruneSplit (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) : EmptinessResult (SysState × Nat) :=
  match createGraph (S := S) (kept.toNNF false) with
  | some st =>
    let tgba := (constructGBA (kept.toNNF false) st).toTGBA
    streettCheck (CompiledSpec.of (streettSpecOf tgba.numAcceptSets sysLabel dss))
      (TGBAProduct.getSuccessors tgba sysSucc sysLabel)
      (TGBAProduct.edgeMarks tgba sysLabel)
      (TGBAProduct.initialStates tgba sysInit)
  | none => .empty 0

omit [LawfulBEq α] [LawfulHashable α] [DecidableEq α] in
private theorem modelCheckPruneSplit_eq (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) {st : ExpandState α S}
    (hcg : createGraph (S := S) (kept.toNNF false) = some st) :
    modelCheckPruneSplit (S := S) kept dss sysInit sysSucc sysLabel =
      streettCheck (CompiledSpec.of (streettSpecOf
          (constructGBA (kept.toNNF false) st).toTGBA.numAcceptSets sysLabel dss))
        (TGBAProduct.getSuccessors (constructGBA (kept.toNNF false) st).toTGBA sysSucc sysLabel)
        (TGBAProduct.edgeMarks (constructGBA (kept.toNNF false) st).toTGBA sysLabel)
        (TGBAProduct.initialStates (constructGBA (kept.toNNF false) st).toTGBA sysInit) := by
  unfold modelCheckPruneSplit
  split
  next st' hcg' =>
    obtain rfl : st' = st := Option.some.inj (hcg'.symm.trans hcg)
    rfl
  next hcg' => exact absurd (hcg'.symm.trans hcg) (by simp)

/-- Completeness of the prune, one conjunct at a time: a reported witness is a run satisfying every hoisted
conjunct through one of its options and violating the kept property. The witness carries the fairness because
it is validated against the specification before it is returned, so nothing here depends on the search. -/
theorem modelCheckPruneSplit_nonEmpty_sat (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) {stem loop : List (SysState × Nat)}
    (h : modelCheckPruneSplit (S := S) kept dss sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      (∀ ds ∈ dss, ∃ d ∈ ds, NNF.FairDisjunct.holds (fun i a => a ∈ sysLabel (τ i)) d) ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) kept := by
  obtain ⟨st, hcg, _⟩ := createGraph_term (S := S) (kept.toNNF false)
  rw [modelCheckPruneSplit_eq kept dss sysInit sysSucc sysLabel hcg] at h
  obtain ⟨ac, -, hcyc, hfair⟩ := streettCheck_nonEmpty_valid _ _ _ _ h
  obtain ⟨τ, hτrun, hlang, hall, hsome⟩ :=
    TGBAProduct.exists_run_of_TAcceptingCycle _ sysSucc sysLabel sysInit ac
  refine ⟨τ, hτrun, fun ds hds => ?_, fun hsat => (Formula.toNNF_correct_neg _ kept).mpr
    ((constructGBA_correct hcg _).mp ((GBA.toTGBA_toSpec_accepts _ _).mp hlang)) hsat⟩
  obtain ⟨opt, hopt, hregion, hmarks⟩ := exists_option_of_fairCycle hfair
    (Array.mem_map_of_mem (f := fun (ds : List (NNF.FairDisjunct α)) => ds.toArray.map fun d =>
      ({ region := d.1.eval, marks := d.2.toArray.map (·.eval) } : StreettOption (Std.HashSet α)))
      (by simpa using hds))
  obtain ⟨d, hd, rfl⟩ := Array.mem_map.mp hopt
  refine ⟨d, by simpa using hd, (TGBAProduct.eventuallyAlways_iff_indexed d.1 sysLabel τ).mpr
    (hall (fun s => d.1.eval (sysLabel s) = true) fun p hp => hregion p (hcyc ▸ hp)), ?_⟩
  refine (TGBAProduct.fair_iff_indexed d.2 sysLabel τ).mpr fun i hi n => ?_
  have hgi : TGBAProduct.fairConj d.2 i = d.2[i] := (List.getElem_eq_getD (l := d.2) (i := i) .ff).symm
  obtain ⟨s, hs, hgs⟩ := hmarks d.2[i].eval (Array.mem_map_of_mem (by simp))
  exact hsome (fun t => (TGBAProduct.fairConj d.2 i).eval (sysLabel t) = true)
    ⟨s, hcyc ▸ hs, by rw [hgi]; exact hgs⟩ n

/-- Does `sys` satisfy `φ` on every run? The negated property is split exactly as `modelCheckUnderFairness`
splits it, and the hoisted conjuncts are then decided per SCC instead of being crossed. -/
def modelCheckUnderFairnessPrune (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) : EmptinessResult (SysState × Nat) :=
  let split := hoistFairness (φ.toNNF false).splitConj
  modelCheckPruneSplit (S := S) (keptProperty split.2) split.1 sysInit sysSucc sysLabel

/-- Soundness of the prune, one conjunct at a time, modulo `streettCheck_empty_no_fairSCC`: an `.empty`
result means every run satisfying the hoisted conjuncts satisfies the kept property. Such a run would settle
into a `FairSCC`, which is what the search reports. -/
theorem modelCheckPruneSplit_empty_unsat (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc) {n : Nat}
    (h : modelCheckPruneSplit (S := S) kept dss sysInit sysSucc sysLabel = .empty n)
    (τ : Nat → SysState) (hτ : (Sys.toSpec sysSucc sysInit sysLabel).isRun τ)
    (hdss : ∀ ds ∈ dss, ∃ d ∈ ds, NNF.FairDisjunct.holds (fun i a => a ∈ sysLabel (τ i)) d) :
    Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) kept := by
  by_contra hviolate
  obtain ⟨st, hcg, _⟩ := createGraph_term (S := S) (kept.toNNF false)
  rw [modelCheckPruneSplit_eq kept dss sysInit sysSucc sysLabel hcg] at h
  obtain ⟨σ, hproj, hrun, hacc⟩ := TGBAProduct.gsp_correct2 _ sysSucc sysLabel sysInit hτ
    ((GBA.toTGBA_toSpec_accepts _ _).mpr
      ((constructGBA_correct hcg _).mpr ((Formula.toNNF_correct_neg _ kept).mp hviolate)))
  subst hproj
  obtain ⟨hinit, htrans, hmarks⟩ :=
    TGBAProduct.acceptingRun_states _ sysSucc sysLabel sysInit hrun hacc
  refine streettCheck_empty_no_fairSCC _ _ _ _
    (fun p p' m hm => modelCheckTGBA_marksBound kept sysLabel st p p' m hm)
    (modelCheckTGBA_finiteReach kept sysInit sysSucc sysLabel sysFR hcg) h
    (Nonempty.some (exists_FairSCC_of_run (σ := fun n => ((σ n).1, (σ n).2.2.1))
      (modelCheckTGBA_finiteReach kept sysInit sysSucc sysLabel sysFR hcg) hinit htrans hmarks ?_))
  intro c hc
  obtain ⟨ds, hds, rfl⟩ := Array.mem_map.mp hc
  obtain ⟨d, hd, hfg, hgf⟩ := hdss ds (by simpa using hds)
  refine ⟨_, Array.mem_map_of_mem (by simpa using hd), ?_, fun g hg K => ?_⟩
  · exact (TGBAProduct.eventuallyAlways_iff_indexed d.1 sysLabel _).mp hfg
  · obtain ⟨b, hb, rfl⟩ := Array.mem_map.mp hg
    obtain ⟨j, hj⟩ := (BoolFormula.satisfies_alwaysEventually _ b).mp (hgf b (by simpa using hb)) K
    exact ⟨K + j, by omega, (BoolFormula.eval_iff_holds b _).mpr hj⟩

/-- Soundness of the prune route, modulo `streettCheck_empty_no_fairSCC`: an `.empty` result means every run
of `sys` satisfies `φ`. -/
theorem modelCheckUnderFairnessPrune_empty_unsat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc) {n : Nat}
    (h : modelCheckUnderFairnessPrune (S := S) φ sysInit sysSucc sysLabel = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  intro τ hτ
  by_contra hviol
  obtain ⟨hdss, hkept⟩ :=
    (hoistFairness_correct (fun i a => a ∈ sysLabel (τ i)) (φ.toNNF false).splitConj).mp
      ((NNF.satisfies_splitConj _ _).mp ((Formula.toNNF_correct_neg _ φ).mp hviol))
  exact (directSatisfies_keptProperty _ _).mp
    (modelCheckPruneSplit_empty_unsat (S := S) _ _ sysInit sysSucc sysLabel sysFR h τ hτ hdss) hkept

/-- Completeness of the prune route: a `.nonEmpty` result yields one run of `sys` that violates `φ`. The
hoisted conjuncts and the kept ones recombine into the negated property exactly as they do on the crossing
route, the only difference being how the hoisted ones were decided. -/
theorem modelCheckUnderFairnessPrune_nonEmpty_sat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) {stem loop : List (SysState × Nat)}
    (h : modelCheckUnderFairnessPrune (S := S) φ sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  obtain ⟨τ, hτ, hdss, hviol⟩ :=
    modelCheckPruneSplit_nonEmpty_sat (S := S) _ _ sysInit sysSucc sysLabel h
  -- the violated goal is the kept conjuncts negated, so they all hold on this run
  have hkept := not_not.mp (fun hno => hviol ((directSatisfies_keptProperty _ _).mpr hno))
  exact ⟨τ, hτ, (Formula.toNNF_correct_neg _ φ).mpr ((NNF.satisfies_splitConj _ _).mpr
    ((hoistFairness_correct _ (φ.toNNF false).splitConj).mpr ⟨hdss, hkept⟩))⟩

end LTLLib
