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
  - `streettSpecOf`: the hoisted conjuncts as a `StreettSpec`
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
import LTLLib.TGBABased.FairCheck
import LTLLib.TGBABased.LTLtoTGBA.Pipeline
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

/-- The hoisted conjuncts as a `StreettSpec`, one entry per conjunct and one option per disjunct, read off the system
label. -/
def streettSpecOf (numMarks : Nat) (sysLabel : SysState → Std.HashSet α)
    (dss : List (List (NNF.FairDisjunct α))) : StreettSpec (SysState × Nat) (Std.HashSet α) where
  numMarks := numMarks
  label := fun p => sysLabel p.1
  conjuncts := dss.toArray.map fun ds => ds.toArray.map fun d =>
    { region := d.1.eval, marks := d.2.toArray.map (·.eval) }

/-- The prune with the split supplied rather than derived, `kept` going to the translator. -/
def modelCheckPruneSplit (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) : EmptinessResult (SysState × Nat) :=
  match ltl3ba (kept.toNNF false) with
  | some tgba =>
    streettCheck (CompiledSpec.of (streettSpecOf tgba.numAcceptSets sysLabel dss))
      (TGBAProduct.getSuccessors tgba sysSucc sysLabel)
      (TGBAProduct.edgeMarks tgba sysLabel)
      (TGBAProduct.initialStates tgba sysInit)
  | none => .empty 0

theorem modelCheckPruneSplit_eq (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) {tgba : TGBA α} (htg : ltl3ba (kept.toNNF false) = some tgba) :
    modelCheckPruneSplit kept dss sysInit sysSucc sysLabel =
      streettCheck (CompiledSpec.of (streettSpecOf tgba.numAcceptSets sysLabel dss))
        (TGBAProduct.getSuccessors tgba sysSucc sysLabel)
        (TGBAProduct.edgeMarks tgba sysLabel)
        (TGBAProduct.initialStates tgba sysInit) := by
  unfold modelCheckPruneSplit
  rw [htg]

variable [LawfulBEq α] [LawfulHashable α] [DecidableEq α]

/-- The crossing with the split supplied rather than derived, one latched check per disjunct of the crossed `dss`. -/
def modelCheckCrossSplit (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool) := dijkstraTChecker)
    (sysChecker : TEmptinessChecker (SysState × Bool) := dijkstraTChecker) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  checkDisjuncts (fun d => modelCheckTGBADisjunctFast kept d.1 d.2 sysInit sysSucc sysLabel sysFR checker sysChecker)
    (NNF.crossAllDNF dss)

/-! ## Soundness -/

/-- Soundness of the crossing with the split given: an `.empty` result means every run satisfying the hoisted
conjuncts satisfies the kept property. -/
theorem modelCheckCrossSplit_empty_unsat (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool)) {n : Nat}
    (h : modelCheckCrossSplit kept dss sysInit sysSucc sysLabel sysFR checker sysChecker = .empty n)
    (τ : Nat → SysState) (hτ : (Sys.toSpec sysSucc sysInit sysLabel).isRun τ)
    (hdss : ∀ ds ∈ dss, ∃ d ∈ ds, NNF.FairDisjunct.holds (fun i a => a ∈ sysLabel (τ i)) d) :
    Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) kept := by
  obtain ⟨d, hd, hholds⟩ := (NNF.holds_crossAllDNF (fun i a => a ∈ sysLabel (τ i)) _).mpr hdss
  obtain ⟨m, hm⟩ := checkDisjuncts_empty h d hd
  exact modelCheckTGBADisjunctFast_empty_unsat _ d.1 d.2 sysInit sysSucc sysLabel sysFR checker sysChecker hm τ hτ
    hholds.1 hholds.2

/-- Soundness of the prune with the split given: an `.empty` result means every run satisfying the hoisted
conjuncts satisfies the kept property. -/
theorem modelCheckPruneSplit_empty_unsat (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc) {n : Nat}
    (h : modelCheckPruneSplit kept dss sysInit sysSucc sysLabel = .empty n)
    (τ : Nat → SysState) (hτ : (Sys.toSpec sysSucc sysInit sysLabel).isRun τ)
    (hdss : ∀ ds ∈ dss, ∃ d ∈ ds, NNF.FairDisjunct.holds (fun i a => a ∈ sysLabel (τ i)) d) :
    Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) kept := by
  by_contra hviolate
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome (kept.toNNF false))
  rw [modelCheckPruneSplit_eq kept dss sysInit sysSucc sysLabel htg] at h
  obtain ⟨σ, hproj, hrun, hacc⟩ := TGBAProduct.gsp_correct2 _ sysSucc sysLabel sysInit hτ
    ((ltl3ba_accepts _ htg _).mpr ((Formula.toNNF_correct_neg _ kept).mp hviolate))
  subst hproj
  obtain ⟨hinit, htrans, hmarks⟩ :=
    TGBAProduct.acceptingRun_states _ sysSucc sysLabel sysInit hrun hacc
  have hFR := TGBAProduct.finiteReach tgba (ltl3ba_wellFormed _ htg) sysSucc sysLabel sysInit sysFR
  refine streettCheck_empty_no_fairSCC _ _ _ _
    (fun p p' m hm => TGBAProduct.edgeMarks_lt tgba sysLabel (ltl3ba_marks_lt _ htg) p p' m hm) hFR h
    (Nonempty.some (exists_FairSCC_of_run (σ := fun n => ((σ n).1, (σ n).2.2.1)) hFR hinit htrans hmarks ?_))
  intro c hc
  obtain ⟨ds, hds, rfl⟩ := Array.mem_map.mp hc
  obtain ⟨d, hd, hfg, hgf⟩ := hdss ds (by simpa using hds)
  refine ⟨_, Array.mem_map_of_mem (by simpa using hd), ?_, fun g hg K => ?_⟩
  · exact (TGBAProduct.eventuallyAlways_iff_indexed d.1 sysLabel _).mp hfg
  · obtain ⟨b, hb, rfl⟩ := Array.mem_map.mp hg
    obtain ⟨j, hj⟩ := (BoolFormula.satisfies_alwaysEventually _ b).mp (hgf b (by simpa using hb)) K
    exact ⟨K + j, by omega, (BoolFormula.eval_iff_holds b _).mpr hj⟩

/-! ## Completeness -/

/-- Completeness of the crossing with the split given: a reported witness is a run satisfying every hoisted
conjunct through one of its disjuncts and violating the kept property. -/
theorem modelCheckCrossSplit_nonEmpty_sat (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool))
    {stem loop : List ((SysState × Nat) × Bool)}
    (h : modelCheckCrossSplit kept dss sysInit sysSucc sysLabel sysFR checker sysChecker = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      (∀ ds ∈ dss, ∃ d ∈ ds, NNF.FairDisjunct.holds (fun i a => a ∈ sysLabel (τ i)) d) ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) kept := by
  obtain ⟨d, hd, hcall⟩ := checkDisjuncts_nonEmpty h
  obtain ⟨τ, hτ, hfg, hgf, hviol⟩ := modelCheckTGBADisjunctFast_nonEmpty_sat _ d.1 d.2
    sysInit sysSucc sysLabel sysFR checker sysChecker hcall
  exact ⟨τ, hτ, (NNF.holds_crossAllDNF _ _).mp ⟨d, hd, hfg, hgf⟩, hviol⟩

/-- Completeness of the prune with the split given: a reported witness is a run satisfying every hoisted
conjunct through one of its options and violating the kept property. -/
theorem modelCheckPruneSplit_nonEmpty_sat (kept : Formula α) (dss : List (List (NNF.FairDisjunct α)))
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) {stem loop : List (SysState × Nat)}
    (h : modelCheckPruneSplit kept dss sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      (∀ ds ∈ dss, ∃ d ∈ ds, NNF.FairDisjunct.holds (fun i a => a ∈ sysLabel (τ i)) d) ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) kept := by
  obtain ⟨tgba, htg⟩ := Option.isSome_iff_exists.mp (ltl3ba_isSome (kept.toNNF false))
  rw [modelCheckPruneSplit_eq kept dss sysInit sysSucc sysLabel htg] at h
  obtain ⟨ac, -, hcyc, hfair⟩ := streettCheck_nonEmpty_valid _ _ _ _ h
  obtain ⟨τ, hτrun, hlang, hall, hsome⟩ :=
    TGBAProduct.exists_run_of_TAcceptingCycle _ sysSucc sysLabel sysInit ac
  refine ⟨τ, hτrun, fun ds hds => ?_, fun hsat => (Formula.toNNF_correct_neg _ kept).mpr
    ((ltl3ba_accepts _ htg _).mp hlang) hsat⟩
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

/-! ## Routes -/

/-- Does `sys` satisfy `φ` on every run? The negated property is split at its conjunctions, every conjunct
that is a fairness becomes marks and a region on the product, and the rest go back to the translator. -/
def modelCheckUnderFairness (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool) := dijkstraTChecker)
    (sysChecker : TEmptinessChecker (SysState × Bool) := dijkstraTChecker) :
    EmptinessResult ((SysState × Nat) × Bool) :=
  let split := hoistFairness (φ.toNNF false).splitConj
  modelCheckCrossSplit (keptProperty split.2) split.1 sysInit sysSucc sysLabel sysFR checker sysChecker

/-- Does `sys` satisfy `φ` on every run? The negated property is split exactly as `modelCheckUnderFairness`
splits it, and the hoisted conjuncts are then decided per SCC instead of being crossed. -/
def modelCheckUnderFairnessPrune (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) : EmptinessResult (SysState × Nat) :=
  let split := hoistFairness (φ.toNNF false).splitConj
  modelCheckPruneSplit (keptProperty split.2) split.1 sysInit sysSucc sysLabel

/-- The prune with only flat fairness hoisted (`hoistFlat`), the conjuncts TLC, PAT and NuSMV recognise, and
everything else translated. -/
def modelCheckUnderFairnessFlat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) : EmptinessResult (SysState × Nat) :=
  let split := hoistFlat (φ.toNNF false).splitConj
  modelCheckPruneSplit (keptProperty split.2) split.1 sysInit sysSucc sysLabel

/-- An `.empty` result means every run of `sys` satisfies `φ`. -/
theorem modelCheckUnderFairness_empty_unsat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool)) {n : Nat}
    (h : modelCheckUnderFairness φ sysInit sysSucc sysLabel sysFR checker sysChecker = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  intro τ hτ
  by_contra hviol
  obtain ⟨hdss, hkept⟩ :=
    (hoistFairness_correct (fun i a => a ∈ sysLabel (τ i)) (φ.toNNF false).splitConj).mp
      ((NNF.satisfies_splitConj _ _).mp ((Formula.toNNF_correct_neg _ φ).mp hviol))
  exact (directSatisfies_keptProperty _ _).mp
    (modelCheckCrossSplit_empty_unsat _ _ sysInit sysSucc sysLabel sysFR checker sysChecker h τ hτ hdss) hkept

/-- A `.nonEmpty` result yields one run of `sys` that violates `φ`. -/
theorem modelCheckUnderFairness_nonEmpty_sat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc)
    (checker : TEmptinessChecker ((SysState × Nat) × Bool))
    (sysChecker : TEmptinessChecker (SysState × Bool))
    {stem loop : List ((SysState × Nat) × Bool)}
    (h : modelCheckUnderFairness φ sysInit sysSucc sysLabel sysFR checker sysChecker = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  obtain ⟨τ, hτ, hdss, hviol⟩ := modelCheckCrossSplit_nonEmpty_sat _ _ sysInit sysSucc sysLabel sysFR checker
    sysChecker h
  -- the violated goal is the kept conjuncts negated, so they all hold on this run
  have hkept := not_not.mp (fun hno => hviol ((directSatisfies_keptProperty _ _).mpr hno))
  exact ⟨τ, hτ, (Formula.toNNF_correct_neg _ φ).mpr ((NNF.satisfies_splitConj _ _).mpr
    ((hoistFairness_correct _ (φ.toNNF false).splitConj).mpr ⟨hdss, hkept⟩))⟩

/-- Soundness of the prune route: an `.empty` result means every run of `sys` satisfies `φ`. -/
theorem modelCheckUnderFairnessPrune_empty_unsat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc) {n : Nat}
    (h : modelCheckUnderFairnessPrune φ sysInit sysSucc sysLabel = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  intro τ hτ
  by_contra hviol
  obtain ⟨hdss, hkept⟩ :=
    (hoistFairness_correct (fun i a => a ∈ sysLabel (τ i)) (φ.toNNF false).splitConj).mp
      ((NNF.satisfies_splitConj _ _).mp ((Formula.toNNF_correct_neg _ φ).mp hviol))
  exact (directSatisfies_keptProperty _ _).mp
    (modelCheckPruneSplit_empty_unsat _ _ sysInit sysSucc sysLabel sysFR h τ hτ hdss) hkept

/-- Completeness of the prune route: a `.nonEmpty` result yields one run of `sys` that violates `φ`. -/
theorem modelCheckUnderFairnessPrune_nonEmpty_sat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) {stem loop : List (SysState × Nat)}
    (h : modelCheckUnderFairnessPrune φ sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  obtain ⟨τ, hτ, hdss, hviol⟩ := modelCheckPruneSplit_nonEmpty_sat _ _ sysInit sysSucc sysLabel h
  -- the violated goal is the kept conjuncts negated, so they all hold on this run
  have hkept := not_not.mp (fun hno => hviol ((directSatisfies_keptProperty _ _).mpr hno))
  exact ⟨τ, hτ, (Formula.toNNF_correct_neg _ φ).mpr ((NNF.satisfies_splitConj _ _).mpr
    ((hoistFairness_correct _ (φ.toNNF false).splitConj).mpr ⟨hdss, hkept⟩))⟩

/-- Soundness of the flat-fairness prune: an `.empty` result means every run of `sys` satisfies `φ`. -/
theorem modelCheckUnderFairnessFlat_empty_unsat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysFR : FiniteReach sysInit sysSucc) {n : Nat}
    (h : modelCheckUnderFairnessFlat φ sysInit sysSucc sysLabel = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  intro τ hτ
  by_contra hviol
  obtain ⟨hdss, hkept⟩ :=
    (hoistFlat_correct (fun i a => a ∈ sysLabel (τ i)) (φ.toNNF false).splitConj).mp
      ((NNF.satisfies_splitConj _ _).mp ((Formula.toNNF_correct_neg _ φ).mp hviol))
  exact (directSatisfies_keptProperty _ _).mp
    (modelCheckPruneSplit_empty_unsat _ _ sysInit sysSucc sysLabel sysFR h τ hτ hdss) hkept

/-- Completeness of the flat-fairness prune: a `.nonEmpty` result yields one run of `sys` that violates `φ`. -/
theorem modelCheckUnderFairnessFlat_nonEmpty_sat (φ : Formula α)
    (sysInit : List SysState) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) {stem loop : List (SysState × Nat)}
    (h : modelCheckUnderFairnessFlat φ sysInit sysSucc sysLabel = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  obtain ⟨τ, hτ, hdss, hviol⟩ := modelCheckPruneSplit_nonEmpty_sat _ _ sysInit sysSucc sysLabel h
  have hkept := not_not.mp (fun hno => hviol ((directSatisfies_keptProperty _ _).mpr hno))
  exact ⟨τ, hτ, (Formula.toNNF_correct_neg _ φ).mpr ((NNF.satisfies_splitConj _ _).mpr
    ((hoistFlat_correct _ (φ.toNNF false).splitConj).mpr ⟨hdss, hkept⟩))⟩

end LTLLib
