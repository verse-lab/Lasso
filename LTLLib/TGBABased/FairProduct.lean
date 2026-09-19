/-
  The product of `Product.lean`, extended with one generalized Büchi mark per propositional fairness conjunct. A conjunct
  `ψ` is carried as a mark on every edge whose source system state satisfies `ψ`, indexed from `tgba.numAcceptSets`, so
  an accepting cycle witnesses one run that both violates the property and satisfies every `□◇ψ`. The emptiness checker
  is left untouched.

  Defines:
  - `fairMarks`: the mark set contributed by the conjuncts at one source label
  - `edgeMarksFair`: `edgeMarks` extended with those marks
  - `toSpecFair`: the abstract product spec with the extended acceptance condition
  - `fgRegion`: the region a propositional `FG` part carves out of the product

  Proves:
  - `gsp_correct1Fair`, `gsp_correct2Fair`: the two directions of the extended product's correctness, acceptance also
    meaning every conjunct holds infinitely often
  - `exists_TAcceptingCycle_of_acceptingRunFair`: an accepting run of the extended product yields a lasso
  - `exists_run_of_TRegionCycle`: a region cycle yields a counterexample run whose tail stays inside the region

  Sections:
  - Fairness marks
  - Extended product spec
  - Acceptance transfer
  - Edge witness
  - From an accepting run to a lasso
  - Lasso witness
  - Region cycles
-/
import LTLLib.LTL.Propositional
import LTLLib.TGBABased.AbstractSpec.RegionLatch
import LTLLib.TGBABased.Product

namespace LTLLib

namespace TGBAProduct

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]

/-! ## Fairness marks -/

/-- The `i`-th fairness conjunct, `⊥` past the end so the lookup is total. -/
def fairConj (extra : List (BoolFormula α)) (i : Nat) : BoolFormula α := extra.getD i .ff

/-- Marks contributed by the conjuncts at a source label, conjunct `i` giving mark `base + i`. -/
def fairMarks (base : Nat) (extra : List (BoolFormula α)) (l : Std.HashSet α) : Std.HashSet Nat :=
  Std.HashSet.ofList
    (((List.range extra.length).filter fun i => (fairConj extra i).eval l).map (base + ·))

theorem mem_fairMarks_iff (base : Nat) (extra : List (BoolFormula α)) (l : Std.HashSet α) (m : Nat) :
    m ∈ fairMarks base extra l ↔
      ∃ i, i < extra.length ∧ m = base + i ∧ (fairConj extra i).eval l = true := by
  simp only [fairMarks, Std.HashSet.mem_ofList, List.contains_iff_mem, List.mem_map,
    List.mem_filter, List.mem_range]
  grind

/-- `edgeMarks` extended with one mark per fairness conjunct, indexed from `tgba.numAcceptSets`. -/
def edgeMarksFair (tgba : TGBA α) (sysLabel : SysState → Std.HashSet α)
    (extra : List (BoolFormula α)) : (SysState × Nat) → (SysState × Nat) → Std.HashSet Nat :=
  fun p p' => (edgeMarks tgba sysLabel p p').union (fairMarks tgba.numAcceptSets extra (sysLabel p.1))

theorem mem_edgeMarksFair_iff (tgba : TGBA α) (sysLabel : SysState → Std.HashSet α)
    (extra : List (BoolFormula α)) (p p' : SysState × Nat) (m : Nat) :
    m ∈ edgeMarksFair tgba sysLabel extra p p' ↔
      m ∈ edgeMarks tgba sysLabel p p' ∨
      ∃ i, i < extra.length ∧ m = tgba.numAcceptSets + i ∧
        (fairConj extra i).eval (sysLabel p.1) = true := by
  rw [← mem_fairMarks_iff]
  simp only [edgeMarksFair, Std.HashSet.mem_iff_contains, Std.HashSet.union_eq,
    Std.HashSet.contains_union, Bool.or_eq_true]

/-- The conjunct marks sit above `numAcceptSets`, so a base mark is never mistaken for a fairness one. -/
theorem mem_edgeMarks_of_mem_edgeMarksFair (tgba : TGBA α) (sysLabel : SysState → Std.HashSet α)
    (extra : List (BoolFormula α)) (p p' : SysState × Nat) (m : Nat) (hlt : m < tgba.numAcceptSets)
    (hm : m ∈ edgeMarksFair tgba sysLabel extra p p') : m ∈ edgeMarks tgba sysLabel p p' := by
  rcases (mem_edgeMarksFair_iff tgba sysLabel extra p p' m).mp hm with h | ⟨i, -, rfl, -⟩
  · exact h
  · omega

/-- Every extended mark stays below `numAcceptSets + extra.length`. -/
theorem edgeMarksFair_lt (tgba : TGBA α) (sysLabel : SysState → Std.HashSet α)
    (hbound : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets)
    (extra : List (BoolFormula α)) (p p' : SysState × Nat) (m : Nat)
    (hm : m ∈ edgeMarksFair tgba sysLabel extra p p') :
    m < tgba.numAcceptSets + extra.length := by
  rcases (mem_edgeMarksFair_iff tgba sysLabel extra p p' m).mp hm with h | ⟨i, hi, rfl, -⟩
  · have := edgeMarks_lt tgba sysLabel hbound p p' m h
    omega
  · omega

/-- The `□◇` reading of the conjuncts and the indexed `eval` reading the marks use are one statement. -/
theorem fair_iff_indexed [LawfulBEq α] (extra : List (BoolFormula α))
    (sysLabel : SysState → Std.HashSet α) (τ : Nat → SysState) :
    (∀ b ∈ extra, (BoolFormula.alwaysEventually b).satisfies (fun i a => a ∈ sysLabel (τ i))) ↔
      ∀ i, i < extra.length → ∀ n, ∃ j, (fairConj extra i).eval (sysLabel (τ (n + j))) = true := by
  have hconj : ∀ i, (h : i < extra.length) → fairConj extra i = extra[i] := by
    intro i h; exact (List.getElem_eq_getD (l := extra) (i := i) .ff).symm
  constructor
  · intro h i hi n
    obtain ⟨j, hj⟩ := (BoolFormula.satisfies_alwaysEventually _ _).mp
      (h extra[i] (List.getElem_mem hi)) n
    exact ⟨j, by rw [hconj i hi, BoolFormula.eval_iff_holds]; exact hj⟩
  · intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    refine (BoolFormula.satisfies_alwaysEventually _ _).mpr fun n => ?_
    obtain ⟨j, hj⟩ := h i hi n
    exact ⟨j, by rw [← BoolFormula.eval_iff_holds, ← hconj i hi]; exact hj⟩

/-- The `◇□` reading of a conjunct and the index form the region restriction uses are one statement. -/
theorem eventuallyAlways_iff_indexed [LawfulBEq α] (b : BoolFormula α)
    (sysLabel : SysState → Std.HashSet α) (τ : Nat → SysState) :
    (BoolFormula.eventuallyAlways b).satisfies (fun i a => a ∈ sysLabel (τ i)) ↔
      ∃ N, ∀ n, N ≤ n → b.eval (sysLabel (τ n)) = true := by
  rw [BoolFormula.satisfies_eventuallyAlways]
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have h := hN (n - N)
    rw [show N + (n - N) = n from by omega] at h
    exact (BoolFormula.eval_iff_holds b (sysLabel (τ n))).mpr h
  · rintro ⟨N, hN⟩
    exact ⟨N, fun k => (BoolFormula.eval_iff_holds b _).mp (hN (N + k) (by omega))⟩

/-! ## Extended product spec -/

/-- The abstract product spec with `extra.length` further marks, conjunct `i` carried by an edge iff the
edge's source system state satisfies it. All other fields are `toSpec`'s. -/
def toSpecFair (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) :
    TOASpec (SysState × Nat) (Edge SysState α) α (tgba.numAcceptSets + extra.length) where
  src e := (e.1, e.2.2.1)
  dst e := (e.2.1, e.2.2.2.target)
  valid e := e.2.2.2 ∈ tgba.getSuccessors e.2.2.1 ∧
    transCompatible e.2.2.2 (sysLabel e.1) = true ∧ e.2.1 ∈ Product.totalizeSucc sysSucc e.1
  initial p := p ∈ initialStates tgba sysInit
  labelCompat e v := ∀ a, v a ↔ a ∈ sysLabel e.1
  acceptMark i e :=
    if (i : Nat) < tgba.numAcceptSets then e.2.2.2.acceptMarks.contains (i : Nat)
    else (fairConj extra ((i : Nat) - tgba.numAcceptSets)).eval (sysLabel e.1) = true

/-- The extended spec differs from `toSpec` only in its acceptance condition. -/
theorem toSpecFair_isRun_iff (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) (σ : TLA.exec (Edge SysState α)) :
    (toSpecFair tgba sysSucc sysLabel sysInit extra).isRun σ ↔
      (toSpec tgba sysSucc sysLabel sysInit).isRun σ := Iff.rfl

/-! ## Acceptance transfer -/

/-- The base half of an extended accepting run is an accepting run of the plain product. -/
theorem isAcceptingRun_toSpec_of_fair (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) {σ : TLA.exec (Edge SysState α)}
    (hacc : (toSpecFair tgba sysSucc sysLabel sysInit extra).isAcceptingRun σ) :
    (toSpec tgba sysSucc sysLabel sysInit).isAcceptingRun σ := by
  intro i n
  obtain ⟨j, hj⟩ := hacc ⟨i.val, by omega⟩ n
  exact ⟨j, by simpa [toSpecFair, toSpec, i.isLt] using hj⟩

/-- The fairness half: conjunct `i` holds at the source of infinitely many edges of the run. -/
theorem fair_of_isAcceptingRun (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) {σ : TLA.exec (Edge SysState α)}
    (hacc : (toSpecFair tgba sysSucc sysLabel sysInit extra).isAcceptingRun σ)
    (i : Nat) (hi : i < extra.length) (n : Nat) :
    ∃ j, (fairConj extra i).eval (sysLabel (σ (n + j)).1) = true := by
  obtain ⟨j, hj⟩ := hacc ⟨tgba.numAcceptSets + i, by omega⟩ n
  have hcond : ¬ (tgba.numAcceptSets + i < tgba.numAcceptSets) := by omega
  exact ⟨j, by simpa [toSpecFair, hcond] using hj⟩

/-- An accepting run of the extended product decomposes into a system run, a language-membership witness for
the plain automaton, and one `□◇` witness per conjunct. -/
theorem gsp_correct1Fair [LawfulBEq α] (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) {σ : TLA.exec (Edge SysState α)}
    (hrun : (toSpecFair tgba sysSucc sysLabel sysInit extra).isRun σ)
    (hacc : (toSpecFair tgba sysSucc sysLabel sysInit extra).isAcceptingRun σ) :
    (Sys.toSpec sysSucc sysInit sysLabel).isRun (fun n => (σ n).1) ∧
    tgba.toSpec.accepts (fun n a => a ∈ sysLabel (σ n).1) ∧
    ∀ i, i < extra.length → ∀ n, ∃ j, (fairConj extra i).eval (sysLabel (σ (n + j)).1) = true := by
  obtain ⟨hsys, hlang⟩ := gsp_correct1 tgba sysSucc sysLabel sysInit
    ⟨(toSpecFair_isRun_iff _ _ _ _ _ _).mp hrun,
      isAcceptingRun_toSpec_of_fair tgba sysSucc sysLabel sysInit extra hacc⟩
  exact ⟨hsys, hlang, fun i hi n => fair_of_isAcceptingRun tgba sysSucc sysLabel sysInit extra hacc i hi n⟩

/-- A system run whose labeling lies in the automaton's language and which satisfies every conjunct infinitely
often lifts to an accepting run of the extended product. -/
theorem gsp_correct2Fair [LawfulBEq α] (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) {τ : TLA.exec SysState}
    (hsys : (Sys.toSpec sysSucc sysInit sysLabel).isRun τ)
    (hlang : tgba.toSpec.accepts (fun n a => a ∈ sysLabel (τ n)))
    (hfair : ∀ i, i < extra.length → ∀ n, ∃ j, (fairConj extra i).eval (sysLabel (τ (n + j))) = true) :
    ∃ σ : TLA.exec (Edge SysState α), τ = (fun n => (σ n).1) ∧
      (toSpecFair tgba sysSucc sysLabel sysInit extra).isRun σ ∧
      (toSpecFair tgba sysSucc sysLabel sysInit extra).isAcceptingRun σ := by
  obtain ⟨σ, hproj, hrun, hacc⟩ := gsp_correct2 tgba sysSucc sysLabel sysInit hsys hlang
  subst hproj
  refine ⟨σ, rfl, (toSpecFair_isRun_iff _ _ _ _ _ _).mpr hrun, fun i n => ?_⟩
  by_cases hi : (i : Nat) < tgba.numAcceptSets
  · obtain ⟨j, hj⟩ := hacc ⟨i.val, hi⟩ n
    exact ⟨j, by simpa [toSpecFair, toSpec, hi] using hj⟩
  · obtain ⟨j, hj⟩ := hfair ((i : Nat) - tgba.numAcceptSets) (by omega) n
    exact ⟨j, by simpa [toSpecFair, hi] using hj⟩

/-! ## Edge witness -/

/-- The extended spec's edge witness. A fairness mark constrains only the source system state, so any step edge
witnesses it. -/
def edgeWitnessFair (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α))
    (hbound : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets) :
    TEdgeWitness (toSpecFair tgba sysSucc sysLabel sysInit extra)
      (getSuccessors tgba sysSucc sysLabel) (edgeMarksFair tgba sysLabel extra) where
  stepEdge := (edgeWitness tgba sysSucc sysLabel sysInit).stepEdge
  stepEdge_spec := (edgeWitness tgba sysSucc sysLabel sysInit).stepEdge_spec
  markEdge p p' m :=
    if m < tgba.numAcceptSets then (edgeWitness tgba sysSucc sysLabel sysInit).markEdge p p' m
    else (edgeWitness tgba sysSucc sysLabel sysInit).stepEdge p p'
  markEdge_spec := by
    intro p p' m hm hstep hmark
    by_cases hlt : m < tgba.numAcceptSets
    · have hbase := (edgeWitness tgba sysSucc sysLabel sysInit).markEdge_spec (k := tgba.numAcceptSets)
        hlt hstep (mem_edgeMarks_of_mem_edgeMarksFair tgba sysLabel extra p p' m hlt hmark)
      simp only [hlt, if_pos]
      exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, by simpa [toSpecFair, hlt] using hbase.2.2.2⟩
    · obtain ⟨i, -, rfl, heval⟩ | hbase :=
        (mem_edgeMarksFair_iff tgba sysLabel extra p p' m).mp hmark |>.symm
      · have hstepspec := (edgeWitness tgba sysSucc sysLabel sysInit).stepEdge_spec hstep
        have hsrc : ((edgeWitness tgba sysSucc sysLabel sysInit).stepEdge p p').1 = p.1 :=
          congrArg Prod.fst hstepspec.2.1
        simp only [hlt, if_neg, not_false_eq_true]
        exact ⟨hstepspec.1, hstepspec.2.1, hstepspec.2.2, by simpa [toSpecFair, hlt, hsrc] using heval⟩
      · exact absurd (edgeMarks_lt tgba sysLabel hbound p p' m hbase) hlt

/-! ## From an accepting run to a lasso -/

/-- The product-state projection of a run of the extended spec steps along the product graph. -/
theorem acceptingRunFair_step (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) {σ : TLA.exec (Edge SysState α)}
    (hrun : (toSpecFair tgba sysSucc sysLabel sysInit extra).isRun σ) (n : Nat) :
    ((σ (n + 1)).1, (σ (n + 1)).2.2.1) ∈
      getSuccessors tgba sysSucc sysLabel ((σ n).1, (σ n).2.2.1) := by
  obtain ⟨⟨ht, hc, hsys⟩, hlink⟩ := hrun.2 n
  have h1 : (σ n).2.1 = (σ (n + 1)).1 := congrArg Prod.fst hlink
  have h2 : (σ n).2.2.2.target = (σ (n + 1)).2.2.1 := congrArg Prod.snd hlink
  exact (getSuccessors_mem_iff tgba sysSucc sysLabel).mpr ⟨(σ n).2.2.2, ht, hc, h1 ▸ hsys, h2⟩

/-- Every extended mark sits on infinitely many edges of the projected run. -/
theorem acceptingRunFair_marks (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) {σ : TLA.exec (Edge SysState α)}
    (hrun : (toSpecFair tgba sysSucc sysLabel sysInit extra).isRun σ)
    (hacc : (toSpecFair tgba sysSucc sysLabel sysInit extra).isAcceptingRun σ)
    (m : Nat) (hm : m < tgba.numAcceptSets + extra.length) (N : Nat) :
    ∃ n ≥ N, m ∈ edgeMarksFair tgba sysLabel extra
      ((σ n).1, (σ n).2.2.1) ((σ (n + 1)).1, (σ (n + 1)).2.2.1) := by
  obtain ⟨j, hj⟩ := hacc ⟨m, hm⟩ N
  refine ⟨N + j, by omega, ?_⟩
  rw [mem_edgeMarksFair_iff]
  by_cases hlt : m < tgba.numAcceptSets
  · obtain ⟨⟨ht, hc, -⟩, hlink⟩ := hrun.2 (N + j)
    have h2 : (σ (N + j)).2.2.2.target = (σ (N + j + 1)).2.2.1 := congrArg Prod.snd hlink
    exact Or.inl (Std.HashSet.mem_iff_contains.mpr
      ((mem_edgeMarks_iff tgba sysLabel _ _ m).mpr
        ⟨(σ (N + j)).2.2.2, ht, h2, hc, by simpa [toSpecFair, hlt] using hj⟩))
  · exact Or.inr ⟨m - tgba.numAcceptSets, by omega, by omega, by simpa [toSpecFair, hlt] using hj⟩

theorem exists_TAcceptingCycle_of_acceptingRunFair (tgba : TGBA α)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState) (extra : List (BoolFormula α))
    (fr : FiniteReach (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel))
    {σ : TLA.exec (Edge SysState α)}
    (hrun : (toSpecFair tgba sysSucc sysLabel sysInit extra).isRun σ)
    (hacc : (toSpecFair tgba sysSucc sysLabel sysInit extra).isAcceptingRun σ) :
    ∃ _ac : TAcceptingCycle (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel)
      (edgeMarksFair tgba sysLabel extra) (tgba.numAcceptSets + extra.length), True :=
  exists_TAcceptingCycle_of_run fr (σ := fun n => ((σ n).1, (σ n).2.2.1)) hrun.1
    (acceptingRunFair_step tgba sysSucc sysLabel sysInit extra hrun)
    (acceptingRunFair_marks tgba sysSucc sysLabel sysInit extra hrun hacc)

/-! ## Lasso witness -/

/-- The `toSpecFair` specialization of `TAcceptingCycle.toTValidLassoOf`. -/
def toTValidLassoProductFair (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α))
    (hbound : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets)
    (ac : TAcceptingCycle (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel)
      (edgeMarksFair tgba sysLabel extra) (tgba.numAcceptSets + extra.length)) :
    TValidLasso (toSpecFair tgba sysSucc sysLabel sysInit extra)
      (stemEdges (edgeWitnessFair tgba sysSucc sysLabel sysInit extra hbound).stepEdge ac.stem)
      (ac.cycleE (edgeWitnessFair tgba sysSucc sysLabel sysInit extra hbound)) :=
  ac.toTValidLassoOf (edgeWitnessFair tgba sysSucc sysLabel sysInit extra hbound) (fun hs => hs)

/-! ## Region cycles -/

/-- The region a propositional `FG` part carves out of the product, read off the system component's label. -/
def fgRegion (fg : BoolFormula α) (sysLabel : SysState → Std.HashSet α) :
    (SysState × Nat) → Bool := fun p => fg.eval (sysLabel p.1)

/-- The counterexample a region cycle describes: one system run that the automaton accepts, that satisfies
every conjunct infinitely often, and whose tail stays inside the region. -/
theorem exists_run_of_TRegionCycle [LawfulBEq α] (tgba : TGBA α)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState) (extra : List (BoolFormula α)) (fg : BoolFormula α)
    (hbound : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets)
    (rc : TRegionCycle (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel)
      (edgeMarksFair tgba sysLabel extra) (tgba.numAcceptSets + extra.length) (fgRegion fg sysLabel)) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      tgba.toSpec.accepts (fun n a => a ∈ sysLabel (τ n)) ∧
      (∀ i, i < extra.length → ∀ n, ∃ j, (fairConj extra i).eval (sysLabel (τ (n + j))) = true) ∧
      (∃ N, ∀ n, N ≤ n → fg.eval (sysLabel (τ n)) = true) := by
  obtain ⟨hτrun, hlang, hfair⟩ := gsp_correct1Fair tgba sysSucc sysLabel sysInit extra
    (toTValidLassoProductFair tgba sysSucc sysLabel sysInit extra hbound rc.toTAcceptingCycle).run_isRun
    (toTValidLassoProductFair tgba sysSucc sysLabel sysInit extra hbound
      rc.toTAcceptingCycle).run_isAccepting
  refine ⟨_, hτrun, hlang, hfair, ⟨(stemEdges (edgeWitnessFair tgba sysSucc sysLabel sysInit extra
    hbound).stepEdge rc.stem).length, fun n hn => ?_⟩⟩
  obtain ⟨i, hi, hsrc⟩ := TValidLasso.run_src_mem_cycle
    (edgeWitnessFair tgba sysSucc sysLabel sysInit extra hbound) rc.toTAcceptingCycle
    (toTValidLassoProductFair tgba sysSucc sysLabel sysInit extra hbound rc.toTAcceptingCycle)
    n (by omega)
  have hreg := rc.cycle_region _ (List.getElem_mem hi)
  rw [← hsrc] at hreg
  exact hreg

end TGBAProduct

end LTLLib
