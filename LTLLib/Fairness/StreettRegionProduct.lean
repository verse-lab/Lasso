module

/-
  The product satisfies the region-indexed Streett interface of `AbstractSpec/StreettSCCRegion.lean`.

  The two operators the interface asks for, the graph restricted to the steps whose letter satisfies a region, and the
  property automaton's marks carried by those same steps, are exactly `keptSuccs` and `keptEdgeMarks`. The four laws are
  their monotonicity and top lemmas, which is what lets the prune conjoin one option's region at a time.

  Defines:
  - `streettRSpecOf`: the hoisted conjuncts as an `RStreettSpec` over the product
  - `acceptingRRun`: the `RRun` a product run walks, carrying the letter and marks of the realization it
    actually takes at each step

  Proves:
  - `streettRSpecOf_compat`: it is compatible with the unrestricted product, so a restricted step is an
    ambient step and the top region restricts nothing
  - `acceptingRRun_marks`: the `RRun` meets the property automaton's marks infinitely often

  Sections:
  - The run a product execution walks
  - The collapse a `StateOnly` region gives
-/
public import LTLLib.AbstractSpec.StreettSCCRegion
public import LTLLib.Product

public section

namespace LTLLib

namespace TGBAProduct

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]
  [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [LawfulHashable SysState]

/-- The hoisted conjuncts as a region-indexed Streett spec over the product. The regions restrict steps by
their letter, so a conjunct's `FG ψ` may mention an edge atom. -/
@[expose] def streettRSpecOf (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (numMarks : Nat)
    (conjuncts : Array (Array (StreettOption (Std.HashSet α)))) :
    RStreettSpec (SysState × Nat) (Std.HashSet α) where
  numMarks := numMarks
  regionSuccs := fun r => keptSuccs tgba sysSucc sysLabel r
  regionMarks := fun r => keptEdgeMarks tgba sysSucc sysLabel r
  conjuncts := conjuncts
  -- the region scan gets a fused expansion instead of `regionMarks` per successor
  regionExpand := fun r => keptExpand tgba sysSucc sysLabel r
  regionExpand_coherent := fun r => keptExpand_coherent tgba sysSucc sysLabel r

/-- `streettRSpecOf` over one system callback, the three region functions being the `OfStep` forms. -/
@[expose] def streettRSpecOfStep (tgba : TGBA α) (sysStep : LSys.StepFn α SysState) (numMarks : Nat)
    (conjuncts : Array (Array (StreettOption (Std.HashSet α)))) :
    RStreettSpec (SysState × Nat) (Std.HashSet α) where
  numMarks := numMarks
  regionSuccs := fun r => keptSuccsOfStep tgba sysStep r
  regionMarks := fun r => keptEdgeMarksOfStep tgba sysStep r
  conjuncts := conjuncts
  regionExpand := fun r => keptExpandOfStep tgba sysStep r
  regionExpand_coherent := fun _ _ => rfl

omit [LawfulBEq SysState] [LawfulHashable SysState] in
theorem streettRSpecOfStep_eq (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (numMarks : Nat)
    (conjuncts : Array (Array (StreettOption (Std.HashSet α)))) :
    streettRSpecOfStep tgba (fun s => (sysSucc s, sysLabel s)) numMarks conjuncts
      = streettRSpecOf tgba sysSucc sysLabel numMarks conjuncts := rfl

omit [LawfulBEq SysState] [LawfulHashable SysState] in
/-- Projections, as rewrite rules, so a goal mentioning `regionSuccs` of this spec is never left to `whnf`. -/
@[simp] theorem streettRSpecOf_regionSuccs (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (numMarks : Nat) (conjuncts : Array (Array (StreettOption (Std.HashSet α))))
    (r : Std.HashSet α → Bool) :
    (streettRSpecOf tgba sysSucc sysLabel numMarks conjuncts).regionSuccs r
      = keptSuccs tgba sysSucc sysLabel r := rfl

omit [LawfulBEq SysState] [LawfulHashable SysState] in
@[simp] theorem streettRSpecOf_numMarks (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (numMarks : Nat) (conjuncts : Array (Array (StreettOption (Std.HashSet α)))) :
    (streettRSpecOf tgba sysSucc sysLabel numMarks conjuncts).numMarks = numMarks := rfl

omit [LawfulBEq SysState] [LawfulHashable SysState] in
@[simp] theorem streettRSpecOf_conjuncts (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (numMarks : Nat) (conjuncts : Array (Array (StreettOption (Std.HashSet α)))) :
    (streettRSpecOf tgba sysSucc sysLabel numMarks conjuncts).conjuncts = conjuncts := rfl

set_option maxHeartbeats 1000000 in
/-- The four compatibility laws, each a monotonicity or top lemma of the kept operators. -/
theorem streettRSpecOf_compat (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (numMarks : Nat)
    (conjuncts : Array (Array (StreettOption (Std.HashSet α)))) :
    (streettRSpecOf tgba sysSucc sysLabel numMarks conjuncts).Compat
      (getSuccessors tgba sysSucc sysLabel) (edgeMarks tgba sysSucc sysLabel) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun hle s t h => keptSuccs_mono tgba sysSucc sysLabel hle s t h
  · exact fun hle s t m h => keptEdgeMarks_mono tgba sysSucc sysLabel hle s t m h
  · exact keptSuccs_top tgba sysSucc sysLabel
  · exact keptEdgeMarks_top tgba sysSucc sysLabel

/-! ## The run a product execution walks

The run carries the letter its chosen realization reads, so "the region holds from some point on" is a statement about the
steps the run takes rather than about the states it passes through. -/

omit [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [LawfulHashable SysState] in
/-- The step law, stated over `keptSuccs` rather than the fields being defined. -/
private theorem rrun_step (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : Lentil.exec (Edge SysState α)} (hrun : (toSpec tgba sysSucc sysLabel sysInit).isRun σ)
    (n : Nat) (r : Std.HashSet α → Bool)
    (hr : r (LSys.letter (sysLabel (σ n).1) (σ n).2.1.1) = true) :
    ((σ (n + 1)).1, (σ (n + 1)).2.2.1)
      ∈ keptSuccs tgba sysSucc sysLabel r ((σ n).1, (σ n).2.2.1) := by
  obtain ⟨⟨ht, hc, hsys⟩, hlink⟩ := hrun.2 n
  show _ ∈ succsFrom tgba (σ n).2.2.1 (sysLabel (σ n).1) (keptSteps sysSucc sysLabel r (σ n).1)
  exact (succsFrom_mem_iff tgba _ _ _ _).mpr
    ⟨(σ n).2.1, mem_keptSteps.mpr ⟨hsys, hr⟩, (σ n).2.2.2, ht, hc,
      congrArg Prod.fst hlink, congrArg Prod.snd hlink⟩

/-- The mark law, the realization the run takes is still there after the restriction, so its marks survive with it. -/
private theorem rrun_mark (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : Lentil.exec (Edge SysState α)} (hrun : (toSpec tgba sysSucc sysLabel sysInit).isRun σ)
    (n : Nat) (r : Std.HashSet α → Bool)
    (hr : r (LSys.letter (sysLabel (σ n).1) (σ n).2.1.1) = true)
    (m : Nat) (hm : m ∈ (σ n).2.2.2.acceptMarks) :
    m ∈ keptEdgeMarks tgba sysSucc sysLabel r ((σ n).1, (σ n).2.2.1)
      ((σ (n + 1)).1, (σ (n + 1)).2.2.1) := by
  obtain ⟨⟨ht, hc, hsys⟩, hlink⟩ := hrun.2 n
  exact mem_keptEdgeMarks_of_realization tgba sysSucc sysLabel r
    ((σ n).1, (σ n).2.2.1) ((σ (n + 1)).1, (σ (n + 1)).2.2.1) ((σ n).2.1, (σ n).2.2.2)
    ((mem_realizationsFrom_iff _ _ _ _ _ _).mpr
      ⟨⟨mem_keptSteps.mpr ⟨hsys, hr⟩, congrArg Prod.fst hlink⟩, ht, congrArg Prod.snd hlink, hc⟩)
    hm

/-- The `RRun` a product run walks: its product states, the letter each step reads, and the marks the
automaton transition it takes carries. -/
@[expose] def acceptingRRun (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) (numMarks : Nat)
    (conjuncts : Array (Array (StreettOption (Std.HashSet α))))
    {σ : Lentil.exec (Edge SysState α)} (hrun : (toSpec tgba sysSucc sysLabel sysInit).isRun σ) :
    RRun (streettRSpecOf tgba sysSucc sysLabel numMarks conjuncts) (initialStates tgba sysInit) where
  st := fun n => ((σ n).1, (σ n).2.2.1)
  lets := fun n => LSys.letter (sysLabel (σ n).1) (σ n).2.1.1
  rmarks := fun n => (σ n).2.2.2.acceptMarks
  init := hrun.1
  step := by exact rrun_step tgba sysSucc sysLabel sysInit hrun
  mark := by exact rrun_mark tgba sysSucc sysLabel sysInit hrun

/-- The run meets every mark of the property automaton infinitely often, read on the realization it takes. -/
theorem acceptingRRun_marks (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) (numMarks : Nat)
    (conjuncts : Array (Array (StreettOption (Std.HashSet α))))
    {σ : Lentil.exec (Edge SysState α)} (hrun : (toSpec tgba sysSucc sysLabel sysInit).isRun σ)
    (hacc : (toSpec tgba sysSucc sysLabel sysInit).isAcceptingRun σ) (hnm : numMarks ≤ tgba.numAcceptSets) :
    ∀ m, m < numMarks → ∀ K, ∃ n ≥ K,
      m ∈ (acceptingRRun tgba sysSucc sysLabel sysInit numMarks conjuncts hrun).rmarks n := by
  intro m hm K
  obtain ⟨j, hj⟩ := hacc ⟨m, by omega⟩ K
  exact ⟨K + j, by omega, Std.HashSet.mem_iff_contains.mpr hj⟩

/-! ## The collapse a `StateOnly` region gives

A region that cannot see a step's own atoms (`LSys.StateOnly`) is decided by the source state alone even on a labelled
system, so the edge reading collapses to the state reading. `LSys.stateOnly_of_unlabelled` gives the stronger form, for
systems with no edge atoms at all. Without the hypothesis, separately available options need not be jointly available. -/

/-- A `StateOnly` region scores a run's letter exactly as it scores the source state's label. -/
theorem acceptingRRun_lets_stateOnly (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) (numMarks : Nat)
    (conjuncts : Array (Array (StreettOption (Std.HashSet α))))
    {σ : Lentil.exec (Edge SysState α)}
    (hrun : (toSpec tgba sysSucc sysLabel sysInit).isRun σ)
    {keep : Std.HashSet α → Bool} (hstate : LSys.StateOnly sysSucc sysLabel keep) (n : Nat) :
    keep ((acceptingRRun tgba sysSucc sysLabel sysInit numMarks conjuncts hrun).lets n)
      = keep (sysLabel (σ n).1) :=
  hstate (σ n).1 (σ n).2.1 (hrun.2 n).1.2.2

omit [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [LawfulHashable SysState] in
/-- A product step that survives a `StateOnly` restriction shows the restriction holds at the source
state, since the step scores as the source's label does. -/
theorem region_of_mem_keptSuccs_stateOnly (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) {keep : Std.HashSet α → Bool}
    (hstate : LSys.StateOnly sysSucc sysLabel keep) {p p' : SysState × Nat}
    (h : p' ∈ keptSuccs tgba sysSucc sysLabel keep p) :
    keep (sysLabel p.1) = true := by
  obtain ⟨st, hst, -, -, -, -, -⟩ := (succsFrom_mem_iff tgba _ _ _ _).mp h
  obtain ⟨hst', hkeep⟩ := mem_keptSteps.mp hst
  rwa [hstate p.1 st hst'] at hkeep

omit [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [LawfulHashable SysState] in
/-- Conversely, a `StateOnly` region that holds at `p.1` admits every product step out of `p`, so the restricted graph
agrees with the ambient one there. -/
theorem mem_keptSuccs_of_stateOnly (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) {keep : Std.HashSet α → Bool}
    (hstate : LSys.StateOnly sysSucc sysLabel keep) {p p' : SysState × Nat}
    (hp : keep (sysLabel p.1) = true) (h : p' ∈ getSuccessors tgba sysSucc sysLabel p) :
    p' ∈ keptSuccs tgba sysSucc sysLabel keep p := by
  obtain ⟨st, hst, t, ht, hc, h1, h2⟩ := (succsFrom_mem_iff tgba _ _ _ _).mp h
  exact (succsFrom_mem_iff tgba _ _ _ _).mpr
    ⟨st, mem_keptSteps.mpr ⟨hst, LSys.mem_of_stateOnly hstate hp hst⟩, t, ht, hc, h1, h2⟩

/-- The mark counterpart of `mem_keptSuccs_of_stateOnly`: where a `StateOnly` region holds, every
realization is in region, so the restricted marks of an edge are all of its marks. -/
theorem mem_keptEdgeMarks_of_stateOnly (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    {keep : Std.HashSet α → Bool} (hstate : LSys.StateOnly sysSucc sysLabel keep)
    {p p' : SysState × Nat} (hp : keep (sysLabel p.1) = true) {m : Nat}
    (hm : m ∈ edgeMarks tgba sysSucc sysLabel p p') :
    m ∈ keptEdgeMarks tgba sysSucc sysLabel keep p p' := by
  obtain ⟨rz, hrz, hmm⟩ :=
    (mem_edgeMarks_iff tgba sysSucc sysLabel p p' m).mp (Std.HashSet.mem_iff_contains.mp hm)
  obtain ⟨⟨hst, hst2⟩, ht, htgt, hc⟩ := (mem_realizations_iff tgba sysSucc sysLabel p p' rz).mp hrz
  exact mem_keptEdgeMarks_of_realization tgba sysSucc sysLabel keep p p' rz
    ((mem_realizationsFrom_iff tgba _ _ _ _ _).mpr
      ⟨⟨mem_keptSteps.mpr ⟨hst, LSys.mem_of_stateOnly hstate hp hst⟩, hst2⟩, ht, htgt, hc⟩)
    (Std.HashSet.mem_iff_contains.mpr hmm)

omit [BEq SysState] [Hashable SysState] [LawfulBEq SysState] [LawfulHashable SysState] in
/-- The unlabelled form, for state-labelled callers. -/
theorem region_of_mem_keptSuccs_unlabelled (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) {p p' : SysState × Nat}
    (h : p' ∈ keptSuccs tgba (LSys.unlabelled sysSucc) sysLabel keep p) :
    keep (sysLabel p.1) = true :=
  region_of_mem_keptSuccs_stateOnly tgba _ sysLabel
    (LSys.stateOnly_of_unlabelled sysSucc sysLabel keep) h

end TGBAProduct

end LTLLib
