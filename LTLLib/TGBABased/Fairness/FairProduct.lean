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
import LTLLib.Tactic.Set

namespace LTLLib

namespace TGBAProduct

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α] [BEq SysState] [Hashable SysState] [LawfulBEq SysState]

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

/-- The steps whose letter satisfies conjunct `i`, under a standing restriction `keep`. Named rather than
written inline so that the witness definitions below can mention it without the elaborator having to
recover it from a metavariable. -/
def fairKeep (keep : Std.HashSet α → Bool) (extra : List (BoolFormula α)) (i : Nat) :
    Std.HashSet α → Bool :=
  fun l => keep l && (fairConj extra i).eval l

theorem fairKeep_le {keep : Std.HashSet α → Bool} {extra : List (BoolFormula α)} {i : Nat}
    {l : Std.HashSet α} (h : fairKeep keep extra i l = true) :
    keep l = true ∧ (fairConj extra i).eval l = true := Bool.and_eq_true _ _ |>.mp h

/-- The fairness conjuncts a product *edge* carries, under a standing letter restriction `keep`: conjunct
`i` gives mark `base + i` exactly when some realization of the edge that survives `keep` reads a letter
satisfying `i`. That is membership of the graph restricted to `keep ∧ conjᵢ`, so this needs no new
machinery — it is §6.4's `keptSuccs` at a conjoined predicate, the same construction §6.5 uses for an
option's marks.

Reading the conjuncts on the *edge* rather than on its source is what lets a `□◇` mention an edge atom.
Unioning across parallel realizations over-approximates a single step, which `EdgeLabels.md` §6.3 shows is
sound for marks (and unsound for regions, which is why the region half is not built this way). -/
def fairMarksEdge (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) (base : Nat)
    (extra : List (BoolFormula α)) (p p' : SysState × Nat) : Std.HashSet Nat :=
  Std.HashSet.ofList
    (((List.range extra.length).filter fun i =>
      (keptSuccs tgba sysSucc sysLabel (fairKeep keep extra i) p).contains p').map (base + ·))

theorem mem_fairMarksEdge_iff (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) (base : Nat)
    (extra : List (BoolFormula α)) (p p' : SysState × Nat) (m : Nat) :
    m ∈ fairMarksEdge tgba sysSucc sysLabel keep base extra p p' ↔
      ∃ i, i < extra.length ∧ m = base + i ∧
        (keptSuccs tgba sysSucc sysLabel (fairKeep keep extra i) p).contains p' := by
  simp only [fairMarksEdge, Std.HashSet.mem_ofList, List.contains_iff_mem, List.mem_map,
    List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨i, ⟨hi, hc⟩, rfl⟩
    exact ⟨i, hi, rfl, hc⟩
  · rintro ⟨i, hi, rfl, hc⟩
    exact ⟨i, ⟨hi, hc⟩, rfl⟩

/-- The same marks read off an already-computed family of conjunct-restricted successor arrays. The fused
expansions build that family once per *source* and then only test membership per target, which is what
keeps `fairMarksEdge`'s `keptSuccs` call out of the inner loop. -/
def fairMarksOf (base : Nat) (extra : List (BoolFormula α))
    (ks : Nat → Array (SysState × Nat)) (p' : SysState × Nat) : Std.HashSet Nat :=
  Std.HashSet.ofList (((List.range extra.length).filter fun i => (ks i).contains p').map (base + ·))

theorem fairMarksEdge_eq_of (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) (base : Nat)
    (extra : List (BoolFormula α)) (p p' : SysState × Nat) :
    fairMarksEdge tgba sysSucc sysLabel keep base extra p p'
      = fairMarksOf base extra
          (fun i => keptSuccs tgba sysSucc sysLabel (fairKeep keep extra i) p) p' := rfl

/-- The conjunct marks with the per-source decision made once. On a source whose steps all carry the
empty letter every step reads `base`, so a conjunct holds on all of the source's edges or on none of them:
the marks are `fairMarks bm extra base`, one set shared by every successor, and the conjunct-restricted
family `ks` need not be built at all. `none` is the general path, `fairMarksOf` over `ks`. -/
def fairMarksGen (bm : Nat) (extra : List (BoolFormula α)) (uniform? : Option (Std.HashSet Nat))
    (ks : Nat → Array (SysState × Nat)) (p' : SysState × Nat) : Std.HashSet Nat :=
  match uniform? with
  | some m => m
  | none => fairMarksOf bm extra ks p'

/-- The shared conjunct marks, when every step reads `base`. -/
def fairMarksTable (bm : Nat) (extra : List (BoolFormula α)) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) : Option (Std.HashSet Nat) :=
  if steps.all (·.1.isEmpty) then some (fairMarks bm extra base) else none

omit [BEq SysState] [Hashable SysState] [LawfulBEq SysState] in
theorem letter_of_isEmpty (base L : Std.HashSet α) (h : L.isEmpty = true) : LSys.letter base L = base := by
  simp [LSys.letter, h]

omit [Hashable SysState] [LawfulBEq SysState] in
/-- On a uniform source, `fairMarksOf` over the conjunct-restricted family is `fairMarks` at the source's
letter, for every successor the source's kept steps generate. -/
theorem fairMarksOf_uniform [LawfulBEq SysState] (tgba : TGBA α) (q : Nat) (base : Std.HashSet α)
    (steps : Array (LStep α SysState)) (keep : Std.HashSet α → Bool) (bm : Nat)
    (extra : List (BoolFormula α)) (p' : SysState × Nat)
    (hu : steps.all (·.1.isEmpty) = true)
    (hp' : ∃ st ∈ steps, keep (LSys.letter base st.1) = true ∧ ∃ t ∈ tgba.getSuccessors q,
      transCompatible t (LSys.letter base st.1) = true ∧ st.2 = p'.1 ∧ t.target = p'.2) :
    fairMarksOf bm extra (fun i => keptSuccsFrom tgba q base steps (fairKeep keep extra i)) p'
      = fairMarks bm extra base := by
  have hl : ∀ st ∈ steps, LSys.letter base st.1 = base := fun st hst =>
    letter_of_isEmpty base st.1 (Array.all_eq_true_iff_forall_mem.mp hu st hst)
  unfold fairMarksOf fairMarks
  congr 2
  refine List.filter_congr fun i _ => ?_
  obtain ⟨st, hst, hk, t, ht, hc, h1, h2⟩ := hp'
  rw [hl st hst] at hk hc
  apply Bool.eq_iff_iff.mpr
  show (keptSuccsFrom tgba q base steps (fairKeep keep extra i)).contains p' = true ↔ _
  rw [Array.contains_iff_mem, keptSuccsFrom, succsFrom_mem_iff]
  constructor
  · rintro ⟨st', hst', -⟩
    simp only [keptStepsFrom, Array.mem_filter] at hst'
    have hk' := hst'.2
    rw [hl st' hst'.1] at hk'
    exact (Bool.and_eq_true _ _ |>.mp hk').2
  · intro hi
    refine ⟨st, ?_, t, ht, ?_, h1, h2⟩
    · simp only [keptStepsFrom, Array.mem_filter]
      exact ⟨hst, by rw [hl st hst]; exact Bool.and_eq_true _ _ |>.mpr ⟨hk, hi⟩⟩
    · rw [hl st hst]; exact hc

/-- `edgeMarks` extended with one mark per fairness conjunct, indexed from `tgba.numAcceptSets`. -/
def edgeMarksFair (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α)
    (extra : List (BoolFormula α)) : (SysState × Nat) → (SysState × Nat) → Std.HashSet Nat :=
  fun p p' => (edgeMarks tgba sysSucc sysLabel p p').union
    (fairMarksEdge tgba sysSucc sysLabel (fun _ => true) tgba.numAcceptSets extra p p')

theorem mem_edgeMarksFair_iff (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α)
    (extra : List (BoolFormula α)) (p p' : SysState × Nat) (m : Nat) :
    m ∈ edgeMarksFair tgba sysSucc sysLabel extra p p' ↔
      m ∈ edgeMarks tgba sysSucc sysLabel p p' ∨
      ∃ i, i < extra.length ∧ m = tgba.numAcceptSets + i ∧
        (keptSuccs tgba sysSucc sysLabel (fairKeep (fun _ => true) extra i) p).contains p' := by
  rw [← mem_fairMarksEdge_iff]
  simp only [edgeMarksFair, Std.HashSet.mem_iff_contains, Std.HashSet.union_eq,
    Std.HashSet.contains_union, Bool.or_eq_true]

/-- The conjunct marks sit above `numAcceptSets`, so a base mark is never mistaken for a fairness one. -/
theorem mem_edgeMarks_of_mem_edgeMarksFair (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α)
    (extra : List (BoolFormula α)) (p p' : SysState × Nat) (m : Nat) (hlt : m < tgba.numAcceptSets)
    (hm : m ∈ edgeMarksFair tgba sysSucc sysLabel extra p p') : m ∈ edgeMarks tgba sysSucc sysLabel p p' := by
  rcases (mem_edgeMarksFair_iff tgba sysSucc sysLabel extra p p' m).mp hm with h | ⟨i, -, rfl, -⟩
  · exact h
  · omega

/-- Every extended mark stays below `numAcceptSets + extra.length`. -/
theorem edgeMarksFair_lt (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α)
    (hbound : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets)
    (extra : List (BoolFormula α)) (p p' : SysState × Nat) (m : Nat)
    (hm : m ∈ edgeMarksFair tgba sysSucc sysLabel extra p p') :
    m < tgba.numAcceptSets + extra.length := by
  rcases (mem_edgeMarksFair_iff tgba sysSucc sysLabel extra p p' m).mp hm with h | ⟨i, hi, rfl, -⟩
  · have := edgeMarks_lt tgba sysSucc sysLabel hbound p p' m h
    omega
  · omega

/-- The `□◇` reading of the conjuncts and the indexed `eval` reading the marks use are one statement, of
the sequence of *letters* a run reads. On a state-labelled system that sequence is `sysLabel ∘ τ`, which is
`fair_iff_indexed`; on a labelled one it is the letter each step contributes, which is what an edge atom in
a `□◇` needs. -/
theorem fair_iff_indexed_letters [LawfulBEq α] (extra : List (BoolFormula α))
    (lets : Nat → Std.HashSet α) :
    (∀ b ∈ extra, (BoolFormula.alwaysEventually b).satisfies (fun i a => a ∈ lets i)) ↔
      ∀ i, i < extra.length → ∀ n, ∃ j, (fairConj extra i).eval (lets (n + j)) = true := by
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

/-- The `◇□` reading of a conjunct and the index form the region restriction uses are one statement, on the
sequence of letters. See `fair_iff_indexed_letters`. -/
theorem eventuallyAlways_iff_indexed_letters [LawfulBEq α] (b : BoolFormula α)
    (lets : Nat → Std.HashSet α) :
    (BoolFormula.eventuallyAlways b).satisfies (fun i a => a ∈ lets i) ↔
      ∃ N, ∀ n, N ≤ n → b.eval (lets n) = true := by
  rw [BoolFormula.satisfies_eventuallyAlways]
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have h := hN (n - N)
    rw [show N + (n - N) = n from by omega] at h
    exact (BoolFormula.eval_iff_holds b (lets n)).mpr h
  · rintro ⟨N, hN⟩
    exact ⟨N, fun k => (BoolFormula.eval_iff_holds b _).mp (hN (N + k) (by omega))⟩

/-- The state-labelled specialization, which is how every caller that has not been lifted reads it. -/
theorem fair_iff_indexed [LawfulBEq α] (extra : List (BoolFormula α))
    (sysLabel : SysState → Std.HashSet α) (τ : Nat → SysState) :
    (∀ b ∈ extra, (BoolFormula.alwaysEventually b).satisfies (fun i a => a ∈ sysLabel (τ i))) ↔
      ∀ i, i < extra.length → ∀ n, ∃ j, (fairConj extra i).eval (sysLabel (τ (n + j))) = true :=
  fair_iff_indexed_letters extra (fun i => sysLabel (τ i))

theorem eventuallyAlways_iff_indexed [LawfulBEq α] (b : BoolFormula α)
    (sysLabel : SysState → Std.HashSet α) (τ : Nat → SysState) :
    (BoolFormula.eventuallyAlways b).satisfies (fun i a => a ∈ sysLabel (τ i)) ↔
      ∃ N, ∀ n, N ≤ n → b.eval (sysLabel (τ n)) = true :=
  eventuallyAlways_iff_indexed_letters b (fun i => sysLabel (τ i))

/-- The labelled specialization: the letters a run of a labelled system reads *are* its valuation, so the
two indexed readings apply to `LSys.valuation` with nothing in between. These are what the fairness entry
points state their hypotheses with. -/
theorem fair_iff_indexed_run [LawfulBEq α] (extra : List (BoolFormula α))
    (sysLabel : SysState → Std.HashSet α) (ρ : Nat → LSys.Edge α SysState) :
    (∀ b ∈ extra, (BoolFormula.alwaysEventually b).satisfies (LSys.valuation sysLabel ρ)) ↔
      ∀ i, i < extra.length → ∀ n, ∃ j,
        (fairConj extra i).eval (LSys.letter (sysLabel (ρ (n + j)).1) (ρ (n + j)).2.1) = true :=
  fair_iff_indexed_letters extra (fun i => LSys.letter (sysLabel (ρ i).1) (ρ i).2.1)

theorem eventuallyAlways_iff_indexed_run [LawfulBEq α] (b : BoolFormula α)
    (sysLabel : SysState → Std.HashSet α) (ρ : Nat → LSys.Edge α SysState) :
    (BoolFormula.eventuallyAlways b).satisfies (LSys.valuation sysLabel ρ) ↔
      ∃ N, ∀ n, N ≤ n → b.eval (LSys.letter (sysLabel (ρ n).1) (ρ n).2.1) = true :=
  eventuallyAlways_iff_indexed_letters b (fun i => LSys.letter (sysLabel (ρ i).1) (ρ i).2.1)

/-- The fused expansion for the extended product: `expand`'s successors, with each edge's marks widened by
the fairness conjuncts *that edge* carries.

PERF: the fairness part is per-edge, so both halves are kept out of the inner loop deliberately. The base
marks come from the grouped table built once per source (`marksTableGen`/`genMarksFromShared`, §13.24).
The conjunct marks are decided once per source when every step reads `base` (`fairMarksTable`: one
`fairMarks` set shared by every successor, `ks` not built), and otherwise from the `extra.length`
conjunct-restricted successor arrays built once per source in `ks`, a membership test per (target,
conjunct) — a deep state comparison per element, which is why the uniform path exists (§13.27, §13.29).
Writing this as `e.1.map (edgeMarksFair … p)` would be much shorter and would cost a full re-expansion of
`p` per (edge, conjunct).

`base` and `steps` are threaded into `ks` through `keptSuccsFrom` rather than letting each conjunct call
`keptSuccs` — which re-enters `sysLabel` *twice* and `sysSucc` once, per conjunct. That made the callbacks
`1 + 2k` and `1 + k` per product state for `k` conjuncts; they are now 1 and 1. On the Veil side each
entry is a `tr` call, and `k` is `3n` on the nested-fairness workload. -/
def expandFair (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (extra : List (BoolFormula α)) (p : SysState × Nat) :
    Array (SysState × Nat) × Array (Std.HashSet Nat) × Array Nat :=
  let base := sysLabel p.1
  let steps := LSys.totalize sysSucc p.1
  -- PERF (§13.29): the base marks come from the grouped table computed once per source, not from a
  -- per-successor `edgeMarksFrom` that rebuilt it; and on a uniform source the conjunct marks are one
  -- shared set and the conjunct-restricted family is not built. The general path is unchanged.
  let byTgt? := marksTableGen tgba p.2 base steps
  let fm? := fairMarksTable tgba.numAcceptSets extra base steps
  let out := succsFrom tgba p.2 base steps
  let ks : Array (Array (SysState × Nat)) :=
    if steps.all (·.1.isEmpty) then #[] else (Array.range extra.length).map fun i =>
      keptSuccsFrom tgba p.2 base steps (fairKeep (fun _ => true) extra i)
  (out, Array.zipWith (fun ms p' =>
    ms.union (fairMarksGen tgba.numAcceptSets extra fm? (fun i => ks[i]!) p'))
    (out.map fun p' => genMarksFromShared tgba p.2 base steps byTgt? p') out, #[])

theorem expandFair_coherent [LawfulHashable SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (extra : List (BoolFormula α)) :
    ExpandCoherent (getSuccessors tgba sysSucc sysLabel) (edgeMarksFair tgba sysSucc sysLabel extra)
      (expandFair tgba sysSucc sysLabel extra) := by
  intro p
  obtain ⟨s, q⟩ := p
  refine Prod.ext rfl ?_
  show Array.zipWith _ ((succsFrom tgba q (sysLabel s) (LSys.totalize sysSucc s)).map _)
    (succsFrom tgba q (sysLabel s) (LSys.totalize sysSucc s))
    = (getSuccessors tgba sysSucc sysLabel (s, q)).map (edgeMarksFair tgba sysSucc sysLabel extra (s, q))
  refine Array.ext (by simp [getSuccessors]) fun k hk1 hk2 => ?_
  simp only [Array.getElem_zipWith, Array.getElem_map, edgeMarksFair, fairMarksEdge_eq_of,
    getSuccessors, edgeMarks]
  have hmem := Array.getElem_mem (xs := succsFrom tgba q (sysLabel s) (LSys.totalize sysSucc s))
    (by simpa using hk1)
  rw [genMarksFromShared_eq tgba q _ _ hmem]
  congr 1
  by_cases hu : (LSys.totalize sysSucc s).all (·.1.isEmpty) = true
  · simp only [fairMarksGen, fairMarksTable, hu, if_true]
    obtain ⟨st, hst, t, ht, hc, h1, h2⟩ := (succsFrom_mem_iff _ _ _ _ _).mp hmem
    exact (fairMarksOf_uniform tgba q _ _ (fun _ => true) tgba.numAcceptSets extra _ hu
      ⟨st, hst, rfl, t, ht, hc, h1, h2⟩).symm
  · simp only [fairMarksGen, fairMarksTable, hu, if_false, Bool.false_eq_true]
    unfold fairMarksOf
    congr 2
    refine List.filter_congr fun i hi => ?_
    simp only []
    rw [getElem!_pos _ i (by simpa using List.mem_range.mp hi), Array.getElem_map,
      Array.getElem_range]
    -- `keptSuccsFrom` with the source's own label and steps *is* `keptSuccs`, but only definitionally
    rfl

/-! ## Extended product spec -/

/-- The abstract product spec with `extra.length` further marks, conjunct `i` carried by an edge iff the
letter *that edge reads* satisfies it. All other fields are `toSpec`'s.

Reading the conjunct on the edge's letter rather than on its source state is what makes a `□◇` over an
edge atom mean anything; on a system with no edge atoms every step reads its source's label and this is
the old condition. -/
def toSpecFair (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) :
    TOASpec (SysState × Nat) (Edge SysState α) α (tgba.numAcceptSets + extra.length) where
  src e := (e.1, e.2.2.1)
  dst e := (e.2.1.2, e.2.2.2.target)
  valid e := e.2.2.2 ∈ tgba.getSuccessors e.2.2.1 ∧
    transCompatible e.2.2.2 (LSys.letter (sysLabel e.1) e.2.1.1) = true ∧
    e.2.1 ∈ LSys.totalize sysSucc e.1
  initial p := p ∈ initialStates tgba sysInit
  labelCompat e v := ∀ a, v a ↔ a ∈ LSys.letter (sysLabel e.1) e.2.1.1
  acceptMark i e :=
    if (i : Nat) < tgba.numAcceptSets then e.2.2.2.acceptMarks.contains (i : Nat)
    else (fairConj extra ((i : Nat) - tgba.numAcceptSets)).eval
      (LSys.letter (sysLabel e.1) e.2.1.1) = true

/-- The extended spec differs from `toSpec` only in its acceptance condition. -/
theorem toSpecFair_isRun_iff (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) (σ : Lentil.exec (Edge SysState α)) :
    (toSpecFair tgba sysSucc sysLabel sysInit extra).isRun σ ↔
      (toSpec tgba sysSucc sysLabel sysInit).isRun σ := Iff.rfl

/-! ## Acceptance transfer -/

/-- The base half of an extended accepting run is an accepting run of the plain product. -/
theorem isAcceptingRun_toSpec_of_fair (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) {σ : Lentil.exec (Edge SysState α)}
    (hacc : (toSpecFair tgba sysSucc sysLabel sysInit extra).isAcceptingRun σ) :
    (toSpec tgba sysSucc sysLabel sysInit).isAcceptingRun σ := by
  intro i n
  obtain ⟨j, hj⟩ := hacc ⟨i.val, by omega⟩ n
  exact ⟨j, by simpa [toSpecFair, toSpec, i.isLt] using hj⟩

/-- The fairness half: conjunct `i` is satisfied by the letter of infinitely many edges of the run. -/
theorem fair_of_isAcceptingRun (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) {σ : Lentil.exec (Edge SysState α)}
    (hacc : (toSpecFair tgba sysSucc sysLabel sysInit extra).isAcceptingRun σ)
    (i : Nat) (hi : i < extra.length) (n : Nat) :
    ∃ j, (fairConj extra i).eval
      (LSys.letter (sysLabel (σ (n + j)).1) (σ (n + j)).2.1.1) = true := by
  obtain ⟨j, hj⟩ := hacc ⟨tgba.numAcceptSets + i, by omega⟩ n
  have hcond : ¬ (tgba.numAcceptSets + i < tgba.numAcceptSets) := by omega
  exact ⟨j, by simpa [toSpecFair, hcond] using hj⟩

/-- An accepting run of the extended product decomposes into a system run, a language-membership witness for
the plain automaton, and one `□◇` witness per conjunct. -/
theorem gsp_correct1Fair [LawfulBEq α] (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) {σ : Lentil.exec (Edge SysState α)}
    (hrun : (toSpecFair tgba sysSucc sysLabel sysInit extra).isRun σ)
    (hacc : (toSpecFair tgba sysSucc sysLabel sysInit extra).isAcceptingRun σ) :
    (LSys.toSpec sysSucc sysInit sysLabel).isRun (fun n => ((σ n).1, (σ n).2.1)) ∧
    tgba.toSpec.accepts (LSys.valuation sysLabel (fun n => ((σ n).1, (σ n).2.1))) ∧
    ∀ i, i < extra.length → ∀ n, ∃ j, (fairConj extra i).eval
      (LSys.letter (sysLabel (σ (n + j)).1) (σ (n + j)).2.1.1) = true := by
  obtain ⟨hsys, hlang⟩ := gsp_correct1 tgba sysSucc sysLabel sysInit
    ⟨(toSpecFair_isRun_iff _ _ _ _ _ _).mp hrun,
      isAcceptingRun_toSpec_of_fair tgba sysSucc sysLabel sysInit extra hacc⟩
  exact ⟨hsys, hlang, fun i hi n => fair_of_isAcceptingRun tgba sysSucc sysLabel sysInit extra hacc i hi n⟩

/-- A system run whose labeling lies in the automaton's language and which satisfies every conjunct infinitely
often lifts to an accepting run of the extended product. -/
theorem gsp_correct2Fair [LawfulBEq α] (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) {ρ : Lentil.exec (LSys.Edge α SysState)}
    (hsys : (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ)
    (hlang : tgba.toSpec.accepts (LSys.valuation sysLabel ρ))
    (hfair : ∀ i, i < extra.length → ∀ n, ∃ j,
      (fairConj extra i).eval (LSys.letter (sysLabel (ρ (n + j)).1) (ρ (n + j)).2.1) = true) :
    ∃ σ : Lentil.exec (Edge SysState α), ρ = (fun n => ((σ n).1, (σ n).2.1)) ∧
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

/-- The extended spec's edge witness. A fairness mark now constrains the *letter*, so it is witnessed by a
realization reading a satisfying one — which is the step edge of `keptEdgeWitness` at the conjunct's own
restriction, no new selection machinery needed. -/
def edgeWitnessFair (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α))
    (hbound : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets) :
    TEdgeWitness (toSpecFair tgba sysSucc sysLabel sysInit extra)
      (getSuccessors tgba sysSucc sysLabel) (edgeMarksFair tgba sysSucc sysLabel extra) where
  stepEdge := (edgeWitness tgba sysSucc sysLabel sysInit).stepEdge
  stepEdge_spec := (edgeWitness tgba sysSucc sysLabel sysInit).stepEdge_spec
  markEdge p p' m :=
    if m < tgba.numAcceptSets then (edgeWitness tgba sysSucc sysLabel sysInit).markEdge p p' m
    else (keptEdgeWitness tgba sysSucc sysLabel
      (fairKeep (fun _ => true) extra (m - tgba.numAcceptSets)) sysInit).stepEdge p p'
  markEdge_spec := by
    intro p p' m hm hstep hmark
    by_cases hlt : m < tgba.numAcceptSets
    · have hbase := (edgeWitness tgba sysSucc sysLabel sysInit).markEdge_spec (k := tgba.numAcceptSets)
        hlt hstep (mem_edgeMarks_of_mem_edgeMarksFair tgba sysSucc sysLabel extra p p' m hlt hmark)
      simp only [hlt, if_pos]
      exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, by simpa [toSpec, toSpecFair, hlt] using hbase.2.2.2⟩
    · obtain ⟨i, -, heq, hmem⟩ | hbase :=
        (mem_edgeMarksFair_iff tgba sysSucc sysLabel extra p p' m).mp hmark |>.symm
      · have hi : m - tgba.numAcceptSets = i := by omega
        have hmem' : p' ∈ keptSuccs tgba sysSucc sysLabel
            (fairKeep (fun _ => true) extra (m - tgba.numAcceptSets)) p := by
          rw [hi]; exact Array.contains_iff_mem.mp hmem
        have hstepspec := (keptEdgeWitness tgba sysSucc sysLabel
          (fairKeep (fun _ => true) extra (m - tgba.numAcceptSets)) sysInit).stepEdge_spec hmem'
        have hletter := keptEdgeWitness_stepEdge_letter tgba sysSucc sysLabel
          (fairKeep (fun _ => true) extra (m - tgba.numAcceptSets)) sysInit p p' hmem'
        simp only [hlt, if_neg, not_false_eq_true]
        exact ⟨hstepspec.1, hstepspec.2.1, hstepspec.2.2,
          by simpa [toSpecFair, hlt] using (fairKeep_le hletter).2⟩
      · exact absurd (edgeMarks_lt tgba sysSucc sysLabel hbound p p' m hbase) hlt

/-! ## From an accepting run to a lasso -/

/-- The product-state projection of a run of the extended spec steps along the product graph. -/
theorem acceptingRunFair_step (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) {σ : Lentil.exec (Edge SysState α)}
    (hrun : (toSpecFair tgba sysSucc sysLabel sysInit extra).isRun σ) (n : Nat) :
    ((σ (n + 1)).1, (σ (n + 1)).2.2.1) ∈
      getSuccessors tgba sysSucc sysLabel ((σ n).1, (σ n).2.2.1) := by
  obtain ⟨⟨ht, hc, hsys⟩, hlink⟩ := hrun.2 n
  have h1 : (σ n).2.1.2 = (σ (n + 1)).1 := congrArg Prod.fst hlink
  have h2 : (σ n).2.2.2.target = (σ (n + 1)).2.2.1 := congrArg Prod.snd hlink
  exact (getSuccessors_mem_iff tgba sysSucc sysLabel).mpr
    ⟨(σ n).2.1, hsys, (σ n).2.2.2, ht, hc, h1, h2⟩

/-- Every extended mark sits on infinitely many edges of the projected run. -/
theorem acceptingRunFair_marks (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) {σ : Lentil.exec (Edge SysState α)}
    (hrun : (toSpecFair tgba sysSucc sysLabel sysInit extra).isRun σ)
    (hacc : (toSpecFair tgba sysSucc sysLabel sysInit extra).isAcceptingRun σ)
    (m : Nat) (hm : m < tgba.numAcceptSets + extra.length) (N : Nat) :
    ∃ n ≥ N, m ∈ edgeMarksFair tgba sysSucc sysLabel extra
      ((σ n).1, (σ n).2.2.1) ((σ (n + 1)).1, (σ (n + 1)).2.2.1) := by
  obtain ⟨j, hj⟩ := hacc ⟨m, hm⟩ N
  refine ⟨N + j, by omega, ?_⟩
  rw [mem_edgeMarksFair_iff]
  by_cases hlt : m < tgba.numAcceptSets
  · obtain ⟨⟨ht, hc, hsys⟩, hlink⟩ := hrun.2 (N + j)
    have h1 : (σ (N + j)).2.1.2 = (σ (N + j + 1)).1 := congrArg Prod.fst hlink
    have h2 : (σ (N + j)).2.2.2.target = (σ (N + j + 1)).2.2.1 := congrArg Prod.snd hlink
    refine Or.inl (Std.HashSet.mem_iff_contains.mpr
      ((mem_edgeMarks_iff tgba sysSucc sysLabel _ _ m).mpr
        ⟨((σ (N + j)).2.1, (σ (N + j)).2.2.2), ?_, by simpa [toSpecFair, hlt] using hj⟩))
    exact (mem_realizations_iff tgba sysSucc sysLabel _ _ _).mpr ⟨⟨hsys, h1⟩, ht, h2, hc⟩
  · refine Or.inr ⟨m - tgba.numAcceptSets, by omega, by omega, ?_⟩
    -- the run's own step reads a letter satisfying the conjunct, so the edge survives that restriction
    obtain ⟨⟨ht, hc, hsys⟩, hlink⟩ := hrun.2 (N + j)
    have heval : fairKeep (fun _ => true) extra (m - tgba.numAcceptSets)
        (LSys.letter (sysLabel (σ (N + j)).1) (σ (N + j)).2.1.1) = true := by
      simpa [fairKeep, toSpecFair, hlt] using hj
    refine Array.contains_iff_mem.mpr ?_
    show _ ∈ succsFrom tgba _ _ (keptSteps sysSucc sysLabel _ _)
    exact (succsFrom_mem_iff tgba _ _ _ _).mpr
      ⟨(σ (N + j)).2.1, mem_keptSteps.mpr ⟨hsys, heval⟩, (σ (N + j)).2.2.2, ht, hc,
        congrArg Prod.fst hlink, congrArg Prod.snd hlink⟩

/-- Where the run's own step reads a letter `keep` admits, the projected product edge survives the
restriction.

This is the labelled counterpart of `mem_keptSuccs_unlabelled`, and it has to be stated on the run rather
than on the endpoints. With edge atoms a product pair `(p, p')` may be realized by several steps reading
different letters (`EdgeLabels.md` §6.3), so "`keep` holds somewhere out of `p.1`" does not put `p'` in the
restricted graph — only the step the run actually takes is known to satisfy it, and that step is what the
membership is built from. -/
theorem acceptingRunFair_keptStep (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) {σ : Lentil.exec (Edge SysState α)}
    (hrun : (toSpecFair tgba sysSucc sysLabel sysInit extra).isRun σ)
    (keep : Std.HashSet α → Bool) (n : Nat)
    (hkeep : keep (LSys.letter (sysLabel (σ n).1) (σ n).2.1.1) = true) :
    ((σ (n + 1)).1, (σ (n + 1)).2.2.1) ∈
      keptSuccs tgba sysSucc sysLabel keep ((σ n).1, (σ n).2.2.1) := by
  obtain ⟨⟨ht, hc, hsys⟩, hlink⟩ := hrun.2 n
  exact (succsFrom_mem_iff tgba _ _ _ _).mpr
    ⟨(σ n).2.1, mem_keptSteps.mpr ⟨hsys, hkeep⟩, (σ n).2.2.2, ht, hc,
      congrArg Prod.fst hlink, congrArg Prod.snd hlink⟩

theorem exists_TAcceptingCycle_of_acceptingRunFair (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState) (extra : List (BoolFormula α))
    (fr : FiniteReach (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel))
    {σ : Lentil.exec (Edge SysState α)}
    (hrun : (toSpecFair tgba sysSucc sysLabel sysInit extra).isRun σ)
    (hacc : (toSpecFair tgba sysSucc sysLabel sysInit extra).isAcceptingRun σ) :
    ∃ _ac : TAcceptingCycle (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel)
      (edgeMarksFair tgba sysSucc sysLabel extra) (tgba.numAcceptSets + extra.length), True :=
  exists_TAcceptingCycle_of_run fr (σ := fun n => ((σ n).1, (σ n).2.2.1)) hrun.1
    (acceptingRunFair_step tgba sysSucc sysLabel sysInit extra hrun)
    (acceptingRunFair_marks tgba sysSucc sysLabel sysInit extra hrun hacc)

/-! ## Lasso witness -/

/-- The `toSpecFair` specialization of `TAcceptingCycle.toTValidLassoOf`. -/
def toTValidLassoProductFair (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α))
    (hbound : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets)
    (ac : TAcceptingCycle (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel)
      (edgeMarksFair tgba sysSucc sysLabel extra) (tgba.numAcceptSets + extra.length)) :
    TValidLasso (toSpecFair tgba sysSucc sysLabel sysInit extra)
      (stemEdges (edgeWitnessFair tgba sysSucc sysLabel sysInit extra hbound).stepEdge ac.stem)
      (ac.cycleE (edgeWitnessFair tgba sysSucc sysLabel sysInit extra hbound)) :=
  ac.toTValidLassoOf (edgeWitnessFair tgba sysSucc sysLabel sysInit extra hbound) (fun hs => hs)

/-! ## Region cycles -/

/-- Marks of the restricted extended product: the restricted base marks, widened by the fairness conjuncts
the source satisfies. -/
def keptEdgeMarksFair (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) (extra : List (BoolFormula α)) :
    (SysState × Nat) → (SysState × Nat) → Std.HashSet Nat :=
  fun p p' => (keptEdgeMarks tgba sysSucc sysLabel keep p p').union
    (fairMarksEdge tgba sysSucc sysLabel keep tgba.numAcceptSets extra p p')

/-- The fused expansion for the restricted extended product. Same shape, and the same `PERF` note as
`expandFair`. -/
def keptExpandFair (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) (extra : List (BoolFormula α)) (p : SysState × Nat) :
    Array (SysState × Nat) × Array (Std.HashSet Nat) × Array Nat :=
  let base := sysLabel p.1
  let steps := LSys.totalize sysSucc p.1
  let kept := keptStepsFrom base steps keep
  let byTgt? := marksTableGen tgba p.2 base kept
  let fm? := fairMarksTable tgba.numAcceptSets extra base steps
  let out := succsFrom tgba p.2 base kept
  let ks : Array (Array (SysState × Nat)) :=
    if steps.all (·.1.isEmpty) then #[] else (Array.range extra.length).map fun i =>
      keptSuccsFrom tgba p.2 base steps (fairKeep keep extra i)
  (out, Array.zipWith (fun ms p' =>
    ms.union (fairMarksGen tgba.numAcceptSets extra fm? (fun i => ks[i]!) p'))
    (out.map fun p' => genMarksFromShared tgba p.2 base kept byTgt? p') out, #[])

theorem keptExpandFair_coherent [LawfulHashable SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) (extra : List (BoolFormula α)) :
    ExpandCoherent (keptSuccs tgba sysSucc sysLabel keep)
      (keptEdgeMarksFair tgba sysSucc sysLabel keep extra)
      (keptExpandFair tgba sysSucc sysLabel keep extra) := by
  intro p
  obtain ⟨s, q⟩ := p
  refine Prod.ext rfl ?_
  show Array.zipWith _ ((succsFrom tgba q (sysLabel s)
      (keptStepsFrom (sysLabel s) (LSys.totalize sysSucc s) keep)).map _)
    (succsFrom tgba q (sysLabel s) (keptStepsFrom (sysLabel s) (LSys.totalize sysSucc s) keep))
    = (keptSuccs tgba sysSucc sysLabel keep (s, q)).map
        (keptEdgeMarksFair tgba sysSucc sysLabel keep extra (s, q))
  refine Array.ext (by simp [keptSuccs, keptSuccsFrom]) fun k hk1 hk2 => ?_
  simp only [Array.getElem_zipWith, Array.getElem_map, keptEdgeMarksFair, fairMarksEdge_eq_of,
    keptSuccs, keptSuccsFrom, keptSteps, keptEdgeMarks]
  have hmem := Array.getElem_mem (xs := succsFrom tgba q (sysLabel s)
    (keptStepsFrom (sysLabel s) (LSys.totalize sysSucc s) keep)) (by simpa using hk1)
  rw [genMarksFromShared_eq tgba q _ _ hmem]
  congr 1
  by_cases hu : (LSys.totalize sysSucc s).all (·.1.isEmpty) = true
  · simp only [fairMarksGen, fairMarksTable, hu, if_true]
    obtain ⟨st, hst, t, ht, hc, h1, h2⟩ := (succsFrom_mem_iff _ _ _ _ _).mp hmem
    simp only [keptStepsFrom, Array.mem_filter] at hst
    exact (fairMarksOf_uniform tgba q _ _ keep tgba.numAcceptSets extra _ hu
      ⟨st, hst.1, hst.2, t, ht, hc, h1, h2⟩).symm
  · simp only [fairMarksGen, fairMarksTable, hu, if_false, Bool.false_eq_true]
    unfold fairMarksOf
    congr 2
    refine List.filter_congr fun i hi => ?_
    simp only []
    rw [getElem!_pos _ i (by simpa using List.mem_range.mp hi), Array.getElem_map,
      Array.getElem_range]

/-- The state-labelled special case for the fairness marks: every step out of `p.1` reads `sysLabel p.1`,
so a restriction that holds there cuts nothing and the conjunct-restricted graphs coincide. -/
theorem fairMarksEdge_unlabelled (tgba : TGBA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (keep : Std.HashSet α → Bool) (base : Nat)
    (extra : List (BoolFormula α)) (p p' : SysState × Nat) (hk : keep (sysLabel p.1) = true) :
    fairMarksEdge tgba (LSys.unlabelled sysSucc) sysLabel keep base extra p p'
      = fairMarksEdge tgba (LSys.unlabelled sysSucc) sysLabel (fun _ => true) base extra p p' := by
  unfold fairMarksEdge
  congr 2
  refine List.filter_congr fun i _ => ?_
  rw [keptSuccs_unlabelled_congr tgba sysSucc sysLabel (fairKeep keep extra i)
    (fairKeep (fun _ => true) extra i) p (by simp [fairKeep, hk])]

/-- The state-labelled special case, lifted to the extended marks: where the source label satisfies the
restriction, restricted and unrestricted marks agree.

Pointwise on marks rather than as a `Std.HashSet` equality, following `keptEdgeMarks_unlabelled` — the
base half may be answered from the grouped table, which agrees on membership but not on representation. -/
theorem mem_keptEdgeMarksFair_unlabelled [LawfulHashable SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) (extra : List (BoolFormula α)) (p p' : SysState × Nat) (m : Nat)
    (hk : keep (sysLabel p.1) = true)
    (h : m ∈ edgeMarksFair tgba (LSys.unlabelled sysSucc) sysLabel extra p p') :
    m ∈ keptEdgeMarksFair tgba (LSys.unlabelled sysSucc) sysLabel keep extra p p' := by
  simp only [keptEdgeMarksFair, edgeMarksFair, Std.HashSet.mem_iff_contains, Std.HashSet.union_eq,
    Std.HashSet.contains_union, Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl (Std.HashSet.mem_iff_contains.mp
      ((keptEdgeMarks_unlabelled tgba sysSucc sysLabel keep p p' m hk).mpr
        (Std.HashSet.mem_iff_contains.mpr h)))
  · rw [fairMarksEdge_unlabelled tgba sysSucc sysLabel keep _ extra p p' hk]
    exact Or.inr h

/-- A restricted extended mark is an extended mark. -/
theorem keptEdgeMarksFair_sub [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) (extra : List (BoolFormula α)) (p p' : SysState × Nat) (m : Nat)
    (h : m ∈ keptEdgeMarksFair tgba sysSucc sysLabel keep extra p p') :
    m ∈ edgeMarksFair tgba sysSucc sysLabel extra p p' := by
  simp only [keptEdgeMarksFair, edgeMarksFair, Std.HashSet.mem_iff_contains,
    Std.HashSet.union_eq, Std.HashSet.contains_union, Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl (Std.HashSet.mem_iff_contains.mp
      (keptEdgeMarks_sub tgba sysSucc sysLabel keep p p' m (Std.HashSet.mem_iff_contains.mpr h)))
  · refine Or.inr (Std.HashSet.mem_iff_contains.mp ?_)
    obtain ⟨i, hi, rfl, hmem⟩ :=
      (mem_fairMarksEdge_iff tgba sysSucc sysLabel keep tgba.numAcceptSets extra p p' m).mp
        (Std.HashSet.mem_iff_contains.mpr h)
    -- dropping `keep` from the conjunction only adds steps
    exact (mem_fairMarksEdge_iff tgba sysSucc sysLabel (fun _ => true) tgba.numAcceptSets extra p p' _).mpr
      ⟨i, hi, rfl, Array.contains_iff_mem.mpr (keptSuccs_mono tgba sysSucc sysLabel
        (fun l hl => by
          simp only [fairKeep, Bool.and_eq_true] at hl
          simp [fairKeep, hl.2]) p p'
        (Array.contains_iff_mem.mp hmem))⟩

theorem keptEdgeMarksFair_lt [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (hbound : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets)
    (keep : Std.HashSet α → Bool) (extra : List (BoolFormula α)) (p p' : SysState × Nat) (m : Nat)
    (hm : m ∈ keptEdgeMarksFair tgba sysSucc sysLabel keep extra p p') :
    m < tgba.numAcceptSets + extra.length :=
  edgeMarksFair_lt tgba sysSucc sysLabel hbound extra p p' m
    (keptEdgeMarksFair_sub tgba sysSucc sysLabel keep extra p p' m hm)

/-- `acceptingRunFair_marks` on the restricted graph: past `N`, where every step of the run reads a letter
`keep` admits, each mark still sits on infinitely many edges of the projected run, and does so *restrictedly*.

Like `acceptingRunFair_keptStep` this replaces a statement about endpoints — `mem_keptEdgeMarksFair_unlabelled`,
which lifted an unrestricted mark to a restricted one whenever the source's label was in region. That does not
survive edge atoms: an unrestricted base mark may sit only on a realization the restriction rejects. Both
halves are therefore rebuilt from the run's own step, the base half through the realization it takes and the
fairness half through `keptSuccs` at `fairKeep keep extra i`. -/
theorem acceptingRunFair_keptMarks (tgba : TGBA α) (sysSucc : SysState → Array (LStep α SysState))
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    (extra : List (BoolFormula α)) {σ : Lentil.exec (Edge SysState α)}
    (hrun : (toSpecFair tgba sysSucc sysLabel sysInit extra).isRun σ)
    (hacc : (toSpecFair tgba sysSucc sysLabel sysInit extra).isAcceptingRun σ)
    (keep : Std.HashSet α → Bool) {N : Nat}
    (hkeep : ∀ n, N ≤ n → keep (LSys.letter (sysLabel (σ n).1) (σ n).2.1.1) = true)
    (m : Nat) (hm : m < tgba.numAcceptSets + extra.length) (K : Nat) :
    ∃ n, K ≤ n ∧ N ≤ n ∧ m ∈ keptEdgeMarksFair tgba sysSucc sysLabel keep extra
      ((σ n).1, (σ n).2.2.1) ((σ (n + 1)).1, (σ (n + 1)).2.2.1) := by
  obtain ⟨j, hj⟩ := hacc ⟨m, hm⟩ (max K N)
  refine ⟨max K N + j, by omega, by omega, ?_⟩
  set n := max K N + j with hn
  have hkn : keep (LSys.letter (sysLabel (σ n).1) (σ n).2.1.1) = true := hkeep n (by omega)
  obtain ⟨⟨ht, hc, hsys⟩, hlink⟩ := hrun.2 n
  have h1 : (σ n).2.1.2 = (σ (n + 1)).1 := congrArg Prod.fst hlink
  have h2 : (σ n).2.2.2.target = (σ (n + 1)).2.2.1 := congrArg Prod.snd hlink
  refine Std.HashSet.mem_iff_contains.mpr ?_
  simp only [keptEdgeMarksFair, Std.HashSet.union_eq, Std.HashSet.contains_union, Bool.or_eq_true]
  by_cases hlt : m < tgba.numAcceptSets
  · -- base mark: the realization the run takes is a kept one, and it carries the mark
    have hr : ((σ n).2.1, (σ n).2.2.2) ∈ realizationsFrom tgba (σ n).2.2.1 (sysLabel (σ n).1)
        (keptSteps sysSucc sysLabel keep (σ n).1) ((σ (n + 1)).1, (σ (n + 1)).2.2.1) :=
      (mem_realizationsFrom_iff tgba _ _ _ _ _).mpr
        ⟨⟨mem_keptSteps.mpr ⟨hsys, hkn⟩, h1⟩, ht, h2, hc⟩
    have hmm : m ∈ (σ n).2.2.2.acceptMarks :=
      Std.HashSet.mem_iff_contains.mpr (by simpa [toSpecFair, hlt] using hj)
    exact Or.inl (Std.HashSet.mem_iff_contains.mp
      (mem_keptEdgeMarks_of_realization tgba sysSucc sysLabel keep
        ((σ n).1, (σ n).2.2.1) ((σ (n + 1)).1, (σ (n + 1)).2.2.1) _ hr hmm))
  · -- fairness mark: the step reads a letter satisfying `keep` and the conjunct, so it survives `fairKeep`
    have hstep : ((σ (n + 1)).1, (σ (n + 1)).2.2.1) ∈ keptSuccs tgba sysSucc sysLabel
        (fairKeep keep extra (m - tgba.numAcceptSets)) ((σ n).1, (σ n).2.2.1) := by
      refine acceptingRunFair_keptStep tgba sysSucc sysLabel sysInit extra hrun _ n ?_
      simp only [fairKeep, Bool.and_eq_true]
      exact ⟨hkn, by simpa [toSpecFair, hlt] using hj⟩
    exact Or.inr (Std.HashSet.mem_iff_contains.mp
      ((mem_fairMarksEdge_iff tgba sysSucc sysLabel keep tgba.numAcceptSets extra
        ((σ n).1, (σ n).2.2.1) ((σ (n + 1)).1, (σ (n + 1)).2.2.1) m).mpr
        ⟨m - tgba.numAcceptSets, by omega, by omega, Array.contains_iff_mem.mpr hstep⟩))

set_option maxHeartbeats 1000000 in
/-- The extended spec's witness over the restricted graph. A fairness mark constrains only the source
system state, so any restricted step edge witnesses it. -/
def edgeWitnessFairKept [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) (sysInit : List SysState) (extra : List (BoolFormula α))
    (hbound : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets) :
    TEdgeWitness (toSpecFair tgba sysSucc sysLabel sysInit extra)
      (keptSuccs tgba sysSucc sysLabel keep)
      (keptEdgeMarksFair tgba sysSucc sysLabel keep extra) where
  stepEdge := (keptEdgeWitness tgba sysSucc sysLabel keep sysInit).stepEdge
  stepEdge_spec := (keptEdgeWitness tgba sysSucc sysLabel keep sysInit).stepEdge_spec
  markEdge p p' m :=
    if m < tgba.numAcceptSets then
      (keptEdgeWitness tgba sysSucc sysLabel keep sysInit).markEdge p p' m
    else (keptEdgeWitness tgba sysSucc sysLabel
      (fairKeep keep extra (m - tgba.numAcceptSets)) sysInit).stepEdge p p'
  markEdge_spec := by
    intro p p' m hm hstep hmark
    by_cases hlt : m < tgba.numAcceptSets
    · have hbase := (keptEdgeWitness tgba sysSucc sysLabel keep sysInit).markEdge_spec
        (k := tgba.numAcceptSets) hlt hstep (by
          simp only [keptEdgeMarksFair, Std.HashSet.mem_iff_contains, Std.HashSet.union_eq,
            Std.HashSet.contains_union, Bool.or_eq_true] at hmark
          rcases hmark with h | h
          · exact Std.HashSet.mem_iff_contains.mpr h
          · obtain ⟨i, -, rfl, -⟩ :=
              (mem_fairMarksEdge_iff tgba sysSucc sysLabel keep tgba.numAcceptSets extra p p' m).mp
                (Std.HashSet.mem_iff_contains.mpr h)
            omega)
      simp only [hlt, if_pos]
      exact ⟨hbase.1, hbase.2.1, hbase.2.2.1, by simpa [toSpec, toSpecFair, hlt] using hbase.2.2.2⟩
    · -- the mark says the edge survives `keep ∧ conjᵢ`, so that witness's step edge reads such a letter
      have hmem : p' ∈ keptSuccs tgba sysSucc sysLabel
          (fairKeep keep extra (m - tgba.numAcceptSets)) p := by
        simp only [keptEdgeMarksFair, Std.HashSet.mem_iff_contains, Std.HashSet.union_eq,
          Std.HashSet.contains_union, Bool.or_eq_true] at hmark
        rcases hmark with h | h
        · exact absurd (edgeMarks_lt tgba sysSucc sysLabel hbound p p' m
            (keptEdgeMarks_sub tgba sysSucc sysLabel keep p p' m
              (Std.HashSet.mem_iff_contains.mpr h))) hlt
        · obtain ⟨i, -, heq, hmm⟩ :=
            (mem_fairMarksEdge_iff tgba sysSucc sysLabel keep tgba.numAcceptSets extra p p' m).mp
              (Std.HashSet.mem_iff_contains.mpr h)
          rw [show m - tgba.numAcceptSets = i from by omega]
          exact Array.contains_iff_mem.mp hmm
      have hstepspec := (keptEdgeWitness tgba sysSucc sysLabel
        (fairKeep keep extra (m - tgba.numAcceptSets)) sysInit).stepEdge_spec hmem
      have hletter := keptEdgeWitness_stepEdge_letter tgba sysSucc sysLabel
        (fairKeep keep extra (m - tgba.numAcceptSets)) sysInit p p' hmem
      simp only [hlt, if_neg, not_false_eq_true]
      exact ⟨hstepspec.1, hstepspec.2.1, hstepspec.2.2,
        by simpa [toSpecFair, hlt] using (fairKeep_le hletter).2⟩

-- Projection equations for the sealed `keptEdgeWitness` underneath: `rfl`, but needed explicitly since
-- `keptEdgeWitness` is irreducible, so nothing downstream can see through the wrapper by defeq.
theorem edgeWitnessFairKept_stepEdge [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) (sysInit : List SysState) (extra : List (BoolFormula α))
    (hbound : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets)
    (p p' : SysState × Nat) :
    (edgeWitnessFairKept tgba sysSucc sysLabel keep sysInit extra hbound).stepEdge p p'
      = (keptEdgeWitness tgba sysSucc sysLabel keep sysInit).stepEdge p p' := rfl

theorem edgeWitnessFairKept_markEdge [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (keep : Std.HashSet α → Bool) (sysInit : List SysState) (extra : List (BoolFormula α))
    (hbound : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets)
    (p p' : SysState × Nat) (m : Nat) :
    (edgeWitnessFairKept tgba sysSucc sysLabel keep sysInit extra hbound).markEdge p p' m
      = if m < tgba.numAcceptSets then
          (keptEdgeWitness tgba sysSucc sysLabel keep sysInit).markEdge p p' m
        else (keptEdgeWitness tgba sysSucc sysLabel
          (fairKeep keep extra (m - tgba.numAcceptSets)) sysInit).stepEdge p p' := rfl

set_option maxHeartbeats 1000000 in
/-- The counterexample a region cycle describes: one labelled system run the automaton accepts, satisfying
every conjunct infinitely often, and whose tail reads only letters the restriction admits. That last part is
`◇□` over *letters*, which is what an edge-indexed `FG` means. -/
theorem exists_run_of_TRegionCycle [LawfulBEq α] [BEq SysState] [Hashable SysState] [LawfulBEq SysState] (tgba : TGBA α)
    (sysSucc : SysState → Array (LStep α SysState)) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState) (extra : List (BoolFormula α)) (keep : Std.HashSet α → Bool)
    (hbound : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets)
    (rc : TRegionCycle (initialStates tgba sysInit) (getSuccessors tgba sysSucc sysLabel)
      (keptSuccs tgba sysSucc sysLabel keep) (edgeMarksFair tgba sysSucc sysLabel extra)
      (keptEdgeMarksFair tgba sysSucc sysLabel keep extra) (tgba.numAcceptSets + extra.length)) :
    ∃ ρ : Nat → LSys.Edge α SysState, (LSys.toSpec sysSucc sysInit sysLabel).isRun ρ ∧
      tgba.toSpec.accepts (LSys.valuation sysLabel ρ) ∧
      (∀ i, i < extra.length → ∀ n, ∃ j,
        (fairConj extra i).eval (LSys.letter (sysLabel (ρ (n + j)).1) (ρ (n + j)).2.1) = true) ∧
      (∃ N, ∀ n, N ≤ n → keep (LSys.letter (sysLabel (ρ n).1) (ρ n).2.1) = true) := by
  have hlasso := rc.toTValidLasso (edgeWitnessFair tgba sysSucc sysLabel sysInit extra hbound)
    (edgeWitnessFairKept tgba sysSucc sysLabel keep sysInit extra hbound) (fun hs => hs)
  obtain ⟨hρrun, hlang, hfair⟩ := gsp_correct1Fair tgba sysSucc sysLabel sysInit extra
    hlasso.run_isRun hlasso.run_isAccepting
  refine ⟨_, hρrun, hlang, hfair, ⟨(stemEdges
    (edgeWitnessFair tgba sysSucc sysLabel sysInit extra hbound).stepEdge rc.stem).length,
    fun n hn => ?_⟩⟩
  -- past the stem the run walks `cycleE` of the *restricted* witness, whose edges read kept letters
  rw [hlasso.run_eq_cycle n (by omega)]
  refine cycleE_forall (edgeWitnessFairKept tgba sysSucc sysLabel keep sysInit extra hbound) rc.cycleAc
    (fun e => keep (LSys.letter (sysLabel e.1) e.2.1.1) = true) ?_ ?_ _ (List.getElem_mem _)
  · intro s s' hs'
    rw [edgeWitnessFairKept_stepEdge]
    exact keptEdgeWitness_stepEdge_letter tgba sysSucc sysLabel keep sysInit s s' hs'
  · intro s s' m hs' hmm
    by_cases hlt : m < tgba.numAcceptSets
    · rw [edgeWitnessFairKept_markEdge, if_pos hlt]
      refine keptEdgeWitness_markEdge_letter tgba sysSucc sysLabel keep sysInit s s' hs' m hlt ?_
      simp only [keptEdgeMarksFair, Std.HashSet.mem_iff_contains, Std.HashSet.union_eq,
        Std.HashSet.contains_union, Bool.or_eq_true] at hmm
      rcases hmm with h | h
      · exact Std.HashSet.mem_iff_contains.mpr h
      · obtain ⟨i, -, rfl, -⟩ :=
          (mem_fairMarksEdge_iff tgba sysSucc sysLabel keep tgba.numAcceptSets extra s s' m).mp
            (Std.HashSet.mem_iff_contains.mpr h)
        omega
    · -- the fairness witness is the step edge at `keep ∧ conjᵢ`, whose letter satisfies `keep` a fortiori
      rw [edgeWitnessFairKept_markEdge, if_neg hlt]
      have hmem : s' ∈ keptSuccs tgba sysSucc sysLabel
          (fairKeep keep extra (m - tgba.numAcceptSets)) s := by
        simp only [keptEdgeMarksFair, Std.HashSet.mem_iff_contains, Std.HashSet.union_eq,
          Std.HashSet.contains_union, Bool.or_eq_true] at hmm
        rcases hmm with h | h
        · exact absurd (edgeMarks_lt tgba sysSucc sysLabel hbound s s' m
            (keptEdgeMarks_sub tgba sysSucc sysLabel keep s s' m
              (Std.HashSet.mem_iff_contains.mpr h))) hlt
        · obtain ⟨i, -, heq, hmm'⟩ :=
            (mem_fairMarksEdge_iff tgba sysSucc sysLabel keep tgba.numAcceptSets extra s s' m).mp
              (Std.HashSet.mem_iff_contains.mpr h)
          rw [show m - tgba.numAcceptSets = i from by omega]
          exact Array.contains_iff_mem.mp hmm'
      exact (fairKeep_le (keptEdgeWitness_stepEdge_letter tgba sysSucc sysLabel
        (fairKeep keep extra (m - tgba.numAcceptSets)) sysInit s s' hmem)).1

/-! ## The same extended product, from one system callback

`LSys.StepFn` in place of the `sysSucc`/`sysLabel` pair. The two expansions repeat their bodies rather
than being refactored, because the `rfl` bridges below are a machine-checked guarantee that the repeat
computes the same thing — a mistyped copy fails to compile. See `EdgeLabels.md` §15. -/

section OfStep

variable (tgba : TGBA α) (sysStep : LSys.StepFn α SysState)

def fairMarksEdgeOfStep (keep : Std.HashSet α → Bool) (base : Nat)
    (extra : List (BoolFormula α)) (p p' : SysState × Nat) : Std.HashSet Nat :=
  Std.HashSet.ofList
    (((List.range extra.length).filter fun i =>
      (keptSuccsOfStep tgba sysStep (fairKeep keep extra i) p).contains p').map (base + ·))

def edgeMarksFairOfStep (extra : List (BoolFormula α)) :
    (SysState × Nat) → (SysState × Nat) → Std.HashSet Nat :=
  fun p p' => (edgeMarksOfStep tgba sysStep p p').union
    (fairMarksEdgeOfStep tgba sysStep (fun _ => true) tgba.numAcceptSets extra p p')

def keptEdgeMarksFairOfStep (keep : Std.HashSet α → Bool) (extra : List (BoolFormula α)) :
    (SysState × Nat) → (SysState × Nat) → Std.HashSet Nat :=
  fun p p' => (keptEdgeMarksOfStep tgba sysStep keep p p').union
    (fairMarksEdgeOfStep tgba sysStep keep tgba.numAcceptSets extra p p')

def expandFairOfStep (extra : List (BoolFormula α)) (p : SysState × Nat) :
    Array (SysState × Nat) × Array (Std.HashSet Nat) × Array Nat :=
  let r := sysStep p.1
  let base := r.2
  let steps := LSys.totalizeAt r.1 p.1
  let byTgt? := marksTableGen tgba p.2 base steps
  let fm? := fairMarksTable tgba.numAcceptSets extra base steps
  let out := succsFrom tgba p.2 base steps
  let ks : Array (Array (SysState × Nat)) :=
    if steps.all (·.1.isEmpty) then #[] else (Array.range extra.length).map fun i =>
      keptSuccsFrom tgba p.2 base steps (fairKeep (fun _ => true) extra i)
  (out, Array.zipWith (fun ms p' =>
    ms.union (fairMarksGen tgba.numAcceptSets extra fm? (fun i => ks[i]!) p'))
    (out.map fun p' => genMarksFromShared tgba p.2 base steps byTgt? p') out, #[])

def keptExpandFairOfStep (keep : Std.HashSet α → Bool) (extra : List (BoolFormula α))
    (p : SysState × Nat) : Array (SysState × Nat) × Array (Std.HashSet Nat) × Array Nat :=
  let r := sysStep p.1
  let base := r.2
  let steps := LSys.totalizeAt r.1 p.1
  let kept := keptStepsFrom base steps keep
  let byTgt? := marksTableGen tgba p.2 base kept
  let fm? := fairMarksTable tgba.numAcceptSets extra base steps
  let out := succsFrom tgba p.2 base kept
  let ks : Array (Array (SysState × Nat)) :=
    if steps.all (·.1.isEmpty) then #[] else (Array.range extra.length).map fun i =>
      keptSuccsFrom tgba p.2 base steps (fairKeep keep extra i)
  (out, Array.zipWith (fun ms p' =>
    ms.union (fairMarksGen tgba.numAcceptSets extra fm? (fun i => ks[i]!) p'))
    (out.map fun p' => genMarksFromShared tgba p.2 base kept byTgt? p') out, #[])

theorem fairMarksEdgeOfStep_eq' (keep : Std.HashSet α → Bool) (base : Nat)
    (extra : List (BoolFormula α)) :
    fairMarksEdgeOfStep tgba sysStep keep base extra
      = fairMarksEdge tgba (fun s => (sysStep s).1) (fun s => (sysStep s).2) keep base extra := rfl

theorem edgeMarksFairOfStep_eq' (extra : List (BoolFormula α)) :
    edgeMarksFairOfStep tgba sysStep extra
      = edgeMarksFair tgba (fun s => (sysStep s).1) (fun s => (sysStep s).2) extra := rfl

theorem keptEdgeMarksFairOfStep_eq' (keep : Std.HashSet α → Bool)
    (extra : List (BoolFormula α)) :
    keptEdgeMarksFairOfStep tgba sysStep keep extra
      = keptEdgeMarksFair tgba (fun s => (sysStep s).1) (fun s => (sysStep s).2) keep extra := rfl

theorem expandFairOfStep_eq' (extra : List (BoolFormula α)) :
    expandFairOfStep tgba sysStep extra
      = expandFair tgba (fun s => (sysStep s).1) (fun s => (sysStep s).2) extra := rfl

theorem keptExpandFairOfStep_eq' (keep : Std.HashSet α → Bool) (extra : List (BoolFormula α)) :
    keptExpandFairOfStep tgba sysStep keep extra
      = keptExpandFair tgba (fun s => (sysStep s).1) (fun s => (sysStep s).2) keep extra := rfl

end OfStep

end TGBAProduct



end LTLLib
