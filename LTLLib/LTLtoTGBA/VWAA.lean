module

/-
  The very weak alternating co-Büchi automaton (VWAA) of an NNF formula, `[BKŘS12]` §5's modified construction without
  suspension, reduced by the paper's generalised VWAA optimisation and restricted to the states reachable from the input
  formula.

  `NNF.rtrans` is the paper's δ with target sets as bitmasks over `SubformulaTable` ids. Every node's δ is reduced before
  its parent combines it, as LTL3BA's `build_alternating` does, a code-level optimisation over the paper, which states
  the reduction per state. `[GO01]` §6's removal of implied transitions is subsumed by the splitting, since `α2 ⇒ α1`
  makes `α2 ∧ ¬α1` empty (`[BKŘS12]` §5).

  Defines:
  - `bit`, `maskSub`, `maskMembers`, `maskSet`, `remapMask`, `maskOf`, `submasks`: target sets as bitmasks
  - `tprod`, `mergeByTarget`, `splitByTarget`, `reduceTrans`: `⊗`, merging equal targets, splitting away subsumed ones
  - `groupByKey`: a list grouped by a key
  - `NNF.rtrans`: the reduced δ of a formula
  - `ConcreteVWAA`, `ConcreteVWAA.build`: δ indexed by id and restricted to the ids reachable from the input formula,
    co-Büchi finals exactly the `until` ids
  - `transSucc`, `restrictReachable`: the successor function and the id-remapped restriction to reachable states
  - `abstractOf`: the `VWAA Nat α` a `ConcreteVWAA` denotes

  Proves:
  - `rtrans_listSim_targetsIn`: `NNF.rtrans` letterwise simulates `NNF.vwaaTrans` in both directions and invents no
    target
  - `ConcreteVWAA.build_correct`: the built VWAA accepts exactly the models of the input formula
  - `ConcreteVWAA.build_veryWeak`, `build_target_lt_size`, `build_initial_lt_size`: very weakness and id bounds

  References:
  - `[BKŘS12]` Babiak, Křetínský, Řehák, Strejček. LTL to Büchi Automata Translation: Fast and More
    Deterministic. TACAS'12, §5.
  - `[GO01]` Gastin, Oddoux. Fast LTL to Büchi Automata Translation. CAV'01, §6.
  - `[LTL3BA-1.1.3]` Babiak. LTL3BA 1.1.3, `alternating.cpp`, `build_alternating` and `transition[i]` keyed by target.
  - `[JN18]` Jantsch, Norrish. Verifying the LTL to Büchi Automata Translation via Very Weak Alternating
    Automata. ITP'18.

  Sections:
  - Target masks
  - Abstract targets
  - Transition product
  - Merging equal targets
  - Splitting overlapping labels
  - The VWAA transition function
  - Concrete VWAA
  - Reachability restriction
  - Building the VWAA
  - The abstract automaton a `ConcreteVWAA` denotes
  - Reachability correspondence
  - State relabeling
  - Reduction correctness
  - Correspondence with the abstract construction
  - The raw stage
  - Final composition
-/
public import LTLLib.LTL.Syntax
public import LTLLib.LTLtoTGBA.Label
public import LTLLib.LTLtoTGBA.Reachability
public import LTLLib.LTLtoTGBA.SubformulaTable
public import LTLLib.LTLtoTGBA.AbstractSpec.VWAA
public import LTLLib.LTLtoTGBA.AbstractSpec.VWAAReduce
public import LTLLib.LTLtoTGBA.AbstractSpec.LTLToVWAA
meta import LTLLib.Tactic.Set
public import LTLLib.Data.FinSet

public section

namespace LTLLib

/-! ## Target masks -/

/-- The singleton target `{i}`. -/
@[expose] def bit (i : Nat) : Nat := 1 <<< i

/-- `a ⊆ b` on masks. -/
@[expose] def maskSub (a b : Nat) : Bool := a &&& b == a

/-- The ids of `m`, increasing. -/
@[expose] def maskMembers (m : Nat) : List Nat := (List.range (m.log2 + 1)).filter m.testBit

/-- The ids of `m` as a `FinSet`. -/
@[expose] def maskSet (m : Nat) : FinSet Nat := (maskMembers m).toFinSet

theorem mem_maskMembers {m j : Nat} : j ∈ maskMembers m ↔ m.testBit j = true := by
  unfold maskMembers
  rw [List.mem_filter, List.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  by_contra hj
  have hlt : m < 2 ^ j := Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by omega) (by omega))
  rw [Nat.testBit_lt_two_pow hlt] at h
  exact absurd h (by simp)

theorem maskMembers_nodup (m : Nat) : (maskMembers m).Nodup := List.filter_sublist.nodup List.nodup_range

theorem mem_maskSet {m j : Nat} : j ∈ maskSet m ↔ m.testBit j = true := by
  unfold maskSet
  rw [List.mem_toFinSet, mem_maskMembers]

theorem maskSet_zero : maskSet 0 = ∅ := by
  ext j; simp [mem_maskSet]

theorem maskSet_or (a b : Nat) : maskSet (a ||| b) = maskSet a ∪ maskSet b := by
  ext j; simp [mem_maskSet, Nat.testBit_or]

theorem maskSet_bit (i : Nat) : maskSet (bit i) = {i} := by
  ext j; simp [mem_maskSet, bit, Nat.one_shiftLeft, Nat.testBit_two_pow, eq_comm]

theorem maskSub_iff {a b : Nat} : maskSub a b = true ↔ ∀ j, a.testBit j = true → b.testBit j = true := by
  unfold maskSub
  rw [beq_iff_eq]
  constructor
  · intro h j hj
    have hj' := congrArg (fun x => x.testBit j) h
    simp only [Nat.testBit_and, hj, Bool.true_and] at hj'
    exact hj'
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    cases ha : a.testBit j
    · simp
    · simp [h j ha]

theorem maskSub_refl (a : Nat) : maskSub a a = true := maskSub_iff.mpr fun _ h => h

theorem maskSub_trans {a b c : Nat} (hab : maskSub a b = true) (hbc : maskSub b c = true) : maskSub a c = true :=
  maskSub_iff.mpr fun j hj => maskSub_iff.mp hbc j (maskSub_iff.mp hab j hj)

theorem maskSet_subset_of_maskSub {a b : Nat} (h : maskSub a b = true) : maskSet a ⊆ maskSet b :=
  fun j hj => mem_maskSet.mpr (maskSub_iff.mp h j (mem_maskSet.mp hj))

/-- A strict sub-mask is numerically smaller. -/
theorem lt_of_maskSub {a b : Nat} (h : maskSub a b = true) (hne : a ≠ b) : a < b := by
  have heq : a &&& b = a := beq_iff_eq.mp h
  have hle : a ≤ b := by rw [← heq]; exact Nat.and_le_right
  omega

/-- `m` with every id `j` renamed to `f j`. -/
def remapMask (f : Nat → Nat) (m : Nat) : Nat := (maskMembers m).foldl (fun acc j => acc ||| bit (f j)) 0

private theorem testBit_foldl_bit (f : Nat → Nat) (l : List Nat) (acc k : Nat) :
    (l.foldl (fun acc j => acc ||| bit (f j)) acc).testBit k = true ↔ acc.testBit k = true ∨ ∃ j ∈ l, f j = k := by
  induction l generalizing acc with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih]
    simp only [Nat.testBit_or, bit, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq,
      List.mem_cons]
    grind

theorem testBit_remapMask {f : Nat → Nat} {m k : Nat} :
    (remapMask f m).testBit k = true ↔ ∃ j, m.testBit j = true ∧ f j = k := by
  unfold remapMask
  rw [testBit_foldl_bit]
  simp [mem_maskMembers]

theorem maskSet_remapMask (f : Nat → Nat) (m : Nat) : maskSet (remapMask f m) = (maskSet m).image f := by
  ext k
  rw [mem_maskSet, testBit_remapMask, FinSet.mem_image]
  simp [mem_maskSet]

/-- A `FinSet` of ids as a mask. -/
@[expose] noncomputable def maskOf (e : FinSet Nat) : Nat := e.toList.foldl (fun acc j => acc ||| bit j) 0

theorem testBit_maskOf {e : FinSet Nat} {j : Nat} : (maskOf e).testBit j = true ↔ j ∈ e := by
  unfold maskOf
  rw [show (fun acc j => acc ||| bit j) = (fun acc (j : Nat) => acc ||| bit (id j)) from rfl, testBit_foldl_bit]
  simp

theorem maskSet_maskOf (e : FinSet Nat) : maskSet (maskOf e) = e := by
  ext j; rw [mem_maskSet, testBit_maskOf]

theorem maskOf_maskSet (m : Nat) : maskOf (maskSet m) = m :=
  Nat.eq_of_testBit_eq fun j => by
    cases h : m.testBit j
    · cases h' : (maskOf (maskSet m)).testBit j
      · rfl
      · exact absurd (mem_maskSet.mp (testBit_maskOf.mp h')) (by simp [h])
    · exact testBit_maskOf.mpr (mem_maskSet.mpr h)

theorem maskOf_singleton (i : Nat) : maskOf {i} = bit i :=
  Nat.eq_of_testBit_eq fun j => by
    apply Bool.eq_iff_iff.mpr
    rw [testBit_maskOf, FinSet.mem_singleton]
    simp [bit, Nat.one_shiftLeft, Nat.testBit_two_pow, eq_comm]

theorem maskSub_iff_subset {a b : Nat} : maskSub a b = true ↔ maskSet a ⊆ maskSet b :=
  ⟨maskSet_subset_of_maskSub, fun h => maskSub_iff.mpr fun _ hj => mem_maskSet.mp (h (mem_maskSet.mpr hj))⟩

theorem maskSub_antisymm {a b : Nat} (hab : maskSub a b = true) (hba : maskSub b a = true) : a = b :=
  Nat.eq_of_testBit_eq fun j => by
    cases ha : a.testBit j
    · cases hb : b.testBit j
      · rfl
      · rw [maskSub_iff.mp hba j hb] at ha; exact absurd ha (by simp)
    · exact (maskSub_iff.mp hab j ha).symm

/-- A mask whose bits all lie below `n` is below `2 ^ n`. -/
theorem lt_two_pow_of_testBit {t n : Nat} (h : ∀ j, t.testBit j = true → j < n) : t < 2 ^ n :=
  Nat.lt_pow_two_of_testBit t fun i hi => by
    cases hb : t.testBit i
    · rfl
    · exact absurd (h i hb) (by omega)

/-- Every sub-mask of `m`, built one id of `m` at a time. -/
@[expose] def submasks (m : Nat) : List Nat := (maskMembers m).foldl (fun acc j => acc ++ acc.map (· ||| bit j)) [0]

private theorem mem_foldl_submasks (P : Nat → Prop) :
    ∀ (l acc : List Nat), (∀ s, (∀ j, s.testBit j = true → P j) → s ∈ acc) →
      ∀ s, (∀ j, s.testBit j = true → P j ∨ j ∈ l) → s ∈ l.foldl (fun acc j => acc ++ acc.map (· ||| bit j)) acc := by
  intro l
  induction l generalizing P with
  | nil => intro acc hacc s hs; exact hacc s fun j hj => (hs j hj).resolve_right (by simp)
  | cons i rest ih =>
    intro acc hacc s hs
    rw [List.foldl_cons]
    refine ih (fun j => P j ∨ j = i) _ ?_ s fun j hj => ?_
    · intro s hs
      rw [List.mem_append]
      cases hsi : s.testBit i
      · exact Or.inl (hacc s fun j hj => (hs j hj).resolve_right fun hji => by rw [hji, hsi] at hj; exact absurd hj (by simp))
      · refine Or.inr (List.mem_map.mpr ⟨s ^^^ bit i, hacc _ fun j hj => ?_, ?_⟩)
        · rw [Nat.testBit_xor, bit, Nat.one_shiftLeft, Nat.testBit_two_pow] at hj
          by_cases hji : j = i
          · subst hji; simp [hsi] at hj
          · have hsj : s.testBit j = true := by simpa [Ne.symm hji] using hj
            exact (hs j hsj).resolve_right hji
        · apply Nat.eq_of_testBit_eq
          intro j
          rw [Nat.testBit_or, Nat.testBit_xor, bit, Nat.one_shiftLeft, Nat.testBit_two_pow]
          by_cases hji : i = j
          · subst hji; simp [hsi]
          · simp [hji]
    · rcases hs j hj with h | h
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

theorem mem_submasks_of_maskSub {s m : Nat} (h : maskSub s m = true) : s ∈ submasks m := by
  unfold submasks
  refine mem_foldl_submasks (fun _ => False) (maskMembers m) [0] (fun s hs => ?_) s
    fun j hj => Or.inr (mem_maskMembers.mpr (maskSub_iff.mp h j hj))
  have : s = 0 := Nat.eq_of_testBit_eq fun j => by
    cases hsj : s.testBit j
    · simp
    · exact absurd (hs j hsj) id
  simp [this]

/-! ## Abstract targets -/

section AbstractTargets

variable {α : Type u}

/-- `NNF.vwaaTrans`'s targets read through `idx`. -/
def encAbs (idx : NNF α → Nat) (l : List (((α → Prop) → Prop) × FinSet (NNF α))) :
    List (((α → Prop) → Prop) × FinSet Nat) :=
  l.map fun p => (p.1, p.2.image idx)

private theorem encAbs_lprod (idx : NNF α → Nat) (A B : List (((α → Prop) → Prop) × FinSet (NNF α))) :
    encAbs idx (VWAA.lprod A B) = VWAA.lprod (encAbs idx A) (encAbs idx B) := by
  unfold encAbs VWAA.lprod
  rw [List.map_flatMap, List.flatMap_map]
  congr 1
  funext p
  rw [List.map_map, List.map_map]
  congr 1
  funext q
  simp [FinSet.image_union]

private theorem encAbs_map_union (idx : NNF α → Nat) (A : List (((α → Prop) → Prop) × FinSet (NNF α)))
    (ψ : NNF α) :
    encAbs idx (A.map fun p => (p.1, p.2 ∪ {ψ})) = (encAbs idx A).map fun p => (p.1, p.2 ∪ {idx ψ}) := by
  unfold encAbs
  rw [List.map_map, List.map_map]
  congr 1
  funext p
  simp [FinSet.image_union]

end AbstractTargets

variable {α : Type u} [BEq α] [Hashable α]

/-! ## Transition product -/

/-- The paper's `⊗`: every combination of a transition from each side, guards conjoined and targets unioned, dropping
a combination whose guard is unsatisfiable. -/
def tprod (xs ys : List (DNF α × Nat)) : List (DNF α × Nat) :=
  xs.flatMap fun p1 => ys.filterMap fun p2 =>
    let g := DNF.and p1.1 p2.1
    if DNF.isEmpty g then none else some (g, p1.2 ||| p2.2)

/-! ## Merging equal targets -/

/-- One merging step, OR-ing `p`'s guard into whatever its key already carries. -/
def mergeStep {K : Type v} [BEq K] [Hashable K] (m : Std.HashMap K (DNF α)) (p : DNF α × K) :
    Std.HashMap K (DNF α) :=
  m.insert p.2 (DNF.or (m.getD p.2 DNF.bot) p.1)

/-- Merge transitions sharing a key into one, guards OR-ed together, keyed like LTL3BA's `transition[i]`. -/
@[expose] def mergeByTarget {K : Type v} [BEq K] [Hashable K] (l : List (DNF α × K)) : List (DNF α × K) :=
  (l.foldl mergeStep (Std.HashMap.emptyWithCapacity 8)).toList.map fun p => (p.2, p.1)

/-- `l` grouped by `key`, each group in `l`'s order. -/
@[expose] def groupByKey {β : Type w} {K : Type v} [BEq K] [Hashable K] (key : β → K) (l : List β) : Std.HashMap K (List β) :=
  l.foldr (fun x m => m.insert (key x) (x :: m.getD (key x) [])) (Std.HashMap.emptyWithCapacity l.length)

private theorem mem_foldr_groupByKey {β : Type w} {K : Type v} [BEq K] [Hashable K] [LawfulBEq K] [LawfulHashable K]
    (key : β → K) (m0 : Std.HashMap K (List β)) (k : K) (x : β) :
    ∀ l : List β, x ∈ (l.foldr (fun x m => m.insert (key x) (x :: m.getD (key x) [])) m0).getD k [] ↔
      (x ∈ l ∧ key x = k) ∨ x ∈ m0.getD k [] := by
  intro l
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.foldr_cons, Std.HashMap.getD_insert]
    by_cases hk : key a = k
    · subst hk
      rw [if_pos (beq_self_eq_true _), List.mem_cons, ih]
      grind
    · rw [if_neg (by simpa using hk), ih]
      grind

theorem mem_groupByKey {β : Type w} {K : Type v} [BEq K] [Hashable K] [LawfulBEq K] [LawfulHashable K] (key : β → K)
    (l : List β) (k : K) (x : β) : x ∈ (groupByKey key l).getD k [] ↔ x ∈ l ∧ key x = k := by
  unfold groupByKey
  rw [mem_foldr_groupByKey]
  simp

/-! ## Splitting overlapping labels -/

/-- `g` narrowed by the guard of every transition of `l` whose target lies strictly inside `t`. -/
def splitGuard (l : List (DNF α × Nat)) (g : DNF α) (t : Nat) : DNF α :=
  l.foldl (fun g p => if maskSub p.2 t && p.2 != t then DNF.diff g p.1 else g) g

/-- Narrow every transition's guard against every transition with a strictly smaller target, `[BKŘS12]` §5's
generalised VWAA optimisation `α2 := α2 ∧ ¬α1` when `O1 ⊊ O2`, dropped once it becomes unsatisfiable. -/
@[expose] def splitByTarget (l : List (DNF α × Nat)) : List (DNF α × Nat) :=
  l.filterMap fun p =>
    let g := splitGuard l p.1 p.2
    if DNF.isEmpty g then none else some (g, p.2)

/-- Merge equal targets, then split away subsumed ones. -/
def reduceTrans (l : List (DNF α × Nat)) : List (DNF α × Nat) := splitByTarget (mergeByTarget l)

/-! ## The VWAA transition function -/

/-- `[BKŘS12]` §5's modified δ without suspension, targets as bitmasks of `idx` ids, `next ψ` targeting `{ψ}` alone.
Every node's δ is reduced before its parent combines it, LTL3BA's `build_alternating` with `det_m`. -/
@[expose] def NNF.rtrans (idx : NNF α → Nat) : NNF α → List (DNF α × Nat)
  | .tt => [(DNF.top, 0)]
  | .ff => []
  | .prop a => [(DNF.lit a true, 0)]
  | .nprop a => [(DNF.lit a false, 0)]
  | .and φ ψ => reduceTrans (tprod (φ.rtrans idx) (ψ.rtrans idx))
  | .or φ ψ => reduceTrans (φ.rtrans idx ++ ψ.rtrans idx)
  | .next ψ => [(DNF.top, bit (idx ψ))]
  | .until φ ψ => reduceTrans (ψ.rtrans idx ++ tprod (φ.rtrans idx) [(DNF.top, bit (idx (.until φ ψ)))])
  | .release φ ψ =>
    reduceTrans (tprod (ψ.rtrans idx) (φ.rtrans idx ++ [(DNF.top, bit (idx (.release φ ψ)))]))

/-! ## Concrete VWAA -/

/-- A VWAA whose states are `table`'s ids. -/
structure ConcreteVWAA (α : Type u) [BEq α] [Hashable α] where
  table : SubformulaTable α
  trans : Array (List (DNF α × Nat))  -- indexed by id
  final : Array Bool  -- indexed by id
  -- the id of the single initial state
  initial : Nat

/-- Every target of `cv`'s transitions at id `i` is `i` itself or a strictly lower-ranked id. -/
@[expose] def ConcreteVWAA.VeryWeak (cv : ConcreteVWAA α) : Prop :=
  ∀ i g t, (g, t) ∈ cv.trans.getD i [] → ∀ j, t.testBit j = true →
    j = i ∨ (cv.table.formulaOf j).rank < (cv.table.formulaOf i).rank

/-- A concrete transition list read as abstract alternatives, guards through `DNF.sat`, targets through `maskSet`. -/
@[expose] def encTrans (l : List (DNF α × Nat)) : List (((α → Prop) → Prop) × FinSet Nat) :=
  l.map fun p => (DNF.sat p.1, maskSet p.2)

/-! ## Reachability restriction -/

/-- Every id a transition of `trans` at `q` can target. -/
def transSucc (trans : Array (List (DNF α × Nat))) (q : Nat) : List Nat :=
  (trans.getD q []).flatMap fun p => maskMembers p.2

/-- The ids reachable from `initial`. -/
def reachIds (cv : ConcreteVWAA α) : Std.HashSet Nat :=
  reachableFrom (transSucc cv.trans) [cv.initial] (List.range cv.table.formulas.size)

/-- The ids `restrictReachable` keeps, in increasing original order. -/
def keptIds (cv : ConcreteVWAA α) : List Nat :=
  (List.range cv.table.formulas.size).filter (reachIds cv).contains

/-- The dense id `restrictReachable` assigns each kept id, its position in `keptIds`. -/
def remapIds (cv : ConcreteVWAA α) : Std.HashMap Nat Nat :=
  ((keptIds cv).foldl (init := (Std.HashMap.emptyWithCapacity (keptIds cv).length, 0))
    fun (m, i) old => (m.insert old i, i + 1)).1

/-- Drop every VWAA state not reachable from `initial`, `[GO01]` §6 `REDUCE_STATE_CORRECT`, ids remapped to a dense
range in increasing original order. -/
def restrictReachable (cv : ConcreteVWAA α) : ConcreteVWAA α :=
  let kept := keptIds cv
  let remap := remapIds cv
  let formulas := kept.toArray.map cv.table.formulaOf
  let index := (formulas.foldl (init := (Std.HashMap.emptyWithCapacity formulas.size, 0))
    fun (m, i) f => (m.insert f i, i + 1)).1
  { table := { formulas, index }
    trans := kept.toArray.map fun old =>
      (cv.trans.getD old []).map fun p => (p.1, remapMask (remap.getD · 0) p.2)
    final := kept.toArray.map fun old => cv.final.getD old false
    initial := remap.getD cv.initial 0 }


/-! ## Building the VWAA -/

/-- Every table id's reduced δ, each computed at most once and only when read. -/
def lazyTrans (table : SubformulaTable α) : Array (Thunk (List (DNF α × Nat))) :=
  table.formulas.map fun f => Thunk.mk fun _ => f.rtrans table.idOf

/-- Id `i`'s entry of `lazyTrans`, `[]` outside the table. -/
def readTrans (δ : Array (Thunk (List (DNF α × Nat)))) (i : Nat) : List (DNF α × Nat) :=
  (δ.getD i (Thunk.pure [])).get

/-- Every id `readTrans` can target from `i`. -/
def readSucc (δ : Array (Thunk (List (DNF α × Nat)))) (i : Nat) : List Nat :=
  (readTrans δ i).flatMap fun p => maskMembers p.2

/-- The reduced δ of every id reachable from `φ`'s id, `[]` elsewhere, before renumbering. -/
def rawStage (φ : NNF α) : ConcreteVWAA α :=
  let table := SubformulaTable.build φ
  let δ := lazyTrans table
  let reach := reachableFrom (readSucc δ) [table.idOf φ] (List.range table.formulas.size)
  { table
    trans := (Array.range table.formulas.size).map fun i => if reach.contains i then readTrans δ i else []
    final := table.formulas.map fun | .until _ _ => true | _ => false
    initial := table.idOf φ }

/-- The reduced δ of every id reachable from `φ`, renumbered densely, `final` the `until` ids. -/
@[expose] def ConcreteVWAA.build (φ : NNF α) : ConcreteVWAA α :=
  restrictReachable (rawStage φ)

/-! ## The abstract automaton a `ConcreteVWAA` denotes -/

/-- The `VWAA Nat α` a `ConcreteVWAA` denotes: guards through `DNF.sat`, targets through `maskSet`, finality and rank
read off the table. -/
@[expose] def abstractOf (cv : ConcreteVWAA α) (hveryWeak : cv.VeryWeak) : VWAA Nat α where
  trans i := encTrans (cv.trans.getD i [])
  initial := [{cv.initial}]
  final i := cv.final.getD i false = true
  rank i := (cv.table.formulaOf i).rank
  veryWeak i g O hmem q hq := by
    obtain ⟨⟨g0, t0⟩, hmem0, heq⟩ := List.mem_map.mp hmem
    injection heq with _ hOeq
    rw [← hOeq, mem_maskSet] at hq
    exact hveryWeak i g0 t0 hmem0 q hq

/-! ## Reachability correspondence -/

/-- `q` is a `transSucc` successor of `p` iff some alternative of `p` in `abstractOf cv hveryWeak` targets it. -/
theorem mem_transSucc_iff [LawfulBEq α] [LawfulHashable α] (cv : ConcreteVWAA α)
    (hveryWeak : cv.VeryWeak) (p q : Nat) :
    q ∈ transSucc cv.trans p ↔ ∃ g O, (g, O) ∈ (abstractOf cv hveryWeak).trans p ∧ q ∈ O := by
  unfold transSucc abstractOf encTrans
  constructor
  · intro hq
    obtain ⟨⟨g, t⟩, hmem, hqt⟩ := List.mem_flatMap.mp hq
    exact ⟨DNF.sat g, maskSet t, List.mem_map.mpr ⟨(g, t), hmem, rfl⟩, mem_maskSet.mpr (mem_maskMembers.mp hqt)⟩
  · rintro ⟨g, O, hgO, hq⟩
    obtain ⟨⟨g0, t0⟩, hmem0, heq⟩ := List.mem_map.mp hgO
    injection heq with _ hOeq
    rw [← hOeq, mem_maskSet] at hq
    exact List.mem_flatMap.mpr ⟨(g0, t0), hmem0, mem_maskMembers.mpr hq⟩

/-- Every `VWAA.Reachable` state of `abstractOf cv hveryWeak` from `{cv.initial}` is found by `reachableFrom`, given
`transSucc` stays within the table's ids. -/
theorem reachableFrom_of_reachable [LawfulBEq α] [LawfulHashable α] (cv : ConcreteVWAA α)
    (hveryWeak : cv.VeryWeak)
    (hinit : cv.initial < cv.table.formulas.size)
    (hbound : ∀ p, p < cv.table.formulas.size → ∀ q ∈ transSucc cv.trans p, q < cv.table.formulas.size) :
    ∀ x, VWAA.Reachable (abstractOf cv hveryWeak) {cv.initial} x →
      (reachableFrom (transSucc cv.trans) [cv.initial] (List.range cv.table.formulas.size)).contains x := by
  intro x hx
  induction hx with
  | base q hq =>
    rw [FinSet.mem_singleton] at hq
    subst hq
    exact starts_subset_reachableFrom _ _ _ _ (List.mem_singleton.mpr rfl)
  | step p _ g O hgO q hq ih =>
    have hqsucc : q ∈ transSucc cv.trans p := (mem_transSucc_iff cv hveryWeak p q).mpr ⟨g, O, hgO, hq⟩
    exact reachableFrom_closed (transSucc cv.trans) [cv.initial] (List.range cv.table.formulas.size)
      (fun x => x < cv.table.formulas.size) hbound
      (fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact hinit)
      (fun x hx => Or.inr (List.mem_range.mpr hx)) p ih q hqsucc

/-- The converse: every state `reachableFrom`'s BFS marks is a genuine `VWAA.Reachable` state. -/
theorem reachable_of_reachableFrom [LawfulBEq α] [LawfulHashable α] (cv : ConcreteVWAA α)
    (hveryWeak : cv.VeryWeak) :
    ∀ x, (reachableFrom (transSucc cv.trans) [cv.initial] (List.range cv.table.formulas.size)).contains x →
      VWAA.Reachable (abstractOf cv hveryWeak) {cv.initial} x :=
  reachableFrom_subset (transSucc cv.trans) (fun x => VWAA.Reachable (abstractOf cv hveryWeak) {cv.initial} x)
    (fun p hp q hq => by
      obtain ⟨g, O, hgO, hqO⟩ := (mem_transSucc_iff cv hveryWeak p q).mp hq
      exact .step p hp g O hgO q hqO)
    [cv.initial] (List.range cv.table.formulas.size)
    (fun x hx => by
      rw [List.mem_singleton] at hx
      subst hx
      exact .base cv.initial (FinSet.mem_singleton_self _))

/-- Every `VWAA.Reachable` state stays inside the table, given every target does. -/
theorem reachable_lt_size [LawfulBEq α] [LawfulHashable α] (cv : ConcreteVWAA α)
    (hveryWeak : cv.VeryWeak)
    (hinit : cv.initial < cv.table.formulas.size)
    (hbound : ∀ p, p < cv.table.formulas.size → ∀ q ∈ transSucc cv.trans p, q < cv.table.formulas.size) :
    ∀ x, VWAA.Reachable (abstractOf cv hveryWeak) {cv.initial} x → x < cv.table.formulas.size := by
  intro x hx
  induction hx with
  | base q hq => rw [FinSet.mem_singleton] at hq; subst hq; exact hinit
  | step p hp g O hgO q hq ih =>
    exact hbound p ih q ((mem_transSucc_iff cv hveryWeak p q).mpr ⟨g, O, hgO, hq⟩)

/-- `keptIds` never repeats an id. -/
theorem keptIds_nodup (cv : ConcreteVWAA α) : (keptIds cv).Nodup :=
  List.filter_sublist.nodup List.nodup_range

/-- `keptIds` is exactly the `VWAA.Reachable` ids. -/
theorem mem_keptIds_iff_reachable [LawfulBEq α] [LawfulHashable α] (cv : ConcreteVWAA α)
    (hveryWeak : cv.VeryWeak)
    (hinit : cv.initial < cv.table.formulas.size)
    (hbound : ∀ p, p < cv.table.formulas.size → ∀ q ∈ transSucc cv.trans p, q < cv.table.formulas.size)
    (old : Nat) :
    old ∈ keptIds cv ↔ VWAA.Reachable (abstractOf cv hveryWeak) {cv.initial} old := by
  unfold keptIds reachIds
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨_, hreach⟩
    exact reachable_of_reachableFrom cv hveryWeak old hreach
  · intro hreach
    exact ⟨reachable_lt_size cv hveryWeak hinit hbound old hreach,
      reachableFrom_of_reachable cv hveryWeak hinit hbound old hreach⟩

/-! ## State relabeling -/

private theorem restrictReachable_trans (cv : ConcreteVWAA α) :
    (restrictReachable cv).trans = (keptIds cv).toArray.map fun old =>
      (cv.trans.getD old []).map fun p => (p.1, remapMask ((remapIds cv).getD · 0) p.2) := rfl

private theorem restrictReachable_final (cv : ConcreteVWAA α) :
    (restrictReachable cv).final = (keptIds cv).toArray.map fun old => cv.final.getD old false := rfl

private theorem remapIds_eq_of_getElem? (cv : ConcreteVWAA α) (old j : Nat)
    (hj : (keptIds cv)[j]? = some old) : (remapIds cv).getD old 0 = j := by
  have h := SubformulaTable.buildIndex_get (keptIds cv) (keptIds_nodup cv)
    (Std.HashMap.emptyWithCapacity (keptIds cv).length) 0 j old hj
  simpa [remapIds] using h

/-- Reading `keptIds` at a kept id's new position gives back the original id. -/
theorem remap_left_inv (cv : ConcreteVWAA α) (old : Nat) (hold : old ∈ keptIds cv) :
    (keptIds cv).getD ((remapIds cv).getD old 0) 0 = old := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hold
  rw [remapIds_eq_of_getElem? cv old j hj, List.getD_eq_getElem?_getD, hj]
  rfl

/-- The new id `remapIds` assigns a kept id always lands inside the dense range. -/
theorem remap_lt_length (cv : ConcreteVWAA α) (old : Nat) (hold : old ∈ keptIds cv) :
    (remapIds cv).getD old 0 < (keptIds cv).length := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hold
  rw [remapIds_eq_of_getElem? cv old j hj]
  exact (List.getElem?_eq_some_iff.mp hj).1

/-- `restrictReachable`'s transitions at a kept id's new position are exactly the source's own, relabeled
through `remapIds`. -/
theorem restrictReachable_trans_eq (cv : ConcreteVWAA α) (old : Nat) (hold : old ∈ keptIds cv) :
    (restrictReachable cv).trans.getD ((remapIds cv).getD old 0) [] =
      (cv.trans.getD old []).map fun p => (p.1, remapMask ((remapIds cv).getD · 0) p.2) := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hold
  rw [remapIds_eq_of_getElem? cv old j hj, restrictReachable_trans, Array.getD_eq_getD_getElem?,
    Array.getElem?_map, List.getElem?_toArray, hj]
  rfl

/-- `restrictReachable`'s finality at a kept id's new position agrees with the source's own. -/
theorem restrictReachable_final_iff (cv : ConcreteVWAA α) (old : Nat) (hold : old ∈ keptIds cv) :
    (restrictReachable cv).final.getD ((remapIds cv).getD old 0) false =
      cv.final.getD old false := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hold
  rw [remapIds_eq_of_getElem? cv old j hj, restrictReachable_final, Array.getD_eq_getD_getElem?,
    Array.getElem?_map, List.getElem?_toArray, hj]
  rfl

private theorem restrictReachable_formulas (cv : ConcreteVWAA α) :
    (restrictReachable cv).table.formulas = (keptIds cv).toArray.map cv.table.formulaOf := rfl

private theorem restrictReachable_initial (cv : ConcreteVWAA α) :
    (restrictReachable cv).initial = (remapIds cv).getD cv.initial 0 := rfl

/-- The original id at a dense position. -/
private def keptAt (cv : ConcreteVWAA α) (i : Nat) : Nat := (keptIds cv).getD i 0

private theorem getElem?_keptIds_eq_keptAt (cv : ConcreteVWAA α) (i : Nat) (hi : i < (keptIds cv).length) :
    (keptIds cv)[i]? = some (keptAt cv i) := by
  unfold keptAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- `keptAt` always names a kept id. -/
private theorem keptAt_mem (cv : ConcreteVWAA α) (i : Nat) (hi : i < (keptIds cv).length) :
    keptAt cv i ∈ keptIds cv := by
  have h := getElem?_keptIds_eq_keptAt cv i hi
  exact List.mem_of_getElem? h

/-- Relabeling `keptAt cv i` gives back the dense id `i`. -/
private theorem remap_keptAt (cv : ConcreteVWAA α) (i : Nat) (hi : i < (keptIds cv).length) :
    (remapIds cv).getD (keptAt cv i) 0 = i :=
  remapIds_eq_of_getElem? cv (keptAt cv i) i (getElem?_keptIds_eq_keptAt cv i hi)

/-- `restrictReachable`'s table reads a dense id's formula off `keptAt`'s original one. -/
private theorem restrictReachable_formulaOf (cv : ConcreteVWAA α) (i : Nat) (hi : i < (keptIds cv).length) :
    (restrictReachable cv).table.formulaOf i = cv.table.formulaOf (keptAt cv i) := by
  unfold SubformulaTable.formulaOf
  rw [restrictReachable_formulas, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    List.getElem?_toArray, getElem?_keptIds_eq_keptAt cv i hi]
  rfl

/-- `restrictReachable` preserves very weakness. -/
theorem build_veryWeak [LawfulBEq α] [LawfulHashable α] (cv : ConcreteVWAA α)
    (hveryWeak : cv.VeryWeak)
    (hinit : cv.initial < cv.table.formulas.size)
    (hbound : ∀ p, p < cv.table.formulas.size → ∀ q ∈ transSucc cv.trans p, q < cv.table.formulas.size) :
    (restrictReachable cv).VeryWeak := by
  intro i g t hmem j hj
  by_cases hi : i < (keptIds cv).length
  · set old := keptAt cv i with holddef
    have holdmem : old ∈ keptIds cv := keptAt_mem cv i hi
    have heold : (remapIds cv).getD old 0 = i := remap_keptAt cv i hi
    rw [← heold, restrictReachable_trans_eq cv old holdmem] at hmem
    obtain ⟨⟨g0, t0⟩, hmem0, heq⟩ := List.mem_map.mp hmem
    injection heq with hgeq hteq
    rw [← hteq, testBit_remapMask] at hj
    obtain ⟨j0, hj0, hjeq⟩ := hj
    rcases hveryWeak old g0 t0 hmem0 j0 hj0 with hj0eq | hj0lt
    · left
      rw [← hjeq, hj0eq]
      exact heold
    · right
      have hreach : VWAA.Reachable (abstractOf cv hveryWeak) {cv.initial} old :=
        (mem_keptIds_iff_reachable cv hveryWeak hinit hbound old).mp holdmem
      have hj0reach : VWAA.Reachable (abstractOf cv hveryWeak) {cv.initial} j0 :=
        .step old hreach (DNF.sat g0) (maskSet t0) (List.mem_map.mpr ⟨(g0, t0), hmem0, rfl⟩) j0 (mem_maskSet.mpr hj0)
      have hj0mem : j0 ∈ keptIds cv := (mem_keptIds_iff_reachable cv hveryWeak hinit hbound j0).mpr hj0reach
      have hjlt : j < (keptIds cv).length := by rw [← hjeq]; exact remap_lt_length cv j0 hj0mem
      have hkeptj : keptAt cv j = j0 := by
        unfold keptAt
        rw [← hjeq]
        exact remap_left_inv cv j0 hj0mem
      rw [restrictReachable_formulaOf cv i hi, restrictReachable_formulaOf cv j hjlt, hkeptj]
      exact hj0lt
  · exfalso
    have hsize : (restrictReachable cv).trans.size = (keptIds cv).length := by
      rw [restrictReachable_trans, Array.size_map, List.size_toArray]
    have hge : (restrictReachable cv).trans.size ≤ i := by omega
    have hnone : (restrictReachable cv).trans.getD i [] = [] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hge]
      rfl
    rw [hnone] at hmem
    exact absurd hmem (by simp)

/-- `restrictReachable`'s transitions never target outside its dense range. -/
theorem restrictReachable_target_lt_size [LawfulBEq α] [LawfulHashable α] (cv : ConcreteVWAA α)
    (hveryWeak : cv.VeryWeak)
    (hinit : cv.initial < cv.table.formulas.size)
    (hbound : ∀ p, p < cv.table.formulas.size → ∀ q ∈ transSucc cv.trans p, q < cv.table.formulas.size) :
    ∀ i g t, (g, t) ∈ (restrictReachable cv).trans.getD i [] → ∀ j, t.testBit j = true →
      j < (restrictReachable cv).trans.size := by
  intro i g t hmem j hj
  have hsize : (restrictReachable cv).trans.size = (keptIds cv).length := by
    rw [restrictReachable_trans, Array.size_map, List.size_toArray]
  by_cases hi : i < (keptIds cv).length
  · set old := keptAt cv i with holddef
    have holdmem : old ∈ keptIds cv := keptAt_mem cv i hi
    have heold : (remapIds cv).getD old 0 = i := remap_keptAt cv i hi
    rw [← heold, restrictReachable_trans_eq cv old holdmem] at hmem
    obtain ⟨⟨g0, t0⟩, hmem0, heq⟩ := List.mem_map.mp hmem
    injection heq with _ hteq
    rw [← hteq, testBit_remapMask] at hj
    obtain ⟨j0, hj0, hjeq⟩ := hj
    have hreach : VWAA.Reachable (abstractOf cv hveryWeak) {cv.initial} old :=
      (mem_keptIds_iff_reachable cv hveryWeak hinit hbound old).mp holdmem
    have hj0reach : VWAA.Reachable (abstractOf cv hveryWeak) {cv.initial} j0 :=
      .step old hreach (DNF.sat g0) (maskSet t0) (List.mem_map.mpr ⟨(g0, t0), hmem0, rfl⟩) j0 (mem_maskSet.mpr hj0)
    have hj0mem : j0 ∈ keptIds cv := (mem_keptIds_iff_reachable cv hveryWeak hinit hbound j0).mpr hj0reach
    rw [hsize, ← hjeq]
    exact remap_lt_length cv j0 hj0mem
  · exfalso
    have hge : (restrictReachable cv).trans.size ≤ i := by omega
    have hnone : (restrictReachable cv).trans.getD i [] = [] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hge]
      rfl
    rw [hnone] at hmem
    exact absurd hmem (by simp)

/-- `restrictReachable`'s initial state lies inside its dense range. -/
theorem restrictReachable_initial_lt_size [LawfulBEq α] [LawfulHashable α] (cv : ConcreteVWAA α)
    (hveryWeak : cv.VeryWeak)
    (hinit : cv.initial < cv.table.formulas.size)
    (hbound : ∀ p, p < cv.table.formulas.size → ∀ q ∈ transSucc cv.trans p, q < cv.table.formulas.size) :
    (restrictReachable cv).initial < (restrictReachable cv).trans.size := by
  have hsize : (restrictReachable cv).trans.size = (keptIds cv).length := by
    rw [restrictReachable_trans, Array.size_map, List.size_toArray]
  have hmem : cv.initial ∈ keptIds cv :=
    (mem_keptIds_iff_reachable cv hveryWeak hinit hbound cv.initial).mpr
      (.base cv.initial (FinSet.mem_singleton_self _))
  rw [restrictReachable_initial, hsize]
  exact remap_lt_length cv cv.initial hmem

/-- `restrictReachable` relabels the reachable states of `abstractOf cv hveryWeak` along `remapIds`, with left inverse
`keptAt`, `[JN18]`'s `concr2AbstrAA`. -/
private theorem relabelsFrom_restrictReachable [LawfulBEq α] [LawfulHashable α] (cv : ConcreteVWAA α)
    (hveryWeak : cv.VeryWeak)
    (hinit : cv.initial < cv.table.formulas.size)
    (hbound : ∀ p, p < cv.table.formulas.size → ∀ q ∈ transSucc cv.trans p, q < cv.table.formulas.size) :
    VWAA.RelabelsFrom (abstractOf cv hveryWeak) {cv.initial} (fun old => (remapIds cv).getD old 0)
      (keptAt cv) (abstractOf (restrictReachable cv) (build_veryWeak cv hveryWeak hinit hbound)) where
  left_inv q hq :=
    remap_left_inv cv q ((mem_keptIds_iff_reachable cv hveryWeak hinit hbound q).mpr hq)
  trans q hq := by
    have hqmem : q ∈ keptIds cv := (mem_keptIds_iff_reachable cv hveryWeak hinit hbound q).mpr hq
    show encTrans ((restrictReachable cv).trans.getD ((remapIds cv).getD q 0) []) =
      (encTrans (cv.trans.getD q [])).map
        fun (p : ((α → Prop) → Prop) × FinSet Nat) => (p.1, p.2.image fun old => (remapIds cv).getD old 0)
    rw [restrictReachable_trans_eq cv q hqmem]
    unfold encTrans
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    rintro ⟨g0, t0⟩ _
    simp only [Function.comp_def, maskSet_remapMask]
  final q hq := by
    have hqmem : q ∈ keptIds cv := (mem_keptIds_iff_reachable cv hveryWeak hinit hbound q).mpr hq
    show (restrictReachable cv).final.getD ((remapIds cv).getD q 0) false = true ↔
      cv.final.getD q false = true
    rw [restrictReachable_final_iff cv q hqmem]

/-- `restrictReachable` accepts from its remapped initial state exactly what the source accepts, `[GO01]` §6
`REDUCE_STATE_CORRECT`. -/
theorem restrictReachable_acceptsFrom_iff [LawfulBEq α] [LawfulHashable α] (cv : ConcreteVWAA α)
    (hveryWeak : cv.VeryWeak)
    (hinit : cv.initial < cv.table.formulas.size)
    (hbound : ∀ p, p < cv.table.formulas.size → ∀ q ∈ transSucc cv.trans p, q < cv.table.formulas.size)
    (ξ : OmegaWord α) :
    (abstractOf (restrictReachable cv) (build_veryWeak cv hveryWeak hinit hbound)).AcceptsFrom
        {(restrictReachable cv).initial} ξ ↔
      (abstractOf cv hveryWeak).AcceptsFrom {cv.initial} ξ := by
  have hr := relabelsFrom_restrictReachable cv hveryWeak hinit hbound
  have hSeq : ({cv.initial} : FinSet Nat).image (fun old => (remapIds cv).getD old 0) =
      {(restrictReachable cv).initial} := by
    rw [FinSet.image_singleton, ← restrictReachable_initial]
  rw [← hSeq]
  exact VWAA.acceptsFrom_relabel hr ξ

/-! ## Reduction correctness -/

theorem encTrans_append (xs ys : List (DNF α × Nat)) : encTrans (xs ++ ys) = encTrans xs ++ encTrans ys :=
  List.map_append

private theorem sat_top_eq : DNF.sat (DNF.top (α := α)) = fun _ => True := by
  funext v; exact propext (iff_of_true (DNF.sat_top v) trivial)

private theorem encTrans_top_bit (i : Nat) : encTrans [(DNF.top (α := α), bit i)] = [(fun _ => True, {i})] := by
  simp [encTrans, sat_top_eq, maskSet_bit]

section Merge

variable {K : Type v} [BEq K] [Hashable K] [LawfulBEq K]

private theorem foldl_mergeStep_contains (l : List (DNF α × K)) (m : Std.HashMap K (DNF α)) (t : K) :
    (l.foldl mergeStep m).contains t = true ↔ m.contains t = true ∨ ∃ g, (g, t) ∈ l := by
  induction l generalizing m with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih]
    unfold mergeStep
    rw [Std.HashMap.contains_insert]
    obtain ⟨g0, t0⟩ := p
    simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro ((rfl | h) | ⟨g, hg⟩)
      · exact Or.inr ⟨g0, Or.inl ⟨rfl, rfl⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨g, Or.inr hg⟩
    · rintro (h | ⟨g, ⟨-, rfl⟩ | hg⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ⟨g, hg⟩

private theorem foldl_mergeStep_sat (l : List (DNF α × K)) (m : Std.HashMap K (DNF α)) (t : K)
    (v : α → Prop) :
    DNF.sat ((l.foldl mergeStep m).getD t DNF.bot) v ↔
      DNF.sat (m.getD t DNF.bot) v ∨ ∃ g, (g, t) ∈ l ∧ DNF.sat g v := by
  induction l generalizing m with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih]
    unfold mergeStep
    rw [Std.HashMap.getD_insert]
    obtain ⟨g0, t0⟩ := p
    simp only [List.mem_cons, Prod.mk.injEq]
    by_cases ht : t0 = t
    · subst ht
      simp only [beq_self_eq_true, if_true, DNF.sat_or]
      grind
    · have hne : (t0 == t) = false := beq_false_of_ne ht
      simp only [hne, Bool.false_eq_true, if_false]
      grind

theorem mem_mergeByTarget (l : List (DNF α × K)) (g : DNF α) (t : K) :
    (g, t) ∈ mergeByTarget l ↔ (∃ g0, (g0, t) ∈ l) ∧
      g = (l.foldl mergeStep (Std.HashMap.emptyWithCapacity 8)).getD t DNF.bot := by
  unfold mergeByTarget
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨t', g'⟩, hmem, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hmem
    have hc : (l.foldl mergeStep (Std.HashMap.emptyWithCapacity 8)).contains t' = true := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, hmem]; rfl
    refine ⟨?_, ?_⟩
    · rcases (foldl_mergeStep_contains l _ t').mp hc with h | h
      · simp [Std.HashMap.contains_emptyWithCapacity] at h
      · exact h
    · rw [Std.HashMap.getD_eq_getD_getElem?, hmem]; rfl
  · rintro ⟨hex, rfl⟩
    have hc : (l.foldl mergeStep (Std.HashMap.emptyWithCapacity 8)).contains t = true :=
      (foldl_mergeStep_contains l _ t).mpr (Or.inr hex)
    exact ⟨(t, _), (Std.HashMap.mem_toList_iff_getElem?_eq_some).mpr
      (Std.HashMap.getElem?_eq_some_getD_of_contains hc), rfl⟩

/-- Merging is exact letterwise: a key is enabled on `v` after merging iff some entry with that key was before. -/
theorem mergeByTarget_sat (l : List (DNF α × K)) (t : K) (v : α → Prop) :
    (∃ g, (g, t) ∈ mergeByTarget l ∧ DNF.sat g v) ↔ ∃ g, (g, t) ∈ l ∧ DNF.sat g v := by
  constructor
  · rintro ⟨g, hmem, hv⟩
    obtain ⟨-, rfl⟩ := (mem_mergeByTarget l g t).mp hmem
    rcases (foldl_mergeStep_sat l _ t v).mp hv with h | h
    · simp [Std.HashMap.getD_emptyWithCapacity, DNF.not_sat_bot] at h
    · exact h
  · rintro ⟨g, hmem, hv⟩
    exact ⟨_, (mem_mergeByTarget l _ t).mpr ⟨⟨g, hmem⟩, rfl⟩,
      (foldl_mergeStep_sat l _ t v).mpr (Or.inr ⟨g, hmem, hv⟩)⟩

theorem mergeByTarget_key_mem {l : List (DNF α × K)} {g : DNF α} {t : K} (h : (g, t) ∈ mergeByTarget l) :
    ∃ g0, (g0, t) ∈ l :=
  ((mem_mergeByTarget l g t).mp h).1

/-- Every entry of `l` survives merging as an entry with the same key and a weaker guard. -/
theorem exists_mergeByTarget_of_mem {l : List (DNF α × K)} {g0 : DNF α} {t : K} (h : (g0, t) ∈ l) :
    ∃ g, (g, t) ∈ mergeByTarget l ∧ ∀ v, DNF.sat g0 v → DNF.sat g v :=
  ⟨_, (mem_mergeByTarget l _ t).mpr ⟨⟨g0, h⟩, rfl⟩,
    fun v hv => (foldl_mergeStep_sat l _ t v).mpr (Or.inr ⟨g0, h, hv⟩)⟩

end Merge

theorem listSim_mergeByTarget (l : List (DNF α × Nat)) :
    VWAA.ListSim (encTrans (mergeByTarget l)) (encTrans l) where
  sound G O v hmem hv := by
    obtain ⟨⟨g, t⟩, hm, heq⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨g0, hg0, hv0⟩ := (mergeByTarget_sat l t v).mp ⟨g, hm, hv⟩
    exact ⟨_, _, List.mem_map.mpr ⟨(g0, t), hg0, rfl⟩, hv0, FinSet.Subset.refl _⟩
  complete G O v hmem hv := by
    obtain ⟨⟨g, t⟩, hm, heq⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨g0, hg0, hv0⟩ := (mergeByTarget_sat l t v).mpr ⟨g, hm, hv⟩
    exact ⟨_, _, List.mem_map.mpr ⟨(g0, t), hg0, rfl⟩, hv0, FinSet.Subset.refl _⟩

theorem targetsIn_mergeByTarget (l : List (DNF α × Nat)) :
    VWAA.TargetsIn (encTrans (mergeByTarget l)) (encTrans l) := by
  intro p hp
  obtain ⟨⟨g, t⟩, hmem, rfl⟩ := List.mem_map.mp hp
  obtain ⟨⟨g0, hg0⟩, -⟩ := (mem_mergeByTarget l g t).mp hmem
  exact ⟨_, List.mem_map.mpr ⟨(g0, t), hg0, rfl⟩, rfl⟩

private theorem mem_splitByTarget (l : List (DNF α × Nat)) (g' : DNF α) (t : Nat) :
    (g', t) ∈ splitByTarget l ↔ ∃ g, (g, t) ∈ l ∧ g' = splitGuard l g t ∧ DNF.isEmpty g' = false := by
  unfold splitByTarget
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨g, t0⟩, hmem, heq⟩
    dsimp only at heq
    split at heq
    · exact absurd heq (by simp)
    · rename_i hne
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨g, hmem, rfl, by simpa using hne⟩
  · rintro ⟨g, hmem, rfl, hne⟩
    refine ⟨(g, t), hmem, ?_⟩
    dsimp only
    rw [if_neg (by simp [hne])]

/-- `true` exactly for the guards `splitGuard l · t` narrows by. -/
private theorem splitCond_iff (p : DNF α × Nat) (t : Nat) :
    (maskSub p.2 t && p.2 != t) = true ↔ maskSub p.2 t = true ∧ p.2 ≠ t := by
  simp [bne_iff_ne]

section Split

variable [LawfulBEq α] [LawfulHashable α]

private theorem sat_splitGuard (l : List (DNF α × Nat)) (g : DNF α) (t : Nat) (v : α → Prop) :
    DNF.sat (splitGuard l g t) v ↔
      DNF.sat g v ∧ ∀ p ∈ l, maskSub p.2 t = true → p.2 ≠ t → ¬ DNF.sat p.1 v := by
  unfold splitGuard
  induction l generalizing g with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih]
    by_cases hc : (maskSub p.2 t && p.2 != t) = true
    · rw [if_pos hc, DNF.sat_diff]
      obtain ⟨hs, hne⟩ := (splitCond_iff p t).mp hc
      constructor
      · rintro ⟨⟨hg, hp⟩, hrest⟩
        refine ⟨hg, fun q hq hqs hqne => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hp
        · exact hrest q hq hqs hqne
      · rintro ⟨hg, hrest⟩
        exact ⟨⟨hg, hrest p List.mem_cons_self hs hne⟩, fun q hq => hrest q (List.mem_cons_of_mem _ hq)⟩
    · rw [if_neg hc]
      constructor
      · rintro ⟨hg, hrest⟩
        refine ⟨hg, fun q hq hqs hqne => ?_⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact absurd ((splitCond_iff q t).mpr ⟨hqs, hqne⟩) hc
        · exact hrest q hq hqs hqne
      · rintro ⟨hg, hrest⟩
        exact ⟨hg, fun q hq => hrest q (List.mem_cons_of_mem _ hq)⟩

/-- A transition firing on `v` with a target inside `t` leaves a split transition firing on `v` with a target inside
`t`. -/
private theorem splitByTarget_complete (l : List (DNF α × Nat)) (t : Nat) (v : α → Prop) :
    ∀ t0 g0, (g0, t0) ∈ l → DNF.sat g0 v → maskSub t0 t = true →
      ∃ g' t', (g', t') ∈ splitByTarget l ∧ DNF.sat g' v ∧ maskSub t' t = true := by
  intro t0
  induction t0 using Nat.strongRecOn with
  | _ t0 ih =>
    intro g0 hmem hv hsub
    by_cases hex : ∃ p ∈ l, maskSub p.2 t0 = true ∧ p.2 ≠ t0 ∧ DNF.sat p.1 v
    · obtain ⟨⟨g1, t1⟩, hm1, hs1, hne1, hv1⟩ := hex
      exact ih t1 (lt_of_maskSub hs1 hne1) g1 hm1 hv1 (maskSub_trans hs1 hsub)
    · have hg : DNF.sat (splitGuard l g0 t0) v :=
        (sat_splitGuard l g0 t0 v).mpr ⟨hv, fun p hp hs hne hpv => hex ⟨p, hp, hs, hne, hpv⟩⟩
      have hne : DNF.isEmpty (splitGuard l g0 t0) = false := by
        cases h : DNF.isEmpty (splitGuard l g0 t0)
        · rfl
        · exact absurd hg (DNF.not_sat_of_isEmpty _ h v)
      exact ⟨_, t0, (mem_splitByTarget l _ t0).mpr ⟨g0, hmem, rfl, hne⟩, hg, hsub⟩

theorem listSim_splitByTarget (l : List (DNF α × Nat)) :
    VWAA.ListSim (encTrans (splitByTarget l)) (encTrans l) where
  sound G O v hmem hv := by
    obtain ⟨⟨g', t⟩, hm, heq⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨g, hg, rfl, -⟩ := (mem_splitByTarget l g' t).mp hm
    exact ⟨_, _, List.mem_map.mpr ⟨(g, t), hg, rfl⟩, ((sat_splitGuard l g t v).mp hv).1,
      FinSet.Subset.refl _⟩
  complete G O v hmem hv := by
    obtain ⟨⟨g, t⟩, hm, heq⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨g', t', hm', hv', hs'⟩ := splitByTarget_complete l t v t g hm hv (maskSub_refl t)
    exact ⟨_, _, List.mem_map.mpr ⟨(g', t'), hm', rfl⟩, hv', maskSet_subset_of_maskSub hs'⟩

end Split

theorem targetsIn_splitByTarget (l : List (DNF α × Nat)) :
    VWAA.TargetsIn (encTrans (splitByTarget l)) (encTrans l) := by
  intro p hp
  obtain ⟨⟨g', t⟩, hmem, rfl⟩ := List.mem_map.mp hp
  obtain ⟨g, hg, -, -⟩ := (mem_splitByTarget l g' t).mp hmem
  exact ⟨_, List.mem_map.mpr ⟨(g, t), hg, rfl⟩, rfl⟩

theorem listSim_reduceTrans [LawfulBEq α] [LawfulHashable α] (l : List (DNF α × Nat)) :
    VWAA.ListSim (encTrans (reduceTrans l)) (encTrans l) :=
  (listSim_splitByTarget _).trans (listSim_mergeByTarget l)

theorem targetsIn_reduceTrans (l : List (DNF α × Nat)) :
    VWAA.TargetsIn (encTrans (reduceTrans l)) (encTrans l) :=
  (targetsIn_splitByTarget _).trans (targetsIn_mergeByTarget l)

private theorem mem_tprod {xs ys : List (DNF α × Nat)} {p : DNF α × Nat} :
    p ∈ tprod xs ys ↔ ∃ p1 ∈ xs, ∃ p2 ∈ ys, DNF.isEmpty (DNF.and p1.1 p2.1) = false ∧
      p = (DNF.and p1.1 p2.1, p1.2 ||| p2.2) := by
  unfold tprod
  simp only [List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨p1, h1, p2, h2, heq⟩
    split at heq
    · exact absurd heq (by simp)
    · rename_i hne
      exact ⟨p1, h1, p2, h2, by simpa using hne, (Option.some.inj heq).symm⟩
  · rintro ⟨p1, h1, p2, h2, hne, rfl⟩
    exact ⟨p1, h1, p2, h2, by rw [if_neg (by simp [hne])]⟩

theorem targetsIn_tprod (xs ys : List (DNF α × Nat)) :
    VWAA.TargetsIn (encTrans (tprod xs ys)) (VWAA.lprod (encTrans xs) (encTrans ys)) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨p1, h1, p2, h2, -, rfl⟩ := mem_tprod.mp hq
  exact ⟨_, VWAA.mem_lprod.mpr ⟨_, List.mem_map.mpr ⟨p1, h1, rfl⟩, _, List.mem_map.mpr ⟨p2, h2, rfl⟩, rfl⟩,
    (maskSet_or _ _).symm⟩

theorem listSim_tprod [LawfulBEq α] [LawfulHashable α] (xs ys : List (DNF α × Nat)) :
    VWAA.ListSim (encTrans (tprod xs ys)) (VWAA.lprod (encTrans xs) (encTrans ys)) where
  sound G O v hmem hv := by
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp hmem
    obtain ⟨p1, h1, p2, h2, -, rfl⟩ := mem_tprod.mp hq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨_, _, VWAA.mem_lprod.mpr ⟨_, List.mem_map.mpr ⟨p1, h1, rfl⟩, _, List.mem_map.mpr ⟨p2, h2, rfl⟩, rfl⟩,
      (DNF.sat_and _ _ v).mp hv, FinSet.subset_of_eq (maskSet_or _ _).symm⟩
  complete G O v hmem hv := by
    obtain ⟨q1, hq1, q2, hq2, heq⟩ := VWAA.mem_lprod.mp hmem
    obtain ⟨p1, h1, rfl⟩ := List.mem_map.mp hq1
    obtain ⟨p2, h2, rfl⟩ := List.mem_map.mp hq2
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hsat : DNF.sat (DNF.and p1.1 p2.1) v := (DNF.sat_and _ _ v).mpr hv
    have hne : DNF.isEmpty (DNF.and p1.1 p2.1) = false := by
      cases h : DNF.isEmpty (DNF.and p1.1 p2.1)
      · rfl
      · exact absurd hsat (DNF.not_sat_of_isEmpty _ h v)
    exact ⟨_, _, List.mem_map.mpr ⟨_, mem_tprod.mpr ⟨p1, h1, p2, h2, hne, rfl⟩, rfl⟩, hsat, FinSet.subset_of_eq (maskSet_or _ _)⟩

/-! ## Correspondence with the abstract construction -/

section Correspondence

variable [LawfulBEq α] [LawfulHashable α]

/-- `NNF.rtrans` letterwise simulates `NNF.vwaaTrans` read through `idx`, in both directions, and every target it has
already occurs in `NNF.vwaaTrans`. -/
theorem rtrans_listSim_targetsIn (idx : NNF α → Nat) (φ : NNF α) :
    VWAA.ListSim (encTrans (φ.rtrans idx)) (encAbs idx φ.vwaaTrans) ∧
      VWAA.TargetsIn (encTrans (φ.rtrans idx)) (encAbs idx φ.vwaaTrans) := by
  induction φ with
  | tt =>
    have h : encTrans (NNF.tt.rtrans idx) = encAbs idx (NNF.tt (α := α)).vwaaTrans := by
      simp [NNF.rtrans, NNF.vwaaTrans, encTrans, encAbs, sat_top_eq, maskSet_zero]
    rw [h]; exact ⟨.refl _, .refl _⟩
  | ff => exact ⟨.refl _, .refl _⟩
  | prop a =>
    have hg : DNF.sat (DNF.lit a true) = fun v => v a := by
      funext v; exact propext (by simp [DNF.sat_lit])
    have h : encTrans ((NNF.prop a).rtrans idx) = encAbs idx (NNF.prop a).vwaaTrans := by
      simp [NNF.rtrans, NNF.vwaaTrans, encTrans, encAbs, hg, maskSet_zero]
    rw [h]; exact ⟨.refl _, .refl _⟩
  | nprop a =>
    have hg : DNF.sat (DNF.lit a false) = fun v => ¬ v a := by
      funext v; exact propext (by simp [DNF.sat_lit])
    have h : encTrans ((NNF.nprop a).rtrans idx) = encAbs idx (NNF.nprop a).vwaaTrans := by
      simp [NNF.rtrans, NNF.vwaaTrans, encTrans, encAbs, hg, maskSet_zero]
    rw [h]; exact ⟨.refl _, .refl _⟩
  | next ψ =>
    have h : encTrans ((NNF.next ψ).rtrans idx) = encAbs idx (NNF.next ψ).vwaaTrans := by
      simp only [NNF.rtrans, NNF.vwaaTrans, encTrans_top_bit, encAbs, List.map_singleton, FinSet.image_singleton]
    rw [h]; exact ⟨.refl _, .refl _⟩
  | and φ ψ ihφ ihψ =>
    have hA : encAbs idx (NNF.and φ ψ).vwaaTrans = VWAA.lprod (encAbs idx φ.vwaaTrans) (encAbs idx ψ.vwaaTrans) :=
      encAbs_lprod idx φ.vwaaTrans ψ.vwaaTrans
    show VWAA.ListSim (encTrans (reduceTrans (tprod _ _))) _ ∧ VWAA.TargetsIn (encTrans (reduceTrans (tprod _ _))) _
    rw [hA]
    exact ⟨(listSim_reduceTrans _).trans ((listSim_tprod _ _).trans (ihφ.1.lprod ihψ.1)),
      (targetsIn_reduceTrans _).trans ((targetsIn_tprod _ _).trans (ihφ.2.lprod ihψ.2))⟩
  | or φ ψ ihφ ihψ =>
    have hA : encAbs idx (NNF.or φ ψ).vwaaTrans = encAbs idx φ.vwaaTrans ++ encAbs idx ψ.vwaaTrans :=
      List.map_append
    show VWAA.ListSim (encTrans (reduceTrans (_ ++ _))) _ ∧ VWAA.TargetsIn (encTrans (reduceTrans (_ ++ _))) _
    rw [hA]
    refine ⟨(listSim_reduceTrans _).trans ?_, (targetsIn_reduceTrans _).trans ?_⟩
    · rw [encTrans_append]; exact ihφ.1.append ihψ.1
    · rw [encTrans_append]; exact ihφ.2.append ihψ.2
  | «until» φ ψ ihφ ihψ =>
    have hA : encAbs idx (NNF.until φ ψ).vwaaTrans =
        encAbs idx ψ.vwaaTrans ++ (encAbs idx φ.vwaaTrans).map fun p => (p.1, p.2 ∪ {idx (NNF.until φ ψ)}) := by
      show encAbs idx (ψ.vwaaTrans ++ φ.vwaaTrans.map fun p => (p.1, p.2 ∪ {NNF.until φ ψ})) = _
      rw [encAbs, List.map_append, ← encAbs, ← encAbs, encAbs_map_union]
    show VWAA.ListSim (encTrans (reduceTrans (_ ++ tprod _ _))) _ ∧
      VWAA.TargetsIn (encTrans (reduceTrans (_ ++ tprod _ _))) _
    rw [hA]
    refine ⟨(listSim_reduceTrans _).trans ?_, (targetsIn_reduceTrans _).trans ?_⟩
    · rw [encTrans_append]
      refine ihψ.1.append ((listSim_tprod _ _).trans ?_)
      rw [encTrans_top_bit]
      exact (ihφ.1.lprod (.refl _)).trans (VWAA.ListSim.lprod_top _ _ _ fun _ => trivial)
    · rw [encTrans_append]
      refine ihψ.2.append ((targetsIn_tprod _ _).trans ?_)
      rw [encTrans_top_bit]
      exact (ihφ.2.lprod (.refl _)).trans (VWAA.TargetsIn.lprod_top _ _ _)
  | «release» φ ψ ihφ ihψ =>
    have hA : encAbs idx (NNF.release φ ψ).vwaaTrans =
        VWAA.lprod (encAbs idx ψ.vwaaTrans) (encAbs idx φ.vwaaTrans ++ [(fun _ => True, {idx (NNF.release φ ψ)})]) := by
      show encAbs idx (VWAA.lprod ψ.vwaaTrans (φ.vwaaTrans ++ [(fun _ => True, {NNF.release φ ψ})])) = _
      rw [encAbs_lprod]
      simp [encAbs]
    show VWAA.ListSim (encTrans (reduceTrans (tprod _ (_ ++ _)))) _ ∧
      VWAA.TargetsIn (encTrans (reduceTrans (tprod _ (_ ++ _)))) _
    rw [hA]
    refine ⟨(listSim_reduceTrans _).trans ((listSim_tprod _ _).trans ?_),
      (targetsIn_reduceTrans _).trans ((targetsIn_tprod _ _).trans ?_)⟩
    · rw [encTrans_append, encTrans_top_bit]; exact ihψ.1.lprod (ihφ.1.append (.refl _))
    · rw [encTrans_append, encTrans_top_bit]; exact ihψ.2.lprod (ihφ.2.append (.refl _))

end Correspondence

/-! ## The raw stage -/

private theorem readTrans_lazyTrans (table : SubformulaTable α) (i : Nat) :
    readTrans (lazyTrans table) i = if i < table.formulas.size then (table.formulaOf i).rtrans table.idOf else [] := by
  unfold readTrans lazyTrans
  split
  · rename_i hi
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hi]
    unfold SubformulaTable.formulaOf
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    rfl
  · rename_i hi
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using hi)]
    rfl

/-- The reachable set `rawStage` computes δ for. -/
private abbrev rawReach (φ : NNF α) : Std.HashSet Nat :=
  reachableFrom (readSucc (lazyTrans (SubformulaTable.build φ))) [(SubformulaTable.build φ).idOf φ]
    (List.range (SubformulaTable.build φ).formulas.size)

private theorem rawStage_trans_getD (φ : NNF α) (i : Nat) :
    (rawStage φ).trans.getD i [] = if i < (SubformulaTable.build φ).formulas.size ∧ (rawReach φ).contains i then
      ((SubformulaTable.build φ).formulaOf i).rtrans (SubformulaTable.build φ).idOf
    else [] := by
  show ((Array.range (SubformulaTable.build φ).formulas.size).map fun i =>
      if (rawReach φ).contains i then readTrans (lazyTrans (SubformulaTable.build φ)) i else []).getD i [] = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  by_cases hi : i < (SubformulaTable.build φ).formulas.size
  · rw [Array.getElem?_range, if_pos hi]
    simp only [Option.map_some, Option.getD_some, readTrans_lazyTrans, if_pos hi]
    by_cases hr : (rawReach φ).contains i = true
    · simp [hr, hi]
    · simp [hr]
  · rw [Array.getElem?_range, if_neg hi]
    simp [hi]

private theorem rawStage_mem_target {φ : NNF α} {i : Nat} {g : DNF α} {t : Nat}
    (h : (g, t) ∈ (rawStage φ).trans.getD i []) :
    i < (SubformulaTable.build φ).formulas.size ∧
      (g, t) ∈ ((SubformulaTable.build φ).formulaOf i).rtrans (SubformulaTable.build φ).idOf := by
  rw [rawStage_trans_getD] at h
  split at h
  · rename_i hc
    exact ⟨hc.1, h⟩
  · simp at h

/-- `ConcreteVWAA.build`'s finality array is no longer than its table. -/
theorem ConcreteVWAA.build_final_size (φ : NNF α) :
    (ConcreteVWAA.build φ).final.size ≤ (ConcreteVWAA.build φ).table.formulas.size := by
  simp [ConcreteVWAA.build, restrictReachable]

/-! ## Final composition -/

section Composition

variable [LawfulBEq α] [LawfulHashable α]

/-- Every target of `NNF.vwaaTrans` at a table id, read through `idOf`, is a table id, and is that id itself or a
strictly lower-ranked one. -/
private theorem vwaaTrans_target_spec [DecidableEq α] (φ : NNF α) (i : Nat)
    (hi : i < (SubformulaTable.build φ).formulas.size) (p : ((α → Prop) → Prop) × FinSet Nat)
    (hp : p ∈ encAbs (SubformulaTable.build φ).idOf ((SubformulaTable.build φ).formulaOf i).vwaaTrans)
    (j : Nat) (hj : j ∈ p.2) :
    j < (SubformulaTable.build φ).formulas.size ∧
      (j = i ∨ ((SubformulaTable.build φ).formulaOf j).rank < ((SubformulaTable.build φ).formulaOf i).rank) := by
  set table := SubformulaTable.build φ
  obtain ⟨⟨g0, O0⟩, hmem, rfl⟩ := List.mem_map.mp hp
  obtain ⟨ψ, hψ, rfl⟩ := FinSet.mem_image.mp hj
  have hsub : NNF.IsSubformula ψ φ :=
    (NNF.vwaaTrans_subformula _ g0 O0 hmem ψ hψ).trans (SubformulaTable.formulaOf_isSubformula φ i hi)
  refine ⟨SubformulaTable.idOf_lt_size φ ψ hsub, ?_⟩
  rcases NNF.vwaaTrans_veryWeak _ g0 O0 hmem ψ hψ with heq | hlt
  · left; rw [heq]; exact SubformulaTable.idOf_formulaOf φ i hi
  · right; rw [SubformulaTable.formulaOf_idOf φ ψ hsub]; exact hlt

/-- Every target bit of `NNF.rtrans` at a table id is a table id, and is that id itself or a strictly lower-ranked
one. -/
private theorem rtrans_target_spec (φ : NNF α) (i : Nat) (hi : i < (SubformulaTable.build φ).formulas.size)
    (g : DNF α) (t : Nat)
    (h : (g, t) ∈ ((SubformulaTable.build φ).formulaOf i).rtrans (SubformulaTable.build φ).idOf)
    (j : Nat) (hj : t.testBit j = true) :
    j < (SubformulaTable.build φ).formulas.size ∧
      (j = i ∨ ((SubformulaTable.build φ).formulaOf j).rank < ((SubformulaTable.build φ).formulaOf i).rank) := by
  classical
  obtain ⟨p, hp, hpt⟩ := (rtrans_listSim_targetsIn (SubformulaTable.build φ).idOf
    ((SubformulaTable.build φ).formulaOf i)).2 _ (List.mem_map.mpr ⟨(g, t), h, rfl⟩)
  exact vwaaTrans_target_spec φ i hi p hp j (by rw [hpt]; exact mem_maskSet.mpr hj)

/-- `NNF.vwaaTrans` on the table ids, `ltlVWAA` relabeled along `idOf`. -/
def tableAbstract [DecidableEq α] (φ : NNF α) : VWAA Nat α where
  trans i := if i < (SubformulaTable.build φ).formulas.size then
    encAbs (SubformulaTable.build φ).idOf ((SubformulaTable.build φ).formulaOf i).vwaaTrans else []
  initial := [{(SubformulaTable.build φ).idOf φ}]
  final i := ((SubformulaTable.build φ).formulaOf i).isUntil
  rank i := ((SubformulaTable.build φ).formulaOf i).rank
  veryWeak i g O hmem q hq := by
    split at hmem
    · exact (vwaaTrans_target_spec φ i ‹_› (g, O) hmem q hq).2
    · simp at hmem

/-- `NNF.rtrans` on the table ids, every id's δ reduced. -/
def reducedAbstract (φ : NNF α) : VWAA Nat α where
  trans i := if i < (SubformulaTable.build φ).formulas.size then
    encTrans (((SubformulaTable.build φ).formulaOf i).rtrans (SubformulaTable.build φ).idOf) else []
  initial := [{(SubformulaTable.build φ).idOf φ}]
  final i := ((SubformulaTable.build φ).formulaOf i).isUntil
  rank i := ((SubformulaTable.build φ).formulaOf i).rank
  veryWeak i g O hmem q hq := by
    split at hmem
    · obtain ⟨⟨g0, t⟩, hm, heq⟩ := List.mem_map.mp hmem
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      exact (rtrans_target_spec φ i ‹_› g0 t hm q (mem_maskSet.mp hq)).2
    · simp at hmem

/-- The reduced table automaton letterwise simulates the unreduced one. -/
theorem reducedAbstract_transSim [DecidableEq α] (φ : NNF α) :
    VWAA.TransSim (reducedAbstract φ) (tableAbstract φ) :=
  VWAA.TransSim.of_listSim fun i => by
    dsimp only [reducedAbstract, tableAbstract]
    split
    · exact (rtrans_listSim_targetsIn _ _).1
    · exact .refl _

/-- `ltlVWAA φ` relabels to the table automaton along `idOf`/`formulaOf`, `[JN18]`'s `concr2AbstrAA`. -/
theorem relabelsFrom_tableAbstract [DecidableEq α] (φ : NNF α) :
    VWAA.RelabelsFrom (ltlVWAA φ) {φ} (SubformulaTable.build φ).idOf (SubformulaTable.build φ).formulaOf
      (tableAbstract φ) where
  left_inv q hq := SubformulaTable.formulaOf_idOf φ q (ltlVWAA_reachable_subformula φ q hq)
  trans q hq := by
    have hsub := ltlVWAA_reachable_subformula φ q hq
    show (if (SubformulaTable.build φ).idOf q < (SubformulaTable.build φ).formulas.size then _ else []) = _
    rw [if_pos (SubformulaTable.idOf_lt_size φ q hsub), SubformulaTable.formulaOf_idOf φ q hsub]
    rfl
  final q hq := by
    have hsub := ltlVWAA_reachable_subformula φ q hq
    show ((SubformulaTable.build φ).formulaOf ((SubformulaTable.build φ).idOf q)).isUntil ↔ q.isUntil
    rw [SubformulaTable.formulaOf_idOf φ q hsub]

/-- `rawStage φ` is very weak. -/
theorem rawStage_veryWeak (φ : NNF α) : (rawStage φ).VeryWeak := by
  intro i g t hmem j hj
  obtain ⟨hi, hm⟩ := rawStage_mem_target hmem
  exact (rtrans_target_spec φ i hi g t hm j hj).2

/-- `rawStage`'s targets always land inside the table. -/
theorem rawStage_transSucc_lt_size (φ : NNF α) (p : Nat) (_hp : p < (SubformulaTable.build φ).formulas.size) :
    ∀ q ∈ transSucc (rawStage φ).trans p, q < (SubformulaTable.build φ).formulas.size := by
  intro q hq
  obtain ⟨⟨g, t⟩, hm, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨hi, hm⟩ := rawStage_mem_target hm
  exact (rtrans_target_spec φ p hi g t hm q (mem_maskMembers.mp hq)).1

/-- Every state the reduced table automaton reaches from `φ`'s id is a table id `rawStage` computed δ for. -/
private theorem reducedAbstract_reachable (φ : NNF α) :
    ∀ q, VWAA.Reachable (reducedAbstract φ) {(SubformulaTable.build φ).idOf φ} q →
      q < (SubformulaTable.build φ).formulas.size ∧ (rawReach φ).contains q = true := by
  set table := SubformulaTable.build φ
  have hinit : table.idOf φ < table.formulas.size := SubformulaTable.idOf_lt_size φ φ .refl
  have hbound : ∀ p, p < table.formulas.size → ∀ q ∈ readSucc (lazyTrans table) p, q < table.formulas.size := by
    intro p hp q hq
    obtain ⟨⟨g, t⟩, hx, hq⟩ := List.mem_flatMap.mp hq
    rw [readTrans_lazyTrans, if_pos hp] at hx
    exact (rtrans_target_spec φ p hp g t hx q (mem_maskMembers.mp hq)).1
  intro q hq
  induction hq with
  | base q hq =>
    rw [FinSet.mem_singleton] at hq
    subst hq
    exact ⟨hinit, starts_subset_reachableFrom _ _ _ _ (List.mem_singleton.mpr rfl)⟩
  | step p _ g O hgO q hq ih =>
    obtain ⟨hp, hpr⟩ := ih
    have hmem : (g, O) ∈ encTrans ((table.formulaOf p).rtrans table.idOf) := by
      have h' : (reducedAbstract φ).trans p = encTrans ((table.formulaOf p).rtrans table.idOf) := if_pos hp
      rw [← h']; exact hgO
    obtain ⟨⟨g0, t⟩, hm, heq⟩ := List.mem_map.mp hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    have hbit := mem_maskSet.mp hq
    have hqlt := (rtrans_target_spec φ p hp g0 t hm q hbit).1
    have hsucc : q ∈ readSucc (lazyTrans table) p := by
      refine List.mem_flatMap.mpr ⟨(g0, t), ?_, mem_maskMembers.mpr hbit⟩
      rw [readTrans_lazyTrans, if_pos hp]; exact hm
    exact ⟨hqlt, reachableFrom_closed (readSucc (lazyTrans table)) [table.idOf φ] (List.range table.formulas.size)
      (fun x => x < table.formulas.size) hbound
      (fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact hinit)
      (fun x hx => Or.inr (List.mem_range.mpr hx)) p hpr q hsucc⟩

/-- `rawStage φ` accepts exactly what the reduced table automaton accepts from `φ`'s id. -/
theorem rawStage_acceptsFrom_iff (φ : NNF α) (ξ : OmegaWord α) :
    (reducedAbstract φ).AcceptsFrom {(SubformulaTable.build φ).idOf φ} ξ ↔
      (abstractOf (rawStage φ) (rawStage_veryWeak φ)).AcceptsFrom {(rawStage φ).initial} ξ := by
  set table := SubformulaTable.build φ
  have htrans : ∀ q, VWAA.Reachable (reducedAbstract φ) {table.idOf φ} q →
      (abstractOf (rawStage φ) (rawStage_veryWeak φ)).trans q = (reducedAbstract φ).trans q := by
    intro q hq
    obtain ⟨hlt, hr⟩ := reducedAbstract_reachable φ q hq
    show encTrans ((rawStage φ).trans.getD q []) =
      if q < table.formulas.size then encTrans ((table.formulaOf q).rtrans table.idOf) else []
    rw [rawStage_trans_getD, if_pos ⟨hlt, hr⟩, if_pos hlt]
  have hfinal : (abstractOf (rawStage φ) (rawStage_veryWeak φ)).final = (reducedAbstract φ).final := by
    funext i
    by_cases hi : i < table.formulas.size
    · show ((table.formulas.map fun | .until _ _ => true | _ => false).getD i false = true) =
        (table.formulaOf i).isUntil
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hi]
      unfold SubformulaTable.formulaOf
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
      simp only [Option.map_some, Option.getD_some]
      split <;> simp_all [NNF.isUntil]
    · have h1 : (rawStage φ).final.getD i false = false := by
        show (table.formulas.map fun | .until _ _ => true | _ => false).getD i false = false
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using hi)]
        rfl
      have hdefault : table.formulaOf i = default := by
        unfold SubformulaTable.formulaOf
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
        rfl
      show ((rawStage φ).final.getD i false = true) = (table.formulaOf i).isUntil
      rw [h1, hdefault]
      simp [show (default : NNF α) = NNF.tt from rfl, NNF.isUntil]
  exact VWAA.acceptsFrom_congr_of_reachable htrans hfinal ξ

/-- `ConcreteVWAA.build φ` is very weak. -/
theorem ConcreteVWAA.build_veryWeak (φ : NNF α) : (ConcreteVWAA.build φ).VeryWeak :=
  LTLLib.build_veryWeak (rawStage φ) (rawStage_veryWeak φ) (SubformulaTable.idOf_lt_size φ φ .refl)
    (rawStage_transSucc_lt_size φ)

/-- `ConcreteVWAA.build`'s transitions never target outside its state array. -/
theorem ConcreteVWAA.build_target_lt_size (φ : NNF α) :
    ∀ i g t, (g, t) ∈ (ConcreteVWAA.build φ).trans.getD i [] → ∀ j, t.testBit j = true →
      j < (ConcreteVWAA.build φ).trans.size :=
  restrictReachable_target_lt_size (rawStage φ) (rawStage_veryWeak φ)
    (SubformulaTable.idOf_lt_size φ φ .refl) (rawStage_transSucc_lt_size φ)

/-- `ConcreteVWAA.build`'s initial id lies inside its state array. -/
theorem ConcreteVWAA.build_initial_lt_size (φ : NNF α) :
    (ConcreteVWAA.build φ).initial < (ConcreteVWAA.build φ).trans.size :=
  restrictReachable_initial_lt_size (rawStage φ) (rawStage_veryWeak φ)
    (SubformulaTable.idOf_lt_size φ φ .refl) (rawStage_transSucc_lt_size φ)

/-- The built VWAA accepts `ξ` from its initial state exactly when `φ` holds on `ξ`. -/
theorem ConcreteVWAA.build_correct [DecidableEq α] (φ : NNF α) (ξ : OmegaWord α) :
    (abstractOf (ConcreteVWAA.build φ) (ConcreteVWAA.build_veryWeak φ)).AcceptsFrom
        {(ConcreteVWAA.build φ).initial} ξ ↔ φ.satisfies ξ := by
  have h1 := restrictReachable_acceptsFrom_iff (rawStage φ) (rawStage_veryWeak φ)
    (SubformulaTable.idOf_lt_size φ φ .refl) (rawStage_transSucc_lt_size φ) ξ
  have h2 := rawStage_acceptsFrom_iff φ ξ
  have h3 := VWAA.acceptsFrom_congr (reducedAbstract_transSim φ) rfl {(SubformulaTable.build φ).idOf φ} ξ
  have h4 : (tableAbstract φ).AcceptsFrom {(SubformulaTable.build φ).idOf φ} ξ ↔ (ltlVWAA φ).AcceptsFrom {φ} ξ := by
    rw [← FinSet.image_singleton]
    exact VWAA.acceptsFrom_relabel (relabelsFrom_tableAbstract φ) ξ
  exact h1.trans (h2.symm.trans (h3.trans (h4.trans (NNF.ltlVWAA_correct φ φ ξ))))

end Composition

end LTLLib
