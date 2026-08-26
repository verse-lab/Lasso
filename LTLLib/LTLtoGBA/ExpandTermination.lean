/-
  Termination of `expand`, the on-the-fly tableau-expansion worklist algorithm (Gerth et al. 1995) that turns an LTL
  formula into a `ExpansionNode` graph.

  `expand` recurses on a node's `new` list, peeling off one formula at a time. The nondeterministic `or`/`until`/`release`
  case can grow the total workload (one node becomes two), so plain structural recursion does not apply. Termination
  instead uses the lexicographic measure `(expandMeasure1, expandMeasure2)`:
  - `expandMeasure1`: unused node "signatures" (`old`/`next` content) left in the finite universe drawable from
    `subformulas topFormula`, strictly decreases whenever a node is finished (merged or added fresh).
  - `expandMeasure2`: weighted size of `node.new`, strictly decreases on every non-finishing recursive step.

  Defines:
  - `weightedSize`: the tie-break measure on `NNF` lists
  - `NodeBounded`/`NodesBounded`/`ExpandInv`: the invariant that `old`/`new`/`next` stay within `subformulas topFormula`,
    carried through `expand_term`
  - `nodeSignature`/`signatureUniverse`/`usedSignatures`: the finite-universe bookkeeping behind `expandMeasure1`
  - `expandMeasure1`/`expandMeasure2`: the termination measure

  Proves:
  - `expand_term`: `expand` always returns `some`, preserving the invariants above
  - `createGraph_term`: `createGraph` always returns `some`

  ## Sections
  - Subformula-list finiteness
  - Weighted formula-size measure
  - Invariant: `old`/`new`/`next` stay within `subformulas topFormula`.
  - The measure
  - Main termination theorem.
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import LTLLib.LTLtoGBA.Invariants

namespace LTLLib

open NNF

/-! ## Subformula-list finiteness -/

section SubformulaFiniteness

variable {α : Type u}

/-- `fold`'s accumulator only ever grows (as membership), regardless of which formula is being folded over -/
theorem NNF.fold_cons_mono (χ : NNF α) {acc acc' : List (NNF α)} (h : acc ⊆ acc') :
    χ.fold (fun a f => f :: a) acc ⊆ χ.fold (fun a f => f :: a) acc' := by
  induction χ generalizing acc acc' with
  | tt | ff | prop _ | nprop _ =>
    simp only [fold]
    exact List.cons_subset_cons _ h
  | next ψ ih =>
    simp only [fold]
    exact ih (List.cons_subset_cons _ h)
  | and ψ1 ψ2 ih1 ih2 | or ψ1 ψ2 ih1 ih2 | «until» ψ1 ψ2 ih1 ih2 | «release» ψ1 ψ2 ih1 ih2 =>
    simp only [fold]
    exact ih2 (ih1 (List.cons_subset_cons _ h))

/-- The accumulator is always a subset of the fold's result. -/
theorem NNF.acc_subset_fold_cons (χ : NNF α) (acc : List (NNF α)) :
    acc ⊆ χ.fold (fun a f => f :: a) acc := by
  induction χ generalizing acc with
  | tt | ff | prop _ | nprop _ =>
    simp only [fold]
    exact List.subset_cons_self _ _
  | next ψ ih =>
    simp only [fold]
    exact (List.subset_cons_self _ _).trans (ih _)
  | and ψ1 ψ2 ih1 ih2 | or ψ1 ψ2 ih1 ih2 | «until» ψ1 ψ2 ih1 ih2 | «release» ψ1 ψ2 ih1 ih2 =>
    simp only [fold]
    exact ((List.subset_cons_self _ _).trans (ih1 _)).trans (ih2 _)

/-- `χ` is always a member of its own fold. -/
theorem NNF.self_mem_fold_cons (χ : NNF α) (acc : List (NNF α)) :
    χ ∈ χ.fold (fun a f => f :: a) acc := by
  cases χ with
  | tt | ff | prop _ | nprop _ => simp only [fold]; exact List.mem_cons_self ..
  | next ψ =>
    simp only [fold]
    exact NNF.acc_subset_fold_cons ψ _ (List.mem_cons_self ..)
  | and ψ1 ψ2 | or ψ1 ψ2 | «until» ψ1 ψ2 | «release» ψ1 ψ2 =>
    simp only [fold]
    exact NNF.acc_subset_fold_cons ψ2 _ (NNF.acc_subset_fold_cons ψ1 _ (List.mem_cons_self ..))

/-- `ψ ∈ subformulas χ` still holds when `χ`'s fold is seeded with a bigger accumulator instead of `[]` -/
theorem NNF.mem_subformulas_imp_mem_fold {χ ψ : NNF α} (h : ψ ∈ χ.subformulas)
    (acc : List (NNF α)) : ψ ∈ χ.fold (fun a f => f :: a) acc :=
  NNF.fold_cons_mono χ (List.nil_subset acc) h

/-- Bridges `NNF.IsSubformula` to `NNF.subformulas`. -/
theorem NNF.IsSubformula.mem_subformulas {φ ψ : NNF α} (h : NNF.IsSubformula ψ φ) :
    ψ ∈ φ.subformulas := by
  induction h with
  | refl => exact NNF.self_mem_fold_cons _ []
  | and_left _ ih =>
    show _ ∈ (NNF.and _ _).fold (fun a f => f :: a) []
    simp only [fold]
    exact NNF.acc_subset_fold_cons _ _ (NNF.mem_subformulas_imp_mem_fold ih _)
  | and_right _ ih =>
    show _ ∈ (NNF.and _ _).fold (fun a f => f :: a) []
    simp only [fold]
    exact NNF.mem_subformulas_imp_mem_fold ih _
  | or_left _ ih =>
    show _ ∈ (NNF.or _ _).fold (fun a f => f :: a) []
    simp only [fold]
    exact NNF.acc_subset_fold_cons _ _ (NNF.mem_subformulas_imp_mem_fold ih _)
  | or_right _ ih =>
    show _ ∈ (NNF.or _ _).fold (fun a f => f :: a) []
    simp only [fold]
    exact NNF.mem_subformulas_imp_mem_fold ih _
  | until_left _ ih =>
    show _ ∈ (NNF.until _ _).fold (fun a f => f :: a) []
    simp only [fold]
    exact NNF.acc_subset_fold_cons _ _ (NNF.mem_subformulas_imp_mem_fold ih _)
  | until_right _ ih =>
    show _ ∈ (NNF.until _ _).fold (fun a f => f :: a) []
    simp only [fold]
    exact NNF.mem_subformulas_imp_mem_fold ih _
  | release_left _ ih =>
    show _ ∈ (NNF.release _ _).fold (fun a f => f :: a) []
    simp only [fold]
    exact NNF.acc_subset_fold_cons _ _ (NNF.mem_subformulas_imp_mem_fold ih _)
  | release_right _ ih =>
    show _ ∈ (NNF.release _ _).fold (fun a f => f :: a) []
    simp only [fold]
    exact NNF.mem_subformulas_imp_mem_fold ih _
  | next_sub _ ih =>
    show _ ∈ (NNF.next _).fold (fun a f => f :: a) []
    simp only [fold]
    exact NNF.mem_subformulas_imp_mem_fold ih _

end SubformulaFiniteness

/-! ## Weighted formula-size measure

Weighting each element by `2·size(x)+1` is what makes `new1_less_sum`/`new2_less_sum` hold, splitting a compound
formula into its immediate, syntactically smaller parts strictly decreases the weighted sum, even though the set
can grow (e.g. one formula becomes two). -/

section WeightedSize

variable {α : Type u}

noncomputable def weightedSize (l : List (NNF α)) : Nat := (l.map (fun x => 2 * sizeOf x + 1)).sum

@[simp] theorem weightedSize_nil : weightedSize ([] : List (NNF α)) = 0 := rfl

@[simp] theorem weightedSize_singleton (φ : NNF α) : weightedSize [φ] = 2 * sizeOf φ + 1 := rfl

@[simp] theorem weightedSize_cons (φ : NNF α) (l : List (NNF α)) :
    weightedSize (φ :: l) = (2 * sizeOf φ + 1) + weightedSize l := rfl

/-- `new1` strictly reduces weighted size. -/
theorem NNF.new1_less_sum (φ : NNF α) : weightedSize (new1 φ) < weightedSize ([φ] : List (NNF α)) := by
  cases φ <;> simp [new1, weightedSize] <;> omega

/-- `new2` strictly reduces weighted size. -/
theorem NNF.new2_less_sum (φ : NNF α) : weightedSize (new2 φ) < weightedSize ([φ] : List (NNF α)) := by
  cases φ <;> simp [new2, weightedSize] <;> omega

end WeightedSize

/-! ## Invariant: `old`/`new`/`next` stay within `subformulas topFormula`. -/

section ExpandInvariant

variable {α : Type u} {S : Type v} [FSet (NNF α) S]

/-- `n`'s `old`/`new`/`next` sets contain only subformulas of `topFormula`. -/
structure NodeBounded (topFormula : NNF α) (n : ExpansionNode α S) : Prop where
  new_sub : ∀ x ∈ n.new, NNF.IsSubformula x topFormula
  old_sub : ∀ x, FSet.contains n.old x → NNF.IsSubformula x topFormula
  next_sub : ∀ x, FSet.contains n.next x → NNF.IsSubformula x topFormula

/-- Every already-finished node in `st.nodes` is bounded too. -/
def NodesBounded (topFormula : NNF α) (st : ExpandState α S) : Prop :=
  ∀ (k : Nat) (n : ExpansionNode α S), st.nodes[k]? = some n →
    (∀ x, FSet.contains n.old x → NNF.IsSubformula x topFormula) ∧
    (∀ x, FSet.contains n.next x → NNF.IsSubformula x topFormula)

/-- Bundles `NodeBounded` for the in-progress node with `NodesBounded` for the already-finished ones. -/
structure ExpandInv (topFormula : NNF α) (n : ExpansionNode α S) (st : ExpandState α S) : Prop where
  node_bounded : NodeBounded topFormula n
  nodes_bounded : NodesBounded topFormula st

end ExpandInvariant

/-! ## The measure -/

section ExpandMeasure

variable {α : Type u} [DecidableEq α] {S : Type v} [FSet (NNF α) S]

/-- A node's "signature": its (old, next) content as `Finset`s, independent of the underlying `S` representation. -/
noncomputable def nodeSignature (n : ExpansionNode α S) : Finset (NNF α) × Finset (NNF α) :=
  ((FSet.toList n.old).toFinset, (FSet.toList n.next).toFinset)

/-- All possible signatures drawable from `subformulas topFormula`. -/
noncomputable def signatureUniverse (topFormula : NNF α) :
    Finset (Finset (NNF α) × Finset (NNF α)) :=
  topFormula.subformulas.toFinset.powerset ×ˢ topFormula.subformulas.toFinset.powerset

/-- A node bounded by `topFormula` has its signature drawn from `signatureUniverse topFormula`. -/
theorem nodeSignature_mem_signatureUniverse {topFormula : NNF α} {n : ExpansionNode α S}
    (ho : ∀ x, FSet.contains n.old x → NNF.IsSubformula x topFormula)
    (hn : ∀ x, FSet.contains n.next x → NNF.IsSubformula x topFormula) :
    nodeSignature n ∈ signatureUniverse topFormula := by
  simp only [signatureUniverse, nodeSignature, Finset.mem_product, Finset.mem_powerset,
    Finset.subset_iff, List.mem_toFinset]
  exact ⟨fun x hx => (ho x ((FSet.mem_toList_iff x n.old).mp hx)).mem_subformulas,
    fun x hx => (hn x ((FSet.mem_toList_iff x n.next).mp hx)).mem_subformulas⟩

/-- Signatures used by the accumulated, already-finished nodes. -/
noncomputable def usedSignatures (st : ExpandState α S) :
    Finset (Finset (NNF α) × Finset (NNF α)) :=
  (st.nodes.toList.map (fun p => nodeSignature p.2)).toFinset

/-- `NodesBounded` lifts `nodeSignature_mem_signatureUniverse` to all signatures used by `st`. -/
theorem usedSignatures_subset_signatureUniverse {topFormula : NNF α} {st : ExpandState α S}
    (h : NodesBounded topFormula st) :
    usedSignatures st ⊆ signatureUniverse topFormula := by
  intro sig hsig
  simp only [usedSignatures, List.mem_toFinset, List.mem_map] at hsig
  obtain ⟨⟨k, n⟩, hkn, rfl⟩ := hsig
  have hmem : st.nodes[k]? = some n := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hkn
  obtain ⟨ho, hn⟩ := h k n hmem
  exact nodeSignature_mem_signatureUniverse ho hn

/-- Primary measure: unused signatures remaining in the finite universe. -/
noncomputable def expandMeasure1 (topFormula : NNF α) (st : ExpandState α S) : Nat :=
  (signatureUniverse topFormula).card - (usedSignatures st).card

/-- Secondary (tie-break) measure: weighted size of `node.new`. -/
noncomputable def expandMeasure2 (n : ExpansionNode α S) : Nat := weightedSize n.new

omit [DecidableEq α] in
/-- `addToNew` only filters/reorders `formulas` before prepending onto `node.new`, so the weighted sum can only shrink
relative to appending everything. -/
theorem weightedSize_foldl_addToNew_le (existing : S) (formulas acc : List (NNF α)) :
    weightedSize (formulas.foldl (fun a f => if FSet.contains existing f then a else f :: a) acc)
      ≤ weightedSize acc + weightedSize formulas := by
  induction formulas generalizing acc with
  | nil => simp
  | cons f fs ih =>
    simp only [List.foldl_cons]
    split
    · exact (ih acc).trans (by simp)
    · calc weightedSize (fs.foldl _ (f :: acc)) ≤ weightedSize (f :: acc) + weightedSize fs := ih _
        _ = weightedSize acc + weightedSize (f :: fs) := by simp; omega

omit [DecidableEq α] in
theorem weightedSize_addToNew_le (node : ExpansionNode α S) (formulas : List (NNF α)) :
    weightedSize (addToNew node formulas) ≤ weightedSize node.new + weightedSize formulas :=
  weightedSize_foldl_addToNew_le node.old formulas node.new

/-- Primary-measure decrease. -/
theorem expandMeasure1_lt {topFormula : NNF α} {st st' : ExpandState α S}
    (hsub : usedSignatures st ⊂ usedSignatures st')
    (hbound' : usedSignatures st' ⊆ signatureUniverse topFormula) :
    expandMeasure1 topFormula st' < expandMeasure1 topFormula st := by
  unfold expandMeasure1
  have h1 : (usedSignatures st).card < (usedSignatures st').card := Finset.card_lt_card hsub
  have h2 : (usedSignatures st').card ≤ (signatureUniverse topFormula).card :=
    Finset.card_le_card hbound'
  omega

/-- Primary-measure non-increase. -/
theorem expandMeasure1_le {topFormula : NNF α} {st st' : ExpandState α S}
    (hsub : usedSignatures st ⊆ usedSignatures st') :
    expandMeasure1 topFormula st' ≤ expandMeasure1 topFormula st := by
  unfold expandMeasure1
  have h1 : (usedSignatures st).card ≤ (usedSignatures st').card := Finset.card_le_card hsub
  omega

end ExpandMeasure

/-! ## Main termination theorem.

Helper lemmas for `insert`/`mergeIncoming` bookkeeping, duplicate detection, and signature freshness, followed by
`expand_term` itself. -/

section ExpandTermHelpers

variable {α : Type u} [DecidableEq α] {S : Type v} [FSet (NNF α) S]

theorem nodeSignature_incoming_irrelevant (n : ExpansionNode α S) (inc : Std.HashSet Nat) :
    nodeSignature ({ n with incoming := inc } : ExpansionNode α S) = nodeSignature n := rfl

/-- Inserting a node at a fresh key (not previously present) only grows `usedSignatures`. -/
theorem usedSignatures_insert_fresh_subset (st : ExpandState α S) (k : Nat) (n : ExpansionNode α S)
    (hfresh : st.nodes[k]? = none) :
    usedSignatures st ⊆ usedSignatures { st with nodes := st.nodes.insert k n } := by
  intro sig hsig
  simp only [usedSignatures, List.mem_toFinset, List.mem_map] at hsig ⊢
  obtain ⟨⟨k', n'⟩, hkn, rfl⟩ := hsig
  refine ⟨(k', n'), ?_, rfl⟩
  have h := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hkn
  refine Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr ?_
  rw [Std.HashMap.getElem?_insert]
  by_cases hk : k == k'
  · exfalso
    rw [← (beq_iff_eq (α := Nat)).mp hk] at h
    rw [hfresh] at h
    exact absurd h (by simp)
  · rw [if_neg hk]; exact h

omit [DecidableEq α] in
/-- Every node bounded before an insert stays bounded, plus the freshly inserted node itself if it too is bounded. -/
theorem NodesBounded_insert {topFormula : NNF α} {st : ExpandState α S}
    (h : NodesBounded topFormula st) {k : Nat} {n : ExpansionNode α S}
    (hold : ∀ x, FSet.contains n.old x → NNF.IsSubformula x topFormula)
    (hnext : ∀ x, FSet.contains n.next x → NNF.IsSubformula x topFormula) :
    NodesBounded topFormula { st with nodes := st.nodes.insert k n } := by
  intro k' n' hk'
  rw [Std.HashMap.getElem?_insert] at hk'
  by_cases hk : k == k'
  · rw [if_pos hk] at hk'
    obtain rfl := Option.some.inj hk'
    exact ⟨hold, hnext⟩
  · rw [if_neg hk] at hk'
    exact h k' n' hk'

omit [DecidableEq α] in
/-- `mergeIncoming` only ever updates the `incoming` field of the target node (never `old`/`next`), so `NodesBounded`
is trivially preserved. -/
theorem NodesBounded_mergeIncoming {topFormula : NNF α} {st : ExpandState α S}
    (h : NodesBounded topFormula st) (node : ExpansionNode α S) (targetName : Nat) :
    NodesBounded topFormula (mergeIncoming st node targetName) := by
  unfold mergeIncoming
  split
  · rename_i target htarget
    intro k n hk
    simp only [Std.HashMap.getElem?_insert] at hk
    by_cases hkeq : targetName == k
    · rw [if_pos hkeq] at hk
      obtain rfl := Option.some.inj hk
      exact h targetName target htarget
    · rw [if_neg hkeq] at hk
      exact h k n hk
  · exact h

/-- Inserting a signature-preserving replacement at an existing key leaves `usedSignatures` unchanged. -/
theorem usedSignatures_insert_matching_subset (st : ExpandState α S) (k : Nat) (n target : ExpansionNode α S)
    (htarget : st.nodes[k]? = some target) (hsig : nodeSignature n = nodeSignature target) :
    usedSignatures st ⊆ usedSignatures { st with nodes := st.nodes.insert k n } := by
  intro sig hsig'
  simp only [usedSignatures, List.mem_toFinset, List.mem_map] at hsig' ⊢
  obtain ⟨⟨k', n'⟩, hkn, rfl⟩ := hsig'
  have h := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hkn
  by_cases hk : k == k'
  · have hkk' : k = k' := (beq_iff_eq (α := Nat)).mp hk
    subst hkk'
    rw [htarget] at h
    obtain rfl := Option.some.inj h
    refine ⟨(k, n), ?_, hsig⟩
    refine Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr ?_
    rw [Std.HashMap.getElem?_insert, if_pos (BEq.refl k)]
  · refine ⟨(k', n'), ?_, rfl⟩
    refine Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr ?_
    rw [Std.HashMap.getElem?_insert, if_neg hk]
    exact h

end ExpandTermHelpers

section FindDuplicateNone

variable {α : Type u} {S : Type v} [FSet (NNF α) S]

theorem findStep_some_persists (node : ExpansionNode α S) (m : Nat) (l : List (Nat × ExpansionNode α S)) :
    List.foldl (fun a b => findStep node a b) (some m) l = some m := by
  induction l with
  | nil => rfl
  | cons p ps ih => simp only [List.foldl_cons, findStep]; exact ih

/-- The negative counterpart to `findDuplicate_spec`: if no duplicate is found, no already-finished node shares
`node`'s signature. -/
theorem findDuplicate_spec_none (st : ExpandState α S) (node : ExpansionNode α S)
    (h : findDuplicate st node = none) :
    ∀ (k : Nat) (n : ExpansionNode α S), st.nodes[k]? = some n → n.sameSignature node = false := by
  unfold findDuplicate at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  change List.foldl (fun a b => findStep node a b) none st.nodes.toList = none at h
  intro k n hk
  have hmem : (k, n) ∈ st.nodes.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hk
  clear hk
  suffices hgen : ∀ (l : List (Nat × ExpansionNode α S)),
      List.foldl (fun a b => findStep node a b) none l = none →
      (k, n) ∈ l → n.sameSignature node = false by
    exact hgen st.nodes.toList h hmem
  intro l
  induction l with
  | nil => intro _ hmem'; simp at hmem'
  | cons p ps ih =>
    intro hfold hmem'
    rw [List.foldl_cons] at hfold
    have hstep : findStep node none p = none := by
      cases hs : findStep node none p with
      | none => rfl
      | some m => rw [hs, findStep_some_persists node m ps] at hfold; simp at hfold
    have hcond : p.2.sameSignature node = false := by
      unfold findStep at hstep
      by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      rw [hcon] at hstep
      simp at hstep
    rw [hstep] at hfold
    rcases List.mem_cons.mp hmem' with hmem' | hmem'
    · rw [← hmem'] at hcond; exact hcond
    · exact ih hfold hmem'

end FindDuplicateNone

section SignatureFreshness

variable {α : Type u} [DecidableEq α] {S : Type v} [FSet (NNF α) S]

/-- Equal signatures imply `sameSignature`. -/
theorem sameSignature_of_nodeSignature_eq {n1 n2 : ExpansionNode α S}
    (h : nodeSignature n1 = nodeSignature n2) : n1.sameSignature n2 = true := by
  unfold ExpansionNode.sameSignature
  simp only [nodeSignature, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [Bool.and_eq_true, FSet.setEq_correct, FSet.setEq_correct]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> intro x hx
  · have hm : x ∈ (FSet.toList n1.old).toFinset :=
      List.mem_toFinset.mpr ((FSet.mem_toList_iff x n1.old).mpr hx)
    rwa [h1, List.mem_toFinset, FSet.mem_toList_iff] at hm
  · have hm : x ∈ (FSet.toList n2.old).toFinset :=
      List.mem_toFinset.mpr ((FSet.mem_toList_iff x n2.old).mpr hx)
    rwa [← h1, List.mem_toFinset, FSet.mem_toList_iff] at hm
  · have hm : x ∈ (FSet.toList n1.next).toFinset :=
      List.mem_toFinset.mpr ((FSet.mem_toList_iff x n1.next).mpr hx)
    rwa [h2, List.mem_toFinset, FSet.mem_toList_iff] at hm
  · have hm : x ∈ (FSet.toList n2.next).toFinset :=
      List.mem_toFinset.mpr ((FSet.mem_toList_iff x n2.next).mpr hx)
    rwa [← h2, List.mem_toFinset, FSet.mem_toList_iff] at hm

/-- If `findDuplicate` finds nothing, `node`'s signature isn't among the already-used ones. -/
theorem nodeSignature_fresh_of_findDuplicate_none {st : ExpandState α S} {node : ExpansionNode α S}
    (h : findDuplicate st node = none) :
    nodeSignature node ∉ usedSignatures st := by
  intro hmem
  simp only [usedSignatures, List.mem_toFinset, List.mem_map] at hmem
  obtain ⟨⟨k, n⟩, hkn, heq⟩ := hmem
  have hget := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hkn
  have hfalse := findDuplicate_spec_none st node h k n hget
  have htrue := sameSignature_of_nodeSignature_eq heq
  rw [htrue] at hfalse
  exact absurd hfalse (by simp)

end SignatureFreshness

section ExpandTerm

variable {α : Type u} [DecidableEq α] [BEq (NNF α)] [LawfulBEq (NNF α)]
  {S : Type v} [FSet (NNF α) S]

theorem cons_head!_tail! {β : Type w} [Inhabited β] {l : List β} (h : l.isEmpty = false) :
    l.head! :: l.tail! = l := by
  cases l with
  | nil => simp at h
  | cons a t => rfl

set_option maxHeartbeats 4000000 in
/-- `expand` always terminates given `ExpandInv` and freshness of `node.name`, returning `some r` with `usedSignatures`
growing monotonically and `NodesBounded` preserved. Terminates on the lexicographic measure `(expandMeasure1,
expandMeasure2)`: finishing a node strictly decreases `expandMeasure1`, every other step strictly decreases
`expandMeasure2`. Formalizes the finite-state-space termination argument of Gerth et al. 1995. -/
theorem expand_term (topFormula : NNF α) (node : ExpansionNode α S) (st : ExpandState α S)
    (hinv : ExpandInv topFormula node st)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName) :
    ∃ r : Nat × ExpandState α S, expand node st = some r ∧
      usedSignatures st ⊆ usedSignatures r.2 ∧ NodesBounded topFormula r.2 := by
  by_cases h_empty : node.new.isEmpty
  · match h_fd : findDuplicate st node with
    | some existingName =>
      -- MERGE: terminal, only `incoming` of the target changes.
      obtain ⟨target, htarget, _⟩ := findDuplicate_spec st node existingName h_fd
      set merged : ExpansionNode α S := { target with incoming := target.incoming.union node.incoming }
        with hmerged_def
      have hmerge_eq : mergeIncoming st node existingName
          = { st with nodes := st.nodes.insert existingName merged } := by
        unfold mergeIncoming
        rw [htarget]
      have heq : expand node st = some (node.name, mergeIncoming st node existingName) := by
        rw [expand.eq_def, if_pos h_empty, h_fd]
        rfl
      have hsub : usedSignatures st ⊆ usedSignatures (mergeIncoming st node existingName) := by
        rw [hmerge_eq]
        exact usedSignatures_insert_matching_subset st existingName _ target htarget
          (nodeSignature_incoming_irrelevant target _)
      have hnb : NodesBounded topFormula (mergeIncoming st node existingName) :=
        NodesBounded_mergeIncoming hinv.nodes_bounded node existingName
      exact ⟨(node.name, mergeIncoming st node existingName), heq, hsub, hnb⟩
    | none =>
      -- FRESH SUCCESSOR: finish `node`, spawn a successor from `node.next`, recurse.
      have hbound_node : nodeSignature node ∈ signatureUniverse topFormula :=
        nodeSignature_mem_signatureUniverse hinv.node_bounded.old_sub hinv.node_bounded.next_sub
      have hfresh_sig : nodeSignature node ∉ usedSignatures st :=
        nodeSignature_fresh_of_findDuplicate_none h_fd
      have h_grow_sub : usedSignatures st ⊆ usedSignatures
          ({ st with nodes := st.nodes.insert node.name node } : ExpandState α S) :=
        usedSignatures_insert_fresh_subset st node.name node h_not_in
      have h_sig_mem : nodeSignature node ∈ usedSignatures
          ({ st with nodes := st.nodes.insert node.name node } : ExpandState α S) := by
        simp only [usedSignatures, List.mem_toFinset, List.mem_map]
        refine ⟨(node.name, node), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr ?_, rfl⟩
        simp only [Std.HashMap.getElem?_insert, BEq.refl, if_pos]
      have h_grow : usedSignatures st ⊂ usedSignatures
          ({ st with nodes := st.nodes.insert node.name node } : ExpandState α S) :=
        h_grow_sub.ssubset_of_ne (fun heq => hfresh_sig (heq ▸ h_sig_mem))
      have hnb1 : NodesBounded topFormula
          ({ st with nodes := st.nodes.insert node.name node } : ExpandState α S) :=
        NodesBounded_insert hinv.nodes_bounded hinv.node_bounded.old_sub hinv.node_bounded.next_sub
      have hub1 : usedSignatures ({ st with nodes := st.nodes.insert node.name node } : ExpandState α S)
          ⊆ signatureUniverse topFormula :=
        usedSignatures_subset_signatureUniverse hnb1
      have hm1_lt : expandMeasure1 topFormula
          ({ st with nodes := st.nodes.insert node.name node } : ExpandState α S)
          < expandMeasure1 topFormula st :=
        expandMeasure1_lt h_grow hub1
      have h_not_in1 : (st.nodes.insert node.name node)[st.nextName]? = none :=
        insert_fresh_key st node.name node h_fresh h_name
      have h_fresh1 : ∀ k, (st.nodes.insert node.name node)[k]? ≠ none → k < st.nextName + 1 :=
        insert_freshInv st node.name node h_fresh h_name
      have h_name1 : st.nextName < st.nextName + 1 := Nat.lt_succ_self _
      have h_succ_bounded : ∀ x, x ∈ FSet.foldl (fun acc f => f :: acc) [] node.next →
          NNF.IsSubformula x topFormula :=
        fun x hx => hinv.node_bounded.next_sub x (fset_fold_cons_mem node.next x hx)
      have hinv_succ : ExpandInv topFormula
          ({ name := st.nextName
             incoming := Std.HashSet.emptyWithCapacity 4 |>.insert node.name
             new := FSet.foldl (fun acc f => f :: acc) [] node.next
             old := FSet.empty
             next := FSet.empty } : ExpansionNode α S)
          ({ st with nodes := st.nodes.insert node.name node, nextName := st.nextName + 1 }) := by
        refine ⟨⟨h_succ_bounded, ?_, ?_⟩, ?_⟩
        · intro x hx; exact absurd hx (by simp [FSet.contains_empty])
        · intro x hx; exact absurd hx (by simp [FSet.contains_empty])
        · exact hnb1
      obtain ⟨r, hr1, hr2, hr3⟩ := expand_term topFormula _ _ hinv_succ h_not_in1 h_fresh1 h_name1
      have heq : expand node st = some r := by
        rw [expand.eq_def, if_pos h_empty, h_fd]
        simp only [freshName]
        exact hr1
      exact ⟨r, heq, h_grow_sub.trans hr2, hr3⟩
  · have h_ne : node.new.isEmpty = false := by
      revert h_empty; cases node.new.isEmpty <;> decide
    have hcons : node.new.head! :: node.new.tail! = node.new := cons_head!_tail! h_ne
    have hφ_mem : node.new.head! ∈ node.new := head!_mem_of_isEmpty_false h_ne
    have hφ_sub : NNF.IsSubformula node.new.head! topFormula := hinv.node_bounded.new_sub _ hφ_mem
    have h_tail_sub : ∀ x, x ∈ node.new.tail! → NNF.IsSubformula x topFormula :=
      fun x hx => hinv.node_bounded.new_sub x (mem_of_mem_tail! hx)
    have hweight : weightedSize node.new
        = (2 * sizeOf node.new.head! + 1) + weightedSize node.new.tail! := by
      conv_lhs => rw [← hcons]
      rw [weightedSize_cons]
    have h_old_ins : ∀ x, FSet.contains (FSet.insert node.old node.new.head!) x →
        NNF.IsSubformula x topFormula := by
      intro x hx
      rcases oldHas_insert hx with h1 | rfl
      · exact hinv.node_bounded.old_sub x h1
      · exact hφ_sub
    by_cases hlit : isLiteral node.new.head!
    · by_cases hcontra : FSet.contains node.old (negateLiteral node.new.head!)
      · -- literal contradiction: terminal
        have heq : expand node st = some (node.name, st) := by
          rw [expand.eq_def, if_neg h_empty]
          simp only
          rw [if_pos hlit, if_pos hcontra]
          rfl
        exact ⟨(node.name, st), heq, Finset.Subset.refl _, hinv.nodes_bounded⟩
      · -- literal insert: single recursive call, unchanged `st`
        have hinv' : ExpandInv topFormula
            ({ node with new := node.new.tail!, old := FSet.insert node.old node.new.head! } : ExpansionNode α S) st :=
          ⟨⟨h_tail_sub, h_old_ins, hinv.node_bounded.next_sub⟩, hinv.nodes_bounded⟩
        have hw2 : expandMeasure2
            ({ node with new := node.new.tail!, old := FSet.insert node.old node.new.head! } : ExpansionNode α S)
            < expandMeasure2 node := by
          show weightedSize node.new.tail! < weightedSize node.new
          rw [hweight]; omega
        obtain ⟨r, hr1, hr2, hr3⟩ := expand_term topFormula _ st hinv' h_not_in h_fresh h_name
        have heq : expand node st = some r := by
          rw [expand.eq_def, if_neg h_empty]
          simp only
          rw [if_pos hlit, if_neg hcontra]
          exact hr1
        exact ⟨r, heq, hr2, hr3⟩
    · by_cases htt_eq : node.new.head! = NNF.tt
      · -- tt: single recursive call, unchanged `st`
        have hinv' : ExpandInv topFormula
            ({ node with new := node.new.tail!, old := FSet.insert node.old node.new.head! } : ExpansionNode α S) st :=
          ⟨⟨h_tail_sub, h_old_ins, hinv.node_bounded.next_sub⟩, hinv.nodes_bounded⟩
        have hw2 : expandMeasure2
            ({ node with new := node.new.tail!, old := FSet.insert node.old node.new.head! } : ExpansionNode α S)
            < expandMeasure2 node := by
          show weightedSize node.new.tail! < weightedSize node.new
          rw [hweight]; omega
        obtain ⟨r, hr1, hr2, hr3⟩ := expand_term topFormula _ st hinv' h_not_in h_fresh h_name
        have heq : expand node st = some r := by
          rw [expand.eq_def, if_neg h_empty]
          simp only
          rw [if_neg hlit]
          simp only [htt_eq, if_true]
          simp only [htt_eq] at hr1
          exact hr1
        exact ⟨r, heq, hr2, hr3⟩
      · by_cases hff_eq : node.new.head! = NNF.ff
        · -- ff: terminal
          have heq : expand node st = some (node.name, st) := by
            rw [expand.eq_def, if_neg h_empty]
            simp only
            rw [if_neg hlit]
            simp only [hff_eq, Bool.false_eq_true, if_false, if_true]
            rfl
          exact ⟨(node.name, st), heq, Finset.Subset.refl _, hinv.nodes_bounded⟩
        · by_cases hdet : isDeterministic node.new.head!
          · -- deterministic split (and/next): single recursive call, unchanged `st`
            have h_new1_sub : ∀ x, x ∈ new1 node.new.head! → NNF.IsSubformula x topFormula :=
              fun x hx => (new1_subformula hx).trans hφ_sub
            have h_next1_sub : ∀ x, x ∈ next1 node.new.head! → NNF.IsSubformula x topFormula :=
              fun x hx => (next1_subformula hx).trans hφ_sub
            have h_new_sub' : ∀ x, x ∈ addToNew { node with new := node.new.tail! } (new1 node.new.head!) →
                NNF.IsSubformula x topFormula := by
              intro x hx
              rcases addToNew_inv _ _ x hx with h1 | h2
              · exact h_tail_sub _ h1
              · exact h_new1_sub _ h2
            have h_next_sub' : ∀ x, FSet.contains (addAllToSet node.next (next1 node.new.head!)) x →
                NNF.IsSubformula x topFormula := by
              intro x hx
              rcases addAllToSet_inv _ _ x hx with h1 | h2
              · exact hinv.node_bounded.next_sub _ h1
              · exact h_next1_sub _ h2
            have hinv' : ExpandInv topFormula
                ({ node with new := addToNew { node with new := node.new.tail! } (new1 node.new.head!), old := FSet.insert node.old node.new.head!, next := addAllToSet node.next (next1 node.new.head!) } : ExpansionNode α S) st :=
              ⟨⟨h_new_sub', h_old_ins, h_next_sub'⟩, hinv.nodes_bounded⟩
            have hw2 : expandMeasure2
                ({ node with new := addToNew { node with new := node.new.tail! } (new1 node.new.head!), old := FSet.insert node.old node.new.head!, next := addAllToSet node.next (next1 node.new.head!) } : ExpansionNode α S)
                < expandMeasure2 node := by
              show weightedSize (addToNew { node with new := node.new.tail! } (new1 node.new.head!))
                < weightedSize node.new
              have h1 : weightedSize (addToNew { node with new := node.new.tail! } (new1 node.new.head!))
                  ≤ weightedSize node.new.tail! + weightedSize (new1 node.new.head!) :=
                weightedSize_addToNew_le { node with new := node.new.tail! } (new1 node.new.head!)
              have h2 := NNF.new1_less_sum node.new.head!
              simp only [weightedSize_singleton] at h2
              rw [hweight]
              omega
            obtain ⟨r, hr1, hr2, hr3⟩ := expand_term topFormula _ st hinv' h_not_in h_fresh h_name
            have heq : expand node st = some r := by
              rw [expand.eq_def, if_neg h_empty]
              simp only
              rw [if_neg hlit]
              simp only [Bool.false_eq_true, if_false]
              rw [if_pos hdet]
              exact hr1
            exact ⟨r, heq, hr2, hr3⟩
          · -- nondeterministic split (or/until/release): two recursive calls
            have h_new1_sub : ∀ x, x ∈ new1 node.new.head! → NNF.IsSubformula x topFormula :=
              fun x hx => (new1_subformula hx).trans hφ_sub
            have h_new2_sub : ∀ x, x ∈ new2 node.new.head! → NNF.IsSubformula x topFormula :=
              fun x hx => (new2_subformula hx).trans hφ_sub
            have h_next1_sub : ∀ x, x ∈ next1 node.new.head! → NNF.IsSubformula x topFormula :=
              fun x hx => (next1_subformula hx).trans hφ_sub
            -- First recursive call: deterministic-shaped, via `new1`/`next1`.
            have h_new_sub1 : ∀ x, x ∈ addToNew { node with new := node.new.tail! } (new1 node.new.head!) →
                NNF.IsSubformula x topFormula := by
              intro x hx
              rcases addToNew_inv _ _ x hx with h1 | h2
              · exact h_tail_sub _ h1
              · exact h_new1_sub _ h2
            have h_next_sub1 : ∀ x, FSet.contains (addAllToSet node.next (next1 node.new.head!)) x →
                NNF.IsSubformula x topFormula := by
              intro x hx
              rcases addAllToSet_inv _ _ x hx with h1 | h2
              · exact hinv.node_bounded.next_sub _ h1
              · exact h_next1_sub _ h2
            have hinv1 : ExpandInv topFormula
                ({ node with new := addToNew { node with new := node.new.tail! } (new1 node.new.head!), old := FSet.insert node.old node.new.head!, next := addAllToSet node.next (next1 node.new.head!) } : ExpansionNode α S) st :=
              ⟨⟨h_new_sub1, h_old_ins, h_next_sub1⟩, hinv.nodes_bounded⟩
            have hw1 : expandMeasure2
                ({ node with new := addToNew { node with new := node.new.tail! } (new1 node.new.head!), old := FSet.insert node.old node.new.head!, next := addAllToSet node.next (next1 node.new.head!) } : ExpansionNode α S)
                < expandMeasure2 node := by
              show weightedSize (addToNew { node with new := node.new.tail! } (new1 node.new.head!))
                < weightedSize node.new
              have h1 : weightedSize (addToNew { node with new := node.new.tail! } (new1 node.new.head!))
                  ≤ weightedSize node.new.tail! + weightedSize (new1 node.new.head!) :=
                weightedSize_addToNew_le { node with new := node.new.tail! } (new1 node.new.head!)
              have h2 := NNF.new1_less_sum node.new.head!
              simp only [weightedSize_singleton] at h2
              rw [hweight]
              omega
            obtain ⟨r1, hr1_1, hr1_2, hr1_3⟩ :=
              expand_term topFormula _ st hinv1 h_not_in h_fresh h_name
            -- Second recursive call: name := r1.1, via `new2`, at state `r1.2`.
            have hinv1' : ExpandInvariants st r1.2 r1.1 :=
              expand_invariants _ st hr1_1 h_not_in h_fresh h_name
            have h_new_sub2 : ∀ x, x ∈ addToNew { node with new := node.new.tail! } (new2 node.new.head!) →
                NNF.IsSubformula x topFormula := by
              intro x hx
              rcases addToNew_inv _ _ x hx with h1 | h2
              · exact h_tail_sub _ h1
              · exact h_new2_sub _ h2
            have hinv2 : ExpandInv topFormula
                ({ node with name := r1.1, new := addToNew { node with new := node.new.tail! } (new2 node.new.head!), old := FSet.insert node.old node.new.head! } : ExpansionNode α S) r1.2 :=
              ⟨⟨h_new_sub2, h_old_ins, hinv.node_bounded.next_sub⟩, hr1_3⟩
            have hm1_le : expandMeasure1 topFormula r1.2 ≤ expandMeasure1 topFormula st :=
              expandMeasure1_le hr1_2
            have hw2 : expandMeasure2
                ({ node with name := r1.1, new := addToNew { node with new := node.new.tail! } (new2 node.new.head!), old := FSet.insert node.old node.new.head! } : ExpansionNode α S)
                < expandMeasure2 node := by
              show weightedSize (addToNew { node with new := node.new.tail! } (new2 node.new.head!))
                < weightedSize node.new
              have h1 : weightedSize (addToNew { node with new := node.new.tail! } (new2 node.new.head!))
                  ≤ weightedSize node.new.tail! + weightedSize (new2 node.new.head!) :=
                weightedSize_addToNew_le { node with new := node.new.tail! } (new2 node.new.head!)
              have h2 := NNF.new2_less_sum node.new.head!
              simp only [weightedSize_singleton] at h2
              rw [hweight]
              omega
            obtain ⟨r2, hr2_1, hr2_2, hr2_3⟩ :=
              expand_term topFormula _ r1.2 hinv2 hinv1'.nameFresh hinv1'.freshInv hinv1'.nameBound
            have heq : expand node st = some r2 := by
              rw [expand.eq_def, if_neg h_empty]
              simp only
              rw [if_neg hlit]
              simp only [Bool.false_eq_true, if_false]
              rw [if_neg hdet]
              simp only [Bind.bind, Option.bind]
              rw [hr1_1]
              exact hr2_1
            exact ⟨r2, heq, hr1_2.trans hr2_2, hr2_3⟩
termination_by (expandMeasure1 topFormula st, expandMeasure2 node)
decreasing_by
  · exact Prod.Lex.left _ _ hm1_lt
  · exact Prod.Lex.right _ hw2
  · exact Prod.Lex.right _ hw2
  · exact Prod.Lex.right _ hw2
  · exact Prod.Lex.right _ hw1
  · rcases eq_or_lt_of_le hm1_le with heq | hlt
    · rw [heq]; exact Prod.Lex.right _ hw2
    · exact Prod.Lex.left _ _ hlt

/-- `createGraph`'s totality. -/
theorem createGraph_term (φ : NNF α) :
    ∃ st : ExpandState α S, createGraph φ = some st ∧ NodesBounded φ st := by
  have hinv : ExpandInv φ
      ({ name := 1, incoming := Std.HashSet.emptyWithCapacity 4 |>.insert expandInit,
         new := [φ], old := FSet.empty, next := FSet.empty } : ExpansionNode α S)
      ({ nextName := 2, nodes := Std.HashMap.emptyWithCapacity 16 } : ExpandState α S) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro x hx; simp only [List.mem_singleton] at hx; exact hx ▸ NNF.IsSubformula.refl
    · intro x hx; exact absurd hx (by simp [FSet.contains_empty])
    · intro x hx; exact absurd hx (by simp [FSet.contains_empty])
    · intro k n hk; simp at hk
  have h_not_in : (Std.HashMap.emptyWithCapacity 16 : Std.HashMap Nat (ExpansionNode α S))[(1 : Nat)]? = none := by
    simp
  have h_fresh : ∀ k, (Std.HashMap.emptyWithCapacity 16 : Std.HashMap Nat (ExpansionNode α S))[k]? ≠ none → k < 2 := by
    intro k hk; simp at hk
  have h_name : (1 : Nat) < 2 := by omega
  obtain ⟨r, hr1, _, hr3⟩ := expand_term φ
      ({ name := 1, incoming := Std.HashSet.emptyWithCapacity 4 |>.insert expandInit,
         new := [φ], old := FSet.empty, next := FSet.empty } : ExpansionNode α S)
      ({ nextName := 2, nodes := Std.HashMap.emptyWithCapacity 16 } : ExpandState α S)
      hinv h_not_in h_fresh h_name
  refine ⟨r.2, ?_, hr3⟩
  unfold createGraph
  simp only
  rw [hr1]

end ExpandTerm

end LTLLib
