/-
  Termination of `expand` (Phase 2, `expand` half).

  Ports CAVA's termination proof for `expand` (`LTL_to_GBA.thy`, "Termination
  proof" section, lines 836-1229): `expand_ord`, `expand_inv`,
  `expand_inv_impl`, `expand_term_prop`, `expand_eq_expand⇩T`,
  `create_graph_finite`.

  CAVA's `expand` is `REC expand_body` (an abstract, possibly-diverging
  least fixpoint over the `nres` CPO); termination is established for a
  *separate* `expand⇩T := RECT expand_body`, well-founded-recursion-checked
  via `RECT_rule` against the measure `expand_ord`, then transported back to
  `expand` via the generic library lemma `RECT_eq_REC`.

  Lean's `partial_fixpoint` (our `expand`'s actual definition, `Expand.lean`)
  is architecturally the same idea as CAVA's `REC` (both are least fixpoints
  over a CCPO — Lean's own `Lean.Order` framework, `Init/Internal/Order/`).
  But Lean has no `RECT`/`RECT_eq_REC` analogue: `partial_fixpoint`'s own
  generated induction principle (`expand.partial_correctness`, `fix_induct`
  under the hood) is Scott/fixpoint induction, which is *structurally*
  conditional (`Option.admissible_eq_some : admissible (x = some y → P)`) —
  it can only ever conclude "if `expand` succeeds, then P", never "`expand`
  succeeds". This is inherent to admissibility, not a gap to work around, and
  mirrors exactly why CAVA needs the separate `RECT`/`expand_term_prop` layer
  in the first place.

  What Lean *does* give unconditionally is `expand`'s own one-step unfolding
  equation (`unfold expand`, already used throughout `GraphComplete.lean`) —
  the direct analogue of Isabelle's `fix_eq`/`lfp_fix`. That is enough to
  prove totality *directly*, by well-founded induction on the same measure
  CAVA uses, entirely avoiding a separate fuel-indexed mirror function (the
  `NestedDFSTermination.lean` playbook) — a genuine simplification found by
  checking what Lean's `partial_fixpoint` machinery actually offers before
  assuming the nested-DFS approach would carry over.

  CAVA's primary measure component lives in `Pow(subfrmlsr φ) × Pow(subfrmlsr φ)`
  (Isabelle set theory). Mathlib is an actual dependency of this project
  (`lakefile.toml`, already used in `Acceptance.lean`/`Soundness.lean`), so
  this is ported directly via `Finset.powerset`/`Finset.card_powerset` — the
  literal Lean analogue, not a hand-rolled encoding.
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import LTLLib.LTLtoGBA.Invariants

namespace LTLLib

open NNF

/-! ## Subformula-list finiteness infrastructure

`NNF.subformulas` (`LTL/Subformulas.lean`) is a `List`, built via `NNF.fold`.
`NNF.IsSubformula` (`Invariants.lean`) is the *relation* already used by
`new1_subformula`/`new2_subformula`/`next1_subformula`. Bridges the two:
`IsSubformula ψ φ → ψ ∈ subformulas φ`, needed to place `new1 φ`/`new2 φ`/
`next1 φ`'s outputs (already known `IsSubformula`-related to `φ`, hence to
any node's `old`/`new`/`next` once `φ` itself is known to be in there) inside
the *finite* Finset universe `(subformulas topFormula).toFinset`. -/

section SubformulaFiniteness

variable {α : Type u}

/-- `fold`'s accumulator only ever grows (as membership), regardless of which
formula is being folded over — proved once, generically, rather than
special-cased per constructor of `NNF.IsSubformula` later. -/
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

/-- `ψ ∈ subformulas χ` still holds when `χ`'s fold is seeded with a bigger
accumulator instead of `[]` — the general-purpose step used by every case of
`IsSubformula.mem_subformulas` below. -/
theorem NNF.mem_subformulas_imp_mem_fold {χ ψ : NNF α} (h : ψ ∈ χ.subformulas)
    (acc : List (NNF α)) : ψ ∈ χ.fold (fun a f => f :: a) acc :=
  NNF.fold_cons_mono χ (List.nil_subset acc) h

/-- Bridges `NNF.IsSubformula` (the inductive relation already used by
`new1_subformula`/`new2_subformula`/`next1_subformula`) to `NNF.subformulas`
(the finite list) — needed to place their outputs inside a genuinely finite
`Finset` universe. -/
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

/-! ## Weighted formula-size measure (`size_set` analogue)

Mirrors `size_set S ≡ sum (λx. 2 * size x + 1) S` (`LTL.thy:519`) — **not**
`|S|` (a mistaken first read corrected by checking the actual definition):
weighting each element by `2·size(x)+1` is what makes `new1_less_sum`/
`new2_less_sum` (below) hold — splitting a compound formula into its
immediate, syntactically smaller parts strictly decreases the weighted sum,
even though the *set* can grow (e.g. one formula becomes two). Uses Lean's
own auto-derived `sizeOf : NNF α → Nat` as the direct analogue of Isabelle's
auto-generated `size`. -/

section WeightedSize

variable {α : Type u}

noncomputable def weightedSize (l : List (NNF α)) : Nat := (l.map (fun x => 2 * sizeOf x + 1)).sum

@[simp] theorem weightedSize_nil : weightedSize ([] : List (NNF α)) = 0 := rfl

@[simp] theorem weightedSize_singleton (φ : NNF α) : weightedSize [φ] = 2 * sizeOf φ + 1 := rfl

@[simp] theorem weightedSize_cons (φ : NNF α) (l : List (NNF α)) :
    weightedSize (φ :: l) = (2 * sizeOf φ + 1) + weightedSize l := rfl

theorem NNF.new1_less_sum (φ : NNF α) : weightedSize (new1 φ) < weightedSize ([φ] : List (NNF α)) := by
  cases φ <;> simp [new1, weightedSize] <;> omega

theorem NNF.new2_less_sum (φ : NNF α) : weightedSize (new2 φ) < weightedSize ([φ] : List (NNF α)) := by
  cases φ <;> simp [new2, weightedSize] <;> omega

end WeightedSize

/-! ## Invariant: `old`/`new`/`next` stay within `subformulas topFormula`

Mirrors `expand_inv`/`expand_inv_node`/`expand_inv_result` (`LTL_to_GBA.thy:857-866`).
Unlike Isabelle's abstract HOL sets, `node.new : List _` and `node.old/next : S`
(via the `FSet` abstraction, always `Std.HashSet`/`Std.TreeSet`) are automatically
finite — Lean drops CAVA's explicit `finite(new n) ∧ finite(old n) ∧ finite(next n)`
and `finite ns` conjuncts entirely, since they're vacuously true by construction. -/

section ExpandInvariant

variable {α : Type u} {S : Type v} [FSet (NNF α) S]

/-- Mirrors `expand_inv_node`: the current node's pending/processed/obligation
sets are all bounded within `subfrmlsr topFormula`. Phrased via `IsSubformula`
(matching the vocabulary already established by `expand_subformula_closure`
and friends in `Invariants.lean`, rather than `subformulas`-list membership)
so per-branch propagation facts can be reused directly from there. -/
structure NodeBounded (topFormula : NNF α) (n : GBANode α S) : Prop where
  new_sub : ∀ x ∈ n.new, NNF.IsSubformula x topFormula
  old_sub : ∀ x, FSet.contains n.old x → NNF.IsSubformula x topFormula
  next_sub : ∀ x, FSet.contains n.next x → NNF.IsSubformula x topFormula

/-- Mirrors `expand_inv_result`: every already-finished node in `st.nodes` is
bounded too. -/
def NodesBounded (topFormula : NNF α) (st : ExpandState α S) : Prop :=
  ∀ (k : Nat) (n : GBANode α S), st.nodes[k]? = some n →
    (∀ x, FSet.contains n.old x → NNF.IsSubformula x topFormula) ∧
    (∀ x, FSet.contains n.next x → NNF.IsSubformula x topFormula)

/-- Mirrors `expand_inv`. -/
structure ExpandInv (topFormula : NNF α) (n : GBANode α S) (st : ExpandState α S) : Prop where
  node_bounded : NodeBounded topFormula n
  nodes_bounded : NodesBounded topFormula st

end ExpandInvariant

/-! ## The measure (`expand_ord` analogue)

Primary component mirrors `old_next_pair `` ns`, ordered by `finite_psupset
(old_next_limit φ)` in CAVA — here phrased as a *shrinking* `Nat` (universe
cardinality minus used-signature cardinality), the same "shrinking
complement of a fixed finite universe" idiom as the nested-DFS measures
(`(fr.univ \ iv).size`), just via `Finset.card` instead of `HashSet.size`.
Secondary mirrors `size_set (new n)`. -/

section ExpandMeasure

variable {α : Type u} [DecidableEq α] {S : Type v} [FSet (NNF α) S]

/-- A node's "signature": its (old, next) content as `Finset`s, independent
of the underlying `S` representation. Mirrors `old_next_pair`. -/
noncomputable def nodeSignature (n : GBANode α S) : Finset (NNF α) × Finset (NNF α) :=
  ((FSet.toList n.old).toFinset, (FSet.toList n.next).toFinset)

/-- All possible signatures drawable from `subformulas topFormula`. Mirrors
`old_next_limit φ ≡ Pow(subfrmlsr φ) × Pow(subfrmlsr φ)`, using Mathlib's
`Finset.powerset` directly rather than a hand-rolled encoding. -/
noncomputable def signatureUniverse (topFormula : NNF α) :
    Finset (Finset (NNF α) × Finset (NNF α)) :=
  topFormula.subformulas.toFinset.powerset ×ˢ topFormula.subformulas.toFinset.powerset

theorem nodeSignature_mem_signatureUniverse {topFormula : NNF α} {n : GBANode α S}
    (ho : ∀ x, FSet.contains n.old x → NNF.IsSubformula x topFormula)
    (hn : ∀ x, FSet.contains n.next x → NNF.IsSubformula x topFormula) :
    nodeSignature n ∈ signatureUniverse topFormula := by
  simp only [signatureUniverse, nodeSignature, Finset.mem_product, Finset.mem_powerset,
    Finset.subset_iff, List.mem_toFinset]
  exact ⟨fun x hx => (ho x ((FSet.mem_toList_iff x n.old).mp hx)).mem_subformulas,
    fun x hx => (hn x ((FSet.mem_toList_iff x n.next).mp hx)).mem_subformulas⟩

/-- Signatures used by the accumulated, already-finished nodes. Mirrors
`old_next_pair `` ns`. -/
noncomputable def usedSignatures (st : ExpandState α S) :
    Finset (Finset (NNF α) × Finset (NNF α)) :=
  (st.nodes.toList.map (fun p => nodeSignature p.2)).toFinset

theorem usedSignatures_subset_signatureUniverse {topFormula : NNF α} {st : ExpandState α S}
    (h : NodesBounded topFormula st) :
    usedSignatures st ⊆ signatureUniverse topFormula := by
  intro sig hsig
  simp only [usedSignatures, List.mem_toFinset, List.mem_map] at hsig
  obtain ⟨⟨k, n⟩, hkn, rfl⟩ := hsig
  have hmem : st.nodes[k]? = some n := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hkn
  obtain ⟨ho, hn⟩ := h k n hmem
  exact nodeSignature_mem_signatureUniverse ho hn

/-- Primary measure component. -/
noncomputable def expandMeasure1 (topFormula : NNF α) (st : ExpandState α S) : Nat :=
  (signatureUniverse topFormula).card - (usedSignatures st).card

/-- Secondary (tie-break) measure component. Mirrors `size_set (new n)`. -/
noncomputable def expandMeasure2 (n : GBANode α S) : Nat := weightedSize n.new

omit [DecidableEq α] in
/-- `addToNew` (`Expand.lean`) only ever *filters or reorders* `formulas`
before prepending onto `node.new` — never duplicates weight — so this bound
holds regardless of the `old`-membership filtering specifics (an
optimization beyond `expand_body`'s own `new n' = new1 ψ ∪ (new n - {ψ})`,
safe here since filtering can only shrink `weightedSize` further). -/
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
theorem weightedSize_addToNew_le (node : GBANode α S) (formulas : List (NNF α)) :
    weightedSize (addToNew node formulas) ≤ weightedSize node.new + weightedSize formulas :=
  weightedSize_foldl_addToNew_le node.old formulas node.new

/-- Primary-measure decrease: mirrors the "used-signatures strictly grow"
half of `expand_ord`'s `finite_psupset` component (the case CAVA's own
`expand_term_prop` uses directly, without going through `expand_inv_impl`,
for the "fresh successor" transition — `old_next_pair `` ns ⊂ old_next_pair
`` (insert n ns)`). -/
theorem expandMeasure1_lt {topFormula : NNF α} {st st' : ExpandState α S}
    (hsub : usedSignatures st ⊂ usedSignatures st')
    (hbound' : usedSignatures st' ⊆ signatureUniverse topFormula) :
    expandMeasure1 topFormula st' < expandMeasure1 topFormula st := by
  unfold expandMeasure1
  have h1 : (usedSignatures st).card < (usedSignatures st').card := Finset.card_lt_card hsub
  have h2 : (usedSignatures st').card ≤ (signatureUniverse topFormula).card :=
    Finset.card_le_card hbound'
  omega

/-- Primary-measure non-increase: the weaker, non-strict form needed for the
nondeterministic-split case, where `expand_inv_impl`'s case 3
(`LTL_to_GBA.thy:946-964`) only assumes `old_next_pair `` ns ⊆ old_next_pair
`` ns'` (non-strict) and relies purely on the *secondary* (`size_set`)
measure for the actual strict decrease. -/
theorem expandMeasure1_le {topFormula : NNF α} {st st' : ExpandState α S}
    (hsub : usedSignatures st ⊆ usedSignatures st') :
    expandMeasure1 topFormula st' ≤ expandMeasure1 topFormula st := by
  unfold expandMeasure1
  have h1 : (usedSignatures st).card ≤ (usedSignatures st').card := Finset.card_le_card hsub
  omega

end ExpandMeasure

/-! ## Main termination theorem (`expand_term_prop` analogue)

Proved directly as a well-founded-recursive `theorem` (`termination_by`/
`decreasing_by`, the same lex-pair idiom already used for `innerDFSCore`/
`outerDFSLoopWF`), unfolding `expand`'s own equation at each step — no
fuel-indexed mirror needed (see the file docstring for why). Mirrors
`expand_term_prop`'s conclusion exactly: totality, plus the two facts it
carries forward across every recursive call (`old_next_pair `` snd n_ns ⊆
old_next_pair `` nds ∧ expand_inv_result φ nds`, here `usedSignatures`
monotonicity and `NodesBounded` preservation). -/

section ExpandTermHelpers

variable {α : Type u} [DecidableEq α] {S : Type v} [FSet (NNF α) S]

theorem nodeSignature_incoming_irrelevant (n : GBANode α S) (inc : Std.HashSet Nat) :
    nodeSignature ({ n with incoming := inc } : GBANode α S) = nodeSignature n := rfl

/-- Inserting a node at a *fresh* key (not previously present) only grows
`usedSignatures`. Used for the "finish node, spawn successor" transition —
mirrors the `old_next_pair n ∉ old_next_pair `` ns` fact CAVA gets for free
from the "no duplicate found" branch condition. -/
theorem usedSignatures_insert_fresh_subset (st : ExpandState α S) (k : Nat) (n : GBANode α S)
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
/-- Every node bounded before an insert stays bounded, plus the freshly
inserted node itself if it too is bounded. Mirrors `expand_inv_result`
preservation for both the "fresh successor" and "merge" transitions. -/
theorem NodesBounded_insert {topFormula : NNF α} {st : ExpandState α S}
    (h : NodesBounded topFormula st) {k : Nat} {n : GBANode α S}
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
/-- `mergeIncoming` only ever updates the `incoming` field of the target node
(never `old`/`next`), so `NodesBounded` is trivially preserved. Mirrors
`expand_inv_upd_incoming` (`LTL_to_GBA.thy:997-1000`). -/
theorem NodesBounded_mergeIncoming {topFormula : NNF α} {st : ExpandState α S}
    (h : NodesBounded topFormula st) (node : GBANode α S) (targetName : Nat) :
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

/-- Inserting a signature-preserving replacement at an *existing* key leaves
`usedSignatures` unchanged (as a `⊆`, all that's needed downstream). Mirrors
`upd_incoming_eq_old_next_pair` (`LTL_to_GBA.thy:1003`) — used for the
"merge" transition (`mergeIncoming`), which only ever updates `incoming`,
never `old`/`next`. -/
theorem usedSignatures_insert_matching_subset (st : ExpandState α S) (k : Nat) (n target : GBANode α S)
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

theorem findStep_some_persists (node : GBANode α S) (m : Nat) (l : List (Nat × GBANode α S)) :
    List.foldl (fun a b => findStep node a b) (some m) l = some m := by
  induction l with
  | nil => rfl
  | cons p ps ih => simp only [List.foldl_cons, findStep]; exact ih

/-- The negative counterpart to `findDuplicate_spec`: if no duplicate is
found, no already-finished node shares `node`'s signature. Mirrors the "no
duplicate found" branch condition CAVA gets for free
(`old_next_pair n ∉ old_next_pair `` ns`, used inline in `expand_term_prop`'s
own case 2, `LTL_to_GBA.thy:1066`) — needed explicitly here since Lean has
no such automatic negation from an `if`/`else` split on a `∃`-statement. -/
theorem findDuplicate_spec_none (st : ExpandState α S) (node : GBANode α S)
    (h : findDuplicate st node = none) :
    ∀ (k : Nat) (n : GBANode α S), st.nodes[k]? = some n → n.sameSignature node = false := by
  unfold findDuplicate at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  change List.foldl (fun a b => findStep node a b) none st.nodes.toList = none at h
  intro k n hk
  have hmem : (k, n) ∈ st.nodes.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hk
  clear hk
  suffices hgen : ∀ (l : List (Nat × GBANode α S)),
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

theorem sameSignature_of_nodeSignature_eq {n1 n2 : GBANode α S}
    (h : nodeSignature n1 = nodeSignature n2) : n1.sameSignature n2 = true := by
  unfold GBANode.sameSignature
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

/-- Mirrors the fact `expand_term_prop`'s own case 2 (`LTL_to_GBA.thy:1066`)
gets for free from the "no duplicate found" branch condition:
`old_next_pair n ∉ old_next_pair `` ns`. -/
theorem nodeSignature_fresh_of_findDuplicate_none {st : ExpandState α S} {node : GBANode α S}
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
/-- The three name-freshness hypotheses `expand_invariants` (`Invariants.lean`)
takes as inputs — needed here (unlike in CAVA) because `ExpandState.nodes` is
a *name-keyed* `Std.HashMap`, not a genuine mathematical set of records as in
CAVA's `'a node set`: inserting at an already-used key would silently
overwrite (lose) data, which is structurally impossible in CAVA's set
encoding. `h_not_in`/`h_fresh`/`h_name` rule this out; they are threaded
through every recursive call below and, at the nondeterministic split's
*second* call (the only point where a call's precondition depends on an
*earlier* call's output rather than purely local bookkeeping), obtained via
`expand_invariants` applied as a black box to the first call's now-realized
result. -/
theorem expand_term (topFormula : NNF α) (node : GBANode α S) (st : ExpandState α S)
    (hinv : ExpandInv topFormula node st)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName) :
    ∃ r : Nat × ExpandState α S, expand node st = some r ∧
      usedSignatures st ⊆ usedSignatures r.2 ∧ NodesBounded topFormula r.2 := by
  by_cases h_empty : node.new.isEmpty
  · -- `node.new = []`
    match h_fd : findDuplicate st node with
    | some existingName =>
      -- MERGE: terminal, only `incoming` of the target changes.
      obtain ⟨target, htarget, _⟩ := findDuplicate_spec st node existingName h_fd
      set merged : GBANode α S := { target with incoming := target.incoming.union node.incoming }
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
             next := FSet.empty } : GBANode α S)
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
  · -- `node.new ≠ []`
    have h_ne : node.new.isEmpty = false := by
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
            ({ node with new := node.new.tail!, old := FSet.insert node.old node.new.head! } : GBANode α S) st :=
          ⟨⟨h_tail_sub, h_old_ins, hinv.node_bounded.next_sub⟩, hinv.nodes_bounded⟩
        have hw2 : expandMeasure2
            ({ node with new := node.new.tail!, old := FSet.insert node.old node.new.head! } : GBANode α S)
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
            ({ node with new := node.new.tail!, old := FSet.insert node.old node.new.head! } : GBANode α S) st :=
          ⟨⟨h_tail_sub, h_old_ins, hinv.node_bounded.next_sub⟩, hinv.nodes_bounded⟩
        have hw2 : expandMeasure2
            ({ node with new := node.new.tail!, old := FSet.insert node.old node.new.head! } : GBANode α S)
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
                ({ node with new := addToNew { node with new := node.new.tail! } (new1 node.new.head!), old := FSet.insert node.old node.new.head!, next := addAllToSet node.next (next1 node.new.head!) } : GBANode α S) st :=
              ⟨⟨h_new_sub', h_old_ins, h_next_sub'⟩, hinv.nodes_bounded⟩
            have hw2 : expandMeasure2
                ({ node with new := addToNew { node with new := node.new.tail! } (new1 node.new.head!), old := FSet.insert node.old node.new.head!, next := addAllToSet node.next (next1 node.new.head!) } : GBANode α S)
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
                ({ node with new := addToNew { node with new := node.new.tail! } (new1 node.new.head!), old := FSet.insert node.old node.new.head!, next := addAllToSet node.next (next1 node.new.head!) } : GBANode α S) st :=
              ⟨⟨h_new_sub1, h_old_ins, h_next_sub1⟩, hinv.nodes_bounded⟩
            have hw1 : expandMeasure2
                ({ node with new := addToNew { node with new := node.new.tail! } (new1 node.new.head!), old := FSet.insert node.old node.new.head!, next := addAllToSet node.next (next1 node.new.head!) } : GBANode α S)
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
                ({ node with name := r1.1, new := addToNew { node with new := node.new.tail! } (new2 node.new.head!), old := FSet.insert node.old node.new.head! } : GBANode α S) r1.2 :=
              ⟨⟨h_new_sub2, h_old_ins, hinv.node_bounded.next_sub⟩, hr1_3⟩
            have hm1_le : expandMeasure1 topFormula r1.2 ≤ expandMeasure1 topFormula st :=
              expandMeasure1_le hr1_2
            have hw2 : expandMeasure2
                ({ node with name := r1.1, new := addToNew { node with new := node.new.tail! } (new2 node.new.head!), old := FSet.insert node.old node.new.head! } : GBANode α S)
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

/-- `createGraph`'s totality, mirroring `create_graph_finite`/`create_graph_nofail`
(`LTL_to_GBA.thy:1213-1226`): assembling `expand_term` at the concrete initial
node (`name := 1`, `incoming := {expandInit}`, `new := [φ]`, `old := next := ∅`)
with trivially-satisfiable freshness hypotheses (`initState.nodes` is empty). -/
theorem createGraph_term (φ : NNF α) :
    ∃ st : ExpandState α S, createGraph φ = some st ∧ NodesBounded φ st := by
  have hinv : ExpandInv φ
      ({ name := 1, incoming := Std.HashSet.emptyWithCapacity 4 |>.insert expandInit,
         new := [φ], old := FSet.empty, next := FSet.empty } : GBANode α S)
      ({ nextName := 2, nodes := Std.HashMap.emptyWithCapacity 16 } : ExpandState α S) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro x hx; simp only [List.mem_singleton] at hx; exact hx ▸ NNF.IsSubformula.refl
    · intro x hx; exact absurd hx (by simp [FSet.contains_empty])
    · intro x hx; exact absurd hx (by simp [FSet.contains_empty])
    · intro k n hk; simp at hk
  have h_not_in : (Std.HashMap.emptyWithCapacity 16 : Std.HashMap Nat (GBANode α S))[(1 : Nat)]? = none := by
    simp
  have h_fresh : ∀ k, (Std.HashMap.emptyWithCapacity 16 : Std.HashMap Nat (GBANode α S))[k]? ≠ none → k < 2 := by
    intro k hk; simp at hk
  have h_name : (1 : Nat) < 2 := by omega
  obtain ⟨r, hr1, _, hr3⟩ := expand_term φ
      ({ name := 1, incoming := Std.HashSet.emptyWithCapacity 4 |>.insert expandInit,
         new := [φ], old := FSet.empty, next := FSet.empty } : GBANode α S)
      ({ nextName := 2, nodes := Std.HashMap.emptyWithCapacity 16 } : ExpandState α S)
      hinv h_not_in h_fresh h_name
  refine ⟨r.2, ?_, hr3⟩
  unfold createGraph
  simp only
  rw [hr1]

end ExpandTerm

end LTLLib
