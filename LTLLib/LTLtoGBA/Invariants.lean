/-
  Structural invariants maintained by the `expand`/`createGraph` worklist algorithm (Expand.lean), used to show that
  its output satisfies the abstract `ExpandSpec` (AbstractSpec/ExpansionSpec.lean).

  Defines:
  - `ProcessingInv`: per-node invariant relating `old` to `old ∪ new` while a node is still being expanded
  - `StateInv`: `ProcessingInv` (with `new = []`) for every finished node in an `ExpandState`
  - `NodesPreserved`, `ExpandInvariants`: monotonicity/freshness bookkeeping across `expand` calls

  Proves:
  - `new1`/`new2`/`next1` only ever produce subformulas of their input
  - `expand` preserves prior node data (`NodesPreserved`), name freshness, and `StateInv`
  - finished nodes stay within the subformula closure of the top-level formula
  - `findDuplicate`, `mergeIncoming`, and the `expandInit`/successor bookkeeping behave as expected
  - `expand` keeps the `sigHash` index valid (`expand_indexValid`), which is what makes the bucketed
    `findDuplicate` exact rather than merely sound
  - `createGraph_spec`: the concrete `createGraph φ` output satisfies the abstract `ExpandSpec φ`

  ## Sections
  - Properties of new1, new2, next1
  - Characterization lemmas for new1, new2, next1
  - Per-node propagation invariant
  - Monotonicity: nodes are preserved across expand calls
  - Freshness and naming invariants
  - StateInv preservation
  - Bridge: ProcessingInv with new = [] implies ExpandSpec propagation
  - Subformula closure
  - findDuplicate spec
  - IndexValid preservation
  - mergeIncoming incoming membership
  - Initial old
  - Successor old
  - No expandInit key
  - Main correctness theorem
-/

import LTLLib.LTLtoGBA.Expand
import LTLLib.LTLtoGBA.ExpansionNode
import LTLLib.LTLtoGBA.AbstractSpec.ExpansionSpec
import LTLLib.LTL.Semantics
import LTLLib.LTL.Subformulas

namespace LTLLib

open NNF

/-! ## Properties of new1, new2, next1

`new1`, `new2`, `next1` only ever produce subformulas of their input. -/

theorem new1_subformula {φ : NNF α} {ψ : NNF α} (h : ψ ∈ new1 φ) :
    NNF.IsSubformula ψ φ := by
  cases φ with
  | and μ ν => simp [new1] at h; rcases h with rfl | rfl
               · exact .and_left .refl
               · exact .and_right .refl
  | or μ _ => simp [new1] at h; subst h; exact .or_left .refl
  | «until» μ _ => simp [new1] at h; subst h; exact .until_left .refl
  | release _ ν => simp [new1] at h; subst h; exact .release_right .refl
  | _ => simp [new1] at h

theorem new2_subformula {φ : NNF α} {ψ : NNF α} (h : ψ ∈ new2 φ) :
    NNF.IsSubformula ψ φ := by
  cases φ with
  | or _ ν => simp [new2] at h; subst h; exact .or_right .refl
  | «until» _ ν => simp [new2] at h; subst h; exact .until_right .refl
  | release μ ν => simp [new2] at h; rcases h with rfl | rfl
                   · exact .release_left .refl
                   · exact .release_right .refl
  | _ => simp [new2] at h

theorem next1_subformula {φ : NNF α} {ψ : NNF α} (h : ψ ∈ next1 φ) :
    NNF.IsSubformula ψ φ := by
  cases φ with
  | next ν => simp [next1] at h; subst h; exact .next_sub .refl
  | «until» μ ν => simp [next1] at h; subst h; exact .refl
  | release μ ν => simp [next1] at h; subst h; exact .refl
  | _ => simp [next1] at h

/-! ## Characterization lemmas for new1, new2, next1

Spell out exactly what each function produces. -/

@[simp] theorem new1_and (μ ψ : NNF α) : new1 (.and μ ψ) = [μ, ψ] := rfl
@[simp] theorem new1_or (μ ψ : NNF α) : new1 (.or μ ψ) = [μ] := rfl
@[simp] theorem new1_until (μ ψ : NNF α) : new1 (.until μ ψ) = [μ] := rfl
@[simp] theorem new1_release (μ ψ : NNF α) : new1 (.release μ ψ) = [ψ] := rfl

@[simp] theorem new2_or (μ ψ : NNF α) : new2 (.or μ ψ) = [ψ] := rfl
@[simp] theorem new2_until (μ ψ : NNF α) : new2 (.until μ ψ) = [ψ] := rfl
@[simp] theorem new2_release (μ ψ : NNF α) : new2 (.release μ ψ) = [μ, ψ] := rfl

@[simp] theorem next1_next (ψ : NNF α) : next1 (.next ψ) = [ψ] := rfl
@[simp] theorem next1_until (μ ψ : NNF α) : next1 (.until μ ψ) = [.until μ ψ] := rfl
@[simp] theorem next1_release (μ ψ : NNF α) : next1 (.release μ ψ) = [.release μ ψ] := rfl

/-! ## Per-node propagation invariant

For each compound formula in `old`, its consequences must be in `old ∪ new`.
When `new = []` this gives the `ExpandSpec` propagation properties directly. -/

variable {α : Type u} {S : Type v} [FSet (NNF α) S] [Hashable (NNF α)] [BEq (NNF α)] [LawfulBEq (NNF α)]

/-- Per-node propagation invariant during processing. For compound formulas in `old`, consequences are in
    `old ∪ new`. -/
structure ProcessingInv (n : ExpansionNode α S) : Prop where
  -- No literal contradiction.
  literal_consistent : ∀ a, n.oldHas (.prop a) → ¬ n.oldHas (.nprop a)
  -- No ff in old.
  no_false : ¬ n.oldHas .ff
  -- And: both conjuncts reachable.
  and_propag : ∀ μ ψ, n.oldHas (.and μ ψ) → n.reachable μ ∧ n.reachable ψ
  -- Or: at least one disjunct reachable.
  or_propag : ∀ μ ψ, n.oldHas (.or μ ψ) → n.reachable μ ∨ n.reachable ψ
  -- Next: inner formula in next set.
  next_propag : ∀ ψ, n.oldHas (.next ψ) → n.nextHas ψ
  -- Until: RHS reachable, or LHS reachable and self in next.
  until_propag : ∀ μ ψ, n.oldHas (.until μ ψ) →
    n.reachable ψ ∨ (n.reachable μ ∧ n.nextHas (.until μ ψ))
  -- Release: RHS reachable, and (LHS reachable or self in next).
  release_propag : ∀ μ ψ, n.oldHas (.release μ ψ) →
    n.reachable ψ ∧ (n.reachable μ ∨ n.nextHas (.release μ ψ))

/-- Invariant for all finished nodes in a state. -/
def StateInv (st : ExpandState α S) : Prop :=
  ∀ (k : Nat) (n : ExpansionNode α S), st.nodes[k]? = some n → ProcessingInv n ∧ n.new = []

/-! ## Monotonicity: nodes are preserved across expand calls -/

/-- Nodes in `st` are preserved in `st'` (their old/next don't change, only incoming may grow via mergeIncoming). -/
def NodesPreserved (st st' : ExpandState α S) : Prop :=
  ∀ (k : Nat) (n : ExpansionNode α S), st.nodes[k]? = some n →
    ∃ n' : ExpansionNode α S, st'.nodes[k]? = some n' ∧
      (∀ ψ, FSet.contains n'.old ψ ↔ FSet.contains n.old ψ) ∧
      (∀ ψ, FSet.contains n'.next ψ ↔ FSet.contains n.next ψ)

/-! ### Helper lemmas -/

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
theorem mergeIncoming_nodesPreserved (st : ExpandState α S) (node : ExpansionNode α S) (targetName : Nat) :
    NodesPreserved st (mergeIncoming st node targetName) := by
  intro k n hk; unfold mergeIncoming; simp only
  split
  · rename_i target htarget
    simp only [Std.HashMap.getElem?_insert]; split
    · rename_i hk_eq
      have : k = targetName := by rw [beq_iff_eq] at hk_eq; exact hk_eq.symm
      subst this; rw [htarget] at hk; obtain rfl := Option.some.inj hk
      exact ⟨_, rfl, fun ψ => Iff.rfl, fun ψ => Iff.rfl⟩
    · exact ⟨n, hk, fun ψ => Iff.rfl, fun ψ => Iff.rfl⟩
  · exact ⟨n, hk, fun ψ => Iff.rfl, fun ψ => Iff.rfl⟩

omit [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
theorem mergeIncoming_nextName (st : ExpandState α S) (node : ExpansionNode α S) (targetName : Nat) :
    (mergeIncoming st node targetName).nextName = st.nextName := by
  unfold mergeIncoming; split <;> rfl

omit [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
theorem mergeIncoming_preserves_absent (st : ExpandState α S) (node : ExpansionNode α S)
    (targetName : Nat) (k : Nat) (hk : st.nodes[k]? = none) :
    (mergeIncoming st node targetName).nodes[k]? = none := by
  unfold mergeIncoming; split
  · rename_i target htarget
    simp only [Std.HashMap.getElem?_insert]; split
    · rename_i heq
      have h := (beq_iff_eq (α := Nat)).mp heq
      rw [← h] at hk; rw [hk] at htarget; simp at htarget
    · exact hk
  · exact hk

omit [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
theorem mergeIncoming_freshInv (st : ExpandState α S) (node : ExpansionNode α S)
    (targetName : Nat) (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName) :
    ∀ k, (mergeIncoming st node targetName).nodes[k]? ≠ none →
      k < (mergeIncoming st node targetName).nextName := by
  intro k hk
  rw [mergeIncoming_nextName]
  unfold mergeIncoming at hk; split at hk
  · rename_i target htarget
    simp only [Std.HashMap.getElem?_insert] at hk; split at hk
    · rename_i heq
      have := (beq_iff_eq (α := Nat)).mp heq
      rw [← this]; exact h_fresh targetName (by simp [htarget])
    · exact h_fresh k hk
  · exact h_fresh k hk

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem NodesPreserved_refl (st : ExpandState α S) : NodesPreserved st st :=
  fun _k n hk => ⟨n, hk, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem NodesPreserved_trans {st₁ st₂ st₃ : ExpandState α S}
    (h₁₂ : NodesPreserved st₁ st₂) (h₂₃ : NodesPreserved st₂ st₃) :
    NodesPreserved st₁ st₃ := by
  intro k n hk
  obtain ⟨n', hk', ho', hn'⟩ := h₁₂ k n hk
  obtain ⟨n'', hk'', ho'', hn''⟩ := h₂₃ k n' hk'
  exact ⟨n'', hk'', fun ψ => (ho'' ψ).trans (ho' ψ), fun ψ => (hn'' ψ).trans (hn' ψ)⟩

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
theorem insert_nodesPreserved (st : ExpandState α S) (node : ExpansionNode α S)
    (h_not_in : st.nodes[node.name]? = none) :
    NodesPreserved st { st with nodes := st.nodes.insert node.name node } := by
  intro k n hk
  have hne : k ≠ node.name := fun heq => by rw [heq, h_not_in] at hk; simp at hk
  simp only [Std.HashMap.getElem?_insert]; split
  · rename_i heq; exact absurd ((beq_iff_eq (α := Nat)).mp heq).symm hne
  · exact ⟨n, hk, fun ψ => Iff.rfl, fun ψ => Iff.rfl⟩

omit [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
theorem insert_fresh_key (st : ExpandState α S) (nodeName : Nat) (node : ExpansionNode α S)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : nodeName < st.nextName) :
    (st.nodes.insert nodeName node)[st.nextName]? = none := by
  simp only [Std.HashMap.getElem?_insert]; split
  · rename_i heq; have := (beq_iff_eq (α := Nat)).mp heq; omega
  · by_contra h; exact absurd (h_fresh st.nextName h) (by omega)

omit [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
theorem insert_freshInv (st : ExpandState α S) (nodeName : Nat) (node : ExpansionNode α S)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : nodeName < st.nextName) :
    ∀ k, (st.nodes.insert nodeName node)[k]? ≠ none →
      k < st.nextName + 1 := by
  intro k hk
  simp only [Std.HashMap.getElem?_insert] at hk; split at hk
  · rename_i heq; have := (beq_iff_eq (α := Nat)).mp heq; omega
  · have := h_fresh k hk; omega

/-! ## Freshness and naming invariants -/

/-- Combined invariants maintained by expand: monotonicity, name freshness, freshness invariant preservation. -/
structure ExpandInvariants (st st' : ExpandState α S) (nm : Nat) : Prop where
  nodesPreserved : NodesPreserved st st'
  nameFresh : st'.nodes[nm]? = none
  freshInv : ∀ k, st'.nodes[k]? ≠ none → k < st'.nextName
  nameBound : nm < st'.nextName
  nextNameMono : st.nextName ≤ st'.nextName

omit [BEq (NNF α)] [LawfulBEq (NNF α)] in
/-- `expand` preserves prior nodes, keeps the fresh-name bound, and returns a name below the new `nextName`. -/
theorem expand_invariants (node : ExpansionNode α S)
    (st : ExpandState α S) {r : Nat × ExpandState α S}
    (h_result : expand node st = some r)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName) :
    ExpandInvariants st r.2 r.1 := by
  revert h_not_in h_fresh h_name
  apply expand.partial_correctness
    (motive := fun node st r =>
      st.nodes[node.name]? = none →
      (∀ k, st.nodes[k]? ≠ none → k < st.nextName) →
      node.name < st.nextName →
      ExpandInvariants st r.2 r.1)
    _ node st r h_result
  intro expand_ih ih node st r h_result h_not_in h_fresh h_name
  split at h_result
  case isTrue h_empty =>
    split at h_result
    · -- Merge case
      rename_i existingName _
      obtain rfl := Option.some.inj h_result
      exact {
        nodesPreserved := mergeIncoming_nodesPreserved st node existingName
        nameFresh := mergeIncoming_preserves_absent st node existingName _ h_not_in
        freshInv := mergeIncoming_freshInv st node existingName h_fresh
        nameBound := by rw [mergeIncoming_nextName]; exact h_name
        nextNameMono := by rw [mergeIncoming_nextName]
      }
    · -- Insert + recurse
      simp only [freshName] at h_result
      have inv := ih _ _ _ h_result
        (insert_fresh_key st node.name node h_fresh h_name)
        (insert_freshInv st node.name node h_fresh h_name)
        (by show st.nextName < st.nextName + 1; omega)
      exact {
        nodesPreserved := NodesPreserved_trans
          (insert_nodesPreserved st node h_not_in) inv.nodesPreserved
        nameFresh := inv.nameFresh
        freshInv := inv.freshInv
        nameBound := inv.nameBound
        nextNameMono := Nat.le_trans (Nat.le_succ _) inv.nextNameMono
      }
  case isFalse h_not_empty =>
    simp only [Bool.not_eq_true] at h_not_empty
    simp only at h_result
    split at h_result
    · -- isLiteral
      split at h_result
      · -- contradiction
        obtain rfl := Option.some.inj h_result
        exact ⟨NodesPreserved_refl st, h_not_in, h_fresh, h_name, Nat.le.refl⟩
      · exact ih _ _ _ h_result h_not_in h_fresh h_name
    · -- After isLiteral=false: handle tt/ff/det/nondet
      split at h_result <;> (try split at h_result) <;> (try split at h_result) <;>
        (try split at h_result) <;> (try split at h_result)
      all_goals (
        first
        | (obtain rfl := Option.some.inj h_result
           exact ⟨NodesPreserved_refl st, h_not_in, h_fresh, h_name, Nat.le.refl⟩)
        | exact ih _ _ _ h_result h_not_in h_fresh h_name
        | (simp only [Bind.bind, Option.bind] at h_result
           split at h_result
           · simp at h_result
           · rename_i h_branch1
             have inv1 := ih _ _ _ h_branch1 h_not_in h_fresh h_name
             have inv2 := ih _ _ _ h_result inv1.nameFresh inv1.freshInv inv1.nameBound
             exact {
               nodesPreserved := NodesPreserved_trans inv1.nodesPreserved inv2.nodesPreserved
               nameFresh := inv2.nameFresh
               freshInv := inv2.freshInv
               nameBound := inv2.nameBound
               nextNameMono := Nat.le_trans inv1.nextNameMono inv2.nextNameMono
             }))

omit [BEq (NNF α)] [LawfulBEq (NNF α)] in
/-- `expand` preserves the old/next data of every node already present in `st`. -/
theorem expand_nodes_preserved (node : ExpansionNode α S)
    (st : ExpandState α S) {r : Nat × ExpandState α S}
    (h_result : expand node st = some r)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName) :
    NodesPreserved st r.2 :=
  (expand_invariants node st h_result h_not_in h_fresh h_name).nodesPreserved

/-! ## StateInv preservation

Case-by-case lemmas showing `ProcessingInv` survives each step of `expand`: literal, tt, deterministic, and the
two nondeterministic branches. -/

omit [Hashable (NNF α)] in
theorem oldHas_insert {s : S} {φ ψ : NNF α}
    (h : FSet.contains (FSet.insert s φ) ψ = true) :
    FSet.contains s ψ = true ∨ ψ = φ := by
  rw [FSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h; exact Or.inr rfl; exact Or.inl h

omit [Hashable (NNF α)] in
private theorem old_subset_insert (s : S) (φ : NNF α) :
    ∀ ψ, FSet.contains s ψ = true → FSet.contains (FSet.insert s φ) ψ = true :=
  fun _ h => by rw [FSet.contains_insert]; simp [h]

omit [Hashable (NNF α)] in
private theorem mem_insert_self' (s : S) (φ : NNF α) :
    FSet.contains (FSet.insert s φ) φ = true := by rw [FSet.contains_insert]; simp

omit [Hashable (NNF α)] in
private theorem addAllToSet_subset (s : S) (fs : List (NNF α)) :
    ∀ ψ, FSet.contains s ψ = true → FSet.contains (addAllToSet s fs) ψ = true := by
  induction fs generalizing s with
  | nil => exact fun _ h => h
  | cons f rest ih =>
    intro ψ h; show FSet.contains (addAllToSet (FSet.insert s f) rest) ψ = true
    exact ih _ ψ (old_subset_insert s f ψ h)

omit [Hashable (NNF α)] in
private theorem addAllToSet_mem (s : S) (fs : List (NNF α)) :
    ∀ ψ, ψ ∈ fs → FSet.contains (addAllToSet s fs) ψ = true := by
  induction fs generalizing s with
  | nil => intro ψ h; simp at h
  | cons f rest ih =>
    intro ψ h; show FSet.contains (addAllToSet (FSet.insert s f) rest) ψ = true
    cases List.mem_cons.mp h with
    | inl heq => subst heq; exact addAllToSet_subset _ rest ψ (mem_insert_self' s ψ)
    | inr hmem => exact ih _ ψ hmem

omit [Hashable (NNF α)] in
theorem addAllToSet_inv (s : S) (fs : List (NNF α)) :
    ∀ ψ, FSet.contains (addAllToSet s fs) ψ = true → FSet.contains s ψ = true ∨ ψ ∈ fs := by
  induction fs generalizing s with
  | nil => intro ψ h; exact Or.inl h
  | cons f rest ih =>
    intro ψ h
    rcases ih (FSet.insert s f) ψ h with h1 | h2
    · rcases oldHas_insert h1 with h1 | rfl
      · exact Or.inl h1
      · exact Or.inr (.head rest)
    · exact Or.inr (.tail f h2)

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem addToNew_foldl_preserves (old : S)
    (formulas : List (NNF α)) (init : List (NNF α)) :
    ∀ ψ, ψ ∈ init → ψ ∈ formulas.foldl (fun acc f => if FSet.contains old f then acc else f :: acc) init := by
  induction formulas generalizing init with
  | nil => exact fun _ h => h
  | cons f rest ih =>
    intro ψ h; simp only [List.foldl]
    apply ih; split <;> [exact h; exact List.mem_cons_of_mem _ h]

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem addToNew_foldl_adds (old : S)
    (formulas : List (NNF α)) (init : List (NNF α)) :
    ∀ ψ, ψ ∈ formulas → FSet.contains old ψ = false →
    ψ ∈ formulas.foldl (fun acc f => if FSet.contains old f then acc else f :: acc) init := by
  induction formulas generalizing init with
  | nil => intro ψ h; simp at h
  | cons f rest ih =>
    intro ψ h hn; simp only [List.foldl]
    cases List.mem_cons.mp h with
    | inl heq => subst heq; apply addToNew_foldl_preserves; simp [hn]
    | inr hmem => exact ih _ ψ hmem hn

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem addToNew_foldl_inv (old : S)
    (formulas : List (NNF α)) (init : List (NNF α)) :
    ∀ ψ, ψ ∈ formulas.foldl (fun acc f => if FSet.contains old f then acc else f :: acc) init →
    ψ ∈ init ∨ ψ ∈ formulas := by
  induction formulas generalizing init with
  | nil => intro ψ h; exact Or.inl h
  | cons f rest ih =>
    intro ψ h; simp only [List.foldl] at h
    rcases ih _ ψ h with h1 | h2
    · split at h1
      · exact Or.inl h1
      · rcases List.mem_cons.mp h1 with rfl | h1
        · exact Or.inr (.head rest)
        · exact Or.inl h1
    · exact Or.inr (List.mem_cons_of_mem _ h2)

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
theorem addToNew_inv (node : ExpansionNode α S) (formulas : List (NNF α)) :
    ∀ ψ, ψ ∈ addToNew node formulas → ψ ∈ node.new ∨ ψ ∈ formulas :=
  addToNew_foldl_inv node.old formulas node.new

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem addToNew_preserves (node : ExpansionNode α S) (formulas : List (NNF α)) :
    ∀ ψ, ψ ∈ node.new → ψ ∈ addToNew node formulas :=
  addToNew_foldl_preserves node.old formulas node.new

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem addToNew_adds (node : ExpansionNode α S) (formulas : List (NNF α)) :
    ∀ ψ, ψ ∈ formulas → FSet.contains node.old ψ = false → ψ ∈ addToNew node formulas :=
  addToNew_foldl_adds node.old formulas node.new

omit [BEq (NNF α)] [LawfulBEq (NNF α)] in
private theorem mem_head_or_tail' [Inhabited β] {l : List β} (h : l.isEmpty = false)
    {φ : β} (hφ : l.head! = φ) {ψ : β} (hψ : ψ ∈ l) : ψ = φ ∨ ψ ∈ l.tail! := by
  cases l with
  | nil => simp at h
  | cons a rest => subst hφ; exact List.mem_cons.mp hψ

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem reachable_step {node : ExpansionNode α S} {φ : NNF α}
    (h_ne : node.new.isEmpty = false) (hφ : node.new.head! = φ)
    (h : node.reachable ψ) {old' : S}
    (h_old : ∀ χ, FSet.contains node.old χ = true → FSet.contains old' χ = true)
    (h_φ : FSet.contains old' φ = true) {new' : List (NNF α)}
    (h_new : ∀ χ, χ ∈ node.new.tail! → χ ∈ new') :
    FSet.contains old' ψ = true ∨ ψ ∈ new' := by
  cases h with
  | inl h => exact Or.inl (h_old ψ h)
  | inr h =>
    rcases mem_head_or_tail' h_ne hφ h with rfl | hmem
    · exact Or.inl h_φ
    · exact Or.inr (h_new ψ hmem)

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem reachable_via_formulas {node : ExpansionNode α S}
    (formulas : List (NNF α)) {ψ : NNF α} (h : ψ ∈ formulas)
    {old' : S}
    (h_old : ∀ χ, FSet.contains node.old χ = true → FSet.contains old' χ = true) :
    FSet.contains old' ψ = true ∨ ψ ∈ addToNew node formulas := by
  by_cases hψ : FSet.contains node.old ψ = true
  · exact Or.inl (h_old ψ hψ)
  · simp only [Bool.not_eq_true] at hψ
    exact Or.inr (addToNew_adds node formulas ψ h hψ)

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem processingInv_empty_old (node : ExpansionNode α S)
    (h : ∀ ψ, FSet.contains node.old ψ = false) : ProcessingInv node where
  literal_consistent a ha := by simp [ExpansionNode.oldHas, h] at ha
  no_false hf := by simp [ExpansionNode.oldHas, h] at hf
  and_propag _ _ ha := by simp [ExpansionNode.oldHas, h] at ha
  or_propag _ _ ha := by simp [ExpansionNode.oldHas, h] at ha
  next_propag _ ha := by simp [ExpansionNode.oldHas, h] at ha
  until_propag _ _ ha := by simp [ExpansionNode.oldHas, h] at ha
  release_propag _ _ ha := by simp [ExpansionNode.oldHas, h] at ha

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem mergeIncoming_stateInv (st : ExpandState α S) (node : ExpansionNode α S)
    (targetName : Nat) (h_inv : StateInv st) :
    StateInv (mergeIncoming st node targetName) := by
  intro k n hk; unfold mergeIncoming at hk; split at hk
  · rename_i target htarget
    simp only [Std.HashMap.getElem?_insert] at hk; split at hk
    · obtain rfl := Option.some.inj hk
      obtain ⟨proc, hnew⟩ := h_inv targetName target htarget
      exact ⟨{
        literal_consistent := proc.literal_consistent
        no_false := proc.no_false
        and_propag := proc.and_propag
        or_propag := proc.or_propag
        next_propag := proc.next_propag
        until_propag := proc.until_propag
        release_propag := proc.release_propag
      }, hnew⟩
    · exact h_inv k n hk
  · exact h_inv k n hk

omit [Hashable (NNF α)] in
private theorem processingInv_literal {node : ExpansionNode α S}
    (h_proc : ProcessingInv node) (h_ne : node.new.isEmpty = false)
    (h_lit : isLiteral node.new.head! = true)
    (h_no_neg : FSet.contains node.old (negateLiteral node.new.head!) = false) :
    ProcessingInv { node with new := node.new.tail!, old := FSet.insert node.old node.new.head! } := by
  generalize hφ : node.new.head! = φ at *
  have h_φ_old := mem_insert_self' node.old φ
  have reach : ∀ ψ, node.reachable ψ →
      FSet.contains (FSet.insert node.old φ) ψ = true ∨ ψ ∈ node.new.tail! :=
    fun ψ h => reachable_step h_ne hφ h (old_subset_insert _ φ) h_φ_old (fun _ h => h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha hna; simp only [ExpansionNode.oldHas] at ha hna
    rcases oldHas_insert ha with ha' | rfl
    · rcases oldHas_insert hna with hna' | rfl
      · exact h_proc.literal_consistent a ha' hna'
      · simp [negateLiteral, ha'] at h_no_neg
    · rcases oldHas_insert hna with hna' | heq
      · simp [negateLiteral, hna'] at h_no_neg
      · simp at heq
  all_goals (
    first | (intro _ _ ha) | (intro _ ha) | (intro ha)
    simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · first
      | exact h_proc.no_false ha'
      | (have ⟨h1, h2⟩ := h_proc.and_propag _ _ ha'; exact ⟨reach _ h1, reach _ h2⟩)
      | exact (h_proc.or_propag _ _ ha').imp (reach _) (reach _)
      | exact h_proc.next_propag _ ha'
      | exact (h_proc.until_propag _ _ ha').imp (reach _) (fun ⟨h1, h2⟩ => ⟨reach _ h1, h2⟩)
      | (have ⟨h1, h2⟩ := h_proc.release_propag _ _ ha';
         exact ⟨reach _ h1, h2.imp (reach _) id⟩)
    · simp [isLiteral] at h_lit)

omit [Hashable (NNF α)] in
private theorem processingInv_tt {node : ExpansionNode α S}
    (h_proc : ProcessingInv node) (h_ne : node.new.isEmpty = false)
    (h_tt : node.new.head! = NNF.tt) :
    ProcessingInv { node with new := node.new.tail!, old := FSet.insert node.old node.new.head! } := by
  generalize hφ : node.new.head! = φ at *
  subst h_tt
  have h_φ_old := mem_insert_self' node.old NNF.tt
  have reach : ∀ ψ, node.reachable ψ →
      FSet.contains (FSet.insert node.old NNF.tt) ψ = true ∨ ψ ∈ node.new.tail! :=
    fun ψ h => reachable_step h_ne hφ h (old_subset_insert _ _) h_φ_old (fun _ h => h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha hna; simp only [ExpansionNode.oldHas] at ha hna
    rcases oldHas_insert ha with ha' | heq
    · rcases oldHas_insert hna with hna' | heq
      · exact h_proc.literal_consistent a ha' hna'
      · simp at heq
    · simp at heq
  all_goals (
    first | (intro _ _ ha) | (intro _ ha) | (intro ha)
    simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | heq
    · first
      | exact h_proc.no_false ha'
      | (have ⟨h1, h2⟩ := h_proc.and_propag _ _ ha'; exact ⟨reach _ h1, reach _ h2⟩)
      | exact (h_proc.or_propag _ _ ha').imp (reach _) (reach _)
      | exact h_proc.next_propag _ ha'
      | exact (h_proc.until_propag _ _ ha').imp (reach _) (fun ⟨h1, h2⟩ => ⟨reach _ h1, h2⟩)
      | (have ⟨h1, h2⟩ := h_proc.release_propag _ _ ha';
         exact ⟨reach _ h1, h2.imp (reach _) id⟩)
    · simp at heq)

omit [Hashable (NNF α)] in
private theorem processingInv_deterministic {node : ExpansionNode α S}
    (h_proc : ProcessingInv node) (h_ne : node.new.isEmpty = false)
    (h_det : isDeterministic node.new.head! = true) :
    let φ := node.new.head!
    let node_tail := { node with new := node.new.tail! }
    ProcessingInv {
      node with
      new := addToNew node_tail (new1 φ)
      old := FSet.insert node.old φ
      next := addAllToSet node.next (next1 φ) } := by
  generalize hφ : node.new.head! = φ at *
  let node_tail := { node with new := node.new.tail! }
  have h_φ_old := mem_insert_self' node.old φ
  have h_old_sub := old_subset_insert node.old φ
  have h_new_sub : ∀ ψ, ψ ∈ node.new.tail! → ψ ∈ addToNew node_tail (new1 φ) :=
    fun ψ h => addToNew_preserves node_tail (new1 φ) ψ h
  have h_next_sub : ∀ ψ, FSet.contains node.next ψ = true → FSet.contains (addAllToSet node.next (next1 φ)) ψ = true :=
    fun ψ h => addAllToSet_subset node.next (next1 φ) ψ h
  have reach : ∀ ψ, node.reachable ψ →
      FSet.contains (FSet.insert node.old φ) ψ = true ∨ ψ ∈ addToNew node_tail (new1 φ) :=
    fun ψ h => reachable_step h_ne hφ h h_old_sub h_φ_old h_new_sub
  have reach_new1 : ∀ ψ, ψ ∈ new1 φ →
      FSet.contains (FSet.insert node.old φ) ψ = true ∨ ψ ∈ addToNew node_tail (new1 φ) :=
    fun ψ h => reachable_via_formulas (new1 φ) h h_old_sub
  have in_next1 : ∀ ψ, ψ ∈ next1 φ → FSet.contains (addAllToSet node.next (next1 φ)) ψ = true :=
    fun ψ h => addAllToSet_mem node.next (next1 φ) ψ h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha hna; simp only [ExpansionNode.oldHas] at ha hna
    rcases oldHas_insert ha with ha' | rfl
    · rcases oldHas_insert hna with hna' | rfl
      · exact h_proc.literal_consistent a ha' hna'
      · simp [isDeterministic] at h_det
    · simp [isDeterministic] at h_det
  · intro hf; simp only [ExpansionNode.oldHas] at hf
    rcases oldHas_insert hf with hf' | rfl
    · exact h_proc.no_false hf'
    · simp [isDeterministic] at h_det
  · intro μ ψ ha; simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · have ⟨h1, h2⟩ := h_proc.and_propag μ ψ ha'; exact ⟨reach _ h1, reach _ h2⟩
    · exact ⟨reach_new1 μ (by simp [new1]), reach_new1 ψ (by simp [new1])⟩
  · intro μ ψ ha; simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact (h_proc.or_propag μ ψ ha').imp (reach _) (reach _)
    · simp [isDeterministic] at h_det
  · intro ψ ha; simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact h_next_sub ψ (h_proc.next_propag ψ ha')
    · exact in_next1 ψ (by simp [next1])
  · intro μ ψ ha; simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact (h_proc.until_propag μ ψ ha').imp (reach _) (fun ⟨h1, h2⟩ => ⟨reach _ h1, h_next_sub _ h2⟩)
    · simp [isDeterministic] at h_det
  · intro μ ψ ha; simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · have ⟨h1, h2⟩ := h_proc.release_propag μ ψ ha'
      exact ⟨reach _ h1, h2.imp (reach _) (h_next_sub _)⟩
    · simp [isDeterministic] at h_det

omit [Hashable (NNF α)] in
private theorem processingInv_nondet1 {node : ExpansionNode α S}
    (h_proc : ProcessingInv node) (h_ne : node.new.isEmpty = false)
    (h_nondet : isDeterministic node.new.head! = false)
    (h_not_lit : isLiteral node.new.head! = false)
    (h_not_tt : ¬ (node.new.head! matches .tt))
    (h_not_ff : ¬ (node.new.head! matches .ff)) :
    let φ := node.new.head!
    let node_tail := { node with new := node.new.tail! }
    ProcessingInv {
      node with
      new := addToNew node_tail (new1 φ)
      old := FSet.insert node.old φ
      next := addAllToSet node.next (next1 φ) } := by
  generalize hφ : node.new.head! = φ at *
  let node_tail := { node with new := node.new.tail! }
  have h_φ_old := mem_insert_self' node.old φ
  have h_old_sub := old_subset_insert node.old φ
  have h_new_sub : ∀ ψ, ψ ∈ node.new.tail! → ψ ∈ addToNew node_tail (new1 φ) :=
    fun ψ h => addToNew_preserves node_tail (new1 φ) ψ h
  have h_next_sub : ∀ ψ, FSet.contains node.next ψ = true → FSet.contains (addAllToSet node.next (next1 φ)) ψ = true :=
    fun ψ h => addAllToSet_subset node.next (next1 φ) ψ h
  have reach : ∀ ψ, node.reachable ψ →
      FSet.contains (FSet.insert node.old φ) ψ = true ∨ ψ ∈ addToNew node_tail (new1 φ) :=
    fun ψ h => reachable_step h_ne hφ h h_old_sub h_φ_old h_new_sub
  have reach_new1 : ∀ ψ, ψ ∈ new1 φ →
      FSet.contains (FSet.insert node.old φ) ψ = true ∨ ψ ∈ addToNew node_tail (new1 φ) :=
    fun ψ h => reachable_via_formulas (new1 φ) h h_old_sub
  have in_next1 : ∀ ψ, ψ ∈ next1 φ → FSet.contains (addAllToSet node.next (next1 φ)) ψ = true :=
    fun ψ h => addAllToSet_mem node.next (next1 φ) ψ h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha hna; simp only [ExpansionNode.oldHas] at ha hna
    rcases oldHas_insert ha with ha' | rfl
    · rcases oldHas_insert hna with hna' | rfl
      · exact h_proc.literal_consistent a ha' hna'
      · simp_all [isLiteral, isDeterministic]
    · simp_all [isLiteral, isDeterministic]
  · intro hf; simp only [ExpansionNode.oldHas] at hf
    rcases oldHas_insert hf with hf' | rfl
    · exact h_proc.no_false hf'
    · simp_all [isLiteral, isDeterministic]
  · intro μ ψ ha; simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · have ⟨h1, h2⟩ := h_proc.and_propag μ ψ ha'; exact ⟨reach _ h1, reach _ h2⟩
    · simp_all [isDeterministic]
  · intro μ ψ ha; simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact (h_proc.or_propag μ ψ ha').imp (reach _) (reach _)
    · exact Or.inl (reach_new1 μ (by simp [new1]))
  · intro ψ ha; simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact h_next_sub ψ (h_proc.next_propag ψ ha')
    · simp_all [isDeterministic]
  · intro μ ψ ha; simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact (h_proc.until_propag μ ψ ha').imp (reach _) (fun ⟨h1, h2⟩ => ⟨reach _ h1, h_next_sub _ h2⟩)
    · exact Or.inr ⟨reach_new1 μ (by simp [new1]), in_next1 _ (by simp [next1])⟩
  · intro μ ψ ha; simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · have ⟨h1, h2⟩ := h_proc.release_propag μ ψ ha'
      exact ⟨reach _ h1, h2.imp (reach _) (h_next_sub _)⟩
    · exact ⟨reach_new1 ψ (by simp [new1]), Or.inr (in_next1 _ (by simp [next1]))⟩

omit [Hashable (NNF α)] in
private theorem processingInv_nondet2 {node : ExpansionNode α S}
    (h_proc : ProcessingInv node) (h_ne : node.new.isEmpty = false)
    (h_nondet : isDeterministic node.new.head! = false)
    (h_not_lit : isLiteral node.new.head! = false)
    (h_not_tt : ¬ (node.new.head! matches .tt))
    (h_not_ff : ¬ (node.new.head! matches .ff))
    (nm : Nat) :
    ProcessingInv {
      node with
      name := nm
      new := addToNew { node with new := node.new.tail! } (new2 node.new.head!)
      old := FSet.insert node.old node.new.head! } := by
  generalize hφ : node.new.head! = φ at *
  let node_tail := { node with new := node.new.tail! }
  have h_φ_old := mem_insert_self' node.old φ
  have h_old_sub := old_subset_insert node.old φ
  have h_new_sub : ∀ ψ, ψ ∈ node.new.tail! → ψ ∈ addToNew node_tail (new2 φ) :=
    fun ψ h => addToNew_preserves node_tail (new2 φ) ψ h
  have reach : ∀ ψ, node.reachable ψ →
      FSet.contains (FSet.insert node.old φ) ψ = true ∨ ψ ∈ addToNew node_tail (new2 φ) :=
    fun ψ h => reachable_step h_ne hφ h h_old_sub h_φ_old h_new_sub
  have reach_new2 : ∀ ψ, ψ ∈ new2 φ →
      FSet.contains (FSet.insert node.old φ) ψ = true ∨ ψ ∈ addToNew node_tail (new2 φ) :=
    fun ψ h => reachable_via_formulas (new2 φ) h h_old_sub
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha hna; simp only [ExpansionNode.oldHas] at ha hna
    rcases oldHas_insert ha with ha' | rfl
    · rcases oldHas_insert hna with hna' | rfl
      · exact h_proc.literal_consistent a ha' hna'
      · simp_all [isLiteral, isDeterministic]
    · simp_all [isLiteral, isDeterministic]
  · intro hf; simp only [ExpansionNode.oldHas] at hf
    rcases oldHas_insert hf with hf' | rfl
    · exact h_proc.no_false hf'
    · simp_all [isLiteral, isDeterministic]
  · intro μ ψ ha; simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · have ⟨h1, h2⟩ := h_proc.and_propag μ ψ ha'; exact ⟨reach _ h1, reach _ h2⟩
    · simp_all [isDeterministic]
  · intro μ ψ ha; simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact (h_proc.or_propag μ ψ ha').imp (reach _) (reach _)
    · exact Or.inr (reach_new2 ψ (by simp [new2]))
  · intro ψ ha; simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact h_proc.next_propag ψ ha'
    · simp_all [isDeterministic]
  · intro μ ψ ha; simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact (h_proc.until_propag μ ψ ha').imp (reach _) (fun ⟨h1, h2⟩ => ⟨reach _ h1, h2⟩)
    · exact Or.inl (reach_new2 ψ (by simp [new2]))
  · intro μ ψ ha; simp only [ExpansionNode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · have ⟨h1, h2⟩ := h_proc.release_propag μ ψ ha'
      exact ⟨reach _ h1, h2.imp (reach _) id⟩
    · exact ⟨reach_new2 ψ (by simp [new2]), Or.inl (reach_new2 μ (by simp [new2]))⟩

/-- If `st` satisfies `StateInv` and `node` satisfies `ProcessingInv`, the result of expanding `node` into `st` again
    satisfies `StateInv`. -/
theorem expand_preserves_stateInv (node : ExpansionNode α S)
    (st : ExpandState α S) {r : Nat × ExpandState α S}
    (h_result : expand node st = some r)
    (h_inv : StateInv st)
    (h_proc : ProcessingInv node) :
    StateInv r.2 := by
  revert h_inv h_proc
  apply expand.partial_correctness
    (motive := fun node st r => StateInv st → ProcessingInv node → StateInv r.2)
    _ node st r h_result
  intro expand_ih ih node st r h_result h_inv h_proc
  split at h_result
  case isTrue h_empty =>
    have h_new_nil : node.new = [] := by
      cases h : node.new with
      | nil => rfl
      | cons _ _ => rw [h] at h_empty; simp [List.isEmpty] at h_empty
    split at h_result
    · rename_i existingName _
      obtain rfl := Option.some.inj h_result
      exact mergeIncoming_stateInv st node existingName h_inv
    · simp only [freshName] at h_result
      have h_inv' : StateInv { st with nodes := st.nodes.insert node.name node } := by
        intro k n hk; simp only [Std.HashMap.getElem?_insert] at hk; split at hk
        · obtain rfl := Option.some.inj hk; exact ⟨h_proc, h_new_nil⟩
        · exact h_inv k n hk
      exact ih _ _ _ h_result h_inv' (processingInv_empty_old _ fun ψ => by
        simp [FSet.contains_empty])
  case isFalse h_not_empty =>
    simp only [Bool.not_eq_true] at h_not_empty
    simp only at h_result
    split at h_result
    · rename_i h_lit
      split at h_result
      · obtain rfl := Option.some.inj h_result; exact h_inv
      · rename_i h_no_neg
        simp only [Bool.not_eq_true] at h_no_neg
        exact ih _ _ _ h_result h_inv (processingInv_literal h_proc h_not_empty h_lit h_no_neg)
    · rename_i h_not_lit
      split at h_result <;> (try split at h_result) <;> (try split at h_result) <;>
        (try split at h_result) <;> (try split at h_result)
      all_goals (
        first
        | (obtain rfl := Option.some.inj h_result; exact h_inv)
        | exact ih _ _ _ h_result h_inv (processingInv_tt h_proc h_not_empty ‹_›)
        | exact ih _ _ _ h_result h_inv (processingInv_deterministic h_proc h_not_empty ‹_›)
        | simp_all)
      -- Nondet case remains
      rename_i _ _ h_nondet
      have h_ne : node.new.isEmpty = false := by
        simp only [List.isEmpty]; split <;> simp_all
      have h_nlit : isLiteral node.new.head! = false := by assumption
      have h_not_tt_prop : ¬ (node.new.head! matches .tt) := by
        intro hc; cases node.new.head! <;> simp_all [isLiteral]
      have h_not_ff_prop : ¬ (node.new.head! matches .ff) := by
        intro hc; cases node.new.head! <;> simp_all [isLiteral]
      simp only [Option.bind] at h_result
      split at h_result
      · simp at h_result
      · rename_i mid h_branch1
        obtain ⟨nm', st_mid⟩ := mid
        simp only [] at h_branch1 h_result
        have inv1 := ih _ _ _ _ h_branch1 h_inv
          (processingInv_nondet1 h_proc h_ne h_nondet h_nlit
            h_not_tt_prop h_not_ff_prop)
        exact ih _ _ _ _ h_result inv1
          (processingInv_nondet2 h_proc h_ne h_nondet h_nlit
            h_not_tt_prop h_not_ff_prop _)

/-! ## Bridge: ProcessingInv with new = [] implies ExpandSpec propagation -/

omit [Hashable (NNF α)] [BEq (NNF α)] [LawfulBEq (NNF α)] in
private theorem reachable_iff_old (n : ExpansionNode α S) (h : n.new = []) (ψ : NNF α) :
    n.reachable ψ ↔ n.oldHas ψ := by
  simp [ExpansionNode.reachable, h]

omit [Hashable (NNF α)] [BEq (NNF α)] [LawfulBEq (NNF α)] in
/-- Reverse lookup for mergeIncoming: every node in the merged state has a preimage in the original state with the
    same old/next. -/
private theorem mergeIncoming_reverse (st : ExpandState α S) (node : ExpansionNode α S) (targetName : Nat)
    (k : Nat) (n : ExpansionNode α S) (hk : (mergeIncoming st node targetName).nodes[k]? = some n) :
    ∃ (n' : ExpansionNode α S), st.nodes[k]? = some n' ∧
      (∀ ψ, FSet.contains n.old ψ ↔ FSet.contains n'.old ψ) ∧
      (∀ ψ, FSet.contains n.next ψ ↔ FSet.contains n'.next ψ) := by
  unfold mergeIncoming at hk; split at hk
  · rename_i target htarget
    simp only [Std.HashMap.getElem?_insert] at hk; split at hk
    · rename_i hk_eq
      have : k = targetName := by rw [beq_iff_eq] at hk_eq; exact hk_eq.symm
      subst this; obtain rfl := Option.some.inj hk
      exact ⟨target, htarget, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
    · exact ⟨n, hk, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  · exact ⟨n, hk, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem head!_mem_of_isEmpty_false {β} [Inhabited β] {l : List β}
    (h : l.isEmpty = false) : l.head! ∈ l := by
  cases l with | nil => simp at h | cons _ _ => exact .head _

theorem mem_of_mem_tail! {β} [Inhabited β] {l : List β} {ψ : β}
    (h : ψ ∈ l.tail!) : ψ ∈ l := by
  cases l with
  | nil => exact absurd h (by simp [List.tail!, default])
  | cons _ _ => exact .tail _ h

/-! ## Subformula closure -/

/-- Subformula closure: expand preserves the property that all formulas in old/next of finished nodes are
    subformulas of the top-level formula. -/
theorem expand_subformula_closure (φ_top : NNF α) (node : ExpansionNode α S) (st : ExpandState α S)
    {r : Nat × ExpandState α S}
    (h_result : expand node st = some r)
    (h_node_old : ∀ ψ, node.oldHas ψ → NNF.IsSubformula ψ φ_top)
    (h_node_new : ∀ ψ, ψ ∈ node.new → NNF.IsSubformula ψ φ_top)
    (h_node_next : ∀ ψ, node.nextHas ψ → NNF.IsSubformula ψ φ_top)
    (h_st_old : ∀ (k : Nat) (n : ExpansionNode α S), st.nodes[k]? = some n → ∀ ψ, FSet.contains n.old ψ → NNF.IsSubformula ψ φ_top)
    (h_st_next : ∀ (k : Nat) (n : ExpansionNode α S), st.nodes[k]? = some n → ∀ ψ, FSet.contains n.next ψ → NNF.IsSubformula ψ φ_top) :
    (∀ (k : Nat) (n : ExpansionNode α S), r.2.nodes[k]? = some n → ∀ ψ, FSet.contains n.old ψ → NNF.IsSubformula ψ φ_top) ∧
    (∀ (k : Nat) (n : ExpansionNode α S), r.2.nodes[k]? = some n → ∀ ψ, FSet.contains n.next ψ → NNF.IsSubformula ψ φ_top) := by
  revert h_node_old h_node_new h_node_next h_st_old h_st_next
  apply expand.partial_correctness
    (motive := fun node st r =>
      (∀ ψ, node.oldHas ψ → NNF.IsSubformula ψ φ_top) →
      (∀ ψ, ψ ∈ node.new → NNF.IsSubformula ψ φ_top) →
      (∀ ψ, node.nextHas ψ → NNF.IsSubformula ψ φ_top) →
      (∀ (k : Nat) (n : ExpansionNode α S), st.nodes[k]? = some n → ∀ ψ, FSet.contains n.old ψ → NNF.IsSubformula ψ φ_top) →
      (∀ (k : Nat) (n : ExpansionNode α S), st.nodes[k]? = some n → ∀ ψ, FSet.contains n.next ψ → NNF.IsSubformula ψ φ_top) →
      (∀ (k : Nat) (n : ExpansionNode α S), r.2.nodes[k]? = some n → ∀ ψ, FSet.contains n.old ψ → NNF.IsSubformula ψ φ_top) ∧
      (∀ (k : Nat) (n : ExpansionNode α S), r.2.nodes[k]? = some n → ∀ ψ, FSet.contains n.next ψ → NNF.IsSubformula ψ φ_top))
    _ node st r h_result
  intro expand_ih ih node st r h_result h_node_old h_node_new h_node_next h_st_old h_st_next
  have h_head_sub : node.new.isEmpty = false → NNF.IsSubformula node.new.head! φ_top :=
    fun hne => h_node_new _ (head!_mem_of_isEmpty_false hne)
  have h_tail_sub : ∀ ψ, ψ ∈ node.new.tail! → NNF.IsSubformula ψ φ_top :=
    fun _ hψ => h_node_new _ (mem_of_mem_tail! hψ)
  have h_old_insert_sub : node.new.isEmpty = false →
      ∀ ψ, FSet.contains (FSet.insert node.old node.new.head!) ψ = true → NNF.IsSubformula ψ φ_top := by
    intro hne ψ hψ; rcases oldHas_insert hψ with h1 | rfl
    · exact h_node_old _ h1
    · exact h_head_sub hne
  split at h_result
  case isTrue h_empty =>
    split at h_result
    · -- merge case: old/next unchanged (mergeIncoming_reverse)
      rename_i existingName _
      obtain rfl := Option.some.inj h_result
      exact ⟨fun k n hk ψ hψ => by
        obtain ⟨n', hn', hold, _⟩ := mergeIncoming_reverse st node existingName k n hk
        exact h_st_old k n' hn' ψ ((hold ψ).mp hψ),
      fun k n hk ψ hψ => by
        obtain ⟨n', hn', _, hnxt⟩ := mergeIncoming_reverse st node existingName k n hk
        exact h_st_next k n' hn' ψ ((hnxt ψ).mp hψ)⟩
    · -- insert + successor case
      simp only [freshName] at h_result
      -- After insert: state includes node
      have h_st_old' : ∀ (k : Nat) (n' : ExpansionNode α S), (st.nodes.insert node.name node)[k]? = some n' →
          ∀ ψ, FSet.contains n'.old ψ → NNF.IsSubformula ψ φ_top := by
        intro k n' hk ψ hψ
        simp only [Std.HashMap.getElem?_insert] at hk; split at hk
        · obtain rfl := Option.some.inj hk; exact h_node_old _ hψ
        · exact h_st_old _ _ hk _ hψ
      have h_st_next' : ∀ (k : Nat) (n' : ExpansionNode α S), (st.nodes.insert node.name node)[k]? = some n' →
          ∀ ψ, FSet.contains n'.next ψ → NNF.IsSubformula ψ φ_top := by
        intro k n' hk ψ hψ
        simp only [Std.HashMap.getElem?_insert] at hk; split at hk
        · obtain rfl := Option.some.inj hk; exact h_node_next _ hψ
        · exact h_st_next _ _ hk _ hψ
      -- Successor: old = ∅, next = ∅, new = node.next elements
      have h_succ_old : ∀ (ψ : NNF α),
          FSet.contains (FSet.empty : S) ψ → NNF.IsSubformula ψ φ_top := by
        intro ψ hψ; simp [FSet.contains_empty] at hψ
      have h_succ_new : ∀ ψ,
          ψ ∈ (nextToNew node.next) → NNF.IsSubformula ψ φ_top := by
        intro ψ hψ; exact h_node_next _ ((mem_nextToNew node.next ψ).mp hψ)
      have h_succ_next : ∀ (ψ : NNF α),
          FSet.contains (FSet.empty : S) ψ → NNF.IsSubformula ψ φ_top := by
        intro ψ hψ; simp [FSet.contains_empty] at hψ
      exact ih _ _ _ h_result h_succ_old h_succ_new h_succ_next h_st_old' h_st_next'
  case isFalse h_not_empty =>
    simp only [Bool.not_eq_true] at h_not_empty
    simp only at h_result
    have hne := h_not_empty
    split at h_result
    · -- literal
      rename_i h_lit
      split at h_result
      · -- contradiction: return st unchanged
        obtain rfl := Option.some.inj h_result
        exact ⟨h_st_old, h_st_next⟩
      · -- ok: recurse with old.insert
        exact ih _ _ _ h_result (h_old_insert_sub hne) h_tail_sub h_node_next h_st_old h_st_next
    · rename_i h_not_lit
      split at h_result <;> (try split at h_result) <;> (try split at h_result) <;>
        (try split at h_result) <;> (try split at h_result)
      all_goals (
        first
        | -- ff or contradiction: return st unchanged
          (obtain rfl := Option.some.inj h_result; exact ⟨h_st_old, h_st_next⟩)
        | -- tt or literal: recurse with old.insert
          exact ih _ _ _ h_result (h_old_insert_sub hne) h_tail_sub h_node_next h_st_old h_st_next
        | -- deterministic: recurse with old.insert, addToNew, addAllToSet
          (have h_φ_sub := h_head_sub hne
           exact ih _ _ _ h_result
            (h_old_insert_sub hne)
            (fun ψ hψ => by
              rcases addToNew_inv _ _ ψ hψ with h1 | h2
              · exact h_tail_sub _ h1
              · exact (new1_subformula h2).trans h_φ_sub)
            (fun ψ hψ => by
              rcases addAllToSet_inv _ _ ψ hψ with h1 | h2
              · exact h_node_next _ h1
              · exact (next1_subformula h2).trans h_φ_sub)
            h_st_old h_st_next)
        | -- contradictory cases from split
          contradiction
        | -- nondet: handled below
          skip)
      -- Nondet case
      rename_i h_nondet
      have h_φ_sub := h_head_sub hne
      simp only [bind, Option.bind] at h_result
      split at h_result
      · simp at h_result
      · rename_i mid h_branch1
        obtain ⟨nm', st_mid⟩ := mid
        simp only [] at h_branch1 h_result
        have ⟨h_mid_old, h_mid_next⟩ := ih _ _ _ h_branch1
          (h_old_insert_sub hne)
          (fun ψ hψ => by
            rcases addToNew_inv _ _ ψ hψ with h1 | h2
            · exact h_tail_sub _ h1
            · exact (new1_subformula h2).trans h_φ_sub)
          (fun ψ hψ => by
            rcases addAllToSet_inv _ _ ψ hψ with h1 | h2
            · exact h_node_next _ h1
            · exact (next1_subformula h2).trans h_φ_sub)
          h_st_old h_st_next
        exact ih _ _ _ h_result
          (h_old_insert_sub hne)
          (fun ψ hψ => by
            rcases addToNew_inv _ _ ψ hψ with h1 | h2
            · exact h_tail_sub _ h1
            · exact (new2_subformula h2).trans h_φ_sub)
          h_node_next
          h_mid_old h_mid_next

/-! ## findDuplicate spec -/

omit [BEq (NNF α)] [LawfulBEq (NNF α)] in
/-- `findDuplicate` returns the name of an existing node with the same signature as `node`. -/
theorem findDuplicate_spec (st : ExpandState α S) (node : ExpansionNode α S)
    (name : Nat) (h : findDuplicate st node = some name) :
    ∃ n, st.nodes[name]? = some n ∧ n.sameSignature node = true := by
  unfold findDuplicate at h
  have hp := List.find?_some h
  match hn : st.nodes[name]? with
  | some n => exact ⟨n, rfl, by rw [hn] at hp; exact hp⟩
  | none => rw [hn] at hp; exact absurd hp (by simp)

/-! ## IndexValid preservation -/

omit [BEq (NNF α)] [LawfulBEq (NNF α)] in
/-- `addNode` records the node in its own bucket, and only ever extends other buckets. -/
theorem indexValid_addNode {st : ExpandState α S} (node : ExpansionNode α S) (h : IndexValid st) :
    IndexValid (st.addNode node) := by
  intro k n hk
  simp only [ExpandState.addNode, Std.HashMap.getElem?_insert] at hk ⊢
  split at hk
  · next heq =>
    obtain rfl := (beq_iff_eq (α := Nat)).mp heq
    cases hk
    simp
  · next hne =>
    have hmem := h k n hk
    split
    · next heq =>
      rw [(beq_iff_eq (α := UInt64)).mp heq]
      exact List.mem_cons_of_mem _ hmem
    · exact hmem

omit [BEq (NNF α)] [LawfulBEq (NNF α)] in
/-- `mergeIncoming` only changes `incoming`, which `sigHash` ignores, so the index still describes the nodes. -/
theorem indexValid_mergeIncoming {st : ExpandState α S} (node : ExpansionNode α S) (targetName : Nat)
    (h : IndexValid st) : IndexValid (mergeIncoming st node targetName) := by
  unfold mergeIncoming; split
  · next target ht =>
    intro k n hk
    simp only [Std.HashMap.getElem?_insert] at hk
    split at hk
    · next heq =>
      obtain rfl := (beq_iff_eq (α := Nat)).mp heq
      cases hk
      exact h targetName target ht
    · exact h k n hk
  · exact h

omit [BEq (NNF α)] [LawfulBEq (NNF α)] in
/-- `expand` keeps the signature index valid, so every state it reaches can still be searched by bucket. -/
theorem expand_indexValid {node : ExpansionNode α S} {st : ExpandState α S}
    {r : Nat × ExpandState α S} (h : expand node st = some r) (hidx : IndexValid st) :
    IndexValid r.2 := by
  revert hidx
  apply expand.partial_correctness
    (motive := fun _node _st r => IndexValid _st → IndexValid r.2) _ _ _ _ h
  intro expand_ih ih node st r hr h_idx
  split at hr
  case isTrue h_empty =>
    split at hr
    · obtain rfl := Option.some.inj hr
      exact indexValid_mergeIncoming _ _ h_idx
    · simp only [freshName] at hr
      exact ih _ _ _ hr (indexValid_addNode node h_idx)
  case isFalse h_not_empty =>
    simp only [Bool.not_eq_true] at h_not_empty
    simp only at hr
    split at hr
    · split at hr
      · obtain rfl := Option.some.inj hr; exact h_idx
      · exact ih _ _ _ hr h_idx
    · rename_i h_not_lit
      split at hr <;> (try split at hr) <;> (try split at hr) <;>
        (try split at hr) <;> (try split at hr)
      all_goals (first
        | (obtain rfl := Option.some.inj hr; exact h_idx)
        | exact ih _ _ _ hr h_idx
        | simp_all)
      rename_i _ _ h_nondet
      revert hr; intro hr
      cases h_branch1 : expand_ih
          { name := node.name, incoming := node.incoming,
            new := addToNew
              { name := node.name, incoming := node.incoming, new := node.new.tail!,
                old := node.old, next := node.next }
              (new1 node.new.head!),
            old := FSet.insert node.old node.new.head!,
            next := addAllToSet node.next (next1 node.new.head!) }
          st with
      | none => simp [h_branch1] at hr
      | some mid =>
        obtain ⟨nm', st_mid⟩ := mid
        simp only [h_branch1, Option.bind] at hr
        have h1 := ih _ _ nm' st_mid h_branch1 h_idx
        exact ih _ _ _ _ hr h1

/-! ## mergeIncoming incoming membership -/

private theorem foldl_insert_contains {l : List Nat} {base : Std.HashSet Nat} {j : Nat}
    (h : (List.foldl Std.HashSet.insert base l).contains j = true) :
    base.contains j = true ∨ j ∈ l := by
  induction l generalizing base with
  | nil => exact Or.inl h
  | cons y ys ih =>
    rcases ih h with h | h
    · rw [Std.HashSet.contains_insert] at h
      rcases Bool.or_eq_true_iff.mp h with heq | h
      · rw [beq_iff_eq] at heq; exact Or.inr (heq ▸ .head _)
      · exact Or.inl h
    · exact Or.inr (.tail _ h)

omit [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem mergeIncoming_incoming (st : ExpandState α S) (node : ExpansionNode α S)
    (targetName k j : Nat) (n : ExpansionNode α S)
    (hk : (mergeIncoming st node targetName).nodes[k]? = some n)
    (hj : n.incoming.contains j = true) :
    (∃ n', st.nodes[k]? = some n' ∧ n'.incoming.contains j = true) ∨
    (k = targetName ∧ node.incoming.contains j = true) := by
  unfold mergeIncoming at hk; split at hk
  · rename_i target htarget
    simp only [Std.HashMap.getElem?_insert] at hk; split at hk
    · rename_i hk_eq
      have hkeq : k = targetName := by rw [beq_iff_eq] at hk_eq; exact hk_eq.symm
      subst hkeq; obtain rfl := Option.some.inj hk
      by_cases h : target.incoming.contains j
      · exact Or.inl ⟨target, htarget, h⟩
      · right; constructor
        · rfl
        · by_contra h2
          simp only [Bool.not_eq_true] at h h2
          -- j is in neither target's nor node's incoming set, contradicting hj.
          simp [Std.HashSet.union_eq, h, h2] at hj
    · exact Or.inl ⟨n, hk, hj⟩
  · exact Or.inl ⟨n, hk, hj⟩

/-! ## Initial old -/

/-- Expand preserves the property that nodes with expandInit in incoming contain φ in old. -/
theorem expand_initial_old (φ_top : NNF α) (node : ExpansionNode α S) (st : ExpandState α S)
    {r : Nat × ExpandState α S}
    (h_result : expand node st = some r)
    (h_node_init : node.incoming.contains expandInit →
      node.oldHas φ_top ∨ φ_top ∈ node.new)
    (h_st_init : ∀ (k : Nat) (n : ExpansionNode α S), st.nodes[k]? = some n →
      n.incoming.contains expandInit → FSet.contains n.old φ_top)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName)
    (h_name_ne : node.name ≠ expandInit) :
    (∀ (k : Nat) (n : ExpansionNode α S), r.2.nodes[k]? = some n →
      n.incoming.contains expandInit → FSet.contains n.old φ_top) ∧
    r.1 ≠ expandInit ∧
    r.2.nodes[r.1]? = none ∧
    (∀ k, r.2.nodes[k]? ≠ none → k < r.2.nextName) ∧
    r.1 < r.2.nextName := by
  revert h_node_init h_st_init h_not_in h_fresh h_name h_name_ne
  apply expand.partial_correctness
    (motive := fun node st r =>
      (node.incoming.contains expandInit →
        node.oldHas φ_top ∨ φ_top ∈ node.new) →
      (∀ (k : Nat) (n : ExpansionNode α S), st.nodes[k]? = some n →
        n.incoming.contains expandInit → FSet.contains n.old φ_top) →
      st.nodes[node.name]? = none →
      (∀ k, st.nodes[k]? ≠ none → k < st.nextName) →
      node.name < st.nextName →
      node.name ≠ expandInit →
      (∀ (k : Nat) (n : ExpansionNode α S), r.2.nodes[k]? = some n →
        n.incoming.contains expandInit → FSet.contains n.old φ_top) ∧
      r.1 ≠ expandInit ∧
      r.2.nodes[r.1]? = none ∧
      (∀ k, r.2.nodes[k]? ≠ none → k < r.2.nextName) ∧
      r.1 < r.2.nextName)
    _ node st r h_result
  intro expand_ih ih node st r h_result h_node_init h_st_init h_not_in h_fresh h_name h_name_ne
  -- Helper: when popping head from new and inserting into old, init condition is preserved
  have h_init_preserved : node.new.isEmpty = false →
      ∀ (new' : List (NNF α)), (∀ ψ, ψ ∈ node.new.tail! → ψ ∈ new') →
      node.incoming.contains expandInit →
      FSet.contains (FSet.insert node.old node.new.head!) φ_top = true ∨ φ_top ∈ new' := by
    intro hne new' hsub hinc
    rcases h_node_init hinc with hold | hnew
    · exact Or.inl (old_subset_insert node.old _ φ_top hold)
    · rcases mem_head_or_tail' hne rfl hnew with rfl | htail
      · exact Or.inl (mem_insert_self' node.old _)
      · exact Or.inr (hsub _ htail)
  split at h_result
  case isTrue h_empty =>
    have h_new_nil : node.new = [] := by
      cases h : node.new with
      | nil => rfl
      | cons _ _ => rw [h] at h_empty; simp [List.isEmpty] at h_empty
    generalize h_fd : findDuplicate st node = fd at h_result
    cases fd with
    | some existingName =>
      obtain rfl := Option.some.inj h_result
      refine ⟨fun k n hk hj => ?_, h_name_ne,
              mergeIncoming_preserves_absent st node existingName _ h_not_in,
              mergeIncoming_freshInv st node existingName h_fresh,
              by rw [mergeIncoming_nextName]; exact h_name⟩
      rcases mergeIncoming_incoming st node existingName k expandInit n hk hj with
        ⟨n', hn', hj'⟩ | ⟨hk_eq, hj'⟩
      · obtain ⟨n'', hn'', hold, _⟩ := mergeIncoming_reverse st node existingName k n hk
        rw [hn'] at hn''; obtain rfl := Option.some.inj hn''
        exact (hold φ_top).mpr (h_st_init k n' hn' hj')
      · have hφ := h_node_init hj'
        rw [h_new_nil] at hφ
        rcases hφ with hφ | hφ
        · obtain ⟨target, htarget, hsig⟩ := findDuplicate_spec st node existingName h_fd
          have hφ_target := ExpansionNode.sameSignature_old_left target node hsig φ_top hφ
          rw [hk_eq] at hk
          obtain ⟨n', hn', hold, _⟩ := mergeIncoming_reverse st node existingName existingName n hk
          rw [htarget] at hn'; obtain rfl := Option.some.inj hn'
          exact (hold φ_top).mpr hφ_target
        · exact absurd hφ (by simp)
    | none =>
      -- Insert + successor
      simp only [freshName] at h_result
      have h_st_init' : ∀ (k : Nat) (n : ExpansionNode α S),
          (st.nodes.insert node.name node)[k]? = some n →
          n.incoming.contains expandInit → FSet.contains n.old φ_top := by
        intro k n hk hj
        simp only [Std.HashMap.getElem?_insert] at hk; split at hk
        · obtain rfl := Option.some.inj hk
          rcases h_node_init hj with hφ | hφ
          · exact hφ
          · rw [h_new_nil] at hφ; exact absurd hφ (by simp)
        · exact h_st_init k n hk hj
      have h_succ_ne : st.nextName ≠ expandInit := by unfold expandInit; omega
      exact ih _ _ _ h_result
        (fun hc => by
          simp [Std.HashSet.contains_insert, Std.HashSet.contains_emptyWithCapacity] at hc
          exact absurd hc h_name_ne)
        h_st_init'
        (insert_fresh_key st node.name node h_fresh h_name)
        (insert_freshInv st node.name node h_fresh h_name)
        (by show st.nextName < st.nextName + 1; omega) h_succ_ne
  case isFalse h_not_empty =>
    simp only [Bool.not_eq_true] at h_not_empty
    simp only at h_result
    split at h_result
    · -- literal
      split at h_result
      · -- contradiction
        obtain rfl := Option.some.inj h_result
        exact ⟨h_st_init, h_name_ne, h_not_in, h_fresh, h_name⟩
      · -- insert literal
        exact ih _ _ _ h_result (h_init_preserved h_not_empty _ fun ψ hψ => hψ)
          h_st_init h_not_in h_fresh h_name h_name_ne
    · rename_i h_not_lit
      split at h_result <;> (try split at h_result) <;> (try split at h_result) <;>
        (try split at h_result) <;> (try split at h_result)
      all_goals (
        first
        | -- ff/contradiction: return unchanged
          (obtain rfl := Option.some.inj h_result;
           exact ⟨h_st_init, h_name_ne, h_not_in, h_fresh, h_name⟩)
        | -- tt: recurse with tail!
          exact ih _ _ _ h_result (h_init_preserved h_not_empty _ fun ψ hψ => hψ)
            h_st_init h_not_in h_fresh h_name h_name_ne
        | -- deterministic: recurse with addToNew preserving tail
          exact ih _ _ _ h_result
            (h_init_preserved h_not_empty _ fun ψ hψ => addToNew_preserves _ _ ψ hψ)
            h_st_init h_not_in h_fresh h_name h_name_ne
        | contradiction
        | skip)
      -- Nondet case
      rename_i h_nondet
      simp only [bind, Option.bind] at h_result
      split at h_result
      · simp at h_result
      · rename_i mid h_branch1
        obtain ⟨nm', st_mid⟩ := mid
        simp only [] at h_branch1 h_result
        have ⟨h_mid_init, h_mid_ne, h_mid_not_in, h_mid_fresh, h_mid_bound⟩ :=
          ih _ _ _ h_branch1
            (h_init_preserved h_not_empty _ fun ψ hψ => addToNew_preserves _ _ ψ hψ)
            h_st_init h_not_in h_fresh h_name h_name_ne
        exact ih _ _ _ h_result
          (h_init_preserved h_not_empty _ fun ψ hψ => addToNew_preserves _ _ ψ hψ)
          h_mid_init h_mid_not_in h_mid_fresh h_mid_bound h_mid_ne

/-! ## Successor old -/

/-- Expand preserves the successor_old property: for finished nodes, predecessors' next ⊆ node's old. -/
theorem expand_successor_old (node : ExpansionNode α S) (st : ExpandState α S)
    {r : Nat × ExpandState α S}
    (h_result : expand node st = some r)
    (h_st_succ : ∀ (k : Nat) (n : ExpansionNode α S), st.nodes[k]? = some n →
      ∀ k', k' ≠ expandInit → n.incoming.contains k' →
      ∃ (n' : ExpansionNode α S), st.nodes[k']? = some n' ∧ ∀ ψ, FSet.contains n'.next ψ → FSet.contains n.old ψ)
    (h_node_succ : ∀ k', k' ≠ expandInit → node.incoming.contains k' →
      ∃ (n' : ExpansionNode α S), st.nodes[k']? = some n' ∧ ∀ ψ, FSet.contains n'.next ψ → node.oldHas ψ ∨ ψ ∈ node.new)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName)
    (h_name_ne : node.name ≠ expandInit) :
    (∀ (k : Nat) (n : ExpansionNode α S), r.2.nodes[k]? = some n →
      ∀ k', k' ≠ expandInit → n.incoming.contains k' →
      ∃ (n' : ExpansionNode α S), r.2.nodes[k']? = some n' ∧ ∀ ψ, FSet.contains n'.next ψ → FSet.contains n.old ψ) ∧
    NodesPreserved st r.2 ∧
    r.2.nodes[r.1]? = none ∧
    (∀ k, r.2.nodes[k]? ≠ none → k < r.2.nextName) ∧
    r.1 < r.2.nextName ∧
    r.1 ≠ expandInit := by
  revert h_st_succ h_node_succ h_not_in h_fresh h_name h_name_ne
  apply expand.partial_correctness
    (motive := fun node st r =>
      (∀ (k : Nat) (n : ExpansionNode α S), st.nodes[k]? = some n →
        ∀ k', k' ≠ expandInit → n.incoming.contains k' →
        ∃ (n' : ExpansionNode α S), st.nodes[k']? = some n' ∧ ∀ ψ, FSet.contains n'.next ψ → FSet.contains n.old ψ) →
      (∀ k', k' ≠ expandInit → node.incoming.contains k' →
        ∃ (n' : ExpansionNode α S), st.nodes[k']? = some n' ∧ ∀ ψ, FSet.contains n'.next ψ → node.oldHas ψ ∨ ψ ∈ node.new) →
      st.nodes[node.name]? = none →
      (∀ k, st.nodes[k]? ≠ none → k < st.nextName) →
      node.name < st.nextName →
      node.name ≠ expandInit →
      (∀ (k : Nat) (n : ExpansionNode α S), r.2.nodes[k]? = some n →
        ∀ k', k' ≠ expandInit → n.incoming.contains k' →
        ∃ (n' : ExpansionNode α S), r.2.nodes[k']? = some n' ∧ ∀ ψ, FSet.contains n'.next ψ → FSet.contains n.old ψ) ∧
      NodesPreserved st r.2 ∧
      r.2.nodes[r.1]? = none ∧
      (∀ k, r.2.nodes[k]? ≠ none → k < r.2.nextName) ∧
      r.1 < r.2.nextName ∧
      r.1 ≠ expandInit)
    _ node st r h_result
  intro expand_ih ih node st r h_result h_st_succ h_node_succ h_not_in h_fresh h_name h_name_ne
  -- Helper: node_succ condition is preserved when popping head and inserting into old
  have h_node_succ_preserved : node.new.isEmpty = false →
      ∀ (new' : List (NNF α)), (∀ ψ, ψ ∈ node.new.tail! → ψ ∈ new') →
      ∀ k', k' ≠ expandInit → node.incoming.contains k' →
        ∃ (n' : ExpansionNode α S), st.nodes[k']? = some n' ∧
        ∀ ψ, FSet.contains n'.next ψ → FSet.contains (FSet.insert node.old node.new.head!) ψ = true ∨ ψ ∈ new' := by
    intro hne new' hsub k' hk'_ne hk'
    obtain ⟨n', hn', hpred⟩ := h_node_succ k' hk'_ne hk'
    exact ⟨n', hn', fun ψ hψ => by
      rcases hpred ψ hψ with hold | hnew
      · exact Or.inl (old_subset_insert node.old _ ψ hold)
      · rcases mem_head_or_tail' hne rfl hnew with rfl | htail
        · exact Or.inl (mem_insert_self' node.old _)
        · exact Or.inr (hsub _ htail)⟩
  split at h_result
  case isTrue h_empty =>
    have h_new_nil : node.new = [] := by
      cases h : node.new with
      | nil => rfl
      | cons _ _ => rw [h] at h_empty; simp [List.isEmpty] at h_empty
    generalize h_fd : findDuplicate st node = fd at h_result
    cases fd with
    | some existingName =>
      -- Merge case
      obtain rfl := Option.some.inj h_result
      refine ⟨fun k n hk k' hk'_ne hk' => ?_,
              mergeIncoming_nodesPreserved st node existingName,
              mergeIncoming_preserves_absent st node existingName _ h_not_in,
              mergeIncoming_freshInv st node existingName h_fresh,
              by rw [mergeIncoming_nextName]; exact h_name,
              h_name_ne⟩
      rcases mergeIncoming_incoming st node existingName k k' n hk hk' with
        ⟨n', hn', hj'⟩ | ⟨hk_eq, hj'⟩
      · -- k' was already in n'.incoming in st
        obtain ⟨pred, hpred, hpred_next⟩ := h_st_succ k n' hn' k' hk'_ne hj'
        obtain ⟨n'', hn'', hold, _⟩ := mergeIncoming_reverse st node existingName k n hk
        rw [hn'] at hn''; obtain rfl := Option.some.inj hn''
        obtain ⟨pred', hpred', _, hpred_nxt'⟩ := mergeIncoming_nodesPreserved st node existingName k' pred hpred
        exact ⟨pred', hpred', fun ψ hψ =>
          (hold ψ).mpr (hpred_next ψ ((hpred_nxt' ψ).mp hψ))⟩
      · -- k = existingName, k' came from node.incoming
        rw [hk_eq] at hk
        obtain ⟨pred, hpred, hpred_next⟩ := h_node_succ k' hk'_ne hj'
        rw [h_new_nil] at hpred_next
        obtain ⟨target, htarget, hsig⟩ := findDuplicate_spec st node existingName h_fd
        obtain ⟨n'', hn'', hold, _⟩ := mergeIncoming_reverse st node existingName existingName n hk
        rw [htarget] at hn''; obtain rfl := Option.some.inj hn''
        obtain ⟨pred', hpred', _, hpred_nxt'⟩ := mergeIncoming_nodesPreserved st node existingName k' pred hpred
        exact ⟨pred', hpred', fun ψ hψ => by
          rcases hpred_next ψ ((hpred_nxt' ψ).mp hψ) with hold' | hmem
          · exact (hold ψ).mpr (ExpansionNode.sameSignature_old_left target node hsig ψ hold')
          · exact absurd hmem (by simp)⟩
    | none =>
      -- Insert + successor case
      simp only [freshName] at h_result
      have h_st_succ' : ∀ (k : Nat) (n : ExpansionNode α S),
          (st.nodes.insert node.name node)[k]? = some n →
          ∀ k', k' ≠ expandInit → n.incoming.contains k' →
          ∃ (n' : ExpansionNode α S), (st.nodes.insert node.name node)[k']? = some n' ∧
          ∀ ψ, FSet.contains n'.next ψ → FSet.contains n.old ψ := by
        intro k n hk k' hk'_ne hk'
        simp only [Std.HashMap.getElem?_insert] at hk ⊢; split at hk
        · -- k = node.name, n = node
          obtain rfl := Option.some.inj hk
          obtain ⟨pred, hpred, hpred_next⟩ := h_node_succ k' hk'_ne hk'
          rw [h_new_nil] at hpred_next
          have hne : k' ≠ node.name := fun heq => by rw [heq] at hpred; simp [h_not_in] at hpred
          split
          · rename_i heq; exact absurd ((beq_iff_eq (α := Nat)).mp heq).symm hne
          · exact ⟨pred, hpred, fun ψ hψ => by
              rcases hpred_next ψ hψ with h | h
              · exact h
              · exact absurd h (by simp)⟩
        · -- k ≠ node.name, n from original st
          rename_i hne_k
          obtain ⟨pred, hpred, hpred_next⟩ := h_st_succ k n hk k' hk'_ne hk'
          have hne : k' ≠ node.name := fun heq => by rw [heq] at hpred; simp [h_not_in] at hpred
          split
          · rename_i heq; exact absurd ((beq_iff_eq (α := Nat)).mp heq).symm hne
          · exact ⟨pred, hpred, hpred_next⟩
      have h_succ_node_succ : ∀ k', k' ≠ expandInit →
          (Std.HashSet.emptyWithCapacity 4 |>.insert node.name : Std.HashSet Nat).contains k' →
          ∃ (n' : ExpansionNode α S), (st.nodes.insert node.name node)[k']? = some n' ∧
          ∀ ψ, FSet.contains n'.next ψ →
            FSet.contains (FSet.empty : S) ψ ∨
            ψ ∈ nextToNew node.next := by
        intro k' _ hk'
        rw [Std.HashSet.contains_insert, Std.HashSet.contains_emptyWithCapacity, Bool.or_false,
            beq_iff_eq] at hk'
        subst hk'
        simp only [Std.HashMap.getElem?_insert, beq_self_eq_true, ↓reduceIte]
        exact ⟨node, rfl, fun ψ hψ => Or.inr ((mem_nextToNew _ ψ).mpr hψ)⟩
      have h_succ_ne : st.nextName ≠ expandInit := by unfold expandInit; omega
      have ⟨h1, h2, h3, h4, h5, h6⟩ := ih _ _ _ h_result h_st_succ' h_succ_node_succ
        (insert_fresh_key st node.name node h_fresh h_name)
        (insert_freshInv st node.name node h_fresh h_name)
        (by show st.nextName < st.nextName + 1; omega)
        h_succ_ne
      exact ⟨h1, NodesPreserved_trans (insert_nodesPreserved st node h_not_in) h2, h3, h4, h5, h6⟩
  case isFalse h_not_empty =>
    simp only [Bool.not_eq_true] at h_not_empty
    simp only at h_result
    split at h_result
    · -- literal
      split at h_result
      · -- contradiction
        obtain rfl := Option.some.inj h_result
        exact ⟨h_st_succ, NodesPreserved_refl st, h_not_in, h_fresh, h_name, h_name_ne⟩
      · -- insert literal
        exact ih _ _ _ h_result h_st_succ
          (h_node_succ_preserved h_not_empty _ fun ψ hψ => hψ)
          h_not_in h_fresh h_name h_name_ne
    · rename_i h_not_lit
      split at h_result <;> (try split at h_result) <;> (try split at h_result) <;>
        (try split at h_result) <;> (try split at h_result)
      all_goals (
        first
        | -- ff/contradiction: return unchanged
          (obtain rfl := Option.some.inj h_result;
           exact ⟨h_st_succ, NodesPreserved_refl st, h_not_in, h_fresh, h_name, h_name_ne⟩)
        | -- tt: recurse with tail!
          exact ih _ _ _ h_result h_st_succ
            (h_node_succ_preserved h_not_empty _ fun ψ hψ => hψ)
            h_not_in h_fresh h_name h_name_ne
        | -- deterministic: recurse with addToNew preserving tail
          exact ih _ _ _ h_result h_st_succ
            (h_node_succ_preserved h_not_empty _ fun ψ hψ => addToNew_preserves _ _ ψ hψ)
            h_not_in h_fresh h_name h_name_ne
        | contradiction
        | skip)
      -- Nondet case
      rename_i h_nondet
      simp only [bind, Option.bind] at h_result
      split at h_result
      · simp at h_result
      · rename_i mid h_branch1
        obtain ⟨nm', st_mid⟩ := mid
        simp only [] at h_branch1 h_result
        have ⟨h_mid_succ, h_mid_np, h_mid_not_in, h_mid_fresh, h_mid_bound, h_mid_ne⟩ :=
          ih _ _ _ h_branch1 h_st_succ
            (h_node_succ_preserved h_not_empty _ fun ψ hψ => addToNew_preserves _ _ ψ hψ)
            h_not_in h_fresh h_name h_name_ne
        -- Lift h_node_succ for branch2 using NodesPreserved st st_mid
        have h_node_succ2 : ∀ k', k' ≠ expandInit → node.incoming.contains k' →
            ∃ (n' : ExpansionNode α S), st_mid.nodes[k']? = some n' ∧
            ∀ ψ, FSet.contains n'.next ψ → FSet.contains (FSet.insert node.old node.new.head!) ψ = true ∨
            ψ ∈ addToNew { node with new := node.new.tail! } (new2 node.new.head!) := by
          intro k' hk'_ne hk'
          obtain ⟨pred, hpred, hpred_next⟩ := h_node_succ k' hk'_ne hk'
          obtain ⟨pred', hpred', _, hpred_nxt'⟩ := h_mid_np k' pred hpred
          exact ⟨pred', hpred', fun ψ hψ => by
            rcases hpred_next ψ ((hpred_nxt' ψ).mp hψ) with hold | hnew
            · exact Or.inl (old_subset_insert node.old _ ψ hold)
            · rcases mem_head_or_tail' h_not_empty rfl hnew with rfl | htail
              · exact Or.inl (mem_insert_self' node.old _)
              · exact Or.inr (addToNew_preserves _ _ _ htail)⟩
        have ⟨h_final_succ, h_final_np, h_final_not_in, h_final_fresh, h_final_bound, h_final_ne⟩ :=
          ih _ _ _ h_result h_mid_succ h_node_succ2
            h_mid_not_in h_mid_fresh h_mid_bound h_mid_ne
        exact ⟨h_final_succ, NodesPreserved_trans h_mid_np h_final_np,
               h_final_not_in, h_final_fresh, h_final_bound, h_final_ne⟩

/-! ## No expandInit key -/

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [FSet (NNF α) S] [Hashable (NNF α)] in
private theorem mergeIncoming_keys_subset (st : ExpandState α S) (node : ExpansionNode α S)
    (targetName : Nat) (k : Nat) (hk : (mergeIncoming st node targetName).nodes[k]? ≠ none) :
    st.nodes[k]? ≠ none := by
  unfold mergeIncoming at hk; split at hk
  · rename_i target htarget
    simp only [Std.HashMap.getElem?_insert] at hk; split at hk
    · rename_i heq; rw [← (beq_iff_eq (α := Nat)).mp heq]; simp [htarget]
    · exact hk
  · exact hk

omit [BEq (NNF α)] [LawfulBEq (NNF α)] in
private theorem expand_no_init_key (node : ExpansionNode α S) (st : ExpandState α S)
    {r : Nat × ExpandState α S}
    (h_result : expand node st = some r)
    (h_st_keys : ∀ k, st.nodes[k]? ≠ none → k ≠ expandInit)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName)
    (h_name_ne : node.name ≠ expandInit) :
    (∀ k, r.2.nodes[k]? ≠ none → k ≠ expandInit) ∧
    r.2.nodes[r.1]? = none ∧
    (∀ k, r.2.nodes[k]? ≠ none → k < r.2.nextName) ∧
    r.1 < r.2.nextName ∧
    r.1 ≠ expandInit := by
  revert h_st_keys h_not_in h_fresh h_name h_name_ne
  apply expand.partial_correctness
    (motive := fun node st r =>
      (∀ k, st.nodes[k]? ≠ none → k ≠ expandInit) →
      st.nodes[node.name]? = none →
      (∀ k, st.nodes[k]? ≠ none → k < st.nextName) →
      node.name < st.nextName →
      node.name ≠ expandInit →
      (∀ k, r.2.nodes[k]? ≠ none → k ≠ expandInit) ∧
      r.2.nodes[r.1]? = none ∧
      (∀ k, r.2.nodes[k]? ≠ none → k < r.2.nextName) ∧
      r.1 < r.2.nextName ∧
      r.1 ≠ expandInit)
    _ node st r h_result
  intro expand_ih ih node st r h_result h_st_keys h_not_in h_fresh h_name h_name_ne
  split at h_result
  case isTrue h_empty =>
    split at h_result
    · -- merge
      rename_i existingName _
      obtain rfl := Option.some.inj h_result
      exact ⟨fun k hk => h_st_keys k (mergeIncoming_keys_subset st node existingName k hk),
             mergeIncoming_preserves_absent st node existingName _ h_not_in,
             mergeIncoming_freshInv st node existingName h_fresh,
             by rw [mergeIncoming_nextName]; exact h_name,
             h_name_ne⟩
    · -- insert + successor
      simp only [freshName] at h_result
      have h_insert_keys : ∀ k, (st.nodes.insert node.name node)[k]? ≠ none → k ≠ expandInit := by
        intro k hk
        simp only [Std.HashMap.getElem?_insert] at hk; split at hk
        · rename_i heq; exact (beq_iff_eq (α := Nat)).mp heq ▸ h_name_ne
        · exact h_st_keys k hk
      have h_succ_ne : st.nextName ≠ expandInit := by unfold expandInit; omega
      have ⟨h1, h2, h3, h4, h5⟩ := ih _ _ _ h_result h_insert_keys
        (insert_fresh_key st node.name node h_fresh h_name)
        (insert_freshInv st node.name node h_fresh h_name)
        (by show st.nextName < st.nextName + 1; omega)
        h_succ_ne
      exact ⟨h1, h2, h3, h4, h5⟩
  case isFalse h_not_empty =>
    simp only [Bool.not_eq_true] at h_not_empty; simp only at h_result
    split at h_result
    · -- literal
      split at h_result
      · obtain rfl := Option.some.inj h_result
        exact ⟨h_st_keys, h_not_in, h_fresh, h_name, h_name_ne⟩
      · exact ih _ _ _ h_result h_st_keys h_not_in h_fresh h_name h_name_ne
    · split at h_result <;> (try split at h_result) <;> (try split at h_result) <;>
        (try split at h_result) <;> (try split at h_result)
      all_goals (
        first
        | (obtain rfl := Option.some.inj h_result;
           exact ⟨h_st_keys, h_not_in, h_fresh, h_name, h_name_ne⟩)
        | exact ih _ _ _ h_result h_st_keys h_not_in h_fresh h_name h_name_ne
        | (simp only [Bind.bind, Option.bind] at h_result
           split at h_result
           · simp at h_result
           · rename_i h_branch1
             have ⟨h1a, h1b, h1c, h1d, h1e⟩ := ih _ _ _ h_branch1 h_st_keys
               h_not_in h_fresh h_name h_name_ne
             exact ih _ _ _ h_result h1a h1b h1c h1d h1e))

/-! ## Main correctness theorem

The output of `createGraph` satisfies `ExpandSpec`. -/

/-- The concrete `createGraph φ` output satisfies the abstract `ExpandSpec φ`: its nodes are propagation-consistent,
    stay within the subformula closure of `φ`, and correctly track successor/initial-old membership. -/
theorem createGraph_spec (φ : NNF α) {st : ExpandState α S}
    (h : createGraph φ = some st) :
    ExpandSpec φ st.toNodes := by
  simp only [createGraph] at h
  split at h
  · -- some case: expand succeeded
    rename_i nm finalState heq
    obtain rfl := Option.some.inj h
    -- Initial state satisfies StateInv (no nodes)
    have h_initStateInv : StateInv
        { nextName := 2, nodes := Std.HashMap.emptyWithCapacity 16,
          index := Std.HashMap.emptyWithCapacity 16 : ExpandState α S } := by
      intro k n hk; simp at hk
    -- Initial node satisfies ProcessingInv (old is empty)
    have h_initProcInv : ProcessingInv
        ({ name := 1,
           incoming := Std.HashSet.emptyWithCapacity 4 |>.insert expandInit,
           new := [φ],
           old := FSet.empty,
           next := FSet.empty } : ExpansionNode α S) := by
      constructor <;> simp (config := { contextual := true }) [ExpansionNode.oldHas, ExpansionNode.reachable,
        ExpansionNode.nextHas, FSet.contains_empty]
    -- Get StateInv for final state
    have h_stateInv : StateInv finalState :=
      expand_preserves_stateInv _ _ heq h_initStateInv h_initProcInv
    -- Helper: extract ProcessingInv from StateInv for any node in toNodes
    have bridge : ∀ q, finalState.toNodes q →
        ∃ n, finalState.nodes[q.name]? = some n ∧
          (∀ k, q.incoming k ↔ n.incoming.contains k) ∧
          (∀ ψ, q.old ψ ↔ FSet.contains n.old ψ) ∧
          (∀ ψ, q.next ψ ↔ FSet.contains n.next ψ) ∧
          ProcessingInv n ∧ n.new = [] := by
      intro q ⟨n, hn, hinc, hold, hnxt⟩
      have ⟨pi, hnil⟩ := h_stateInv _ _ hn
      exact ⟨n, hn, hinc, hold, hnxt, pi, hnil⟩
    exact {
      literal_consistent := by
        intro q hq a ha_prop ha_nprop
        obtain ⟨n, _, _, hold, _, pi, _⟩ := bridge q hq
        exact pi.literal_consistent a ((hold _).mp ha_prop) ((hold _).mp ha_nprop)
      no_false := by
        intro q hq hff
        obtain ⟨n, _, _, hold, _, pi, _⟩ := bridge q hq
        exact pi.no_false ((hold _).mp hff)
      and_propag := by
        intro q hq μ ψ ha
        obtain ⟨n, _, _, hold, _, pi, hnil⟩ := bridge q hq
        have := pi.and_propag μ ψ ((hold _).mp ha)
        exact ⟨(hold _).mpr ((reachable_iff_old n hnil μ).mp this.1),
               (hold _).mpr ((reachable_iff_old n hnil ψ).mp this.2)⟩
      or_propag := by
        intro q hq μ ψ ha
        obtain ⟨n, _, _, hold, _, pi, hnil⟩ := bridge q hq
        have := pi.or_propag μ ψ ((hold _).mp ha)
        exact this.imp (fun h => (hold _).mpr ((reachable_iff_old n hnil μ).mp h))
                       (fun h => (hold _).mpr ((reachable_iff_old n hnil ψ).mp h))
      next_propag := by
        intro q hq ψ ha
        obtain ⟨n, _, _, hold, hnxt, pi, _⟩ := bridge q hq
        exact (hnxt _).mpr (pi.next_propag ψ ((hold _).mp ha))
      until_propag := by
        intro q hq μ ψ ha
        obtain ⟨n, _, _, hold, hnxt, pi, hnil⟩ := bridge q hq
        have := pi.until_propag μ ψ ((hold _).mp ha)
        exact this.imp
          (fun h => (hold _).mpr ((reachable_iff_old n hnil ψ).mp h))
          (fun ⟨h1, h2⟩ => ⟨(hold _).mpr ((reachable_iff_old n hnil μ).mp h1),
                             (hnxt _).mpr h2⟩)
      release_propag := by
        intro q hq μ ψ ha
        obtain ⟨n, _, _, hold, hnxt, pi, hnil⟩ := bridge q hq
        have := pi.release_propag μ ψ ((hold _).mp ha)
        exact ⟨(hold _).mpr ((reachable_iff_old n hnil ψ).mp this.1),
               this.2.imp (fun h => (hold _).mpr ((reachable_iff_old n hnil μ).mp h))
                          (fun h => (hnxt _).mpr h)⟩
      old_subformula := by
        have ⟨h_old, _⟩ := expand_subformula_closure φ _ _ heq
          (fun ψ hψ => by simp [ExpansionNode.oldHas, FSet.contains_empty] at hψ)
          (fun ψ hψ => by cases hψ with | head => exact .refl | tail _ h => exact nomatch h)
          (fun ψ hψ => by simp [ExpansionNode.nextHas, FSet.contains_empty] at hψ)
          (fun k n hk => by simp at hk)
          (fun k n hk => by simp at hk)
        intro q hq ψ hψ
        obtain ⟨n, hn, _, hold, _⟩ := bridge q hq
        exact h_old _ _ hn _ ((hold _).mp hψ)
      next_subformula := by
        have ⟨_, h_next⟩ := expand_subformula_closure φ _ _ heq
          (fun ψ hψ => by simp [ExpansionNode.oldHas, FSet.contains_empty] at hψ)
          (fun ψ hψ => by cases hψ with | head => exact .refl | tail _ h => exact nomatch h)
          (fun ψ hψ => by simp [ExpansionNode.nextHas, FSet.contains_empty] at hψ)
          (fun k n hk => by simp at hk)
          (fun k n hk => by simp at hk)
        intro q hq ψ hψ
        obtain ⟨n, hn, _, _, hnxt, _, _⟩ := bridge q hq
        exact h_next _ _ hn _ ((hnxt _).mp hψ)
      successor_old := by
        have h_no_init := (expand_no_init_key _ _ heq
          (fun k hk => by simp at hk)
          (by simp)
          (fun k hk => by simp at hk)
          (by omega : (1 : Nat) < 2)
          (by unfold expandInit; omega : (1 : Nat) ≠ expandInit)).1
        have ⟨h_succ, _, _, _, _, _⟩ := expand_successor_old _ _ heq
          (fun k n hk => by simp at hk)
          (fun k' hk'_ne hk' => by
            simp [Std.HashSet.contains_insert, Std.HashSet.contains_emptyWithCapacity,
                  beq_iff_eq] at hk'
            exact absurd hk'.symm hk'_ne)
          (by simp)
          (fun k hk => by simp at hk)
          (by omega : (1 : Nat) < 2)
          (by unfold expandInit; omega : (1 : Nat) ≠ expandInit)
        intro q hq q' hq' hinc ψ hψ
        obtain ⟨n, hn, hinc_n, hold_n, hnxt_n, _, _⟩ := bridge q hq
        obtain ⟨n', hn', hinc_n', hold_n', _, _, _⟩ := bridge q' hq'
        have hk'_ne : q.name ≠ expandInit :=
          h_no_init q.name (by simp [hn])
        obtain ⟨pred, hpred, hpred_next⟩ := h_succ _ _ hn' q.name hk'_ne ((hinc_n' _).mp hinc)
        rw [hn] at hpred; obtain rfl := Option.some.inj hpred
        exact (hold_n' _).mpr (hpred_next ψ ((hnxt_n _).mp hψ))
      initial_old := by
        have ⟨h_init, _, _, _, _⟩ := expand_initial_old φ _ _ heq
          (fun _ => Or.inr (.head _))
          (fun k n hk => by simp at hk)
          (by simp)
          (fun k hk => by simp at hk)
          (by omega : (1 : Nat) < 2)
          (by unfold expandInit; omega : (1 : Nat) ≠ expandInit)
        intro q hq hinc
        obtain ⟨n, hn, hinc_n, hold_n, _, _, _⟩ := bridge q hq
        exact (hold_n _).mpr (h_init _ _ hn ((hinc_n _).mp hinc))
    }
  · -- none case: impossible
    simp at h

end LTLLib
