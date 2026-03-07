/-
  Structural invariants of the LTL-to-GBA expansion algorithm.

  Defines:
  - `NNF.IsSubformula`: inductive subformula relation
  - Properties of `new1`/`new2`/`next1` (subformula preservation)
  - `ExpandSpec`: abstract specification of what the expand output satisfies

  These invariants are the building blocks for the GBA correctness proof
  (soundness L4_9 and completeness L4_10).
-/

import LTLLib.LTLtoGBA.Expand
import LTLLib.LTL.Semantics

namespace LTLLib

open NNF

/-! ## Subformula relation -/

/-- `IsSubformula ψ φ` means ψ is a (reflexive) subformula of φ. -/
inductive NNF.IsSubformula : NNF α → NNF α → Prop where
  | refl : IsSubformula φ φ
  | and_left : IsSubformula ψ φ₁ → IsSubformula ψ (.and φ₁ φ₂)
  | and_right : IsSubformula ψ φ₂ → IsSubformula ψ (.and φ₁ φ₂)
  | or_left : IsSubformula ψ φ₁ → IsSubformula ψ (.or φ₁ φ₂)
  | or_right : IsSubformula ψ φ₂ → IsSubformula ψ (.or φ₁ φ₂)
  | until_left : IsSubformula ψ φ₁ → IsSubformula ψ (.until φ₁ φ₂)
  | until_right : IsSubformula ψ φ₂ → IsSubformula ψ (.until φ₁ φ₂)
  | release_left : IsSubformula ψ φ₁ → IsSubformula ψ (.release φ₁ φ₂)
  | release_right : IsSubformula ψ φ₂ → IsSubformula ψ (.release φ₁ φ₂)
  | next_sub : IsSubformula ψ φ → IsSubformula ψ (.next φ)

namespace NNF.IsSubformula

variable {α : Type} {φ ψ χ : NNF α}

theorem trans (h₁ : IsSubformula ψ χ) (h₂ : IsSubformula χ φ) :
    IsSubformula ψ φ := by
  induction h₂ with
  | refl => exact h₁
  | and_left _ ih => exact .and_left ih
  | and_right _ ih => exact .and_right ih
  | or_left _ ih => exact .or_left ih
  | or_right _ ih => exact .or_right ih
  | until_left _ ih => exact .until_left ih
  | until_right _ ih => exact .until_right ih
  | release_left _ ih => exact .release_left ih
  | release_right _ ih => exact .release_right ih
  | next_sub _ ih => exact .next_sub ih

end NNF.IsSubformula

/-! ## Properties of new1, new2, next1

These lemmas show that the expansion helpers produce subformulas (or the
formula itself), ensuring the subformula closure property is maintained
during expansion. -/

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

Spell out exactly what each function produces, for use in propagation proofs. -/

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

/-! ## Expansion specification

`ExpandSpec φ nodes` describes the invariants that the output of `expand`
(applied to the initial node for formula φ) must satisfy. These are stated
abstractly over spec-level node data, independent of the computational
details of the expand implementation. -/

/-- Spec-level representation of a finished node.
Uses predicates instead of hash sets for proof convenience. -/
structure NodeData (α : Type) where
  name : Nat
  incoming : Nat → Prop
  old : NNF α → Prop
  next : NNF α → Prop

/-- The abstract specification of a valid expansion result for formula φ.
`nodes` is a predicate selecting the finished nodes. -/
structure ExpandSpec {α : Type} (φ : NNF α) (nodes : NodeData α → Prop) : Prop where
  /-- Literal consistency: no node contains both prop(a) and nprop(a). -/
  literal_consistent :
    ∀ q, nodes q → ∀ a, q.old (.prop a) → ¬ q.old (.nprop a)

  /-- No node contains ⊥ (false). -/
  no_false :
    ∀ q, nodes q → ¬ q.old .ff

  /-- And propagation. -/
  and_propag :
    ∀ q, nodes q → ∀ μ ψ, q.old (.and μ ψ) → q.old μ ∧ q.old ψ

  /-- Or propagation: at least one disjunct is in old. -/
  or_propag :
    ∀ q, nodes q → ∀ μ ψ, q.old (.or μ ψ) → q.old μ ∨ q.old ψ

  /-- Next propagation: the inner formula goes to next. -/
  next_propag :
    ∀ q, nodes q → ∀ ψ, q.old (.next ψ) → q.next ψ

  /-- Until propagation: either the RHS is satisfied now, or the LHS holds
      and the obligation carries forward. -/
  until_propag :
    ∀ q, nodes q → ∀ μ ψ, q.old (.until μ ψ) →
      q.old ψ ∨ (q.old μ ∧ q.next (.until μ ψ))

  /-- Release propagation: the RHS must hold now, and either the LHS holds
      (releasing the obligation) or the obligation carries forward. -/
  release_propag :
    ∀ q, nodes q → ∀ μ ψ, q.old (.release μ ψ) →
      q.old ψ ∧ (q.old μ ∨ q.next (.release μ ψ))

  /-- Subformula closure: everything in old is a subformula of φ. -/
  old_subformula :
    ∀ q, nodes q → ∀ ψ, q.old ψ → NNF.IsSubformula ψ φ

  /-- Subformula closure: everything in next is a subformula of φ. -/
  next_subformula :
    ∀ q, nodes q → ∀ ψ, q.next ψ → NNF.IsSubformula ψ φ

  /-- Successor inheritance: if q' is a successor of q (i.e., q.name is in
      q'.incoming and both are in nodes), then next(q) ⊆ old(q'). -/
  successor_old :
    ∀ q, nodes q → ∀ q', nodes q' → q'.incoming q.name →
      ∀ ψ, q.next ψ → q'.old ψ

  /-- Initial formula: nodes reachable from the init marker contain φ in old. -/
  initial_old :
    ∀ q, nodes q → q.incoming expandInit → q.old φ

/-! ## Bridge: computational → abstract

Convert `GBANode` (with `HashSet`) to `NodeData` (with predicates),
and `ExpandState` to a predicate on `NodeData`. -/

variable {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]

/-- Convert a computational node to its abstract representation. -/
def GBANode.toNodeData (n : GBANode α) : NodeData α where
  name := n.name
  incoming k := n.incoming.contains k
  old ψ := n.old.contains ψ
  next ψ := n.next.contains ψ

/-- The abstract node predicate induced by an `ExpandState`:
    a `NodeData` is in the predicate iff it matches some finished node. -/
def ExpandState.toNodes (st : ExpandState α) : NodeData α → Prop :=
  fun nd => ∃ n, st.nodes[nd.name]? = some n ∧
    (∀ k, nd.incoming k ↔ n.incoming.contains k) ∧
    (∀ ψ, nd.old ψ ↔ n.old.contains ψ) ∧
    (∀ ψ, nd.next ψ ↔ n.next.contains ψ)

/-! ## Per-node propagation invariant

During processing, a node's `old` set may have formulas whose consequences
haven't been fully expanded yet — they're still in `new`. The `ProcessingInv`
captures this: for each compound formula in `old`, its consequences are in
`old ∪ new`. When `new` is empty (finished node), this implies `ExpandSpec`
properties directly. -/

/-- A formula is "in" a node's old set. -/
abbrev GBANode.oldHas (n : GBANode α) (ψ : NNF α) : Prop := n.old.contains ψ

/-- A formula is "in" a node's next set. -/
abbrev GBANode.nextHas (n : GBANode α) (ψ : NNF α) : Prop := n.next.contains ψ

/-- A formula is "reachable" — either already processed (old) or pending (new). -/
def GBANode.reachable (n : GBANode α) (ψ : NNF α) : Prop :=
  n.old.contains ψ ∨ ψ ∈ n.new

/-- Per-node propagation invariant during processing.
    For compound formulas in `old`, consequences are in `old ∪ new`. -/
structure ProcessingInv (n : GBANode α) : Prop where
  /-- No literal contradiction: prop(a) ∈ old → nprop(a) ∉ old. -/
  literal_consistent : ∀ a, n.oldHas (.prop a) → ¬ n.oldHas (.nprop a)
  /-- No ff in old. -/
  no_false : ¬ n.oldHas .ff
  /-- And: both conjuncts reachable. -/
  and_propag : ∀ μ ψ, n.oldHas (.and μ ψ) → n.reachable μ ∧ n.reachable ψ
  /-- Or: at least one disjunct reachable. -/
  or_propag : ∀ μ ψ, n.oldHas (.or μ ψ) → n.reachable μ ∨ n.reachable ψ
  /-- Next: inner formula in next set. -/
  next_propag : ∀ ψ, n.oldHas (.next ψ) → n.nextHas ψ
  /-- Until: RHS reachable, or LHS reachable and self in next. -/
  until_propag : ∀ μ ψ, n.oldHas (.until μ ψ) →
    n.reachable ψ ∨ (n.reachable μ ∧ n.nextHas (.until μ ψ))
  /-- Release: RHS reachable, and (LHS reachable or self in next). -/
  release_propag : ∀ μ ψ, n.oldHas (.release μ ψ) →
    n.reachable ψ ∧ (n.reachable μ ∨ n.nextHas (.release μ ψ))

/-- Invariant for all finished nodes in a state. -/
def StateInv (st : ExpandState α) : Prop :=
  ∀ (k : Nat) (n : GBANode α), st.nodes[k]? = some n → ProcessingInv n ∧ n.new = []

/-! ## Monotonicity: nodes are preserved across expand calls -/

/-- Nodes in `st` are preserved in `st'` (their old/next don't change,
    only incoming may grow via mergeIncoming). -/
def NodesPreserved (st st' : ExpandState α) : Prop :=
  ∀ (k : Nat) (n : GBANode α), st.nodes[k]? = some n →
    ∃ n' : GBANode α, st'.nodes[k]? = some n' ∧
      (∀ ψ, n'.old.contains ψ ↔ n.old.contains ψ) ∧
      (∀ ψ, n'.next.contains ψ ↔ n.next.contains ψ)

/-! ### Helper lemmas -/

omit [LawfulBEq α] [LawfulHashable α] in
private theorem mergeIncoming_nodesPreserved (st : ExpandState α) (node : GBANode α) (targetName : Nat) :
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

omit [LawfulBEq α] [LawfulHashable α] in
private theorem mergeIncoming_nextName (st : ExpandState α) (node : GBANode α) (targetName : Nat) :
    (mergeIncoming st node targetName).nextName = st.nextName := by
  unfold mergeIncoming; split <;> rfl

omit [LawfulBEq α] [LawfulHashable α] in
private theorem mergeIncoming_preserves_absent (st : ExpandState α) (node : GBANode α)
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

omit [LawfulBEq α] [LawfulHashable α] in
private theorem mergeIncoming_freshInv (st : ExpandState α) (node : GBANode α)
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

omit [LawfulBEq α] [LawfulHashable α] in
private theorem NodesPreserved_refl (st : ExpandState α) : NodesPreserved st st :=
  fun _k n hk => ⟨n, hk, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

omit [LawfulBEq α] [LawfulHashable α] in
private theorem NodesPreserved_trans {st₁ st₂ st₃ : ExpandState α}
    (h₁₂ : NodesPreserved st₁ st₂) (h₂₃ : NodesPreserved st₂ st₃) :
    NodesPreserved st₁ st₃ := by
  intro k n hk
  obtain ⟨n', hk', ho', hn'⟩ := h₁₂ k n hk
  obtain ⟨n'', hk'', ho'', hn''⟩ := h₂₃ k n' hk'
  exact ⟨n'', hk'', fun ψ => (ho'' ψ).trans (ho' ψ), fun ψ => (hn'' ψ).trans (hn' ψ)⟩

omit [LawfulBEq α] [LawfulHashable α] in
private theorem insert_nodesPreserved (st : ExpandState α) (node : GBANode α)
    (h_not_in : st.nodes[node.name]? = none) :
    NodesPreserved st { st with nodes := st.nodes.insert node.name node } := by
  intro k n hk
  have hne : k ≠ node.name := fun heq => by rw [heq, h_not_in] at hk; simp at hk
  simp only [Std.HashMap.getElem?_insert]; split
  · rename_i heq; exact absurd ((beq_iff_eq (α := Nat)).mp heq).symm hne
  · exact ⟨n, hk, fun ψ => Iff.rfl, fun ψ => Iff.rfl⟩

omit [LawfulBEq α] [LawfulHashable α] in
private theorem insert_fresh_key (st : ExpandState α) (nodeName : Nat) (node : GBANode α)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : nodeName < st.nextName) :
    (st.nodes.insert nodeName node)[st.nextName]? = none := by
  simp only [Std.HashMap.getElem?_insert]; split
  · rename_i heq; have := (beq_iff_eq (α := Nat)).mp heq; omega
  · by_contra h; exact absurd (h_fresh st.nextName h) (by omega)

omit [LawfulBEq α] [LawfulHashable α] in
private theorem insert_freshInv (st : ExpandState α) (nodeName : Nat) (node : GBANode α)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : nodeName < st.nextName) :
    ∀ k, (st.nodes.insert nodeName node)[k]? ≠ none →
      k < st.nextName + 1 := by
  intro k hk
  simp only [Std.HashMap.getElem?_insert] at hk; split at hk
  · rename_i heq; have := (beq_iff_eq (α := Nat)).mp heq; omega
  · have := h_fresh k hk; omega

/-! ### Combined expansion invariants -/

/-- Combined invariants maintained by expand:
    monotonicity, name freshness, freshness invariant preservation. -/
structure ExpandInvariants (st st' : ExpandState α) (nm : Nat) : Prop where
  nodesPreserved : NodesPreserved st st'
  nameFresh : st'.nodes[nm]? = none
  freshInv : ∀ k, st'.nodes[k]? ≠ none → k < st'.nextName
  nameBound : nm < st'.nextName
  nextNameMono : st.nextName ≤ st'.nextName

omit [LawfulBEq α] [LawfulHashable α] in
theorem expand_invariants (node : GBANode α)
    (st : ExpandState α) {r : Nat × ExpandState α}
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
        nextNameMono := by rw [mergeIncoming_nextName]; omega
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
      -- Chain splits across all goals with try to handle branches needing different depth
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

omit [LawfulBEq α] [LawfulHashable α] in
theorem expand_nodes_preserved (node : GBANode α)
    (st : ExpandState α) {r : Nat × ExpandState α}
    (h_result : expand node st = some r)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName) :
    NodesPreserved st r.2 :=
  (expand_invariants node st h_result h_not_in h_fresh h_name).nodesPreserved

/-! ### Helper lemmas for StateInv preservation -/

private theorem oldHas_insert {s : Std.HashSet (NNF α)} {φ ψ : NNF α}
    (h : (s.insert φ).contains ψ = true) :
    s.contains ψ = true ∨ ψ = φ := by
  rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h; exact Or.inr rfl; exact Or.inl h

private theorem old_subset_insert (s : Std.HashSet (NNF α)) (φ : NNF α) :
    ∀ ψ, s.contains ψ = true → (s.insert φ).contains ψ = true :=
  fun _ h => by rw [Std.HashSet.contains_insert]; simp [h]

private theorem mem_insert_self' (s : Std.HashSet (NNF α)) (φ : NNF α) :
    (s.insert φ).contains φ = true := by rw [Std.HashSet.contains_insert]; simp

private theorem addAllToSet_subset (s : Std.HashSet (NNF α)) (fs : List (NNF α)) :
    ∀ ψ, s.contains ψ = true → (addAllToSet s fs).contains ψ = true := by
  induction fs generalizing s with
  | nil => exact fun _ h => h
  | cons f rest ih =>
    intro ψ h; show (addAllToSet (s.insert f) rest).contains ψ = true
    exact ih _ ψ (old_subset_insert s f ψ h)

private theorem addAllToSet_mem (s : Std.HashSet (NNF α)) (fs : List (NNF α)) :
    ∀ ψ, ψ ∈ fs → (addAllToSet s fs).contains ψ = true := by
  induction fs generalizing s with
  | nil => intro ψ h; simp at h
  | cons f rest ih =>
    intro ψ h; show (addAllToSet (s.insert f) rest).contains ψ = true
    cases List.mem_cons.mp h with
    | inl heq => subst heq; exact addAllToSet_subset _ rest ψ (mem_insert_self' s ψ)
    | inr hmem => exact ih _ ψ hmem

private theorem addAllToSet_inv (s : Std.HashSet (NNF α)) (fs : List (NNF α)) :
    ∀ ψ, (addAllToSet s fs).contains ψ = true → s.contains ψ = true ∨ ψ ∈ fs := by
  induction fs generalizing s with
  | nil => intro ψ h; exact Or.inl h
  | cons f rest ih =>
    intro ψ h
    rcases ih (s.insert f) ψ h with h1 | h2
    · rcases oldHas_insert h1 with h1 | rfl
      · exact Or.inl h1
      · exact Or.inr (.head rest)
    · exact Or.inr (.tail f h2)

omit [LawfulBEq α] [LawfulHashable α] in
private theorem addToNew_foldl_preserves (old : Std.HashSet (NNF α))
    (formulas : List (NNF α)) (init : List (NNF α)) :
    ∀ ψ, ψ ∈ init → ψ ∈ formulas.foldl (fun acc f => if old.contains f then acc else f :: acc) init := by
  induction formulas generalizing init with
  | nil => exact fun _ h => h
  | cons f rest ih =>
    intro ψ h; simp only [List.foldl]
    apply ih; split <;> [exact h; exact List.mem_cons_of_mem _ h]

omit [LawfulBEq α] [LawfulHashable α] in
private theorem addToNew_foldl_adds (old : Std.HashSet (NNF α))
    (formulas : List (NNF α)) (init : List (NNF α)) :
    ∀ ψ, ψ ∈ formulas → old.contains ψ = false →
    ψ ∈ formulas.foldl (fun acc f => if old.contains f then acc else f :: acc) init := by
  induction formulas generalizing init with
  | nil => intro ψ h; simp at h
  | cons f rest ih =>
    intro ψ h hn; simp only [List.foldl]
    cases List.mem_cons.mp h with
    | inl heq => subst heq; apply addToNew_foldl_preserves; simp [hn]
    | inr hmem => exact ih _ ψ hmem hn

omit [LawfulBEq α] [LawfulHashable α] in
private theorem addToNew_foldl_inv (old : Std.HashSet (NNF α))
    (formulas : List (NNF α)) (init : List (NNF α)) :
    ∀ ψ, ψ ∈ formulas.foldl (fun acc f => if old.contains f then acc else f :: acc) init →
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

omit [LawfulBEq α] [LawfulHashable α] in
private theorem addToNew_inv (node : GBANode α) (formulas : List (NNF α)) :
    ∀ ψ, ψ ∈ addToNew node formulas → ψ ∈ node.new ∨ ψ ∈ formulas :=
  addToNew_foldl_inv node.old formulas node.new

omit [LawfulBEq α] [LawfulHashable α] in
private theorem addToNew_preserves (node : GBANode α) (formulas : List (NNF α)) :
    ∀ ψ, ψ ∈ node.new → ψ ∈ addToNew node formulas :=
  addToNew_foldl_preserves node.old formulas node.new

omit [LawfulBEq α] [LawfulHashable α] in
private theorem addToNew_adds (node : GBANode α) (formulas : List (NNF α)) :
    ∀ ψ, ψ ∈ formulas → node.old.contains ψ = false → ψ ∈ addToNew node formulas :=
  addToNew_foldl_adds node.old formulas node.new

omit [LawfulBEq α] [LawfulHashable α] in
private theorem mem_head_or_tail' [Inhabited β] {l : List β} (h : l.isEmpty = false)
    {φ : β} (hφ : l.head! = φ) {ψ : β} (hψ : ψ ∈ l) : ψ = φ ∨ ψ ∈ l.tail! := by
  cases l with
  | nil => simp at h
  | cons a rest => subst hφ; exact List.mem_cons.mp hψ

omit [LawfulBEq α] [LawfulHashable α] in
private theorem reachable_step {node : GBANode α} {φ : NNF α}
    (h_ne : node.new.isEmpty = false) (hφ : node.new.head! = φ)
    (h : node.reachable ψ) {old' : Std.HashSet (NNF α)}
    (h_old : ∀ χ, node.old.contains χ = true → old'.contains χ = true)
    (h_φ : old'.contains φ = true) {new' : List (NNF α)}
    (h_new : ∀ χ, χ ∈ node.new.tail! → χ ∈ new') :
    old'.contains ψ = true ∨ ψ ∈ new' := by
  cases h with
  | inl h => exact Or.inl (h_old ψ h)
  | inr h =>
    rcases mem_head_or_tail' h_ne hφ h with rfl | hmem
    · exact Or.inl h_φ
    · exact Or.inr (h_new ψ hmem)

omit [LawfulBEq α] [LawfulHashable α] in
private theorem reachable_via_formulas {node : GBANode α}
    (formulas : List (NNF α)) {ψ : NNF α} (h : ψ ∈ formulas)
    {old' : Std.HashSet (NNF α)}
    (h_old : ∀ χ, node.old.contains χ = true → old'.contains χ = true) :
    old'.contains ψ = true ∨ ψ ∈ addToNew node formulas := by
  by_cases hψ : node.old.contains ψ = true
  · exact Or.inl (h_old ψ hψ)
  · simp only [Bool.not_eq_true] at hψ
    exact Or.inr (addToNew_adds node formulas ψ h hψ)

omit [LawfulBEq α] [LawfulHashable α] in
private theorem processingInv_empty_old (node : GBANode α)
    (h : ∀ ψ, node.old.contains ψ = false) : ProcessingInv node where
  literal_consistent a ha := by simp [GBANode.oldHas, h] at ha
  no_false hf := by simp [GBANode.oldHas, h] at hf
  and_propag _ _ ha := by simp [GBANode.oldHas, h] at ha
  or_propag _ _ ha := by simp [GBANode.oldHas, h] at ha
  next_propag _ ha := by simp [GBANode.oldHas, h] at ha
  until_propag _ _ ha := by simp [GBANode.oldHas, h] at ha
  release_propag _ _ ha := by simp [GBANode.oldHas, h] at ha

omit [LawfulBEq α] [LawfulHashable α] in
private theorem mergeIncoming_stateInv (st : ExpandState α) (node : GBANode α)
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

private theorem processingInv_literal {node : GBANode α}
    (h_proc : ProcessingInv node) (h_ne : node.new.isEmpty = false)
    (h_lit : isLiteral node.new.head! = true)
    (h_no_neg : node.old.contains (negateLiteral node.new.head!) = false) :
    ProcessingInv { node with new := node.new.tail!, old := node.old.insert node.new.head! } := by
  generalize hφ : node.new.head! = φ at *
  have h_φ_old := mem_insert_self' node.old φ
  have reach : ∀ ψ, node.reachable ψ →
      (node.old.insert φ).contains ψ = true ∨ ψ ∈ node.new.tail! :=
    fun ψ h => reachable_step h_ne hφ h (old_subset_insert _ φ) h_φ_old (fun _ h => h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha hna; simp only [GBANode.oldHas] at ha hna
    rcases oldHas_insert ha with ha' | rfl
    · rcases oldHas_insert hna with hna' | rfl
      · exact h_proc.literal_consistent a ha' hna'
      · simp [negateLiteral, ha'] at h_no_neg
    · rcases oldHas_insert hna with hna' | heq
      · simp [negateLiteral, hna'] at h_no_neg
      · simp at heq
  all_goals (
    first | (intro _ _ ha) | (intro _ ha) | (intro ha)
    simp only [GBANode.oldHas] at ha
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

private theorem processingInv_tt {node : GBANode α}
    (h_proc : ProcessingInv node) (h_ne : node.new.isEmpty = false)
    (h_tt : node.new.head! = NNF.tt) :
    ProcessingInv { node with new := node.new.tail!, old := node.old.insert node.new.head! } := by
  generalize hφ : node.new.head! = φ at *
  subst h_tt
  have h_φ_old := mem_insert_self' node.old NNF.tt
  have reach : ∀ ψ, node.reachable ψ →
      (node.old.insert NNF.tt).contains ψ = true ∨ ψ ∈ node.new.tail! :=
    fun ψ h => reachable_step h_ne hφ h (old_subset_insert _ _) h_φ_old (fun _ h => h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha hna; simp only [GBANode.oldHas] at ha hna
    rcases oldHas_insert ha with ha' | heq
    · rcases oldHas_insert hna with hna' | heq
      · exact h_proc.literal_consistent a ha' hna'
      · simp at heq
    · simp at heq
  all_goals (
    first | (intro _ _ ha) | (intro _ ha) | (intro ha)
    simp only [GBANode.oldHas] at ha
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

private theorem processingInv_deterministic {node : GBANode α}
    (h_proc : ProcessingInv node) (h_ne : node.new.isEmpty = false)
    (h_det : isDeterministic node.new.head! = true) :
    let φ := node.new.head!
    let node_tail := { node with new := node.new.tail! }
    ProcessingInv {
      node with
      new := addToNew node_tail (new1 φ)
      old := node.old.insert φ
      next := addAllToSet node.next (next1 φ) } := by
  generalize hφ : node.new.head! = φ at *
  let node_tail := { node with new := node.new.tail! }
  have h_φ_old := mem_insert_self' node.old φ
  have h_old_sub := old_subset_insert node.old φ
  have h_new_sub : ∀ ψ, ψ ∈ node.new.tail! → ψ ∈ addToNew node_tail (new1 φ) :=
    fun ψ h => addToNew_preserves node_tail (new1 φ) ψ h
  have h_next_sub : ∀ ψ, node.next.contains ψ = true → (addAllToSet node.next (next1 φ)).contains ψ = true :=
    fun ψ h => addAllToSet_subset node.next (next1 φ) ψ h
  have reach : ∀ ψ, node.reachable ψ →
      (node.old.insert φ).contains ψ = true ∨ ψ ∈ addToNew node_tail (new1 φ) :=
    fun ψ h => reachable_step h_ne hφ h h_old_sub h_φ_old h_new_sub
  have reach_new1 : ∀ ψ, ψ ∈ new1 φ →
      (node.old.insert φ).contains ψ = true ∨ ψ ∈ addToNew node_tail (new1 φ) :=
    fun ψ h => reachable_via_formulas (new1 φ) h h_old_sub
  have in_next1 : ∀ ψ, ψ ∈ next1 φ → (addAllToSet node.next (next1 φ)).contains ψ = true :=
    fun ψ h => addAllToSet_mem node.next (next1 φ) ψ h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha hna; simp only [GBANode.oldHas] at ha hna
    rcases oldHas_insert ha with ha' | rfl
    · rcases oldHas_insert hna with hna' | rfl
      · exact h_proc.literal_consistent a ha' hna'
      · simp [isDeterministic] at h_det
    · simp [isDeterministic] at h_det
  · intro hf; simp only [GBANode.oldHas] at hf
    rcases oldHas_insert hf with hf' | rfl
    · exact h_proc.no_false hf'
    · simp [isDeterministic] at h_det
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · have ⟨h1, h2⟩ := h_proc.and_propag μ ψ ha'; exact ⟨reach _ h1, reach _ h2⟩
    · exact ⟨reach_new1 μ (by simp [new1]), reach_new1 ψ (by simp [new1])⟩
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact (h_proc.or_propag μ ψ ha').imp (reach _) (reach _)
    · simp [isDeterministic] at h_det
  · intro ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact h_next_sub ψ (h_proc.next_propag ψ ha')
    · exact in_next1 ψ (by simp [next1])
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact (h_proc.until_propag μ ψ ha').imp (reach _) (fun ⟨h1, h2⟩ => ⟨reach _ h1, h_next_sub _ h2⟩)
    · simp [isDeterministic] at h_det
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · have ⟨h1, h2⟩ := h_proc.release_propag μ ψ ha'
      exact ⟨reach _ h1, h2.imp (reach _) (h_next_sub _)⟩
    · simp [isDeterministic] at h_det

private theorem processingInv_nondet1 {node : GBANode α}
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
      old := node.old.insert φ
      next := addAllToSet node.next (next1 φ) } := by
  generalize hφ : node.new.head! = φ at *
  let node_tail := { node with new := node.new.tail! }
  have h_φ_old := mem_insert_self' node.old φ
  have h_old_sub := old_subset_insert node.old φ
  have h_new_sub : ∀ ψ, ψ ∈ node.new.tail! → ψ ∈ addToNew node_tail (new1 φ) :=
    fun ψ h => addToNew_preserves node_tail (new1 φ) ψ h
  have h_next_sub : ∀ ψ, node.next.contains ψ = true → (addAllToSet node.next (next1 φ)).contains ψ = true :=
    fun ψ h => addAllToSet_subset node.next (next1 φ) ψ h
  have reach : ∀ ψ, node.reachable ψ →
      (node.old.insert φ).contains ψ = true ∨ ψ ∈ addToNew node_tail (new1 φ) :=
    fun ψ h => reachable_step h_ne hφ h h_old_sub h_φ_old h_new_sub
  have reach_new1 : ∀ ψ, ψ ∈ new1 φ →
      (node.old.insert φ).contains ψ = true ∨ ψ ∈ addToNew node_tail (new1 φ) :=
    fun ψ h => reachable_via_formulas (new1 φ) h h_old_sub
  have in_next1 : ∀ ψ, ψ ∈ next1 φ → (addAllToSet node.next (next1 φ)).contains ψ = true :=
    fun ψ h => addAllToSet_mem node.next (next1 φ) ψ h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha hna; simp only [GBANode.oldHas] at ha hna
    rcases oldHas_insert ha with ha' | rfl
    · rcases oldHas_insert hna with hna' | rfl
      · exact h_proc.literal_consistent a ha' hna'
      · simp_all [isLiteral, isDeterministic]
    · simp_all [isLiteral, isDeterministic]
  · intro hf; simp only [GBANode.oldHas] at hf
    rcases oldHas_insert hf with hf' | rfl
    · exact h_proc.no_false hf'
    · simp_all [isLiteral, isDeterministic]
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · have ⟨h1, h2⟩ := h_proc.and_propag μ ψ ha'; exact ⟨reach _ h1, reach _ h2⟩
    · simp_all [isDeterministic]
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact (h_proc.or_propag μ ψ ha').imp (reach _) (reach _)
    · exact Or.inl (reach_new1 μ (by simp [new1]))
  · intro ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact h_next_sub ψ (h_proc.next_propag ψ ha')
    · simp_all [isDeterministic]
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact (h_proc.until_propag μ ψ ha').imp (reach _) (fun ⟨h1, h2⟩ => ⟨reach _ h1, h_next_sub _ h2⟩)
    · exact Or.inr ⟨reach_new1 μ (by simp [new1]), in_next1 _ (by simp [next1])⟩
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · have ⟨h1, h2⟩ := h_proc.release_propag μ ψ ha'
      exact ⟨reach _ h1, h2.imp (reach _) (h_next_sub _)⟩
    · exact ⟨reach_new1 ψ (by simp [new1]), Or.inr (in_next1 _ (by simp [next1]))⟩

private theorem processingInv_nondet2 {node : GBANode α}
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
      old := node.old.insert node.new.head! } := by
  generalize hφ : node.new.head! = φ at *
  let node_tail := { node with new := node.new.tail! }
  have h_φ_old := mem_insert_self' node.old φ
  have h_old_sub := old_subset_insert node.old φ
  have h_new_sub : ∀ ψ, ψ ∈ node.new.tail! → ψ ∈ addToNew node_tail (new2 φ) :=
    fun ψ h => addToNew_preserves node_tail (new2 φ) ψ h
  have reach : ∀ ψ, node.reachable ψ →
      (node.old.insert φ).contains ψ = true ∨ ψ ∈ addToNew node_tail (new2 φ) :=
    fun ψ h => reachable_step h_ne hφ h h_old_sub h_φ_old h_new_sub
  have reach_new2 : ∀ ψ, ψ ∈ new2 φ →
      (node.old.insert φ).contains ψ = true ∨ ψ ∈ addToNew node_tail (new2 φ) :=
    fun ψ h => reachable_via_formulas (new2 φ) h h_old_sub
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha hna; simp only [GBANode.oldHas] at ha hna
    rcases oldHas_insert ha with ha' | rfl
    · rcases oldHas_insert hna with hna' | rfl
      · exact h_proc.literal_consistent a ha' hna'
      · simp_all [isLiteral, isDeterministic]
    · simp_all [isLiteral, isDeterministic]
  · intro hf; simp only [GBANode.oldHas] at hf
    rcases oldHas_insert hf with hf' | rfl
    · exact h_proc.no_false hf'
    · simp_all [isLiteral, isDeterministic]
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · have ⟨h1, h2⟩ := h_proc.and_propag μ ψ ha'; exact ⟨reach _ h1, reach _ h2⟩
    · simp_all [isDeterministic]
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact (h_proc.or_propag μ ψ ha').imp (reach _) (reach _)
    · exact Or.inr (reach_new2 ψ (by simp [new2]))
  · intro ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact h_proc.next_propag ψ ha'
    · simp_all [isDeterministic]
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact (h_proc.until_propag μ ψ ha').imp (reach _) (fun ⟨h1, h2⟩ => ⟨reach _ h1, h2⟩)
    · exact Or.inl (reach_new2 ψ (by simp [new2]))
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · have ⟨h1, h2⟩ := h_proc.release_propag μ ψ ha'
      exact ⟨reach _ h1, h2.imp (reach _) id⟩
    · exact ⟨reach_new2 ψ (by simp [new2]), Or.inl (reach_new2 μ (by simp [new2]))⟩

theorem expand_preserves_stateInv (node : GBANode α)
    (st : ExpandState α) {r : Nat × ExpandState α}
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
        simp [Std.HashSet.contains_emptyWithCapacity])
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

private theorem reachable_iff_old (n : GBANode α) (h : n.new = []) (ψ : NNF α) :
    n.reachable ψ ↔ n.oldHas ψ := by
  simp [GBANode.reachable, h]

/-- Reverse lookup for mergeIncoming: every node in the merged state
    has a preimage in the original state with the same old/next. -/
private theorem mergeIncoming_reverse (st : ExpandState α) (node : GBANode α) (targetName : Nat)
    (k : Nat) (n : GBANode α) (hk : (mergeIncoming st node targetName).nodes[k]? = some n) :
    ∃ (n' : GBANode α), st.nodes[k]? = some n' ∧
      (∀ ψ, n.old.contains ψ ↔ n'.old.contains ψ) ∧
      (∀ ψ, n.next.contains ψ ↔ n'.next.contains ψ) := by
  unfold mergeIncoming at hk; split at hk
  · rename_i target htarget
    simp only [Std.HashMap.getElem?_insert] at hk; split at hk
    · rename_i hk_eq
      have : k = targetName := by rw [beq_iff_eq] at hk_eq; exact hk_eq.symm
      subst this; obtain rfl := Option.some.inj hk
      exact ⟨target, htarget, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
    · exact ⟨n, hk, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  · exact ⟨n, hk, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

private theorem head!_mem_of_isEmpty_false [Inhabited β] {l : List β}
    (h : l.isEmpty = false) : l.head! ∈ l := by
  cases l with | nil => simp at h | cons _ _ => exact .head _

private theorem mem_of_mem_tail! [Inhabited β] {l : List β} {ψ : β}
    (h : ψ ∈ l.tail!) : ψ ∈ l := by
  cases l with
  | nil => exact absurd h (by simp [List.tail!, default])
  | cons _ _ => exact .tail _ h

/-! ## Subformula closure -/

/-- Elements of `s.fold (init := []) (fun acc f => f :: acc)` are in `s`. -/
private theorem foldl_cons_subset {β : Type _} (l : List β) :
    ∀ init : List β, ∀ ψ,
      ψ ∈ List.foldl (fun acc f => f :: acc) init l → ψ ∈ init ∨ ψ ∈ l := by
  induction l with
  | nil => intro _ _ h; exact Or.inl h
  | cons x xs ih =>
    intro init ψ h
    rcases ih _ _ h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (.head _)
      · exact Or.inl h
    · exact Or.inr (.tail _ h)

private theorem foldl_cons_preserves {β : Type _} (l : List β) (init : List β) :
    ∀ ψ, ψ ∈ init → ψ ∈ List.foldl (fun acc f => f :: acc) init l := by
  induction l generalizing init with
  | nil => exact fun _ h => h
  | cons _ xs ih => intro ψ h; exact ih _ ψ (.tail _ h)

private theorem foldl_cons_complete {β : Type _} (l : List β) :
    ∀ init : List β, ∀ ψ, ψ ∈ l → ψ ∈ List.foldl (fun acc f => f :: acc) init l := by
  induction l with
  | nil => intro _ _ h; exact absurd h (by simp)
  | cons x xs ih =>
    intro init ψ h
    cases List.mem_cons.mp h with
    | inl heq => subst heq; exact foldl_cons_preserves xs _ _ (.head _)
    | inr htail => exact ih _ ψ htail

/-- Elements of the hashset are in the fold-cons result. -/
private theorem hashset_fold_cons_complete (s : Std.HashSet (NNF α)) :
    ∀ ψ, s.contains ψ = true → ψ ∈ s.fold (init := []) (fun acc f => f :: acc) := by
  intro ψ hψ
  rw [Std.HashSet.fold_eq_foldl_toList]
  exact foldl_cons_complete s.toList [] ψ
    (Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hψ))

private theorem hashset_fold_cons_mem (s : Std.HashSet (NNF α)) :
    ∀ ψ, ψ ∈ s.fold (init := []) (fun acc f => f :: acc) → s.contains ψ = true := by
  intro ψ hψ
  rw [Std.HashSet.fold_eq_foldl_toList] at hψ
  have hmem : ψ ∈ s.toList :=
    (foldl_cons_subset s.toList [] ψ hψ).resolve_left (by intro h; exact nomatch h)
  exact Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hmem)

/-- Subformula closure: expand preserves the property that all formulas
    in old/next of finished nodes are subformulas of the top-level formula. -/
theorem expand_subformula_closure (φ_top : NNF α) (node : GBANode α) (st : ExpandState α)
    {r : Nat × ExpandState α}
    (h_result : expand node st = some r)
    (h_node_old : ∀ ψ, node.oldHas ψ → NNF.IsSubformula ψ φ_top)
    (h_node_new : ∀ ψ, ψ ∈ node.new → NNF.IsSubformula ψ φ_top)
    (h_node_next : ∀ ψ, node.nextHas ψ → NNF.IsSubformula ψ φ_top)
    (h_st_old : ∀ (k : Nat) (n : GBANode α), st.nodes[k]? = some n → ∀ ψ, n.old.contains ψ → NNF.IsSubformula ψ φ_top)
    (h_st_next : ∀ (k : Nat) (n : GBANode α), st.nodes[k]? = some n → ∀ ψ, n.next.contains ψ → NNF.IsSubformula ψ φ_top) :
    (∀ (k : Nat) (n : GBANode α), r.2.nodes[k]? = some n → ∀ ψ, n.old.contains ψ → NNF.IsSubformula ψ φ_top) ∧
    (∀ (k : Nat) (n : GBANode α), r.2.nodes[k]? = some n → ∀ ψ, n.next.contains ψ → NNF.IsSubformula ψ φ_top) := by
  revert h_node_old h_node_new h_node_next h_st_old h_st_next
  apply expand.partial_correctness
    (motive := fun node st r =>
      (∀ ψ, node.oldHas ψ → NNF.IsSubformula ψ φ_top) →
      (∀ ψ, ψ ∈ node.new → NNF.IsSubformula ψ φ_top) →
      (∀ ψ, node.nextHas ψ → NNF.IsSubformula ψ φ_top) →
      (∀ (k : Nat) (n : GBANode α), st.nodes[k]? = some n → ∀ ψ, n.old.contains ψ → NNF.IsSubformula ψ φ_top) →
      (∀ (k : Nat) (n : GBANode α), st.nodes[k]? = some n → ∀ ψ, n.next.contains ψ → NNF.IsSubformula ψ φ_top) →
      (∀ (k : Nat) (n : GBANode α), r.2.nodes[k]? = some n → ∀ ψ, n.old.contains ψ → NNF.IsSubformula ψ φ_top) ∧
      (∀ (k : Nat) (n : GBANode α), r.2.nodes[k]? = some n → ∀ ψ, n.next.contains ψ → NNF.IsSubformula ψ φ_top))
    _ node st r h_result
  intro expand_ih ih node st r h_result h_node_old h_node_new h_node_next h_st_old h_st_next
  -- Helper: formula at head of new is a subformula
  have h_head_sub : node.new.isEmpty = false → NNF.IsSubformula node.new.head! φ_top :=
    fun hne => h_node_new _ (head!_mem_of_isEmpty_false hne)
  -- Helper: formulas in tail of new are subformulas
  have h_tail_sub : ∀ ψ, ψ ∈ node.new.tail! → NNF.IsSubformula ψ φ_top :=
    fun _ hψ => h_node_new _ (mem_of_mem_tail! hψ)
  -- Helper: old.insert preserves subformula closure
  have h_old_insert_sub : node.new.isEmpty = false →
      ∀ ψ, (node.old.insert node.new.head!).contains ψ = true → NNF.IsSubformula ψ φ_top := by
    intro hne ψ hψ; rcases oldHas_insert hψ with h1 | rfl
    · exact h_node_old _ h1
    · exact h_head_sub hne
  split at h_result
  case isTrue h_empty =>
    -- new is empty
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
      have h_st_old' : ∀ (k : Nat) (n' : GBANode α), (st.nodes.insert node.name node)[k]? = some n' →
          ∀ ψ, n'.old.contains ψ → NNF.IsSubformula ψ φ_top := by
        intro k n' hk ψ hψ
        simp only [Std.HashMap.getElem?_insert] at hk; split at hk
        · obtain rfl := Option.some.inj hk; exact h_node_old _ hψ
        · exact h_st_old _ _ hk _ hψ
      have h_st_next' : ∀ (k : Nat) (n' : GBANode α), (st.nodes.insert node.name node)[k]? = some n' →
          ∀ ψ, n'.next.contains ψ → NNF.IsSubformula ψ φ_top := by
        intro k n' hk ψ hψ
        simp only [Std.HashMap.getElem?_insert] at hk; split at hk
        · obtain rfl := Option.some.inj hk; exact h_node_next _ hψ
        · exact h_st_next _ _ hk _ hψ
      -- Successor: old = ∅, next = ∅, new = node.next elements
      have h_succ_old : ∀ (ψ : NNF α),
          (Std.HashSet.emptyWithCapacity 8 : Std.HashSet (NNF α)).contains ψ → NNF.IsSubformula ψ φ_top := by
        intro ψ hψ; simp [Std.HashSet.contains_emptyWithCapacity] at hψ
      have h_succ_new : ∀ ψ,
          ψ ∈ (node.next.fold (init := []) fun acc f => f :: acc) → NNF.IsSubformula ψ φ_top := by
        intro ψ hψ; exact h_node_next _ (hashset_fold_cons_mem node.next ψ hψ)
      have h_succ_next : ∀ (ψ : NNF α),
          (Std.HashSet.emptyWithCapacity 8 : Std.HashSet (NNF α)).contains ψ → NNF.IsSubformula ψ φ_top := by
        intro ψ hψ; simp [Std.HashSet.contains_emptyWithCapacity] at hψ
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

private def findStep (node : GBANode α) (acc : Option Nat) (b : Nat × GBANode α) : Option Nat :=
  match acc with | some _ => acc | none => if b.2.sameSignature node then some b.1 else none

private theorem findDuplicate_spec (st : ExpandState α) (node : GBANode α)
    (name : Nat) (h : findDuplicate st node = some name) :
    ∃ n, st.nodes[name]? = some n ∧ n.sameSignature node = true := by
  unfold findDuplicate at h
  rw [Std.HashMap.fold_eq_foldl_toList] at h
  change List.foldl (fun a b => findStep node a b) none st.nodes.toList = some name at h
  suffices ∀ (init : Option Nat) (l : List (Nat × GBANode α)),
      (∀ p ∈ l, st.nodes[p.1]? = some p.2) →
      (init = some name →
        ∃ m, st.nodes[name]? = some m ∧ m.sameSignature node = true) →
      List.foldl (fun a b => findStep node a b) init l = some name →
      ∃ m, st.nodes[name]? = some m ∧ m.sameSignature node = true by
    exact this none st.nodes.toList
      (fun p hp => Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp)
      (fun h => nomatch h) h
  intro init l hl hinit hfold
  induction l generalizing init with
  | nil => exact hinit hfold
  | cons p ps ih =>
    simp only [List.foldl_cons] at hfold
    have hps : ∀ q ∈ ps, st.nodes[q.1]? = some q.2 := fun q hq => hl q (.tail _ hq)
    have hinit' : findStep node init p = some name →
        ∃ m, st.nodes[name]? = some m ∧ m.sameSignature node = true := by
      intro hstep
      unfold findStep at hstep
      split at hstep
      · exact hinit hstep
      · split at hstep
        · obtain rfl := Option.some.inj hstep
          exact ⟨p.2, hl p (.head _), by assumption⟩
        · exact nomatch hstep
    exact ih _ hps hinit' hfold

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

private theorem mergeIncoming_incoming (st : ExpandState α) (node : GBANode α)
    (targetName k j : Nat) (n : GBANode α)
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
      rw [Std.HashSet.fold_eq_foldl_toList] at hj
      rcases foldl_insert_contains hj with h | h
      · exact Or.inl ⟨target, htarget, h⟩
      · exact Or.inr ⟨rfl, Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp h)⟩
    · exact Or.inl ⟨n, hk, hj⟩
  · exact Or.inl ⟨n, hk, hj⟩

/-! ## Initial old -/

/-- Expand preserves the property that nodes with expandInit in incoming contain φ in old. -/
theorem expand_initial_old (φ_top : NNF α) (node : GBANode α) (st : ExpandState α)
    {r : Nat × ExpandState α}
    (h_result : expand node st = some r)
    (h_node_init : node.incoming.contains expandInit →
      node.oldHas φ_top ∨ φ_top ∈ node.new)
    (h_st_init : ∀ (k : Nat) (n : GBANode α), st.nodes[k]? = some n →
      n.incoming.contains expandInit → n.old.contains φ_top)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName)
    (h_name_ne : node.name ≠ expandInit) :
    (∀ (k : Nat) (n : GBANode α), r.2.nodes[k]? = some n →
      n.incoming.contains expandInit → n.old.contains φ_top) ∧
    r.1 ≠ expandInit ∧
    r.2.nodes[r.1]? = none ∧
    (∀ k, r.2.nodes[k]? ≠ none → k < r.2.nextName) ∧
    r.1 < r.2.nextName := by
  revert h_node_init h_st_init h_not_in h_fresh h_name h_name_ne
  apply expand.partial_correctness
    (motive := fun node st r =>
      (node.incoming.contains expandInit →
        node.oldHas φ_top ∨ φ_top ∈ node.new) →
      (∀ (k : Nat) (n : GBANode α), st.nodes[k]? = some n →
        n.incoming.contains expandInit → n.old.contains φ_top) →
      st.nodes[node.name]? = none →
      (∀ k, st.nodes[k]? ≠ none → k < st.nextName) →
      node.name < st.nextName →
      node.name ≠ expandInit →
      (∀ (k : Nat) (n : GBANode α), r.2.nodes[k]? = some n →
        n.incoming.contains expandInit → n.old.contains φ_top) ∧
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
      (node.old.insert node.new.head!).contains φ_top = true ∨ φ_top ∈ new' := by
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
          have hφ_target := GBANode.sameSignature_old_left target node hsig φ_top hφ
          rw [hk_eq] at hk
          obtain ⟨n', hn', hold, _⟩ := mergeIncoming_reverse st node existingName existingName n hk
          rw [htarget] at hn'; obtain rfl := Option.some.inj hn'
          exact (hold φ_top).mpr hφ_target
        · exact absurd hφ (by simp)
    | none =>
      -- Insert + successor
      simp only [freshName] at h_result
      have h_st_init' : ∀ (k : Nat) (n : GBANode α),
          (st.nodes.insert node.name node)[k]? = some n →
          n.incoming.contains expandInit → n.old.contains φ_top := by
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

/-- Expand preserves the successor_old property:
    for finished nodes, predecessors' next ⊆ node's old. -/
theorem expand_successor_old (node : GBANode α) (st : ExpandState α)
    {r : Nat × ExpandState α}
    (h_result : expand node st = some r)
    (h_st_succ : ∀ (k : Nat) (n : GBANode α), st.nodes[k]? = some n →
      ∀ k', k' ≠ expandInit → n.incoming.contains k' →
      ∃ (n' : GBANode α), st.nodes[k']? = some n' ∧ ∀ ψ, n'.next.contains ψ → n.old.contains ψ)
    (h_node_succ : ∀ k', k' ≠ expandInit → node.incoming.contains k' →
      ∃ (n' : GBANode α), st.nodes[k']? = some n' ∧ ∀ ψ, n'.next.contains ψ → node.oldHas ψ ∨ ψ ∈ node.new)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName)
    (h_name_ne : node.name ≠ expandInit) :
    (∀ (k : Nat) (n : GBANode α), r.2.nodes[k]? = some n →
      ∀ k', k' ≠ expandInit → n.incoming.contains k' →
      ∃ (n' : GBANode α), r.2.nodes[k']? = some n' ∧ ∀ ψ, n'.next.contains ψ → n.old.contains ψ) ∧
    NodesPreserved st r.2 ∧
    r.2.nodes[r.1]? = none ∧
    (∀ k, r.2.nodes[k]? ≠ none → k < r.2.nextName) ∧
    r.1 < r.2.nextName ∧
    r.1 ≠ expandInit := by
  revert h_st_succ h_node_succ h_not_in h_fresh h_name h_name_ne
  apply expand.partial_correctness
    (motive := fun node st r =>
      (∀ (k : Nat) (n : GBANode α), st.nodes[k]? = some n →
        ∀ k', k' ≠ expandInit → n.incoming.contains k' →
        ∃ (n' : GBANode α), st.nodes[k']? = some n' ∧ ∀ ψ, n'.next.contains ψ → n.old.contains ψ) →
      (∀ k', k' ≠ expandInit → node.incoming.contains k' →
        ∃ (n' : GBANode α), st.nodes[k']? = some n' ∧ ∀ ψ, n'.next.contains ψ → node.oldHas ψ ∨ ψ ∈ node.new) →
      st.nodes[node.name]? = none →
      (∀ k, st.nodes[k]? ≠ none → k < st.nextName) →
      node.name < st.nextName →
      node.name ≠ expandInit →
      (∀ (k : Nat) (n : GBANode α), r.2.nodes[k]? = some n →
        ∀ k', k' ≠ expandInit → n.incoming.contains k' →
        ∃ (n' : GBANode α), r.2.nodes[k']? = some n' ∧ ∀ ψ, n'.next.contains ψ → n.old.contains ψ) ∧
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
        ∃ (n' : GBANode α), st.nodes[k']? = some n' ∧
        ∀ ψ, n'.next.contains ψ → (node.old.insert node.new.head!).contains ψ = true ∨ ψ ∈ new' := by
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
          · exact (hold ψ).mpr (GBANode.sameSignature_old_left target node hsig ψ hold')
          · exact absurd hmem (by simp)⟩
    | none =>
      -- Insert + successor case
      simp only [freshName] at h_result
      have h_st_succ' : ∀ (k : Nat) (n : GBANode α),
          (st.nodes.insert node.name node)[k]? = some n →
          ∀ k', k' ≠ expandInit → n.incoming.contains k' →
          ∃ (n' : GBANode α), (st.nodes.insert node.name node)[k']? = some n' ∧
          ∀ ψ, n'.next.contains ψ → n.old.contains ψ := by
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
          ∃ (n' : GBANode α), (st.nodes.insert node.name node)[k']? = some n' ∧
          ∀ ψ, n'.next.contains ψ →
            (Std.HashSet.emptyWithCapacity 8 : Std.HashSet (NNF α)).contains ψ ∨
            ψ ∈ node.next.fold (init := []) fun acc f => f :: acc := by
        intro k' _ hk'
        rw [Std.HashSet.contains_insert, Std.HashSet.contains_emptyWithCapacity, Bool.or_false,
            beq_iff_eq] at hk'
        subst hk'
        simp only [Std.HashMap.getElem?_insert, beq_self_eq_true, ↓reduceIte]
        exact ⟨node, rfl, fun ψ hψ => Or.inr (hashset_fold_cons_complete _ ψ hψ)⟩
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
            ∃ (n' : GBANode α), st_mid.nodes[k']? = some n' ∧
            ∀ ψ, n'.next.contains ψ → (node.old.insert node.new.head!).contains ψ = true ∨
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

omit [LawfulBEq α] [LawfulHashable α] in
private theorem mergeIncoming_keys_subset (st : ExpandState α) (node : GBANode α)
    (targetName : Nat) (k : Nat) (hk : (mergeIncoming st node targetName).nodes[k]? ≠ none) :
    st.nodes[k]? ≠ none := by
  unfold mergeIncoming at hk; split at hk
  · rename_i target htarget
    simp only [Std.HashMap.getElem?_insert] at hk; split at hk
    · rename_i heq; rw [← (beq_iff_eq (α := Nat)).mp heq]; simp [htarget]
    · exact hk
  · exact hk

omit [LawfulBEq α] [LawfulHashable α] in
private theorem expand_no_init_key (node : GBANode α) (st : ExpandState α)
    {r : Nat × ExpandState α}
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

theorem createGraph_spec (φ : NNF α)
    (h : createGraph φ = some st) :
    ExpandSpec φ st.toNodes := by
  -- Unfold createGraph and split on expand result
  simp only [createGraph] at h
  split at h
  · -- some case: expand succeeded
    rename_i nm finalState heq
    obtain rfl := Option.some.inj h
    -- heq : expand initNode initState = some (nm, finalState)
    -- Initial state satisfies StateInv (no nodes)
    have h_initStateInv : StateInv
        { nextName := 2, nodes := Std.HashMap.emptyWithCapacity 16 : ExpandState α } := by
      intro k n hk; simp at hk
    -- Initial node satisfies ProcessingInv (old is empty)
    have h_initProcInv : ProcessingInv
        ({ name := 1,
           incoming := Std.HashSet.emptyWithCapacity 4 |>.insert expandInit,
           new := [φ],
           old := Std.HashSet.emptyWithCapacity 8,
           next := Std.HashSet.emptyWithCapacity 8 } : GBANode α) := by
      constructor <;> simp (config := { contextual := true }) [GBANode.oldHas, GBANode.reachable,
        GBANode.nextHas, Std.HashSet.contains_emptyWithCapacity]
    -- Get StateInv for final state
    have h_stateInv : StateInv finalState :=
      expand_preserves_stateInv _ _ heq h_initStateInv h_initProcInv
    -- Helper: extract ProcessingInv from StateInv for any node in toNodes
    have bridge : ∀ q, finalState.toNodes q →
        ∃ n, finalState.nodes[q.name]? = some n ∧
          (∀ k, q.incoming k ↔ n.incoming.contains k) ∧
          (∀ ψ, q.old ψ ↔ n.old.contains ψ) ∧
          (∀ ψ, q.next ψ ↔ n.next.contains ψ) ∧
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
          (fun ψ hψ => by simp [GBANode.oldHas, Std.HashSet.contains_emptyWithCapacity] at hψ)
          (fun ψ hψ => by cases hψ with | head => exact .refl | tail _ h => exact nomatch h)
          (fun ψ hψ => by simp [GBANode.nextHas, Std.HashSet.contains_emptyWithCapacity] at hψ)
          (fun k n hk => by simp [Std.HashMap.getElem?_emptyWithCapacity] at hk)
          (fun k n hk => by simp [Std.HashMap.getElem?_emptyWithCapacity] at hk)
        intro q hq ψ hψ
        obtain ⟨n, hn, _, hold, _⟩ := bridge q hq
        exact h_old _ _ hn _ ((hold _).mp hψ)
      next_subformula := by
        have ⟨_, h_next⟩ := expand_subformula_closure φ _ _ heq
          (fun ψ hψ => by simp [GBANode.oldHas, Std.HashSet.contains_emptyWithCapacity] at hψ)
          (fun ψ hψ => by cases hψ with | head => exact .refl | tail _ h => exact nomatch h)
          (fun ψ hψ => by simp [GBANode.nextHas, Std.HashSet.contains_emptyWithCapacity] at hψ)
          (fun k n hk => by simp [Std.HashMap.getElem?_emptyWithCapacity] at hk)
          (fun k n hk => by simp [Std.HashMap.getElem?_emptyWithCapacity] at hk)
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
