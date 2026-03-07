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

private theorem mergeIncoming_nextName (st : ExpandState α) (node : GBANode α) (targetName : Nat) :
    (mergeIncoming st node targetName).nextName = st.nextName := by
  unfold mergeIncoming; split <;> rfl

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

private theorem NodesPreserved_refl (st : ExpandState α) : NodesPreserved st st :=
  fun _k n hk => ⟨n, hk, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

private theorem NodesPreserved_trans {st₁ st₂ st₃ : ExpandState α}
    (h₁₂ : NodesPreserved st₁ st₂) (h₂₃ : NodesPreserved st₂ st₃) :
    NodesPreserved st₁ st₃ := by
  intro k n hk
  obtain ⟨n', hk', ho', hn'⟩ := h₁₂ k n hk
  obtain ⟨n'', hk'', ho'', hn''⟩ := h₂₃ k n' hk'
  exact ⟨n'', hk'', fun ψ => (ho'' ψ).trans (ho' ψ), fun ψ => (hn'' ψ).trans (hn' ψ)⟩

private theorem insert_nodesPreserved (st : ExpandState α) (node : GBANode α)
    (h_not_in : st.nodes[node.name]? = none) :
    NodesPreserved st { st with nodes := st.nodes.insert node.name node } := by
  intro k n hk
  have hne : k ≠ node.name := fun heq => by rw [heq, h_not_in] at hk; simp at hk
  simp only [Std.HashMap.getElem?_insert]; split
  · rename_i heq; exact absurd ((beq_iff_eq (α := Nat)).mp heq).symm hne
  · exact ⟨n, hk, fun ψ => Iff.rfl, fun ψ => Iff.rfl⟩

private theorem insert_fresh_key (st : ExpandState α) (nodeName : Nat) (node : GBANode α)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : nodeName < st.nextName) :
    (st.nodes.insert nodeName node)[st.nextName]? = none := by
  simp only [Std.HashMap.getElem?_insert]; split
  · rename_i heq; have := (beq_iff_eq (α := Nat)).mp heq; omega
  · by_contra h; exact absurd (h_fresh st.nextName h) (by omega)

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

/-- Combined invariants maintained by expandFuel:
    monotonicity, name freshness, freshness invariant preservation. -/
structure ExpandInvariants (st st' : ExpandState α) (nm : Nat) : Prop where
  nodesPreserved : NodesPreserved st st'
  nameFresh : st'.nodes[nm]? = none
  freshInv : ∀ k, st'.nodes[k]? ≠ none → k < st'.nextName
  nameBound : nm < st'.nextName
  nextNameMono : st.nextName ≤ st'.nextName

theorem expandFuel_invariants (fuel : Nat) (node : GBANode α)
    (st : ExpandState α) {nm : Nat} {st' : ExpandState α}
    (h_result : expandFuel fuel node st = some (nm, st'))
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName) :
    ExpandInvariants st st' nm := by
  induction fuel generalizing node st nm st' with
  | zero => simp [expandFuel] at h_result
  | succ fuel ih =>
    unfold expandFuel at h_result
    split at h_result
    case isTrue h_empty =>
      split at h_result
      · -- Merge case
        rename_i existingName _
        simp only [Option.some.injEq, Prod.mk.injEq] at h_result
        obtain ⟨rfl, rfl⟩ := h_result
        exact {
          nodesPreserved := mergeIncoming_nodesPreserved st node existingName
          nameFresh := mergeIncoming_preserves_absent st node existingName _ h_not_in
          freshInv := mergeIncoming_freshInv st node existingName h_fresh
          nameBound := by rw [mergeIncoming_nextName]; exact h_name
          nextNameMono := by rw [mergeIncoming_nextName]; omega
        }
      · -- Insert + recurse
        simp only [freshName] at h_result
        have inv := ih _ _ h_result
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
          simp only [Option.some.injEq, Prod.mk.injEq] at h_result
          obtain ⟨rfl, rfl⟩ := h_result
          exact ⟨NodesPreserved_refl st, h_not_in, h_fresh, h_name, Nat.le.refl⟩
        · exact ih _ _ h_result h_not_in h_fresh h_name
      · split at h_result
        · -- tt
          try rw [if_pos rfl] at h_result
          exact ih _ _ h_result h_not_in h_fresh h_name
        · try rw [if_neg (by decide)] at h_result
          split at h_result
          · -- ff
            try rw [if_pos rfl] at h_result
            simp only [Option.some.injEq, Prod.mk.injEq] at h_result
            obtain ⟨rfl, rfl⟩ := h_result
            exact ⟨NodesPreserved_refl st, h_not_in, h_fresh, h_name, Nat.le.refl⟩
          · try rw [if_neg (by decide)] at h_result
            split at h_result
            · -- deterministic
              try rw [if_pos rfl] at h_result
              exact ih _ _ h_result h_not_in h_fresh h_name
            · -- nondeterministic
              try rw [if_neg (by decide)] at h_result
              split at h_result
              · exact absurd h_result (by simp)
              · rename_i h_branch1
                have inv1 := ih _ _ h_branch1 h_not_in h_fresh h_name
                have inv2 := ih _ _ h_result inv1.nameFresh inv1.freshInv inv1.nameBound
                exact {
                  nodesPreserved := NodesPreserved_trans inv1.nodesPreserved inv2.nodesPreserved
                  nameFresh := inv2.nameFresh
                  freshInv := inv2.freshInv
                  nameBound := inv2.nameBound
                  nextNameMono := Nat.le_trans inv1.nextNameMono inv2.nextNameMono
                }

theorem expandFuel_nodes_preserved (fuel : Nat) (node : GBANode α)
    (st : ExpandState α) {nm : Nat} {st' : ExpandState α}
    (h_result : expandFuel fuel node st = some (nm, st'))
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName) :
    NodesPreserved st st' :=
  (expandFuel_invariants fuel node st h_result h_not_in h_fresh h_name).nodesPreserved

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
    · simp_all [isLiteral, isDeterministic]
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact (h_proc.or_propag μ ψ ha').imp (reach _) (reach _)
    · exact Or.inl (reach_new1 μ (by simp [new1]))
  · intro ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact h_next_sub ψ (h_proc.next_propag ψ ha')
    · simp_all [isLiteral, isDeterministic]
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
    · simp_all [isLiteral, isDeterministic]
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact (h_proc.or_propag μ ψ ha').imp (reach _) (reach _)
    · exact Or.inr (reach_new2 ψ (by simp [new2]))
  · intro ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact h_proc.next_propag ψ ha'
    · simp_all [isLiteral, isDeterministic]
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · exact (h_proc.until_propag μ ψ ha').imp (reach _) (fun ⟨h1, h2⟩ => ⟨reach _ h1, h2⟩)
    · exact Or.inl (reach_new2 ψ (by simp [new2]))
  · intro μ ψ ha; simp only [GBANode.oldHas] at ha
    rcases oldHas_insert ha with ha' | rfl
    · have ⟨h1, h2⟩ := h_proc.release_propag μ ψ ha'
      exact ⟨reach _ h1, h2.imp (reach _) id⟩
    · exact ⟨reach_new2 ψ (by simp [new2]), Or.inl (reach_new2 μ (by simp [new2]))⟩

theorem expandFuel_preserves_stateInv (fuel : Nat) (node : GBANode α)
    (st : ExpandState α) {nm : Nat} {st' : ExpandState α}
    (h_result : expandFuel fuel node st = some (nm, st'))
    (h_inv : StateInv st)
    (h_proc : ProcessingInv node) :
    StateInv st' := by
  induction fuel generalizing node st nm st' with
  | zero => simp [expandFuel] at h_result
  | succ fuel ih =>
    unfold expandFuel at h_result
    split at h_result
    case isTrue h_empty =>
      have h_new_nil : node.new = [] := by
        cases h : node.new with
        | nil => rfl
        | cons _ _ => rw [h] at h_empty; simp [List.isEmpty] at h_empty
      split at h_result
      · rename_i existingName _
        simp only [Option.some.injEq, Prod.mk.injEq] at h_result
        obtain ⟨_, rfl⟩ := h_result
        exact mergeIncoming_stateInv st node existingName h_inv
      · simp only [freshName] at h_result
        have h_inv' : StateInv { st with nodes := st.nodes.insert node.name node } := by
          intro k n hk; simp only [Std.HashMap.getElem?_insert] at hk; split at hk
          · obtain rfl := Option.some.inj hk; exact ⟨h_proc, h_new_nil⟩
          · exact h_inv k n hk
        exact ih _ _ h_result h_inv' (processingInv_empty_old _ fun ψ => by
          simp [Std.HashSet.contains_emptyWithCapacity])
    case isFalse h_not_empty =>
      simp only [Bool.not_eq_true] at h_not_empty
      simp only at h_result
      split at h_result
      · rename_i h_lit
        split at h_result
        · simp only [Option.some.injEq, Prod.mk.injEq] at h_result
          obtain ⟨_, rfl⟩ := h_result; exact h_inv
        · rename_i h_no_neg
          simp only [Bool.not_eq_true] at h_no_neg
          exact ih _ _ h_result h_inv (processingInv_literal h_proc h_not_empty h_lit h_no_neg)
      · rename_i h_not_lit
        split at h_result
        · rename_i h_tt_match
          exact ih _ _ h_result h_inv (processingInv_tt h_proc h_not_empty h_tt_match)
        · try rw [if_neg (by decide)] at h_result
          split at h_result
          · try rw [if_pos rfl] at h_result
            simp only [Option.some.injEq, Prod.mk.injEq] at h_result
            obtain ⟨_, rfl⟩ := h_result; exact h_inv
          · try rw [if_neg (by decide)] at h_result
            rename_i h_not_ff _
            split at h_result
            · rename_i h_det
              try rw [if_pos rfl] at h_result
              exact ih _ _ h_result h_inv
                (processingInv_deterministic h_proc h_not_empty h_det)
            · rename_i h_nondet
              simp only [Bool.not_eq_true] at h_nondet h_not_lit
              try rw [if_neg (by decide)] at h_result
              split at h_result
              · exact absurd h_result (by simp)
              · rename_i h_branch1
                have h_not_tt_prop : ¬ (node.new.head! matches .tt) := by
                  intro hc; cases node.new.head! <;> simp_all [isLiteral]
                have h_not_ff_prop : ¬ (node.new.head! matches .ff) := by
                  intro hc; cases node.new.head! <;> simp_all [isLiteral]
                exact ih _ _ h_result
                  (ih _ _ h_branch1 h_inv
                    (processingInv_nondet1 h_proc h_not_empty h_nondet h_not_lit
                      h_not_tt_prop h_not_ff_prop))
                  (processingInv_nondet2 h_proc h_not_empty h_nondet h_not_lit
                    h_not_tt_prop h_not_ff_prop _)

/-! ## Main correctness theorem

The output of `createGraphFuel` satisfies `ExpandSpec`. -/

theorem createGraphFuel_spec (fuel : Nat) (φ : NNF α)
    (h : createGraphFuel fuel φ = some st) :
    ExpandSpec φ st.toNodes := by
  sorry

end LTLLib
