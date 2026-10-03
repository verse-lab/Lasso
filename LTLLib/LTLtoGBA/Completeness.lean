module

/-
  Completeness of the LTL-to-GBA construction: proves that the graph produced by `createGraph` satisfies
  `GraphComplete` (GPVW95, Gerth et al. 1995) — every node's `old` set implies satisfaction (the forward direction
  of `old ↔ (subformula ∧ satisfied)`), plus `until`-RHS completeness. `GraphComplete` holds unconditionally for
  any `createGraph φ = some st`, so combined with soundness this gives unconditional end-to-end correctness (see
  `Correctness.lean`), with no side hypothesis needed.

  The core argument (`expand_exist`/`expand_all`) is that whenever a node's obligations are all satisfied by some
  ξ, `expand` is guaranteed to produce a finished successor node whose obligations are satisfied by `ξ.drop 1`, and
  iterating this builds the run witnessing `GraphComplete` (`createGraph_graphComplete`).

  Defines:
  - `ExpandAssmExist`/`ExpandRsltExistProp`: pre/postconditions for `expand_exist`
  - `NodesPreservedInc`: `NodesPreserved` (`Invariants.lean`) with incoming sets allowed to grow
  - `ExpandNPIResult`: `ExpandInvariants` (`Invariants.lean`) bundled with `NodesPreservedInc`
  - `NodeSemanticValid`: semantic validity of a finished node's `old`/`next`
  - `GraphComplete`: the completeness property `createGraph` actually establishes

  Proves:
  - `expand_exist`: a node whose obligations are all satisfied by ξ has a semantically-valid finished successor
    in `expand`'s output
  - `expand_nodesPreservedInc`: nodes already in the input state survive `expand`, with unchanged `old`/`next`
    and only-growing `incoming`
  - `expand_all`: every newly-added semantically-valid finished node has a semantically-valid successor reachable
    via `incoming`
  - `createGraph_exist`/`createGraph_all`: lift the above from `expand` to `createGraph`
  - `createGraph_graphComplete`: assembles a full run witnessing `GraphComplete`
  - `expandOASpec_completeness`: `GraphComplete` + `ExpandSpec` give acceptance of `expandOASpec`

  ## Sections
  - Semantic preconditions and postconditions
  - Semantic unfolding helpers
  - Node preservation with incoming growth
  - Combined result structure for expand inductions
  - Theorem 1: expand_exist
  - Theorem 2: expand_nodesPreservedInc
  - Key-equals-name invariant
  - Theorem 3: expand_all
  - Lifting to createGraph level
  - GraphComplete: completeness property sufficient for correctness
  - Helper: drop shifting for NodeSemanticValid
  - Main theorem: GraphComplete from createGraph
  - Completeness from GraphComplete
-/

public import LTLLib.LTLtoGBA.Invariants
public import LTLLib.LTLtoGBA.Bridge

public section

namespace LTLLib

open NNF Lentil

variable {α : Type u} {S : Type v} [FSet (NNF α) S] [Hashable (NNF α)] [BEq (NNF α)] [LawfulBEq (NNF α)]

/-! ## Semantic preconditions and postconditions -/

/-- Precondition for `expand_exist`: all formulas in the node are satisfied by ξ, and Until-RHS formulas that are satisfied
    are reachable (in old ∪ new). -/
structure ExpandAssmExist (ξ : OmegaWord α) (node : ExpansionNode α S) : Prop where
  new_sat : ∀ ψ, ψ ∈ node.new → NNF.satisfies ξ ψ
  old_sat : ∀ ψ, FSet.contains node.old ψ → NNF.satisfies ξ ψ
  next_sat : ∀ ψ, FSet.contains node.next ψ → NNF.satisfies (ξ.drop 1) ψ
  until_rhs : ∀ η μ, FSet.contains node.old (.until μ η) → NNF.satisfies ξ η →
    FSet.contains node.old η ∨ η ∈ node.new

/-- Postcondition node property for `expand_exist`: the finished node inherits incoming, and all its formulas are
    semantically valid. -/
structure ExpandRsltExistProp (ξ : OmegaWord α) (node nd : ExpansionNode α S) : Prop where
  incoming_sub : ∀ k, node.incoming.contains k → nd.incoming.contains k
  old_sat : ∀ ψ, FSet.contains nd.old ψ → NNF.satisfies ξ ψ
  next_sat : ∀ ψ, FSet.contains nd.next ψ → NNF.satisfies (ξ.drop 1) ψ
  until_rhs : ∀ η μ, FSet.contains nd.old (.until μ η) → NNF.satisfies ξ η →
    FSet.contains nd.old η

/-! ## Semantic unfolding helpers -/

omit [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem satisfies_and_iff (ξ : OmegaWord α) (μ η : NNF α) :
    NNF.satisfies ξ (.and μ η) ↔ NNF.satisfies ξ μ ∧ NNF.satisfies ξ η :=
  Iff.rfl

omit [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem satisfies_or_iff (ξ : OmegaWord α) (μ η : NNF α) :
    NNF.satisfies ξ (.or μ η) ↔ NNF.satisfies ξ μ ∨ NNF.satisfies ξ η :=
  Iff.rfl

omit [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem satisfies_next_iff (ξ : OmegaWord α) (ψ : NNF α) :
    NNF.satisfies ξ (.next ψ) ↔ NNF.satisfies (ξ.drop 1) ψ :=
  NNF.satisfies_next ξ ψ

omit [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem satisfies_until_expand (ξ : OmegaWord α) (μ η : NNF α) :
    NNF.satisfies ξ (.until μ η) →
    NNF.satisfies ξ η ∨ (NNF.satisfies ξ μ ∧ NNF.satisfies (ξ.drop 1) (.until μ η)) := by
  simp only [NNF.satisfies_until]
  intro ⟨j, hη, hμ⟩
  cases j with
  | zero => left; exact hη
  | succ j' =>
    right; refine ⟨hμ 0 (Nat.zero_lt_succ _), j', ?_, ?_⟩
    · have : (ξ.drop 1).drop j' = ξ.drop (j' + 1) := by rw [exec.drop_drop, Nat.add_comm]
      rw [this]; exact hη
    · intro i hi
      have : (ξ.drop 1).drop i = ξ.drop (i + 1) := by rw [exec.drop_drop, Nat.add_comm]
      rw [this]; exact hμ (i + 1) (by omega)

omit [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem satisfies_release_expand (ξ : OmegaWord α) (μ η : NNF α) :
    NNF.satisfies ξ (.release μ η) →
    NNF.satisfies ξ η ∧ (NNF.satisfies ξ μ ∨ NNF.satisfies (ξ.drop 1) (.release μ η)) := by
  simp only [NNF.satisfies_release]
  intro h
  refine ⟨?_, ?_⟩
  · have := h 0; simp [exec.drop] at this; exact this
  · by_cases hμ : NNF.satisfies ξ μ
    · exact Or.inl hμ
    · right; intro j
      have hdrop : (ξ.drop 1).drop j = ξ.drop (j + 1) := by rw [exec.drop_drop, Nat.add_comm]
      have := h (j + 1)
      rcases this with hη' | ⟨i, hi, hμ'⟩
      · left; rw [hdrop]; exact hη'
      · cases i with
        | zero => exact absurd hμ' hμ
        | succ i' =>
          have hdrop' : (ξ.drop 1).drop i' = ξ.drop (i' + 1) := by rw [exec.drop_drop, Nat.add_comm]
          right; exact ⟨i', by omega, by rw [hdrop']; exact hμ'⟩

omit [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem satisfies_tt (ξ : OmegaWord α) :
    NNF.satisfies ξ .tt := trivial

omit [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem not_satisfies_ff (ξ : OmegaWord α) :
    ¬ NNF.satisfies ξ .ff :=
  not_false

omit [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem satisfies_prop_neg (ξ : OmegaWord α) (a : α) :
    NNF.satisfies ξ (.prop a) → ¬ NNF.satisfies ξ (.nprop a) :=
  fun h hn => hn h

/-! ## Node preservation with incoming growth

Extends `NodesPreserved` to also track that incoming sets grow monotonically. -/

/-- Nodes are preserved with possibly enlarged incoming sets. -/
@[expose] def NodesPreservedInc (st st' : ExpandState α S) : Prop :=
  ∀ (k : Nat) (n : ExpansionNode α S), st.nodes[k]? = some n →
    ∃ n' : ExpansionNode α S, st'.nodes[k]? = some n' ∧
      (∀ ψ, FSet.contains n'.old ψ ↔ FSet.contains n.old ψ) ∧
      (∀ ψ, FSet.contains n'.next ψ ↔ FSet.contains n.next ψ) ∧
      (∀ j, n.incoming.contains j → n'.incoming.contains j)

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem NodesPreservedInc_refl (st : ExpandState α S) : NodesPreservedInc st st :=
  fun _k n hk => ⟨n, hk, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ h => h⟩

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem NodesPreservedInc_trans {st₁ st₂ st₃ : ExpandState α S}
    (h₁₂ : NodesPreservedInc st₁ st₂) (h₂₃ : NodesPreservedInc st₂ st₃) :
    NodesPreservedInc st₁ st₃ := by
  intro k n hk
  obtain ⟨n', hk', ho', hn', hi'⟩ := h₁₂ k n hk
  obtain ⟨n'', hk'', ho'', hn'', hi''⟩ := h₂₃ k n' hk'
  exact ⟨n'', hk'', fun ψ => (ho'' ψ).trans (ho' ψ), fun ψ => (hn'' ψ).trans (hn' ψ),
         fun j hj => hi'' j (hi' j hj)⟩

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem mergeIncoming_nodesPreservedInc (st : ExpandState α S) (node : ExpansionNode α S) (targetName : Nat) :
    NodesPreservedInc st (mergeIncoming st node targetName) := by
  intro k n hk; unfold mergeIncoming; simp only
  split
  · rename_i target htarget
    simp only [Std.HashMap.getElem?_insert]; split
    · rename_i hk_eq
      have : k = targetName := by rw [beq_iff_eq] at hk_eq; exact hk_eq.symm
      subst this; rw [htarget] at hk; obtain rfl := Option.some.inj hk
      refine ⟨_, rfl, fun ψ => Iff.rfl, fun ψ => Iff.rfl, ?_⟩
      intro j hj
      simp [Std.HashSet.contains_union, hj]
    · exact ⟨n, hk, fun ψ => Iff.rfl, fun ψ => Iff.rfl, fun _ h => h⟩
  · exact ⟨n, hk, fun ψ => Iff.rfl, fun ψ => Iff.rfl, fun _ h => h⟩

omit [FSet (NNF α) S] [Hashable (NNF α)] [BEq (NNF α)] [LawfulBEq (NNF α)] in
private theorem mergeIncoming_source_incoming (st : ExpandState α S) (node : ExpansionNode α S)
    (targetName : Nat) {target : ExpansionNode α S}
    (htarget : st.nodes[targetName]? = some target) (j : Nat)
    (hj : node.incoming.contains j) :
    ∃ nd', (mergeIncoming st node targetName).nodes[targetName]? = some nd' ∧
      nd'.incoming.contains j := by
  simp only [mergeIncoming, htarget, Std.HashMap.getElem?_insert, beq_self_eq_true, ↓reduceIte]
  exact ⟨_, rfl, by simp [Std.HashSet.contains_union, hj]⟩

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem insert_nodesPreservedInc (st : ExpandState α S) (node : ExpansionNode α S)
    (h_not_in : st.nodes[node.name]? = none) :
    NodesPreservedInc st { st with nodes := st.nodes.insert node.name node } := by
  intro k n hk
  have hne : k ≠ node.name := fun heq => by rw [heq, h_not_in] at hk; simp at hk
  simp only [Std.HashMap.getElem?_insert]; split
  · rename_i heq; exact absurd ((beq_iff_eq (α := Nat)).mp heq).symm hne
  · exact ⟨n, hk, fun ψ => Iff.rfl, fun ψ => Iff.rfl, fun _ h => h⟩

/-! ## Combined result structure for expand inductions -/

/-- `ExpandInvariants`-style bundle (name freshness/bound, `nextName` monotonicity), with `NodesPreservedInc` in place
    of `NodesPreserved`. -/
structure ExpandNPIResult (st st' : ExpandState α S) (nm : Nat) : Prop where
  npi : NodesPreservedInc st st'
  nameFresh : st'.nodes[nm]? = none
  freshInv : ∀ k, st'.nodes[k]? ≠ none → k < st'.nextName
  nameBound : nm < st'.nextName
  nextNameMono : st.nextName ≤ st'.nextName

/-! ## Theorem 1: expand_exist

If all formulas in a node are satisfied by ξ, the expand output contains a finished node where all old formulas
are satisfied. -/

/-! ### addToNew membership helpers -/

omit [Hashable (NNF α)] [BEq (NNF α)] [LawfulBEq (NNF α)] in
private theorem addToNew_foldl_inv' (old : S) (formulas init : List (NNF α)) :
    ∀ ψ, ψ ∈ formulas.foldl (fun acc f => if FSet.contains old f then acc else f :: acc) init →
    ψ ∈ init ∨ ψ ∈ formulas := by
  induction formulas generalizing init with
  | nil => exact fun _ h => Or.inl h
  | cons f rest ih =>
    intro ψ h; simp only [List.foldl] at h
    have h' : ψ ∈ (if FSet.contains old f then init else f :: init) ∨ ψ ∈ rest :=
      ih _ ψ h
    rcases h' with h1 | h2
    · split at h1
      · exact Or.inl h1
      · rcases List.mem_cons.mp h1 with rfl | h1
        · exact Or.inr (.head _)
        · exact Or.inl h1
    · exact Or.inr (.tail _ h2)

omit [Hashable (NNF α)] [BEq (NNF α)] [LawfulBEq (NNF α)] in
private theorem addToNew_mem_inv (node : ExpansionNode α S) (formulas : List (NNF α)) :
    ∀ ψ, ψ ∈ addToNew node formulas → ψ ∈ node.new ∨ ψ ∈ formulas :=
  addToNew_foldl_inv' node.old formulas node.new

omit [Hashable (NNF α)] [BEq (NNF α)] [LawfulBEq (NNF α)] in
private theorem addToNew_foldl_preserves' (old : S) (formulas init : List (NNF α)) :
    ∀ ψ, ψ ∈ init → ψ ∈ formulas.foldl (fun acc f => if FSet.contains old f then acc else f :: acc) init := by
  induction formulas generalizing init with
  | nil => exact fun _ h => h
  | cons f rest ih =>
    intro ψ h; simp only [List.foldl]; apply ih; split <;> [exact h; exact .tail _ h]

omit [Hashable (NNF α)] [BEq (NNF α)] [LawfulBEq (NNF α)] in
private theorem addToNew_mem_preserves (node : ExpansionNode α S) (formulas : List (NNF α)) :
    ∀ ψ, ψ ∈ node.new → ψ ∈ addToNew node formulas :=
  addToNew_foldl_preserves' node.old formulas node.new

omit [Hashable (NNF α)] [BEq (NNF α)] [LawfulBEq (NNF α)] in
private theorem addToNew_foldl_adds' (old : S) (formulas init : List (NNF α)) :
    ∀ ψ, ψ ∈ formulas → FSet.contains old ψ = false →
    ψ ∈ formulas.foldl (fun acc f => if FSet.contains old f then acc else f :: acc) init := by
  induction formulas generalizing init with
  | nil => intro ψ h; simp at h
  | cons f rest ih =>
    intro ψ h hn; simp only [List.foldl]
    rcases List.mem_cons.mp h with rfl | h
    · apply addToNew_foldl_preserves'; simp [hn]
    · exact ih _ ψ h hn

omit [Hashable (NNF α)] [BEq (NNF α)] [LawfulBEq (NNF α)] in
private theorem addToNew_mem_adds (node : ExpansionNode α S) (formulas : List (NNF α)) :
    ∀ ψ, ψ ∈ formulas → FSet.contains node.old ψ = false →
    ψ ∈ addToNew node formulas :=
  addToNew_foldl_adds' node.old formulas node.new

/-! ### addAllToSet membership helper -/

omit [Hashable (NNF α)] in
private theorem addAllToSet_contains (s : S) (fs : List (NNF α)) (ψ : NNF α) :
    FSet.contains s ψ → FSet.contains (addAllToSet s fs) ψ := by
  intro h; unfold addAllToSet
  induction fs generalizing s with
  | nil => exact h
  | cons f rest ih =>
    simp only [List.foldl]; apply ih
    simp [FSet.contains_insert, h]

omit [Hashable (NNF α)] in
private theorem addAllToSet_contains_of_mem (s : S) (fs : List (NNF α)) (ψ : NNF α) :
    ψ ∈ fs → FSet.contains (addAllToSet s fs) ψ := by
  intro h; unfold addAllToSet
  induction fs generalizing s with
  | nil => simp at h
  | cons f rest ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp h with rfl | h
    · apply addAllToSet_contains; simp [FSet.contains_insert]
    · exact ih _ h

/-! ### Helper: oldHas for FSet.insert -/

omit [Hashable (NNF α)] in
private theorem oldHas_insert_cases {s : S} {ψ φ : NNF α}
    (h : FSet.contains (FSet.insert s φ) ψ) : FSet.contains s ψ ∨ ψ = φ := by
  simp [FSet.contains_insert] at h; exact h.symm.imp_left id

/-! ### Helper: the `fun acc f => f :: acc`-fold used to build the successor's `new` list -/

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

/-! ### Main theorem: expand_exist -/

set_option maxHeartbeats 800000 in
private theorem expand_exist_aux (ξ : OmegaWord α) (node : ExpansionNode α S) (st : ExpandState α S)
    {r : Nat × ExpandState α S}
    (h_result : expand node st = some r)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName) :
    (ExpandAssmExist ξ node →
      ∃ (k : Nat) (nd : ExpansionNode α S), r.2.nodes[k]? = some nd ∧
        ExpandRsltExistProp ξ node nd) ∧
    ExpandNPIResult st r.2 r.1 := by
  revert h_not_in h_fresh h_name
  apply expand.partial_correctness
    (motive := fun node st r =>
      st.nodes[node.name]? = none →
      (∀ k, st.nodes[k]? ≠ none → k < st.nextName) →
      node.name < st.nextName →
      (ExpandAssmExist ξ node →
        ∃ (k : Nat) (nd : ExpansionNode α S), r.2.nodes[k]? = some nd ∧
          ExpandRsltExistProp ξ node nd) ∧
      ExpandNPIResult st r.2 r.1)
    _ node st r h_result
  intro expand_ih ih node st r h_result h_not_in h_fresh h_name
  -- Helpers for insert case (same as expand_npi_result)
  have mk_succ_not_in (st' : ExpandState α S) (nn : Nat) (nd : ExpansionNode α S)
      (hni : st'.nodes[nn]? = none) (hfr : ∀ k, st'.nodes[k]? ≠ none → k < st'.nextName)
      (hlt : nn < st'.nextName) :
      (st'.nodes.insert nn nd)[st'.nextName]? = none := by
    simp only [Std.HashMap.getElem?_insert]; split
    · rename_i heq; have := (beq_iff_eq (α := Nat)).mp heq; omega
    · by_contra h; exact absurd (hfr st'.nextName h) (by omega)
  have mk_succ_fresh (st' : ExpandState α S) (nn : Nat) (nd : ExpansionNode α S)
      (hfr : ∀ k, st'.nodes[k]? ≠ none → k < st'.nextName) (hlt : nn < st'.nextName) :
      ∀ k, (st'.nodes.insert nn nd)[k]? ≠ none → k < st'.nextName + 1 := by
    intro k hk; simp only [Std.HashMap.getElem?_insert] at hk; split at hk
    · rename_i heq; have := (beq_iff_eq (α := Nat)).mp heq; omega
    · exact Nat.lt_succ_of_lt (hfr k hk)
  -- Helper: until_rhs transfer when new ∈ head!::tail!
  have until_rhs_transfer (h_assm : ExpandAssmExist ξ node)
      (hne : node.new.isEmpty = false) (η μ : NNF α)
      (hold : FSet.contains node.old (.until μ η))
      (hη : NNF.satisfies ξ η)
      (new' : List (NNF α)) (hsub : ∀ ψ, ψ ∈ node.new.tail! → ψ ∈ new') :
      FSet.contains (FSet.insert node.old node.new.head!) η ∨ η ∈ new' := by
    rcases h_assm.until_rhs η μ hold hη with hold' | hnew
    · exact Or.inl (by simp [FSet.contains_insert, hold'])
    · cases h_new : node.new with
      | nil => rw [h_new] at hne; simp at hne
      | cons hd tl =>
        simp only [h_new, List.head!, List.tail!] at *
        rcases List.mem_cons.mp hnew with rfl | htail
        · exact Or.inl (by simp [FSet.contains_insert])
        · exact Or.inr (hsub _ htail)
  -- Helper: construct ExpandAssmExist when popping head and inserting into old
  have mk_assm_insert (h_assm : ExpandAssmExist ξ node) (hne : node.new.isEmpty = false)
      (hhead_sat : NNF.satisfies ξ node.new.head!)
      (new' : List (NNF α)) (hsub : ∀ ψ, ψ ∈ node.new.tail! → ψ ∈ new')
      (hnew_sat : ∀ ψ, ψ ∈ new' → NNF.satisfies ξ ψ)
      (h_until_head : ∀ η μ, NNF.until μ η = node.new.head! → NNF.satisfies ξ η →
          FSet.contains (FSet.insert node.old node.new.head!) η ∨ η ∈ new') :
      ExpandAssmExist ξ { node with new := new', old := FSet.insert node.old node.new.head! } := {
    new_sat := hnew_sat
    old_sat := fun ψ hψ => by
      rcases oldHas_insert_cases hψ with hold | rfl
      · exact h_assm.old_sat ψ hold
      · exact hhead_sat
    next_sat := h_assm.next_sat
    until_rhs := fun η μ hμη hη => by
      rcases oldHas_insert_cases hμη with hold | heq
      · exact until_rhs_transfer h_assm hne η μ hold hη new' hsub
      · exact h_until_head η μ heq hη
  }
  -- Same as `mk_assm_insert`, but also extends `next` (needed for the deterministic case, which can add
  -- obligations to `next` via `next1`).
  have mk_assm_insert_next (h_assm : ExpandAssmExist ξ node) (hne : node.new.isEmpty = false)
      (hhead_sat : NNF.satisfies ξ node.new.head!)
      (new' : List (NNF α)) (hsub : ∀ ψ, ψ ∈ node.new.tail! → ψ ∈ new')
      (hnew_sat : ∀ ψ, ψ ∈ new' → NNF.satisfies ξ ψ)
      (next' : S) (hnext_sat : ∀ ψ, FSet.contains next' ψ → NNF.satisfies (ξ.drop 1) ψ)
      (h_until_head : ∀ η μ, NNF.until μ η = node.new.head! → NNF.satisfies ξ η →
          FSet.contains (FSet.insert node.old node.new.head!) η ∨ η ∈ new') :
      ExpandAssmExist ξ
        { node with new := new', old := FSet.insert node.old node.new.head!, next := next' } := {
    new_sat := hnew_sat
    old_sat := fun ψ hψ => by
      rcases oldHas_insert_cases hψ with hold | rfl
      · exact h_assm.old_sat ψ hold
      · exact hhead_sat
    next_sat := hnext_sat
    until_rhs := fun η μ hμη hη => by
      rcases oldHas_insert_cases hμη with hold | heq
      · exact until_rhs_transfer h_assm hne η μ hold hη new' hsub
      · exact h_until_head η μ heq hη
  }
  split at h_result
  case isTrue h_empty =>
    have h_new_nil : node.new = [] := by
      cases h : node.new with
      | nil => rfl
      | cons _ _ => rw [h] at h_empty; simp [List.isEmpty] at h_empty
    generalize h_fd : findDuplicate st node = fd at h_result
    cases fd with
    | some existingName =>
      -- MERGE CASE
      obtain rfl := Option.some.inj h_result
      obtain ⟨target, htarget, hsig⟩ := findDuplicate_spec st node existingName h_fd
      -- Characterize the merged node
      have h_merged : (mergeIncoming st node existingName).nodes[existingName]? =
          some { target with incoming := target.incoming.union node.incoming } := by
        simp only [mergeIncoming, htarget, Std.HashMap.getElem?_insert, beq_self_eq_true,
          ↓reduceIte]
      constructor
      · -- exist part
        intro h_assm
        refine ⟨existingName, _, h_merged, ?_⟩
        constructor
        · -- incoming_sub
          intro k hk; simp [Std.HashSet.contains_union, hk]
        · -- old_sat: nd'.old = target.old, and target has same old as node
          intro ψ hψ
          exact h_assm.old_sat ψ (ExpansionNode.sameSignature_old_right target node hsig ψ hψ)
        · -- next_sat: nd'.next = target.next, and target has same next as node
          intro ψ hψ
          have h_next := (Bool.and_eq_true_iff.mp hsig).2
          exact h_assm.next_sat ψ (((FSet.setEq_correct target.next node.next).mp h_next).1 ψ hψ)
        · -- until_rhs: nd'.old = target.old = node.old, and node.new = []
          intro η μ hμη hη
          have hμη_node := ExpansionNode.sameSignature_old_right target node hsig _ hμη
          rcases h_assm.until_rhs η μ hμη_node hη with hold | hnew
          · exact ExpansionNode.sameSignature_old_left target node hsig η hold
          · rw [h_new_nil] at hnew; exact absurd hnew (by simp)
      · -- NPI part
        have h_mn : (mergeIncoming st node existingName).nextName = st.nextName := by
          unfold mergeIncoming; split <;> rfl
        constructor
        · exact mergeIncoming_nodesPreservedInc st node existingName
        · unfold mergeIncoming; split
          · simp only [Std.HashMap.getElem?_insert]; split
            · rename_i _ heq; have := (beq_iff_eq (α := Nat)).mp heq
              rw [← this] at h_not_in; simp_all
            · exact h_not_in
          · exact h_not_in
        · intro k hk; rw [h_mn]; apply h_fresh
          unfold mergeIncoming at hk; split at hk
          · rename_i target' htarget'
            simp only [Std.HashMap.getElem?_insert] at hk; split at hk
            · rename_i heq; rw [← (beq_iff_eq (α := Nat)).mp heq]; simp [htarget']
            · exact hk
          · exact hk
        · rw [h_mn]; exact h_name
        · rw [h_mn]; exact Nat.le_refl _
    | none =>
      -- INSERT + RECURSE CASE
      simp only [freshName] at h_result
      have ih_result := ih _ _ _ h_result
        (mk_succ_not_in st node.name node h_not_in h_fresh h_name)
        (mk_succ_fresh st node.name node h_fresh h_name)
        (by show st.nextName < st.nextName + 1; omega)
      constructor
      · -- exist part
        intro h_assm
        obtain ⟨npi, _, _, _, _⟩ := ih_result.2
        obtain ⟨nd', hnd', hold', hnext', hinc'⟩ := npi node.name node
          (by simp only [ExpandState.addNode, Std.HashMap.getElem?_insert, beq_self_eq_true, ↓reduceIte])
        exact ⟨node.name, nd', hnd', {
          incoming_sub := fun k hk => hinc' k hk
          old_sat := fun ψ hψ => h_assm.old_sat ψ ((hold' ψ).mp hψ)
          next_sat := fun ψ hψ => h_assm.next_sat ψ ((hnext' ψ).mp hψ)
          until_rhs := fun η μ hμη hη => by
            have hμη_node := (hold' _).mp hμη
            rcases h_assm.until_rhs η μ hμη_node hη with hold | hnew
            · exact (hold' η).mpr hold
            · rw [h_new_nil] at hnew; exact absurd hnew (by simp)
        }⟩
      · -- NPI part
        exact ⟨NodesPreservedInc_trans (insert_nodesPreservedInc st node h_not_in) ih_result.2.npi,
          ih_result.2.nameFresh, ih_result.2.freshInv, ih_result.2.nameBound,
          Nat.le_trans (Nat.le_succ _) ih_result.2.nextNameMono⟩
  case isFalse h_not_empty =>
    simp only [Bool.not_eq_true] at h_not_empty
    simp only at h_result
    split at h_result
    · -- isLiteral
      split at h_result
      · -- LITERAL CONTRADICTION CASE
        obtain rfl := Option.some.inj h_result
        constructor
        · intro h_assm
          exfalso
          have h_φ_sat := h_assm.new_sat node.new.head!
            (head!_mem_of_isEmpty_false h_not_empty)
          have h_neg_sat := h_assm.old_sat _ ‹_›
          revert h_φ_sat h_neg_sat
          generalize node.new.head! = φ at *
          intro h_φ_sat h_neg_sat
          cases φ with
          | prop a => exact satisfies_prop_neg ξ a h_φ_sat h_neg_sat
          | nprop a => exact h_φ_sat h_neg_sat
          | _ => simp [isLiteral] at *
        · exact ⟨NodesPreservedInc_refl st, h_not_in, h_fresh, h_name, Nat.le.refl⟩
      · -- LITERAL NO-CONTRADICTION CASE
        have ih_result := ih _ _ _ h_result h_not_in h_fresh h_name
        constructor
        · intro h_assm
          have h_assm' := mk_assm_insert h_assm h_not_empty
            (h_assm.new_sat _ (head!_mem_of_isEmpty_false h_not_empty))
            node.new.tail! (fun _ h => h)
            (fun ψ hψ => h_assm.new_sat ψ (by
              cases h_new : node.new with
              | nil => rw [h_new] at h_not_empty; simp at h_not_empty
              | cons _ tl => rw [h_new] at hψ; exact .tail _ hψ))
            (fun η μ heq _ => by
              -- head! is a literal, so .until μ η = head! is impossible
              have h_lit : isLiteral node.new.head! = true := ‹_›
              rw [← heq] at h_lit; simp [isLiteral] at h_lit)
          exact (ih_result.1 h_assm').imp fun k ⟨nd, hnd, hprop⟩ => ⟨nd, hnd, {
            incoming_sub := hprop.incoming_sub
            old_sat := hprop.old_sat
            next_sat := hprop.next_sat
            until_rhs := hprop.until_rhs
          }⟩
        · exact ih_result.2
    · -- NOT LITERAL (tt / ff / det / nondet)
      rename_i h_notlit
      split at h_result
      · -- tt case
        have ih_result := ih _ _ _ h_result h_not_in h_fresh h_name
        exact ⟨fun h_assm => by
          have h_assm' := mk_assm_insert h_assm h_not_empty
            (h_assm.new_sat _ (head!_mem_of_isEmpty_false h_not_empty))
            node.new.tail! (fun _ h => h)
            (fun ψ hψ => h_assm.new_sat ψ (mem_of_mem_tail! hψ))
            (fun η μ heq _ => by grind [isLiteral, isDeterministic])
          exact (ih_result.1 h_assm').imp fun k ⟨nd, hnd, hp⟩ => ⟨nd, hnd,
            ⟨hp.incoming_sub, hp.old_sat, hp.next_sat, hp.until_rhs⟩⟩,
          ih_result.2⟩
      · rename_i h_nottt
        split at h_result
        · -- unreachable: auxiliary matcher artifact (h : false = true)
          rename_i h
          exact absurd h (by decide)
        · split at h_result
          · -- real ff case
            rename_i heq
            obtain rfl := Option.some.inj h_result
            refine ⟨fun h_assm => absurd (h_assm.new_sat node.new.head!
              (head!_mem_of_isEmpty_false h_not_empty))
              (by rw [heq]; exact not_satisfies_ff ξ),
              NodesPreservedInc_refl st, h_not_in, h_fresh, h_name, Nat.le.refl⟩
          · rename_i h_notff
            split at h_result
            · -- unreachable: auxiliary matcher artifact
              rename_i h
              exact absurd h (by decide)
            · -- real isDeterministic split
              split at h_result
              · -- det case (and / next)
                rename_i hdet
                have ih_result := ih _ _ _ h_result h_not_in h_fresh h_name
                refine ⟨fun h_assm => ?_, ih_result.2⟩
                have h_head_sat := h_assm.new_sat _ (head!_mem_of_isEmpty_false h_not_empty)
                have h_assm' : ExpandAssmExist ξ
                    { node with
                      new := addToNew { node with new := node.new.tail! } (new1 node.new.head!)
                      old := FSet.insert node.old node.new.head!
                      next := addAllToSet node.next (next1 node.new.head!) } := by
                  apply mk_assm_insert_next h_assm h_not_empty h_head_sat
                  · -- hsub : tail ⊆ new'
                    exact fun ψ hψ => addToNew_mem_preserves { node with new := node.new.tail! }
                      (new1 node.new.head!) ψ hψ
                  · -- hnew_sat : new' satisfied by ξ
                    intro ψ hψ
                    rcases addToNew_mem_inv { node with new := node.new.tail! }
                        (new1 node.new.head!) ψ hψ with hold | hnew
                    · exact h_assm.new_sat ψ (mem_of_mem_tail! hold)
                    · revert hnew h_head_sat hdet
                      generalize node.new.head! = φ
                      intro hdet h_head_sat hnew
                      cases φ with
                      | and μ η =>
                        obtain ⟨hμ, hη⟩ := (satisfies_and_iff ξ μ η).mp h_head_sat
                        simp only [new1, List.mem_cons, List.not_mem_nil, _root_.or_false] at hnew
                        rcases hnew with rfl | rfl
                        · exact hμ
                        · exact hη
                      | next η => simp [new1] at hnew
                      | _ => simp [isDeterministic] at hdet
                  · -- hnext_sat : next' satisfied by ξ.drop 1
                    intro ψ hψ
                    rcases addAllToSet_inv node.next (next1 node.new.head!) ψ hψ
                        with hold | hnew
                    · exact h_assm.next_sat ψ hold
                    · revert hnew h_head_sat hdet
                      generalize node.new.head! = φ
                      intro hdet h_head_sat hnew
                      cases φ with
                      | next η =>
                        simp only [next1, List.mem_cons, List.not_mem_nil, _root_.or_false] at hnew
                        subst hnew
                        exact (satisfies_next_iff ξ ψ).mp h_head_sat
                      | and μ η => simp [next1] at hnew
                      | _ => simp [isDeterministic] at hdet
                  · -- until_rhs: head! is deterministic, so .until μ η = head! is impossible
                    intro η μ heq _
                    rw [← heq] at hdet
                    simp [isDeterministic] at hdet
                exact (ih_result.1 h_assm').imp fun k ⟨nd, hnd, hp⟩ => ⟨nd, hnd,
                  ⟨hp.incoming_sub, hp.old_sat, hp.next_sat, hp.until_rhs⟩⟩
              · -- nondet case (or / until / release)
                rename_i hndet
                simp only [Bind.bind, Option.bind] at h_result
                split at h_result
                · simp at h_result
                · rename_i p heq1
                  have ih1 := ih _ _ _ heq1 h_not_in h_fresh h_name
                  have ih2 := ih _ _ _ h_result ih1.2.nameFresh ih1.2.freshInv ih1.2.nameBound
                  refine ⟨fun h_assm => ?_, ⟨NodesPreservedInc_trans ih1.2.npi ih2.2.npi,
                    ih2.2.nameFresh, ih2.2.freshInv, ih2.2.nameBound,
                    Nat.le_trans ih1.2.nextNameMono ih2.2.nextNameMono⟩⟩
                  have h_head_sat := h_assm.new_sat _ (head!_mem_of_isEmpty_false h_not_empty)
                  have transport1 : ∀ {k : Nat} {nd : ExpansionNode α S},
                      p.snd.nodes[k]? = some nd → ExpandRsltExistProp ξ node nd →
                      ∃ (k' : Nat) (nd' : ExpansionNode α S), r.snd.nodes[k']? = some nd' ∧
                        ExpandRsltExistProp ξ node nd' := by
                    intro k nd hnd hp
                    obtain ⟨nd', hnd', hold', hnext', hinc'⟩ := ih2.2.npi k nd hnd
                    exact ⟨k, nd', hnd', {
                      incoming_sub := fun j hj => hinc' j (hp.incoming_sub j hj)
                      old_sat := fun ψ hψ => hp.old_sat ψ ((hold' ψ).mp hψ)
                      next_sat := fun ψ hψ => hp.next_sat ψ ((hnext' ψ).mp hψ)
                      until_rhs := fun η μ hμη hη' =>
                        (hold' η).mpr (hp.until_rhs η μ ((hold' _).mp hμη) hη')
                    }⟩
                  cases hφ : node.new.head! with
                  | tt => exact absurd hφ h_nottt
                  | ff => exact absurd hφ h_notff
                  | prop a => simp [hφ, isLiteral] at h_notlit
                  | nprop a => simp [hφ, isLiteral] at h_notlit
                  | and μ η => simp [hφ, isDeterministic] at hndet
                  | or μ η =>
                    have h_head_sat' : NNF.satisfies ξ (NNF.or μ η) := hφ ▸ h_head_sat
                    by_cases hη : NNF.satisfies ξ η
                    · -- x2 branch (selector true): new2(or μ η) = [η]
                      have h_assm2 : ExpandAssmExist ξ
                          { node with
                            new := addToNew { node with new := node.new.tail! }
                              (new2 node.new.head!)
                            old := FSet.insert node.old node.new.head! } := by
                        apply mk_assm_insert h_assm h_not_empty h_head_sat
                        · exact fun ψ hψ => addToNew_mem_preserves
                            { node with new := node.new.tail! } (new2 node.new.head!) ψ hψ
                        · intro ψ hψ
                          rcases addToNew_mem_inv { node with new := node.new.tail! }
                              (new2 node.new.head!) ψ hψ with hold | hnew
                          · exact h_assm.new_sat ψ (mem_of_mem_tail! hold)
                          · rw [hφ] at hnew; simp only [new2, List.mem_singleton] at hnew
                            exact hnew ▸ hη
                        · intro η' μ' heq _
                          rw [hφ] at heq; simp at heq
                      have h_assm2' : ExpandAssmExist ξ
                          { node with
                            name := p.fst
                            new := addToNew { node with new := node.new.tail! }
                              (new2 node.new.head!)
                            old := FSet.insert node.old node.new.head! } :=
                        ⟨h_assm2.new_sat, h_assm2.old_sat, h_assm2.next_sat, h_assm2.until_rhs⟩
                      obtain ⟨k, nd, hnd, hp⟩ := ih2.1 h_assm2'
                      exact ⟨k, nd, hnd, ⟨hp.incoming_sub, hp.old_sat, hp.next_sat, hp.until_rhs⟩⟩
                    · -- x1 branch (selector false): μ must hold
                      have hμ : NNF.satisfies ξ μ :=
                        ((satisfies_or_iff ξ μ η).mp h_head_sat').resolve_right hη
                      have h_assm1 : ExpandAssmExist ξ
                          { node with
                            new := addToNew { node with new := node.new.tail! }
                              (new1 node.new.head!)
                            old := FSet.insert node.old node.new.head!
                            next := addAllToSet node.next (next1 node.new.head!) } := by
                        apply mk_assm_insert_next h_assm h_not_empty h_head_sat
                        · exact fun ψ hψ => addToNew_mem_preserves
                            { node with new := node.new.tail! } (new1 node.new.head!) ψ hψ
                        · intro ψ hψ
                          rcases addToNew_mem_inv { node with new := node.new.tail! }
                              (new1 node.new.head!) ψ hψ with hold | hnew
                          · exact h_assm.new_sat ψ (mem_of_mem_tail! hold)
                          · rw [hφ] at hnew; simp only [new1, List.mem_singleton] at hnew
                            exact hnew ▸ hμ
                        · intro ψ hψ
                          rcases addAllToSet_inv node.next (next1 node.new.head!) ψ hψ
                              with hold | hnew
                          · exact h_assm.next_sat ψ hold
                          · rw [hφ] at hnew; simp [next1] at hnew
                        · intro η' μ' heq _
                          rw [hφ] at heq; simp at heq
                      obtain ⟨k, nd, hnd, hp⟩ := ih1.1 h_assm1
                      exact transport1 hnd
                        ⟨hp.incoming_sub, hp.old_sat, hp.next_sat, hp.until_rhs⟩
                  | next η => simp [hφ, isDeterministic] at hndet
                  | «until» μ η =>
                    have h_head_sat' : NNF.satisfies ξ (NNF.until μ η) := hφ ▸ h_head_sat
                    by_cases hη : NNF.satisfies ξ η
                    · -- x2 branch (selector true): new2(until μ η) = [η]
                      have h_assm2 : ExpandAssmExist ξ
                          { node with
                            new := addToNew { node with new := node.new.tail! }
                              (new2 node.new.head!)
                            old := FSet.insert node.old node.new.head! } := by
                        apply mk_assm_insert h_assm h_not_empty h_head_sat
                        · exact fun ψ hψ => addToNew_mem_preserves
                            { node with new := node.new.tail! } (new2 node.new.head!) ψ hψ
                        · intro ψ hψ
                          rcases addToNew_mem_inv { node with new := node.new.tail! }
                              (new2 node.new.head!) ψ hψ with hold | hnew
                          · exact h_assm.new_sat ψ (mem_of_mem_tail! hold)
                          · rw [hφ] at hnew; simp only [new2, List.mem_singleton] at hnew
                            exact hnew ▸ hη
                        · intro η' μ' heq hη'
                          rw [hφ] at heq
                          injection heq with hμeq hηeq
                          rw [hηeq] at hη' ⊢
                          by_cases hold : FSet.contains node.old η = true
                          · exact Or.inl (by simp [FSet.contains_insert, hold])
                          · refine Or.inr ?_
                            rw [hφ]
                            exact addToNew_mem_adds { node with new := node.new.tail! }
                              (new2 (NNF.until μ η)) η (by simp [new2])
                              (by simpa using hold)
                      have h_assm2' : ExpandAssmExist ξ
                          { node with
                            name := p.fst
                            new := addToNew { node with new := node.new.tail! }
                              (new2 node.new.head!)
                            old := FSet.insert node.old node.new.head! } :=
                        ⟨h_assm2.new_sat, h_assm2.old_sat, h_assm2.next_sat, h_assm2.until_rhs⟩
                      obtain ⟨k, nd, hnd, hp⟩ := ih2.1 h_assm2'
                      exact ⟨k, nd, hnd, ⟨hp.incoming_sub, hp.old_sat, hp.next_sat, hp.until_rhs⟩⟩
                    · -- x1 branch (selector false): from unfold, μ ∧ next-obligation
                      obtain ⟨hμ, hnext_obl⟩ :=
                        (satisfies_until_expand ξ μ η h_head_sat').resolve_left hη
                      have h_assm1 : ExpandAssmExist ξ
                          { node with
                            new := addToNew { node with new := node.new.tail! }
                              (new1 node.new.head!)
                            old := FSet.insert node.old node.new.head!
                            next := addAllToSet node.next (next1 node.new.head!) } := by
                        apply mk_assm_insert_next h_assm h_not_empty h_head_sat
                        · exact fun ψ hψ => addToNew_mem_preserves
                            { node with new := node.new.tail! } (new1 node.new.head!) ψ hψ
                        · intro ψ hψ
                          rcases addToNew_mem_inv { node with new := node.new.tail! }
                              (new1 node.new.head!) ψ hψ with hold | hnew
                          · exact h_assm.new_sat ψ (mem_of_mem_tail! hold)
                          · rw [hφ] at hnew; simp only [new1, List.mem_singleton] at hnew
                            exact hnew ▸ hμ
                        · intro ψ hψ
                          rcases addAllToSet_inv node.next (next1 node.new.head!) ψ hψ
                              with hold | hnew
                          · exact h_assm.next_sat ψ hold
                          · rw [hφ] at hnew; simp only [next1, List.mem_singleton] at hnew
                            exact hnew ▸ hnext_obl
                        · intro η' μ' heq hη'
                          exfalso; apply hη
                          rw [hφ] at heq
                          injection heq with hμeq hηeq
                          subst hμeq; subst hηeq
                          exact hη'
                      obtain ⟨k, nd, hnd, hp⟩ := ih1.1 h_assm1
                      exact transport1 hnd
                        ⟨hp.incoming_sub, hp.old_sat, hp.next_sat, hp.until_rhs⟩
                  | release μ η =>
                    have h_head_sat' : NNF.satisfies ξ (NNF.release μ η) := hφ ▸ h_head_sat
                    obtain ⟨hη_now, hdisj⟩ := satisfies_release_expand ξ μ η h_head_sat'
                    by_cases hμ : NNF.satisfies ξ μ
                    · -- x2 branch (selector true): new2(release μ η) = [μ, η]
                      have h_assm2 : ExpandAssmExist ξ
                          { node with
                            new := addToNew { node with new := node.new.tail! }
                              (new2 node.new.head!)
                            old := FSet.insert node.old node.new.head! } := by
                        apply mk_assm_insert h_assm h_not_empty h_head_sat
                        · exact fun ψ hψ => addToNew_mem_preserves
                            { node with new := node.new.tail! } (new2 node.new.head!) ψ hψ
                        · intro ψ hψ
                          rcases addToNew_mem_inv { node with new := node.new.tail! }
                              (new2 node.new.head!) ψ hψ with hold | hnew
                          · exact h_assm.new_sat ψ (mem_of_mem_tail! hold)
                          · rw [hφ] at hnew
                            simp only [new2, List.mem_cons, List.not_mem_nil,
                              _root_.or_false] at hnew
                            rcases hnew with rfl | rfl
                            · exact hμ
                            · exact hη_now
                        · intro η' μ' heq _
                          rw [hφ] at heq; simp at heq
                      have h_assm2' : ExpandAssmExist ξ
                          { node with
                            name := p.fst
                            new := addToNew { node with new := node.new.tail! }
                              (new2 node.new.head!)
                            old := FSet.insert node.old node.new.head! } :=
                        ⟨h_assm2.new_sat, h_assm2.old_sat, h_assm2.next_sat, h_assm2.until_rhs⟩
                      obtain ⟨k, nd, hnd, hp⟩ := ih2.1 h_assm2'
                      exact ⟨k, nd, hnd, ⟨hp.incoming_sub, hp.old_sat, hp.next_sat, hp.until_rhs⟩⟩
                    · -- x1 branch (selector false): next-obligation must hold
                      have hnext_obl := hdisj.resolve_left hμ
                      have h_assm1 : ExpandAssmExist ξ
                          { node with
                            new := addToNew { node with new := node.new.tail! }
                              (new1 node.new.head!)
                            old := FSet.insert node.old node.new.head!
                            next := addAllToSet node.next (next1 node.new.head!) } := by
                        apply mk_assm_insert_next h_assm h_not_empty h_head_sat
                        · exact fun ψ hψ => addToNew_mem_preserves
                            { node with new := node.new.tail! } (new1 node.new.head!) ψ hψ
                        · intro ψ hψ
                          rcases addToNew_mem_inv { node with new := node.new.tail! }
                              (new1 node.new.head!) ψ hψ with hold | hnew
                          · exact h_assm.new_sat ψ (mem_of_mem_tail! hold)
                          · rw [hφ] at hnew; simp only [new1, List.mem_singleton] at hnew
                            exact hnew ▸ hη_now
                        · intro ψ hψ
                          rcases addAllToSet_inv node.next (next1 node.new.head!) ψ hψ
                              with hold | hnew
                          · exact h_assm.next_sat ψ hold
                          · rw [hφ] at hnew; simp only [next1, List.mem_singleton] at hnew
                            exact hnew ▸ hnext_obl
                        · intro η' μ' heq _
                          rw [hφ] at heq; simp at heq
                      obtain ⟨k, nd, hnd, hp⟩ := ih1.1 h_assm1
                      exact transport1 hnd
                        ⟨hp.incoming_sub, hp.old_sat, hp.next_sat, hp.until_rhs⟩


/-- A node whose obligations are all satisfied by ξ has a semantically-valid finished successor in `expand`'s
    output. -/
theorem expand_exist (ξ : OmegaWord α) (node : ExpansionNode α S) (st : ExpandState α S)
    {r : Nat × ExpandState α S}
    (h_result : expand node st = some r)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName)
    (h_assm : ExpandAssmExist ξ node) :
    ∃ (k : Nat) (nd : ExpansionNode α S), r.2.nodes[k]? = some nd ∧
      ExpandRsltExistProp ξ node nd :=
  (expand_exist_aux ξ node st h_result h_not_in h_fresh h_name).1 h_assm

/-! ## Theorem 2: expand_nodesPreservedInc

Nodes from the input state survive in the output with same old/next and possibly enlarged incoming sets. -/

omit [BEq (NNF α)] [LawfulBEq (NNF α)] in
private theorem expand_npi_result (node : ExpansionNode α S) (st : ExpandState α S)
    {r : Nat × ExpandState α S}
    (h_result : expand node st = some r)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName) :
    ExpandNPIResult st r.2 r.1 := by
  revert h_not_in h_fresh h_name
  apply expand.partial_correctness
    (motive := fun node st r =>
      st.nodes[node.name]? = none →
      (∀ k, st.nodes[k]? ≠ none → k < st.nextName) →
      node.name < st.nextName →
      ExpandNPIResult st r.2 r.1)
    _ node st r h_result
  intro expand_ih ih node st r h_result h_not_in h_fresh h_name
  -- Helpers for insert case
  have mk_succ_not_in (st' : ExpandState α S) (nn : Nat) (nd : ExpansionNode α S)
      (hni : st'.nodes[nn]? = none) (hfr : ∀ k, st'.nodes[k]? ≠ none → k < st'.nextName)
      (hlt : nn < st'.nextName) :
      (st'.nodes.insert nn nd)[st'.nextName]? = none := by
    simp only [Std.HashMap.getElem?_insert]; split
    · rename_i heq; have := (beq_iff_eq (α := Nat)).mp heq; omega
    · by_contra h; exact absurd (hfr st'.nextName h) (by omega)
  have mk_succ_fresh (st' : ExpandState α S) (nn : Nat) (nd : ExpansionNode α S)
      (hfr : ∀ k, st'.nodes[k]? ≠ none → k < st'.nextName) (hlt : nn < st'.nextName) :
      ∀ k, (st'.nodes.insert nn nd)[k]? ≠ none → k < st'.nextName + 1 := by
    intro k hk; simp only [Std.HashMap.getElem?_insert] at hk; split at hk
    · rename_i heq; have := (beq_iff_eq (α := Nat)).mp heq; omega
    · exact Nat.lt_succ_of_lt (hfr k hk)
  split at h_result
  case isTrue h_empty =>
    split at h_result
    · -- Merge
      rename_i existingName _
      obtain rfl := Option.some.inj h_result
      have h_mn : (mergeIncoming st node existingName).nextName = st.nextName := by
        unfold mergeIncoming; split <;> rfl
      constructor
      · exact mergeIncoming_nodesPreservedInc st node existingName
      · -- nameFresh: mergeIncoming preserves absence
        unfold mergeIncoming; split
        · simp only [Std.HashMap.getElem?_insert]; split
          · rename_i _ heq; have := (beq_iff_eq (α := Nat)).mp heq
            rw [← this] at h_not_in; simp_all
          · exact h_not_in
        · exact h_not_in
      · -- freshInv
        intro k hk
        rw [h_mn]
        apply h_fresh
        unfold mergeIncoming at hk; split at hk
        · rename_i target htarget
          simp only [Std.HashMap.getElem?_insert] at hk; split at hk
          · rename_i heq; rw [← (beq_iff_eq (α := Nat)).mp heq]; simp [htarget]
          · exact hk
        · exact hk
      · -- nameBound
        rw [h_mn]; exact h_name
      · -- nextNameMono
        rw [h_mn]; exact Nat.le_refl _
    · -- Insert + recurse
      simp only [freshName] at h_result
      have res := ih _ _ _ h_result
        (mk_succ_not_in st node.name node h_not_in h_fresh h_name)
        (mk_succ_fresh st node.name node h_fresh h_name)
        (by show st.nextName < st.nextName + 1; omega)
      exact ⟨NodesPreservedInc_trans (insert_nodesPreservedInc st node h_not_in) res.npi,
        res.nameFresh, res.freshInv, res.nameBound,
        Nat.le_trans (Nat.le_succ _) res.nextNameMono⟩
  case isFalse h_not_empty =>
    simp only [Bool.not_eq_true] at h_not_empty
    simp only at h_result
    split at h_result
    · -- isLiteral
      split at h_result
      · obtain rfl := Option.some.inj h_result
        exact ⟨NodesPreservedInc_refl st, h_not_in, h_fresh, h_name, Nat.le.refl⟩
      · exact ih _ _ _ h_result h_not_in h_fresh h_name
    · split at h_result <;> (try split at h_result) <;> (try split at h_result) <;>
        (try split at h_result) <;> (try split at h_result)
      all_goals (
        first
        | (obtain rfl := Option.some.inj h_result
           exact ⟨NodesPreservedInc_refl st, h_not_in, h_fresh, h_name, Nat.le.refl⟩)
        | exact ih _ _ _ h_result h_not_in h_fresh h_name
        | (simp only [Bind.bind, Option.bind] at h_result
           split at h_result
           · simp at h_result
           · rename_i h_branch1
             have r1 := ih _ _ _ h_branch1 h_not_in h_fresh h_name
             have r2 := ih _ _ _ h_result r1.nameFresh r1.freshInv r1.nameBound
             exact ⟨NodesPreservedInc_trans r1.npi r2.npi,
               r2.nameFresh, r2.freshInv, r2.nameBound,
               Nat.le_trans r1.nextNameMono r2.nextNameMono⟩))

omit [BEq (NNF α)] [LawfulBEq (NNF α)] in
/-- Nodes already in the input state survive `expand`, with unchanged `old`/`next` and only-growing `incoming`. -/
theorem expand_nodesPreservedInc (node : ExpansionNode α S) (st : ExpandState α S)
    {r : Nat × ExpandState α S}
    (h_result : expand node st = some r)
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName) :
    NodesPreservedInc st r.2 :=
  (expand_npi_result node st h_result h_not_in h_fresh h_name).npi

/-! ## Key-equals-name invariant

`expand` always stores each finished node at the key equal to its own `.name` field (every insertion in
`Expand.lean` uses `<value>.name` as the key). `expand_key_eq_name` establishes this; `expand_name_ident_preserved`
derives from it that stored node names are injective in their keys. -/

omit [BEq (NNF α)] [LawfulBEq (NNF α)] in
private theorem expand_key_eq_name (node : ExpansionNode α S) (st : ExpandState α S)
    {r : Nat × ExpandState α S}
    (h_result : expand node st = some r)
    (h_key_eq : ∀ k (n : ExpansionNode α S), st.nodes[k]? = some n → n.name = k) :
    ∀ k (n : ExpansionNode α S), r.2.nodes[k]? = some n → n.name = k := by
  revert h_key_eq
  apply expand.partial_correctness
    (motive := fun node st r =>
      (∀ k (n : ExpansionNode α S), st.nodes[k]? = some n → n.name = k) →
      ∀ k (n : ExpansionNode α S), r.2.nodes[k]? = some n → n.name = k)
    _ node st r h_result
  intro expand_ih ih node st r h_result h_key_eq
  split at h_result
  case isTrue h_empty =>
    split at h_result
    · -- Merge
      obtain rfl := Option.some.inj h_result
      intro k n hk
      unfold mergeIncoming at hk
      split at hk
      · rename_i target htarget
        simp only [Std.HashMap.getElem?_insert] at hk
        split at hk
        · rename_i heq
          obtain rfl := Option.some.inj hk
          have hkeq := (beq_iff_eq (α := Nat)).mp heq
          rw [← hkeq]
          exact h_key_eq _ target htarget
        · exact h_key_eq k n hk
      · exact h_key_eq k n hk
    · -- Insert + recurse
      simp only [freshName] at h_result
      apply ih _ _ _ h_result
      intro k n hk
      simp only [ExpandState.addNode, Std.HashMap.getElem?_insert] at hk
      split at hk
      · rename_i heq
        obtain rfl := Option.some.inj hk
        exact (beq_iff_eq (α := Nat)).mp heq
      · exact h_key_eq k n hk
  case isFalse h_not_empty =>
    simp only [Bool.not_eq_true] at h_not_empty
    simp only at h_result
    split at h_result
    · -- isLiteral
      split at h_result
      · obtain rfl := Option.some.inj h_result; exact h_key_eq
      · exact ih _ _ _ h_result h_key_eq
    · split at h_result <;> (try split at h_result) <;> (try split at h_result) <;>
        (try split at h_result) <;> (try split at h_result)
      all_goals (
        first
        | (obtain rfl := Option.some.inj h_result; exact h_key_eq)
        | exact ih _ _ _ h_result h_key_eq
        | (simp only [Bind.bind, Option.bind] at h_result
           split at h_result
           · simp at h_result
           · rename_i h_branch1
             exact ih _ _ _ h_result (ih _ _ _ h_branch1 h_key_eq)))

-- Corollary: injectivity of `.name` among stored nodes, derived from `expand_key_eq_name`.
omit [BEq (NNF α)] [LawfulBEq (NNF α)] in
private theorem expand_name_ident_preserved (node : ExpansionNode α S) (st : ExpandState α S)
    {r : Nat × ExpandState α S}
    (h_result : expand node st = some r)
    (h_key_eq : ∀ k (n : ExpansionNode α S), st.nodes[k]? = some n → n.name = k) :
    ∀ (k₁ k₂ : Nat) (n₁ n₂ : ExpansionNode α S),
      r.2.nodes[k₁]? = some n₁ → r.2.nodes[k₂]? = some n₂ → n₁.name = n₂.name → k₁ = k₂ := by
  have hke := expand_key_eq_name node st h_result h_key_eq
  intro k₁ k₂ n₁ n₂ hk₁ hk₂ hname
  rw [← hke k₁ n₁ hk₁, ← hke k₂ n₂ hk₂, hname]

/-! ## Theorem 3: expand_all

For every newly added finished node in the output that is semantically valid at ξ (`NodeSemanticValid`), there
is a successor node reachable via `incoming` that is semantically valid at `ξ.drop 1`. -/

/-- Semantic validity of a finished node at ξ. -/
structure NodeSemanticValid (ξ : OmegaWord α) (nd : ExpansionNode α S) : Prop where
  old_sat : ∀ ψ, FSet.contains nd.old ψ → NNF.satisfies ξ ψ
  next_sat : ∀ ψ, FSet.contains nd.next ψ → NNF.satisfies (ξ.drop 1) ψ
  until_rhs : ∀ η μ, FSet.contains nd.old (.until μ η) → NNF.satisfies ξ η →
    FSet.contains nd.old η

/-- Every newly-added semantically-valid finished node has a semantically-valid successor reachable via
    `incoming`. -/
theorem expand_all (ξ : OmegaWord α) (node : ExpansionNode α S) (st : ExpandState α S)
    {r : Nat × ExpandState α S}
    (h_result : expand node st = some r)
    -- structural preconditions
    (h_not_in : st.nodes[node.name]? = none)
    (h_fresh : ∀ k, st.nodes[k]? ≠ none → k < st.nextName)
    (h_name : node.name < st.nextName)
    (h_key_eq : ∀ k (n : ExpansionNode α S), st.nodes[k]? = some n → n.name = k) :
    ∀ (k : Nat) (nd : ExpansionNode α S),
      r.2.nodes[k]? = some nd →
      st.nodes[k]? = none →
      NodeSemanticValid ξ nd →
      ∃ (k' : Nat) (nd' : ExpansionNode α S),
        r.2.nodes[k']? = some nd' ∧
        nd'.incoming.contains k ∧
        NodeSemanticValid (ξ.drop 1) nd' := by
  have combined :
      expand node st = some r ∧
      (st.nodes[node.name]? = none →
      (∀ k, st.nodes[k]? ≠ none → k < st.nextName) →
      node.name < st.nextName →
      (∀ k (n : ExpansionNode α S), st.nodes[k]? = some n → n.name = k) →
      ∀ (k : Nat) (nd : ExpansionNode α S),
        r.2.nodes[k]? = some nd →
        st.nodes[k]? = none →
        NodeSemanticValid ξ nd →
        ∃ (k' : Nat) (nd' : ExpansionNode α S),
          r.2.nodes[k']? = some nd' ∧
          nd'.incoming.contains k ∧
          NodeSemanticValid (ξ.drop 1) nd') := by
    apply expand.partial_correctness
      (motive := fun node st r =>
        -- Also carries the literal `expand node st = some r` equation, needed to invoke `expand_exist` and
        -- `expand_nodesPreservedInc` on recursive sub-calls.
        expand node st = some r ∧
        (st.nodes[node.name]? = none →
        (∀ k, st.nodes[k]? ≠ none → k < st.nextName) →
        node.name < st.nextName →
        (∀ k (n : ExpansionNode α S), st.nodes[k]? = some n → n.name = k) →
        ∀ (k : Nat) (nd : ExpansionNode α S),
          r.2.nodes[k]? = some nd →
          st.nodes[k]? = none →
          NodeSemanticValid ξ nd →
          ∃ (k' : Nat) (nd' : ExpansionNode α S),
            r.2.nodes[k']? = some nd' ∧
            nd'.incoming.contains k ∧
            NodeSemanticValid (ξ.drop 1) nd'))
      _ node st r h_result
    intro expand_ih ih node st r h_result
    -- Helpers for insert case (same as expand_npi_result / expand_exist_aux)
    have mk_succ_not_in (st' : ExpandState α S) (nn : Nat) (nd : ExpansionNode α S)
        (hni : st'.nodes[nn]? = none) (hfr : ∀ k, st'.nodes[k]? ≠ none → k < st'.nextName)
        (hlt : nn < st'.nextName) :
        (st'.nodes.insert nn nd)[st'.nextName]? = none := by
      simp only [Std.HashMap.getElem?_insert]; split
      · rename_i heq; have := (beq_iff_eq (α := Nat)).mp heq; omega
      · by_contra h; exact absurd (hfr st'.nextName h) (by omega)
    have mk_succ_fresh (st' : ExpandState α S) (nn : Nat) (nd : ExpansionNode α S)
        (hfr : ∀ k, st'.nodes[k]? ≠ none → k < st'.nextName) (hlt : nn < st'.nextName) :
        ∀ k, (st'.nodes.insert nn nd)[k]? ≠ none → k < st'.nextName + 1 := by
      intro k hk; simp only [Std.HashMap.getElem?_insert] at hk; split at hk
      · rename_i heq; have := (beq_iff_eq (α := Nat)).mp heq; omega
      · exact Nat.lt_succ_of_lt (hfr k hk)
    have mk_succ_key_eq (st' : ExpandState α S) (nn : Nat) (nd : ExpansionNode α S)
        (hnn : nd.name = nn) (hke : ∀ k (n : ExpansionNode α S), st'.nodes[k]? = some n → n.name = k) :
        ∀ k (n : ExpansionNode α S), (st'.nodes.insert nn nd)[k]? = some n → n.name = k := by
      intro k n hk
      simp only [Std.HashMap.getElem?_insert] at hk; split at hk
      · rename_i heq; obtain rfl := Option.some.inj hk
        rw [hnn]; exact (beq_iff_eq (α := Nat)).mp heq
      · exact hke k n hk
    split at h_result
    case isTrue h_empty =>
      generalize h_fd : findDuplicate st node = fd at h_result
      cases fd with
      | some existingName =>
        -- MERGE CASE: vacuous for all_prop (merge never adds a new key to st.nodes)
        obtain ⟨target, htarget, hsig⟩ := findDuplicate_spec st node existingName h_fd
        refine ⟨?_, ?_⟩
        · show expand node st = some r
          unfold expand
          rw [if_pos h_empty, h_fd]
          exact h_result
        · obtain rfl := Option.some.inj h_result
          intro h_not_in h_fresh h_name h_key_eq
          intro k nd hnd hnew_k hvalid
          exfalso
          unfold mergeIncoming at hnd
          rw [htarget] at hnd
          simp only [Std.HashMap.getElem?_insert] at hnd
          split at hnd
          · rename_i heq
            rw [← (beq_iff_eq (α := Nat)).mp heq] at hnew_k
            rw [htarget] at hnew_k
            simp at hnew_k
          · rw [hnew_k] at hnd; simp at hnd
      | none =>
        -- INSERT + RECURSE CASE
        simp only [freshName] at h_result
        refine ⟨?_, ?_⟩
        · show expand node st = some r
          unfold expand
          rw [if_pos h_empty, h_fd]
          simp only [freshName]
          exact (ih _ _ _ h_result).1
        · intro h_not_in h_fresh h_name h_key_eq
          intro k nd hnd hnew_k hvalid
          have h_real : expand _ _ = some r := (ih _ _ _ h_result).1
          by_cases hkeq : k = node.name
          · -- k = node.name: the just-finished node itself; use `expand_exist` on its successor (whose `new` is
            -- `node.next`) at `ξ.drop 1`.
            subst hkeq
            have hnpi := expand_nodesPreservedInc _ _ h_real
              (mk_succ_not_in st node.name node h_not_in h_fresh h_name)
              (mk_succ_fresh st node.name node h_fresh h_name)
              (by show st.nextName < st.nextName + 1; omega)
            obtain ⟨nd0, hnd0, hold0, hnext0, hinc0⟩ := hnpi node.name node
              (by simp only [ExpandState.addNode, Std.HashMap.getElem?_insert, beq_self_eq_true, ↓reduceIte])
            have hnd_eq : nd0 = nd := by rw [hnd0] at hnd; exact Option.some.inj hnd
            have h_assm_succ : ExpandAssmExist (ξ.drop 1)
                ({ name := st.nextName
                   incoming := Std.HashSet.emptyWithCapacity 4 |>.insert node.name
                   new := nextToNew node.next
                   old := FSet.empty
                   next := FSet.empty } : ExpansionNode α S) := by
              constructor
              · intro ψ hψ
                have hcontains := (mem_nextToNew node.next ψ).mp hψ
                have hnd0_next := (hnext0 ψ).mpr hcontains
                rw [hnd_eq] at hnd0_next
                exact hvalid.next_sat ψ hnd0_next
              · intro ψ hψ; simp [FSet.contains_empty] at hψ
              · intro ψ hψ; simp [FSet.contains_empty] at hψ
              · intro η μ hμη; simp [FSet.contains_empty] at hμη
            obtain ⟨k'', nd'', hk'', hprop⟩ := expand_exist (ξ.drop 1) _ _ h_real
              (mk_succ_not_in st node.name node h_not_in h_fresh h_name)
              (mk_succ_fresh st node.name node h_fresh h_name)
              (by show st.nextName < st.nextName + 1; omega)
              h_assm_succ
            refine ⟨k'', nd'', hk'', ?_, ⟨hprop.old_sat, hprop.next_sat, hprop.until_rhs⟩⟩
            exact hprop.incoming_sub node.name (by simp)
          · -- k ≠ node.name: propagate via `ih`
            have hst'_none : (st.nodes.insert node.name node)[k]? = none := by
              simp only [Std.HashMap.getElem?_insert]; split
              · rename_i heq; exact absurd ((beq_iff_eq (α := Nat)).mp heq).symm hkeq
              · exact hnew_k
            exact (ih _ _ _ h_result).2
              (mk_succ_not_in st node.name node h_not_in h_fresh h_name)
              (mk_succ_fresh st node.name node h_fresh h_name)
              (by show st.nextName < st.nextName + 1; omega)
              (mk_succ_key_eq st node.name node rfl h_key_eq)
              k nd hnd hst'_none hvalid
    case isFalse h_not_empty =>
      simp only [Bool.not_eq_true] at h_not_empty
      simp only at h_result
      have hnot_empty' : ¬ node.new.isEmpty = true := by simp [h_not_empty]
      split at h_result
      · -- isLiteral
        rename_i hlit
        split at h_result
        · -- LITERAL CONTRADICTION CASE: terminal, r.2 = st unchanged, vacuous
          rename_i hcontra
          refine ⟨?_, ?_⟩
          · show expand node st = some r
            unfold expand
            rw [if_neg hnot_empty']
            simp only
            rw [if_pos hlit, if_pos hcontra]
            exact h_result
          · obtain rfl := Option.some.inj h_result
            intro h_not_in h_fresh h_name h_key_eq
            intro k nd hnd hnew_k hvalid
            simp_all
        · -- LITERAL NO-CONTRADICTION CASE: single recursive call, st unchanged
          rename_i hcontra
          refine ⟨?_, ?_⟩
          · show expand node st = some r
            unfold expand
            rw [if_neg hnot_empty']
            simp only
            rw [if_pos hlit, if_neg hcontra]
            exact (ih _ _ _ h_result).1
          · exact (ih _ _ _ h_result).2
      · -- NOT LITERAL (tt / ff / det / nondet)
        rename_i h_notlit
        split at h_result
        · -- tt case: single recursive call, st unchanged
          rename_i htt
          refine ⟨?_, ?_⟩
          · show expand node st = some r
            unfold expand
            rw [if_neg hnot_empty']
            simp only
            rw [if_neg h_notlit]
            split
            · exact (ih _ _ _ h_result).1
            · rename_i h; exact absurd htt h
          · exact (ih _ _ _ h_result).2
        · rename_i h_nottt
          split at h_result
          · -- unreachable: auxiliary matcher artifact (h : false = true)
            rename_i h
            exact absurd h (by decide)
          · split at h_result
            · -- real ff case: terminal, r.2 = st unchanged, vacuous
              rename_i hff
              refine ⟨?_, ?_⟩
              · show expand node st = some r
                unfold expand
                rw [if_neg hnot_empty']
                simp only
                rw [if_neg h_notlit]
                split
                · rename_i h; exact absurd h (by decide)
                · split
                  · exact h_result
                  · rename_i h; exact absurd hff h
              · obtain rfl := Option.some.inj h_result
                intro h_not_in h_fresh h_name h_key_eq
                intro k nd hnd hnew_k hvalid
                simp_all
            · rename_i h_notff
              split at h_result
              · -- unreachable: auxiliary matcher artifact
                rename_i h
                exact absurd h (by decide)
              · -- real isDeterministic split
                split at h_result
                · -- det case (and / next): single recursive call, st unchanged
                  rename_i hdet
                  refine ⟨?_, ?_⟩
                  · show expand node st = some r
                    unfold expand
                    rw [if_neg hnot_empty']
                    simp only
                    rw [if_neg h_notlit]
                    split
                    · rename_i h; exact absurd h (by decide)
                    · exact (ih _ _ _ h_result).1
                  · exact (ih _ _ _ h_result).2
                · -- nondet case (or / until / release)
                  simp only [Bind.bind, Option.bind] at h_result
                  split at h_result
                  · simp at h_result
                  · rename_i p heq1
                    have ih1 := ih _ _ _ heq1
                    have ih2 := ih _ _ _ h_result
                    refine ⟨?_, ?_⟩
                    · show expand node st = some r
                      unfold expand
                      rw [if_neg hnot_empty']
                      simp only
                      rw [if_neg h_notlit]
                      split
                      · rename_i h; exact absurd h (by decide)
                      · simp only [Bind.bind, Option.bind]
                        rw [ih1.1]
                        exact ih2.1
                    · -- all_prop
                      intro h_not_in h_fresh h_name h_key_eq
                      intro k nd hnd hnew_k hvalid
                      have res1 := expand_npi_result _ st ih1.1 h_not_in h_fresh h_name
                      have hkeq1 := expand_key_eq_name _ st ih1.1 h_key_eq
                      have hnpi2 := expand_nodesPreservedInc _ p.snd ih2.1
                        res1.nameFresh res1.freshInv res1.nameBound
                      by_cases hk : p.snd.nodes[k]? = none
                      · -- k genuinely new only during phase 2: use ih2's own all_prop
                        exact ih2.2 res1.nameFresh res1.freshInv res1.nameBound hkeq1
                          k nd hnd hk hvalid
                      · -- k already populated after phase 1: use ih1's all_prop, then transport the witness
                        -- through phase 2 via hnpi2
                        obtain ⟨nd0, hnd0⟩ := Option.ne_none_iff_exists'.mp hk
                        obtain ⟨nd', hnd', hold', hnext', _⟩ := hnpi2 k nd0 hnd0
                        have hnd_eq : nd = nd' := by rw [hnd] at hnd'; exact Option.some.inj hnd'
                        have hvalid0 : NodeSemanticValid ξ nd0 :=
                          ⟨fun ψ hψ => hvalid.old_sat ψ (hnd_eq ▸ (hold' ψ).mpr hψ),
                           fun ψ hψ => hvalid.next_sat ψ (hnd_eq ▸ (hnext' ψ).mpr hψ),
                           fun η μ hμη hη => (hold' η).mp (hnd_eq ▸
                             hvalid.until_rhs η μ (hnd_eq ▸ (hold' _).mpr hμη) hη)⟩
                        obtain ⟨k', nd'', hk'', hinc'', hvalid''⟩ :=
                          ih1.2 h_not_in h_fresh h_name h_key_eq k nd0 hnd0 hnew_k hvalid0
                        obtain ⟨nd''', hnd''', hold''', hnext''', hincsub'''⟩ := hnpi2 k' nd'' hk''
                        exact ⟨k', nd''', hnd''', hincsub''' k hinc'',
                          ⟨fun ψ hψ => hvalid''.old_sat ψ ((hold''' ψ).mp hψ),
                           fun ψ hψ => hvalid''.next_sat ψ ((hnext''' ψ).mp hψ),
                           fun η μ hμη hη => (hold''' η).mpr
                             (hvalid''.until_rhs η μ ((hold''' _).mp hμη) hη)⟩⟩
  exact combined.2 h_not_in h_fresh h_name h_key_eq

/-! ## Lifting to createGraph level -/

/-- For any ξ ⊨ φ, createGraph produces a node with expandInit in incoming and semantically valid old/next. -/
theorem createGraph_exist (φ : NNF α) {st : ExpandState α S}
    (hcg : createGraph φ = some st) (ξ : OmegaWord α) (hsat : NNF.satisfies ξ φ) :
    ∃ (k : Nat) (nd : ExpansionNode α S), st.nodes[k]? = some nd ∧
      nd.incoming.contains expandInit ∧
      NodeSemanticValid ξ nd := by
  simp only [createGraph] at hcg
  split at hcg
  · rename_i nm finalState heq
    obtain rfl := Option.some.inj hcg
    have h_assm : ExpandAssmExist ξ
        ({ name := 1,
           incoming := Std.HashSet.emptyWithCapacity 4 |>.insert expandInit,
           new := [φ],
           old := FSet.empty,
           next := FSet.empty } : ExpansionNode α S) := by
      constructor
      · intro ψ hψ; cases hψ with | head => exact hsat | tail _ h => exact nomatch h
      · intro ψ hψ; simp [FSet.contains_empty] at hψ
      · intro ψ hψ; simp [FSet.contains_empty] at hψ
      · intro η μ hμη; simp [FSet.contains_empty] at hμη
    obtain ⟨k, nd, hnd, hprop⟩ := expand_exist ξ _ _ heq
      (by simp) (fun k hk => by simp at hk) (by omega : (1 : Nat) < 2) h_assm
    exact ⟨k, nd, hnd,
      hprop.incoming_sub expandInit (by simp [Std.HashSet.contains_insert]),
      ⟨hprop.old_sat, hprop.next_sat, hprop.until_rhs⟩⟩
  · simp at hcg

/-- For any semantically valid node in createGraph's output, there exists a successor that is semantically valid
    at suffix 1 ξ. -/
theorem createGraph_all (φ : NNF α) {st : ExpandState α S}
    (hcg : createGraph φ = some st) (ξ : OmegaWord α) :
    ∀ (k : Nat) (nd : ExpansionNode α S),
      st.nodes[k]? = some nd →
      NodeSemanticValid ξ nd →
      ∃ (k' : Nat) (nd' : ExpansionNode α S),
        st.nodes[k']? = some nd' ∧
        nd'.incoming.contains k ∧
        NodeSemanticValid (ξ.drop 1) nd' := by
  simp only [createGraph] at hcg
  split at hcg
  · rename_i nm finalState heq
    obtain rfl := Option.some.inj hcg
    intro k nd hnd hvalid
    exact expand_all ξ _ _ heq
      (by simp)
      (fun k hk => by simp at hk)
      (by omega : (1 : Nat) < 2)
      (fun k n hk => by simp at hk)
      k nd hnd (by simp) hvalid
  · simp at hcg

/-! ## GraphComplete: completeness property sufficient for correctness -/

/-- Completeness property that `createGraph` actually establishes.
    Combined with `ExpandSpec`, it suffices to prove GBA acceptance. -/
@[expose] def GraphComplete (φ : NNF α) (nodes : NodeData α → Prop) : Prop :=
  ∀ ξ : OmegaWord α, NNF.satisfies ξ φ →
    ∃ σ : Nat → NodeData α,
      (∀ n, nodes (σ n)) ∧
      (σ 0).incoming expandInit ∧
      (∀ n, (σ (n + 1)).incoming (σ n).name) ∧
      -- → direction: old implies satisfied
      (∀ n ψ, (σ n).old ψ → NNF.satisfies (ξ.drop n) ψ) ∧
      -- until-RHS completeness
      (∀ n η μ, (σ n).old (.until μ η) → NNF.satisfies (ξ.drop n) η → (σ n).old η)

/-! ## Helper: drop shifting for NodeSemanticValid -/

omit [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem drop_succ_eq (ξ : OmegaWord α) (n : Nat) :
    (ξ.drop n).drop 1 = ξ.drop (n + 1) := by
  rw [exec.drop_drop, Nat.add_comm]

omit [BEq (NNF α)] [LawfulBEq (NNF α)] [Hashable (NNF α)] in
private theorem NodeSemanticValid_shift {ξ : OmegaWord α} {nd : ExpansionNode α S} {n : Nat}
    (hv : NodeSemanticValid ((ξ.drop n).drop 1) nd) :
    NodeSemanticValid (ξ.drop (n + 1)) nd :=
  drop_succ_eq ξ n ▸ hv

/-! ## Main theorem: GraphComplete from createGraph -/

/-- The main theorem: `createGraph` produces a graph satisfying `GraphComplete`. -/
theorem createGraph_graphComplete (φ : NNF α) {st : ExpandState α S}
    (hcg : createGraph φ = some st) :
    GraphComplete φ st.toNodes := by
  intro ξ hsat
  -- Step 1: Get the initial node
  obtain ⟨k₀, nd₀, hnd₀, hinc₀, hvalid₀⟩ := createGraph_exist φ hcg ξ hsat
  -- Step 2: successor step with shifted ξ
  have step : ∀ n (k : Nat) (nd : ExpansionNode α S),
      st.nodes[k]? = some nd → NodeSemanticValid (ξ.drop n) nd →
      ∃ (k' : Nat) (nd' : ExpansionNode α S),
        st.nodes[k']? = some nd' ∧ nd'.incoming.contains k ∧
        NodeSemanticValid (ξ.drop (n + 1)) nd' := by
    intro n k nd hk hv
    obtain ⟨k', nd', hk', hinc', hv'⟩ := createGraph_all φ hcg (ξ.drop n) k nd hk hv
    exact ⟨k', nd', hk', hinc', NodeSemanticValid_shift hv'⟩
  -- Step 3: Build the sequence by dependent recursion
  -- Bundle: (key, node, membership proof, validity proof)
  let RunData (n : Nat) := { p : Nat × ExpansionNode α S //
    st.nodes[p.1]? = some p.2 ∧ NodeSemanticValid (ξ.drop n) p.2 }
  have hvalid₀' : NodeSemanticValid (ξ.drop 0) nd₀ := by
    have : ξ.drop 0 = ξ := by funext n; simp [exec.drop]
    rw [this]; exact hvalid₀
  -- Build the sequence by strong induction
  have seq_exists : ∀ n, ∃ (k : Nat) (nd : ExpansionNode α S),
      st.nodes[k]? = some nd ∧ NodeSemanticValid (ξ.drop n) nd := by
    intro n; induction n with
    | zero => exact ⟨k₀, nd₀, hnd₀, hvalid₀'⟩
    | succ n ih =>
      obtain ⟨k, nd, hk, hv⟩ := ih
      obtain ⟨k', nd', hk', _, hv'⟩ := step n k nd hk hv
      exact ⟨k', nd', hk', hv'⟩
  -- Use dependent choice to build a CONNECTED sequence
  -- RunData stores (key, node) — key is the HashMap key, which equals node.name
  have step_rd : ∀ (n : Nat) (prev : RunData n),
      ∃ (next : RunData (n + 1)), next.1.2.incoming.contains prev.1.1 := by
    intro n ⟨⟨k, nd⟩, hk, hv⟩
    obtain ⟨k', nd', hk', hinc', hv'⟩ := step n k nd hk hv
    exact ⟨⟨(k', nd'), hk', hv'⟩, hinc'⟩
  -- Build the sequence by Nat.rec on RunData
  let init_rd : RunData 0 := ⟨(k₀, nd₀), hnd₀, hvalid₀'⟩
  let seq : (n : Nat) → RunData n :=
    Nat.rec init_rd (fun n prev => (step_rd n prev).choose)
  have seq_incoming : ∀ n, (seq (n + 1)).1.2.incoming.contains (seq n).1.1 :=
    fun n => (step_rd n (seq n)).choose_spec
  -- Convert to NodeData: use KEY as name (not node.name, to avoid needing NameConsistent)
  let σ : Nat → NodeData α := fun n =>
    { name := (seq n).1.1
      incoming := fun k => (seq n).1.2.incoming.contains k
      old := fun ψ => FSet.contains (seq n).1.2.old ψ
      next := fun ψ => FSet.contains (seq n).1.2.next ψ }
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_⟩
  · -- ∀ n, st.toNodes (σ n)
    intro n
    exact ⟨(seq n).1.2, by simp [σ, (seq n).2.1],
           fun k => Iff.rfl, fun ψ => Iff.rfl, fun ψ => Iff.rfl⟩
  · -- (σ 0).incoming expandInit
    show (seq 0).1.2.incoming.contains expandInit
    exact hinc₀
  · -- ∀ n, (σ (n+1)).incoming (σ n).name
    intro n
    show (seq (n + 1)).1.2.incoming.contains (seq n).1.1
    exact seq_incoming n
  · -- ∀ n ψ, (σ n).old ψ → satisfies (ξ.drop n) ψ
    intro n ψ hold; exact (seq n).2.2.old_sat ψ hold
  · -- ∀ n η μ, (σ n).old (until μ η) → satisfies (ξ.drop n) η → (σ n).old η
    intro n η μ hμη hη; exact (seq n).2.2.until_rhs η μ hμη hη

/-! ## Completeness from GraphComplete -/

omit [Hashable (NNF α)] [BEq (NNF α)] [LawfulBEq (NNF α)] in
/-- One step of until propagation: if `μ U η ∈ old(σ n)` and `η ∉ old(σ n)`, then `μ ∈ old(σ n)` and `μ U η ∈ old(σ(n+1))`. -/
private theorem until_step
    {φ : NNF α} {nodes : NodeData α → Prop}
    (spec : ExpandSpec φ nodes)
    {σ : Nat → NodeData α}
    (h_nodes : ∀ n, nodes (σ n))
    (h_succ : ∀ n, (σ (n + 1)).incoming (σ n).name)
    {μ η : NNF α} {n : Nat}
    (h_old : (σ n).old (.until μ η))
    (h_no_eta : ¬(σ n).old η) :
    (σ n).old μ ∧ (σ (n + 1)).old (.until μ η) := by
  rcases spec.until_propag _ (h_nodes n) _ _ h_old with h | ⟨hμ, h_next⟩
  · exact absurd h h_no_eta
  · exact ⟨hμ, spec.successor_old _ (h_nodes n) _ (h_nodes (n+1)) (h_succ n) _ h_next⟩

omit [Hashable (NNF α)] [BEq (NNF α)] [LawfulBEq (NNF α)] in
/-- Completeness from `GraphComplete` + `ExpandSpec`: if `GraphComplete` holds, then the abstract automaton accepts ξ. -/
theorem expandOASpec_completeness
    {φ : NNF α} {nodes : NodeData α → Prop}
    {untils : List (NNF α × NNF α)}
    (spec : ExpandSpec φ nodes)
    (h_complete : GraphComplete φ nodes)
    {ξ : OmegaWord α}
    (hsat : NNF.satisfies ξ φ)
    : (expandOASpec φ nodes untils).accepts ξ := by
  obtain ⟨σ, h_nodes, h_init, h_succ, h_old_sat, h_until_rhs⟩ := h_complete ξ hsat
  refine ⟨σ, ?_, ?_, ?_⟩
  · -- isRun
    exact ⟨⟨h_nodes 0, h_init⟩, fun n => ⟨h_nodes n, h_nodes (n + 1), h_succ n⟩⟩
  · -- runCompatible: label compatibility
    intro n; constructor
    · -- prop a ∈ old → ξ(n)(a)
      intro a hold
      have := h_old_sat n (.prop a) hold
      simp [NNF.satisfies, NNF.toPred, state_pred, exec.drop] at this
      exact this
    · -- nprop a ∈ old → ¬ξ(n)(a)
      intro a hold
      have := h_old_sat n (.nprop a) hold
      simp [NNF.satisfies, NNF.toPred, state_pred, exec.drop] at this
      exact this
  · -- isAcceptingRun
    intro i n
    by_cases h : (σ n).old (.until (untils[i]).1 (untils[i]).2)
    · -- until formula IS in old(σ n)
      -- By old_sat: ξ.drop n ⊨ μ U η
      have hsat_u := h_old_sat n _ h
      -- Unfold until semantics: ∃ j, η satisfied at n+j
      obtain ⟨j, hη_sat, _⟩ : ∃ j, NNF.satisfies (ξ.drop (n + j)) (untils[i]).2 ∧
          ∀ i_1, i_1 < j → NNF.satisfies (ξ.drop (n + i_1)) (untils[i]).1 := by
        simpa only [NNF.satisfies_until, exec.drop_drop] using hsat_u
      -- Find the FIRST position where η ∈ old (may be before j), rather than showing until persists to exactly n+j.
      suffices ∃ j', (σ (n + j')).old (untils[i]).2 by
        obtain ⟨j', hη_old⟩ := this
        exact ⟨j', by simp only [expandOASpec]; right; exact hη_old⟩
      -- Induction on k ≤ j: μ U η persists in old (via until_step) until η first appears in old; at k = j, until_rhs then forces
      -- η ∈ old since ξ.drop(n+j) ⊨ η.
      have h_persist : ∀ k, k ≤ j →
          (∃ k' : Nat, k' < k ∧ (σ (n + k')).old (untils[i]).2) ∨
          (σ (n + k)).old (.until (untils[i]).1 (untils[i]).2) := by
        intro k hk; induction k with
        | zero => right; simpa
        | succ k ih_k =>
          rcases ih_k (by omega) with ⟨k', hk', hη'⟩ | h_u_k
          · left; exact ⟨k', by omega, hη'⟩
          · by_cases h_eta_k : (σ (n + k)).old (untils[i]).2
            · left; exact ⟨k, by omega, h_eta_k⟩
            · right
              have ⟨_, h_carry⟩ := until_step spec h_nodes h_succ h_u_k h_eta_k
              rwa [show n + k + 1 = n + (k + 1) from by omega] at h_carry
      rcases h_persist j (Nat.le_refl _) with ⟨k', _, hη'⟩ | h_u_j
      · exact ⟨k', hη'⟩
      · exact ⟨j, h_until_rhs (n + j) _ _ h_u_j hη_sat⟩
    · -- until formula NOT in old(σ n)
      exact ⟨0, by simp only [expandOASpec, Nat.add_zero]; left; exact h⟩

end LTLLib
