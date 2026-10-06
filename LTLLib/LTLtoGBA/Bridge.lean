module

/-
  Bridge between the computational `constructGBA` (HashMap-based, states = `Nat`) and the abstract `expandOASpec`
  (predicate-based, states = `NodeData`), showing they accept the same ω-words. This lets soundness/completeness
  proved for `expandOASpec` transfer to `constructGBA`'s actual output (see `Correctness.lean` for the combined result).

  Defines:
  - `ExpandState.liftNode`: lifts a computational node name to its `NodeData`
  - `NameConsistent`: invariant that `st.nodes` stores each node at its own name

  Proves, for `createGraph φ = some st`:
  - `constructGBA_iff_expandOASpec`: `constructGBA` and `expandOASpec` accept the same words
  - `constructGBA_wellFormed`: initial/successor states of `constructGBA` are always known states
  - `constructGBA_canonicalLabel_compat`: `canonicalLabel` on `constructGBA`'s labeling satisfies `labelCompat`

  ## Sections
  - Generic fold helpers
  - Build function correctness
  - Node lifting
  - Labeling correctness
  - Accept-set correctness
  - Name consistency from createGraph
  - Literal consistency from createGraph
  - Direction 1: GBA.toSpec accepts → expandOASpec accepts
  - Direction 2: expandOASpec accepts → GBA.toSpec accepts
  - Combined bridge
  - Well-formedness of constructGBA
  - Canonical labeling for constructGBA
-/

public import LTLLib.LTLtoGBA.Invariants
public import LTLLib.LTLtoGBA.ToGBA
public import LTLLib.AbstractSpec.Acceptance

public section

namespace LTLLib

open NNF

variable {α : Type u} {S : Type v}

/-! ### Generic fold helpers -/

/-- Pairwise distinct keys imply pairwise distinct names (when name = key). -/
private theorem pairwise_name_of_pairwise_key
    {l : List (Nat × ExpansionNode α S)}
    (h_distinct : l.Pairwise (fun a b => (a.1 == b.1) = false))
    (h_names : ∀ x ∈ l, x.2.name = x.1) :
    l.Pairwise (fun a b => (a.2.name == b.2.name) = false) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons hd tl ih =>
    rw [List.pairwise_cons] at h_distinct ⊢
    exact ⟨fun a ha => by
      rw [h_names hd (.head _), h_names a (.tail _ ha)]
      exact h_distinct.1 a ha,
    ih h_distinct.2 (fun x hx => h_names x (.tail _ hx))⟩

/-- Folding conditional inserts over a list into a HashSet: the result contains `q` iff `init` already contained it
    or some list element satisfies `p` and maps to `q` via `f`. -/
private theorem HashSet_foldl_insert_contains
    [BEq γ] [Hashable γ] [LawfulBEq γ] [LawfulHashable γ]
    (l : List β) (p : β → Bool) (f : β → γ) (init : Std.HashSet γ) (q : γ) :
    (l.foldl (fun acc x => if p x then acc.insert (f x) else acc) init).contains q =
      (init.contains q || l.any (fun x => p x && (f x == q))) := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.any_cons]
    split
    · next hp =>
      rw [ih]; simp only [Std.HashSet.contains_insert, hp, Bool.true_and]; ac_rfl
    · next hp =>
      rw [ih]; simp only [Bool.not_eq_true] at hp; simp [hp]

/-- Folding unconditional inserts over a list into a HashSet: the result contains `q` iff `init` already contained it
    or some list element maps to `q` via `f`. Unconditional special case of `HashSet_foldl_insert_contains`. -/
private theorem HashSet_foldl_insert_contains'
    [BEq γ] [Hashable γ] [LawfulBEq γ] [LawfulHashable γ]
    (l : List β) (f : β → γ) (init : Std.HashSet γ) (q : γ) :
    (l.foldl (fun acc x => acc.insert (f x)) init).contains q =
      (init.contains q || l.any (fun x => f x == q)) := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.any_cons, ih, Std.HashSet.contains_insert]
    ac_rfl

/-! ### Build function correctness

These lemmas connect the computational build functions to the abstract predicates they compute.

**Key invariant**: nodes are stored by their name, i.e., `st.nodes[k]? = some node → node.name = k`. -/

/-- `buildStates` contains `q` iff `q` is a key of `nodeMap` (i.e. `q` has a stored node). -/
theorem buildStates_mem_iff
    {nodeMap : Std.HashMap Nat (ExpansionNode α S)} (q : Nat) :
    (buildStates nodeMap).contains q = true ↔ nodeMap.contains q = true := by
  simp only [buildStates, Std.HashMap.fold_eq_foldl_toList]
  rw [HashSet_foldl_insert_contains' _ Prod.fst]
  simp only [Std.HashSet.contains_emptyWithCapacity, Bool.false_or, List.any_eq_true,
    beq_iff_eq]
  constructor
  · rintro ⟨⟨k, nd⟩, hmem, rfl⟩
    have hk := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem
    rw [Std.HashMap.contains_eq_isSome_getElem?, hk]
    rfl
  · intro hcontains
    rw [Std.HashMap.contains_eq_isSome_getElem?] at hcontains
    obtain ⟨nd, hnd⟩ := Option.isSome_iff_exists.mp hcontains
    exact ⟨(q, nd), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hnd, rfl⟩

/-- Folding inserts into a HashMap: keys not in the list fall back to `init`. -/
private theorem HashMap_foldl_insert_not_mem
    [BEq γ] [Hashable γ] [LawfulBEq γ] [LawfulHashable γ]
    (l : List (γ × δ)) (init : Std.HashMap γ δ) (q : γ)
    (h : ∀ p : γ × δ, p ∈ l → (p.1 == q) = false) :
    (l.foldl (fun acc (k, v) => acc.insert k v) init)[q]? = init[q]? := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun p hp => h p (List.mem_cons_of_mem _ hp))]
    rw [Std.HashMap.getElem?_insert, if_neg (by exact h hd (.head _) ▸ fun h => nomatch h)]

/-- Folding inserts with pairwise distinct keys: if `(q, v) ∈ l`, the result maps `q` to `v`. -/
private theorem HashMap_foldl_insert_of_mem
    [BEq γ] [Hashable γ] [LawfulBEq γ] [LawfulHashable γ]
    (l : List (γ × δ)) (init : Std.HashMap γ δ) (q : γ) (v : δ)
    (hmem : (q, v) ∈ l)
    (h_distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    (l.foldl (fun acc (k, v) => acc.insert k v) init)[q]? = some v := by
  induction l generalizing init with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    obtain ⟨h_all, h_pw_tl⟩ := List.pairwise_cons.mp h_distinct
    cases hmem with
    | head =>
      rw [HashMap_foldl_insert_not_mem _ _ q
        (fun p hp => by rw [BEq.comm]; exact h_all p hp)]
      simp
    | tail _ hmem =>
      exact ih _ hmem h_pw_tl

/-- All elements satisfy negation → any is false. -/
private theorem List_any_false_of_key_ne
    [BEq γ] [LawfulBEq γ]
    (l : List (γ × δ)) (p : δ → Bool) (q : γ)
    (h : ∀ x ∈ l, (x.1 == q) = false) :
    l.any (fun x => p x.2 && (x.1 == q)) = false := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.any_cons]
    have := h hd List.mem_cons_self
    simp only [this, Bool.and_false, Bool.false_or]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- For a list with distinct keys, `any` with a key equality check reduces to the predicate at the unique matching element. -/
private theorem List_any_beq_unique
    [BEq γ] [LawfulBEq γ]
    (l : List (γ × δ)) (p : δ → Bool) (q : γ) (v : δ)
    (hmem : (q, v) ∈ l)
    (h_distinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) :
    l.any (fun x => p x.2 && (x.1 == q)) = p v := by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    obtain ⟨h_all, h_pw_tl⟩ := List.pairwise_cons.mp h_distinct
    simp only [List.any_cons]
    cases hmem with
    | head =>
      simp only [beq_self_eq_true, Bool.and_true]
      rw [List_any_false_of_key_ne _ _ _ (fun x hx => by rw [BEq.comm]; exact h_all x hx)]
      simp
    | tail _ hmem_tl =>
      have h1 : (hd.1 == q) = false := h_all ⟨q, v⟩ hmem_tl
      simp only [h1, Bool.and_false, Bool.false_or]
      exact ih hmem_tl h_pw_tl

/-- Inner fold for buildSuccessors: characterizes membership after processing a list of predecessor names. -/
private theorem inner_fold_mem
    (l : List Nat) (nodeName : Nat)
    (succMap : Std.HashMap Nat (Array Nat)) (q q' : Nat) :
    q' ∈ (l.foldl (fun acc predName =>
      acc.insert predName ((acc[predName]?.getD #[]).push nodeName)) succMap)[q]?.getD #[] ↔
    q' ∈ succMap[q]?.getD #[] ∨ (q ∈ l ∧ q' = nodeName) := by
  induction l generalizing succMap with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    by_cases heq : hd = q
    · subst heq
      simp [Array.mem_push]
      grind
    · simp [Std.HashMap.getElem?_insert, show ¬((hd == q) = true) from by simp [beq_iff_eq, heq]]
      grind

/-- Folding inserts preserves entries at keys not touched by the fold. -/
private theorem foldl_insert_preserves
    [BEq γ] [Hashable γ] [LawfulBEq γ] [LawfulHashable γ]
    {β : Type w} (l : List β) (key : β → γ) (val : β → ε)
    (init : Std.HashMap γ ε) (q : γ)
    (h_no_key : ∀ x ∈ l, (key x == q) = false) :
    (l.foldl (fun acc x => acc.insert (key x) (val x)) init)[q]? = init[q]? := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h_tl := fun x hx => h_no_key x (List.mem_cons_of_mem _ hx)
    rw [ih _ h_tl, Std.HashMap.getElem?_insert]
    simp [h_no_key hd List.mem_cons_self]

/-- Folding inserts with key/val functions: if element x maps to key q, result[q]? = some (val x). -/
private theorem HashMap_foldl_insert_gen
    [BEq γ] [Hashable γ] [LawfulBEq γ] [LawfulHashable γ]
    {β : Type w} (l : List β) (key : β → γ) (val : β → ε)
    (init : Std.HashMap γ ε) (x : β)
    (hmem : x ∈ l) (hkey : key x = q)
    (h_distinct : l.Pairwise (fun a b => (key a == key b) = false)) :
    (l.foldl (fun acc y => acc.insert (key y) (val y)) init)[q]? = some (val x) := by
  subst hkey
  induction l generalizing init with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    obtain ⟨h_all, h_pw_tl⟩ := List.pairwise_cons.mp h_distinct
    cases hmem with
    | head =>
      rw [foldl_insert_preserves tl key val _ (key x)
        (fun y hy => by rw [BEq.comm]; exact h_all y hy)]
      rw [Std.HashMap.getElem?_insert]; simp
    | tail _ hmem_tl =>
      exact ih _ hmem_tl h_pw_tl

/-- buildInitialStates contains q iff some node with name q has expandInit in incoming. -/
theorem buildInitialStates_correct
    {nodeMap : Std.HashMap Nat (ExpansionNode α S)}
    (hname : ∀ k (node : ExpansionNode α S), nodeMap[k]? = some node → node.name = k)
    (q : Nat) :
    (buildInitialStates nodeMap).contains q = true ↔
      ∃ node, nodeMap[q]? = some node ∧ node.incoming.contains expandInit = true := by
  simp only [buildInitialStates, Std.HashMap.fold_eq_foldl_toList]
  have h_distinct := Std.HashMap.distinct_keys_toList (m := nodeMap)
  constructor
  · intro h
    rw [HashSet_foldl_insert_contains] at h
    simp only [Std.HashSet.contains_emptyWithCapacity, Bool.false_or] at h
    rw [List.any_eq_true] at h
    obtain ⟨⟨k, node⟩, hmem, h_and⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h_and
    have hkv := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem
    rw [hname k node hkv] at h_and
    rw [h_and.2] at hkv
    exact ⟨node, hkv, h_and.1⟩
  · rintro ⟨node, hq, hinc⟩
    rw [HashSet_foldl_insert_contains]
    simp only [Std.HashSet.contains_emptyWithCapacity, Bool.false_or]
    rw [List.any_eq_true]
    refine ⟨⟨q, node⟩, Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hq, ?_⟩
    simp [hinc, hname q node hq]

/-- q' ∈ getSuccessors q (via buildSuccessors) iff some node with name q' has q in its incoming set. -/
theorem buildSuccessors_mem_iff
    {nodeMap : Std.HashMap Nat (ExpansionNode α S)}
    (hname : ∀ k (node : ExpansionNode α S), nodeMap[k]? = some node → node.name = k)
    (q q' : Nat) :
    q' ∈ (buildSuccessors nodeMap)[q]?.getD #[] ↔
      ∃ node, nodeMap[q']? = some node ∧ node.incoming.contains q = true := by
  simp only [buildSuccessors, Std.HashMap.fold_eq_foldl_toList, Std.HashSet.fold_eq_foldl_toList]
  -- Prove invariant for the outer fold
  suffices h : ∀ (l : List (Nat × ExpansionNode α S)) (init : Std.HashMap Nat (Array Nat)),
      (∀ x ∈ l, x.2.name = x.1) →
      (q' ∈ (l.foldl (fun succMap (_, node) =>
        node.incoming.toList.foldl (fun succMap predName =>
          succMap.insert predName ((succMap[predName]?.getD #[]).push node.name)) succMap)
        init)[q]?.getD #[] ↔
      q' ∈ init[q]?.getD #[] ∨
        ∃ x ∈ l, q ∈ x.2.incoming.toList ∧ q' = x.2.name) by
    rw [h _ _ (fun ⟨k, nd⟩ hx =>
      hname k nd (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hx))]
    constructor
    · rintro (h_init | ⟨⟨k, nd⟩, hmem_l, hinc, rfl⟩)
      · simp at h_init
      · have hkv := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hmem_l
        rw [show (k, nd).snd.name = k from hname k nd hkv]
        exact ⟨nd, hkv, (Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hinc))⟩
    · rintro ⟨nd, hq_nd, hinc⟩
      exact Or.inr ⟨⟨q', nd⟩, Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hq_nd,
        Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hinc),
        (hname q' nd hq_nd).symm⟩
  intro l init h_names
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih _ (fun x hx => h_names x (List.mem_cons_of_mem _ hx)),
        inner_fold_mem]
    grind

variable [FSet (NNF α) S]

/-! ### Node lifting

Lift a node name (Nat) to a NodeData by looking up in the ExpandState. -/

/-- Lift a node name to its abstract NodeData representation. -/
noncomputable def ExpandState.liftNode (st : ExpandState α S) (q : Nat) : NodeData α where
  name := q
  incoming k := ∃ node, st.nodes[q]? = some node ∧ node.incoming.contains k = true
  old ψ := ∃ node, st.nodes[q]? = some node ∧ FSet.contains node.old ψ = true
  next ψ := ∃ node, st.nodes[q]? = some node ∧ FSet.contains node.next ψ = true

/-- If the node exists in the HashMap, the lifted NodeData is in toNodes. -/
theorem ExpandState.liftNode_mem_toNodes (st : ExpandState α S) (q : Nat)
    {node : ExpansionNode α S} (hq : st.nodes[q]? = some node) :
    st.toNodes (st.liftNode q) := by
  refine ⟨node, hq, ?_, ?_, ?_⟩ <;> intro x <;> simp only [liftNode] <;> constructor
  · rintro ⟨n, hn, hk⟩; rw [hq] at hn; cases hn; assumption
  · exact fun h => ⟨node, hq, h⟩
  · rintro ⟨n, hn, ho⟩; rw [hq] at hn; cases hn; assumption
  · exact fun h => ⟨node, hq, h⟩
  · rintro ⟨n, hn, hx⟩; rw [hq] at hn; cases hn; assumption
  · exact fun h => ⟨node, hq, h⟩

/-- Name consistency: nodes are stored at their own name as key. -/
@[expose] def NameConsistent (st : ExpandState α S) : Prop :=
  ∀ (k : Nat) (node : ExpansionNode α S), st.nodes[k]? = some node → node.name = k

variable [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]

/-! ### Labeling correctness

`buildLabeling` computes each node's positive/negative atom sets and these lemmas connect it to `node.old`. -/

/-- The list fold for labeling: `.1` tracks positive atoms. -/
private theorem labeling_list_fold_fst
    (l : List (NNF α)) (init_pos init_neg : Std.HashSet α) (a : α) :
    (l.foldl (fun (acc : Std.HashSet α × Std.HashSet α) (formula : NNF α) =>
      match formula with
      | .prop b => (acc.1.insert b, acc.2)
      | .nprop b => (acc.1, acc.2.insert b)
      | _ => acc)
      (init_pos, init_neg)).1.contains a = true ↔
    init_pos.contains a = true ∨ NNF.prop a ∈ l := by
  induction l generalizing init_pos init_neg with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons]
    match hd with
    | .prop b =>
      dsimp only []; rw [ih]
      simp only [Std.HashSet.contains_insert, Bool.or_eq_true_iff, beq_iff_eq, NNF.prop.injEq]
      grind
    | .nprop _ => dsimp only []; rw [ih]; grind
    | .tt => dsimp only []; rw [ih]; grind
    | .ff => dsimp only []; rw [ih]; grind
    | .and _ _ => dsimp only []; rw [ih]; grind
    | .or _ _ => dsimp only []; rw [ih]; grind
    | .next _ => dsimp only []; rw [ih]; grind
    | .until _ _ => dsimp only []; rw [ih]; grind
    | .release _ _ => dsimp only []; rw [ih]; grind

/-- The list fold for labeling: `.2` tracks negative atoms. -/
private theorem labeling_list_fold_snd
    (l : List (NNF α)) (init_pos init_neg : Std.HashSet α) (a : α) :
    (l.foldl (fun (acc : Std.HashSet α × Std.HashSet α) (formula : NNF α) =>
      match formula with
      | .prop b => (acc.1.insert b, acc.2)
      | .nprop b => (acc.1, acc.2.insert b)
      | _ => acc)
      (init_pos, init_neg)).2.contains a = true ↔
    init_neg.contains a = true ∨ NNF.nprop a ∈ l := by
  induction l generalizing init_pos init_neg with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons]
    match hd with
    | .nprop b =>
      dsimp only []; rw [ih]
      simp only [Std.HashSet.contains_insert, Bool.or_eq_true_iff, beq_iff_eq, NNF.nprop.injEq]
      grind
    | .prop _ => dsimp only []; rw [ih]; grind
    | .tt => dsimp only []; rw [ih]; grind
    | .ff => dsimp only []; rw [ih]; grind
    | .and _ _ => dsimp only []; rw [ih]; grind
    | .or _ _ => dsimp only []; rw [ih]; grind
    | .next _ => dsimp only []; rw [ih]; grind
    | .until _ _ => dsimp only []; rw [ih]; grind
    | .release _ _ => dsimp only []; rw [ih]; grind

/-- Compute the labeling (positive, negative atom sets) for a single node. -/
private def computeNodeLabeling [BEq α] [Hashable α] [FSet (NNF α) S]
    (node : ExpansionNode α S) : Std.HashSet α × Std.HashSet α :=
  (FSet.toList node.old).foldl
    (fun (pos, neg) (formula : NNF α) =>
      match formula with
      | .prop a => (pos.insert a, neg)
      | .nprop a => (pos, neg.insert a)
      | _ => (pos, neg))
    (Std.HashSet.emptyWithCapacity 4, Std.HashSet.emptyWithCapacity 4)

omit [LawfulBEq α] [LawfulHashable α] in
/-- Helper: buildLabeling at q equals the value computed from the node at q. -/
private theorem buildLabeling_eq
    {nodeMap : Std.HashMap Nat (ExpansionNode α S)}
    (hname : ∀ k (node : ExpansionNode α S), nodeMap[k]? = some node → node.name = k)
    {q : Nat} {node : ExpansionNode α S} (hq : nodeMap[q]? = some node) :
    (buildLabeling nodeMap)[q]? = some (computeNodeLabeling node) := by
  simp only [buildLabeling, Std.HashMap.fold_eq_foldl_toList, FSet.foldl_eq_foldl_toList]
  have hmem := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hq
  have h_names_list : ∀ x ∈ nodeMap.toList, x.2.name = x.1 :=
    fun ⟨k, nd⟩ hx => hname k nd (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hx)
  have h_pw := pairwise_name_of_pairwise_key
    (Std.HashMap.distinct_keys_toList (m := nodeMap)) h_names_list
  exact HashMap_foldl_insert_gen nodeMap.toList
    (fun x => x.2.name)
    (fun x => computeNodeLabeling x.2)
    _ ⟨q, node⟩ hmem (by simp [hname q node hq]) h_pw

omit [LawfulBEq α] [LawfulHashable α] in
/-- `buildLabeling` is defined at every key that has a stored node. -/
theorem buildLabeling_some
    {nodeMap : Std.HashMap Nat (ExpansionNode α S)}
    (hname : ∀ k (node : ExpansionNode α S), nodeMap[k]? = some node → node.name = k)
    {q : Nat} {node : ExpansionNode α S} (hq : nodeMap[q]? = some node) :
    ∃ pos neg, (buildLabeling nodeMap)[q]? = some (pos, neg) := by
  rw [buildLabeling_eq hname hq]
  exact ⟨_, _, rfl⟩

/-- buildLabeling at q: positive atoms match node.old. -/
theorem buildLabeling_pos_correct
    {nodeMap : Std.HashMap Nat (ExpansionNode α S)}
    (hname : ∀ k (node : ExpansionNode α S), nodeMap[k]? = some node → node.name = k)
    {q : Nat} {node : ExpansionNode α S} (hq : nodeMap[q]? = some node)
    {pos neg : Std.HashSet α} (hlab : (buildLabeling nodeMap)[q]? = some (pos, neg))
    (a : α) :
    pos.contains a = FSet.contains node.old (.prop a) := by
  rw [buildLabeling_eq hname hq] at hlab
  simp only [computeNodeLabeling] at hlab
  have hinj := Option.some.inj hlab
  rw [Prod.ext_iff] at hinj; obtain ⟨hfst, _⟩ := hinj
  simp only [] at hfst; rw [← hfst]
  apply Bool.eq_iff_iff.mpr
  rw [labeling_list_fold_fst]
  simp only [Std.HashSet.contains_emptyWithCapacity, Bool.false_eq_true, false_or]
  exact FSet.mem_toList_iff (.prop a) node.old

/-- buildLabeling at q: negative atoms match node.old. -/
theorem buildLabeling_neg_correct
    {nodeMap : Std.HashMap Nat (ExpansionNode α S)}
    (hname : ∀ k (node : ExpansionNode α S), nodeMap[k]? = some node → node.name = k)
    {q : Nat} {node : ExpansionNode α S} (hq : nodeMap[q]? = some node)
    {pos neg : Std.HashSet α} (hlab : (buildLabeling nodeMap)[q]? = some (pos, neg))
    (a : α) :
    neg.contains a = FSet.contains node.old (.nprop a) := by
  rw [buildLabeling_eq hname hq] at hlab
  simp only [computeNodeLabeling] at hlab
  have hinj := Option.some.inj hlab
  rw [Prod.ext_iff] at hinj; obtain ⟨_, hsnd⟩ := hinj
  simp only [] at hsnd; rw [← hsnd]
  apply Bool.eq_iff_iff.mpr
  rw [labeling_list_fold_snd]
  simp only [Std.HashSet.contains_emptyWithCapacity, Bool.false_eq_true, false_or]
  exact FSet.mem_toList_iff (.nprop a) node.old

/-! ### Accept-set correctness -/

set_option backward.isDefEq.respectTransparency false in
omit [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] in
/-- `buildAcceptSets[i]` contains `q` iff node `q` either lacks the `i`-th until-formula in `old`, or has that
formula's right operand in `old`. -/
theorem buildAcceptSets_correct
    {nodeMap : Std.HashMap Nat (ExpansionNode α S)}
    (hname : ∀ k (node : ExpansionNode α S), nodeMap[k]? = some node → node.name = k)
    (untilSubs : List (NNF α × NNF α))
    (i : Fin untilSubs.length) {q : Nat} {node : ExpansionNode α S}
    (hq : nodeMap[q]? = some node) :
    let asets := buildAcceptSets nodeMap untilSubs
    let hi : i.val < asets.size := by
      simp only [asets, buildAcceptSets]; rw [Array.size_map]; exact i.isLt
    (asets[i.val]'hi).contains q =
      (!FSet.contains node.old (NNF.until (untilSubs[i]).1 (untilSubs[i]).2) ||
        FSet.contains node.old (untilSubs[i]).2) := by
  intro asets hi
  dsimp only [asets, buildAcceptSets]
  rw [Array.getElem_map]
  simp only [List.getElem_toArray]
  rw [Std.HashMap.fold_eq_foldl_toList, HashSet_foldl_insert_contains]
  simp only [Std.HashSet.contains_emptyWithCapacity, Bool.false_or]
  have hmem := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hq
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨k, nd⟩, hx, h_and⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h_and
    have hkv := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hx
    rw [hname k nd hkv] at h_and
    rw [h_and.2] at hkv; rw [hkv] at hq; cases hq
    exact h_and.1
  · intro h
    refine ⟨⟨q, node⟩, hmem, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨h, hname q node hq⟩

omit [LawfulBEq α] [LawfulHashable α] in
/-- numAcceptSets of constructGBA equals untilSubformulas length. -/
theorem constructGBA_numAcceptSets (φ : NNF α) (st : ExpandState α S) :
    (constructGBA φ st).numAcceptSets = φ.untilSubformulasDedup.length := by
  unfold constructGBA GBA.numAcceptSets buildAcceptSets
  simp

/-- Helper: isAccepting at a valid index equals direct array access. -/
private theorem GBA.isAccepting_eq_contains [BEq α'] [Hashable α']
    (gba : GBA α') {i : Nat} (hi : i < gba.acceptSets.size) (q : Nat) :
    gba.isAccepting i q = (gba.acceptSets[i]'hi).contains q := by
  unfold GBA.isAccepting
  rw [Array.getElem?_eq_getElem hi]

variable [Hashable (NNF α)]

/-! ### Name consistency from createGraph -/

omit [FSet (NNF α) S] [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [Hashable (NNF α)] in
/-- `mergeIncoming` preserves name consistency. -/
private theorem nameConsistent_mergeIncoming
    {st : ExpandState α S} {node : ExpansionNode α S} {targetName : Nat}
    (h_nc : NameConsistent st) :
    NameConsistent (mergeIncoming st node targetName) := by
  unfold mergeIncoming; split
  · next target ht =>
    intro k n hk
    simp only [Std.HashMap.getElem?_insert] at hk; split at hk
    · next heq =>
      have := (beq_iff_eq (α := Nat)).mp heq
      subst this; cases hk
      exact h_nc targetName target ht
    · exact h_nc k n hk
  · exact h_nc

omit [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] in
/-- createGraph produces a name-consistent ExpandState. -/
theorem createGraph_nameConsistent (φ : NNF α)
    {st : ExpandState α S} (hcg : createGraph φ = some st) :
    NameConsistent st := by
  simp only [createGraph] at hcg; split at hcg
  · rename_i nm finalState hr
    obtain rfl := Option.some.inj hcg
    show NameConsistent finalState
    have h_init : NameConsistent
        ({ nextName := 2, nodes := Std.HashMap.emptyWithCapacity 16,
            index := Std.HashMap.emptyWithCapacity 16 } : ExpandState α S) := by
      intro k n hk; simp at hk
    revert h_init
    apply expand.partial_correctness
      (motive := fun _node _st r => NameConsistent _st → NameConsistent r.2)
      _ _ _ _ hr
    intro expand_ih ih node st r hr h_nc
    split at hr
    case isTrue h_empty =>
      split at hr
      · -- merge with existing node
        obtain rfl := Option.some.inj hr
        exact nameConsistent_mergeIncoming h_nc
      · -- insert node, then recurse
        simp only [freshName] at hr
        have h_nc' : NameConsistent
            { st with nodes := st.nodes.insert node.name node,
                      nextName := st.nextName + 1 } := by
          intro k n hk
          simp only [Std.HashMap.getElem?_insert] at hk; split at hk
          · next heq =>
            have := (beq_iff_eq (α := Nat)).mp heq
            subst this; cases hk; rfl
          · exact h_nc k n hk
        exact ih _ _ _ hr h_nc'
    case isFalse h_not_empty =>
      simp only [Bool.not_eq_true] at h_not_empty
      simp only at hr
      split at hr
      · -- literal
        split at hr
        · obtain rfl := Option.some.inj hr; exact h_nc
        · exact ih _ _ _ hr h_nc
      · rename_i h_not_lit
        split at hr <;> (try split at hr) <;> (try split at hr) <;>
          (try split at hr) <;> (try split at hr)
        all_goals (first
          | (obtain rfl := Option.some.inj hr; exact h_nc)
          | exact ih _ _ _ hr h_nc
          | simp_all)
        -- Nondet case remains
        rename_i _ _ h_nondet
        revert hr; intro hr
        -- Nondeterministic step: split on the intermediate state produced by the first recursive call
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
          have h1 := ih _ _ nm' st_mid h_branch1 h_nc
          exact ih _ _ _ _ hr h1
  · nomatch hcg

/-! ### Literal consistency from createGraph -/

omit [Hashable α] [LawfulHashable α] in
/-- A finished node's `old` set never contains both `prop a` and `nprop a`. -/
theorem createGraph_literal_consistent (φ : NNF α) {st : ExpandState α S}
    (hcg : createGraph φ = some st) {q : Nat} {node : ExpansionNode α S}
    (hnode : st.nodes[q]? = some node) (a : α)
    (hp : FSet.contains node.old (.prop a) = true)
    (hn : FSet.contains node.old (.nprop a) = true) : False := by
  have hspec := createGraph_spec φ hcg
  have hmem := ExpandState.liftNode_mem_toNodes st q hnode
  have hp' : (st.liftNode q).old (.prop a) := ⟨node, hnode, hp⟩
  have hn' : (st.liftNode q).old (.nprop a) := ⟨node, hnode, hn⟩
  exact hspec.literal_consistent (st.liftNode q) hmem a hp' hn'

/-- The positive/negative atom sets `buildLabeling` computes for a `createGraph` node are always disjoint. -/
theorem buildLabeling_disjoint (φ : NNF α) {st : ExpandState α S}
    (hcg : createGraph φ = some st) {q : Nat} {node : ExpansionNode α S}
    (hnode : st.nodes[q]? = some node)
    {pos neg : Std.HashSet α} (hlab : (buildLabeling st.nodes)[q]? = some (pos, neg))
    (a : α) (hpos : pos.contains a = true) (hneg : neg.contains a = true) : False := by
  have hname := createGraph_nameConsistent φ hcg
  rw [buildLabeling_pos_correct hname hnode hlab a] at hpos
  rw [buildLabeling_neg_correct hname hnode hlab a] at hneg
  exact createGraph_literal_consistent φ hcg hnode a hpos hneg

/-! ### Direction 1: GBA.toSpec accepts → expandOASpec accepts

Given a run σ : Nat → Nat in the computational GBA, lift it to σ' : Nat → NodeData α in the abstract automaton. -/

/-- Every word `constructGBA` accepts is also accepted by `expandOASpec`. -/
theorem constructGBA_toSpec_refines_expandOASpec
    {φ : NNF α} {st : ExpandState α S}
    (hcg : createGraph φ = some st)
    {ξ : OmegaWord α}
    (hacc : (constructGBA φ st).toSpec.accepts ξ) :
    (expandOASpec φ st.toNodes φ.untilSubformulasDedup).accepts ξ := by
  obtain ⟨σ, hrun, hcompat, haccRun⟩ := hacc
  have hname := createGraph_nameConsistent φ hcg
  -- Show each σ n corresponds to an actual node in st.nodes
  have h_exists : ∀ n, ∃ node, st.nodes[σ n]? = some node := by
    intro n
    cases n with
    | zero =>
      have hinit := hrun.1
      simp only [GBA.toSpec, GBA.isInitial, constructGBA] at hinit
      exact ((buildInitialStates_correct hname (σ 0)).mp hinit).imp fun _ h => h.1
    | succ n =>
      have htrans := hrun.2 n
      simp only [GBA.toSpec, constructGBA] at htrans
      exact ((buildSuccessors_mem_iff hname (σ n) (σ (n + 1))).mp htrans).imp fun _ h => h.1
  -- Lift the run
  let σ' : Nat → NodeData α := fun n => st.liftNode (σ n)
  have h_nodes : ∀ n, st.toNodes (σ' n) := by
    intro n; obtain ⟨node, hnode⟩ := h_exists n
    exact ExpandState.liftNode_mem_toNodes st (σ n) hnode
  refine ⟨σ', ?_, ?_, ?_⟩
  · -- isRun
    constructor
    · -- initial
      refine ⟨h_nodes 0, ?_⟩
      have hinit := hrun.1
      simp only [GBA.toSpec, GBA.isInitial, constructGBA] at hinit
      obtain ⟨node, hnode, hinc⟩ := (buildInitialStates_correct hname (σ 0)).mp hinit
      show (st.liftNode (σ 0)).incoming expandInit
      exact ⟨node, hnode, hinc⟩
    · -- transitions
      intro n
      refine ⟨h_nodes n, h_nodes (n + 1), ?_⟩
      have htrans := hrun.2 n
      simp only [GBA.toSpec, constructGBA] at htrans
      obtain ⟨node, hnode, hinc⟩ :=
        (buildSuccessors_mem_iff hname (σ n) (σ (n + 1))).mp htrans
      show (st.liftNode (σ (n + 1))).incoming (σ n)
      exact ⟨node, hnode, hinc⟩
  · -- runCompatible
    intro n
    obtain ⟨node, hnode⟩ := h_exists n
    constructor
    · -- positive atoms: old(.prop a) → ξ(n)(a)
      intro a ⟨node', hnode', hprop⟩
      rw [hnode] at hnode'; cases hnode'
      have hcompat_n := hcompat n
      simp only [GBA.toSpec, constructGBA] at hcompat_n
      obtain ⟨pos, neg, hlab⟩ := buildLabeling_some hname hnode
      rw [hlab] at hcompat_n
      have := (buildLabeling_pos_correct hname hnode hlab a).symm ▸ hprop
      exact hcompat_n.1 a this
    · -- negative atoms: old(.nprop a) → ¬ξ(n)(a)
      intro a ⟨node', hnode', hnprop⟩
      rw [hnode] at hnode'; cases hnode'
      have hcompat_n := hcompat n
      simp only [GBA.toSpec, constructGBA] at hcompat_n
      obtain ⟨pos, neg, hlab⟩ := buildLabeling_some hname hnode
      rw [hlab] at hcompat_n
      have := (buildLabeling_neg_correct hname hnode hlab a).symm ▸ hnprop
      exact hcompat_n.2 a this
  · -- isAcceptingRun
    intro i n
    have hnum := constructGBA_numAcceptSets φ st
    obtain ⟨j, hj⟩ := haccRun ⟨i.val, by rw [hnum]; exact i.isLt⟩ n
    refine ⟨j, ?_⟩
    obtain ⟨node, hnode⟩ := h_exists (n + j)
    have hacc_eq := buildAcceptSets_correct hname φ.untilSubformulasDedup i hnode
    -- Convert hj from GBA.isAccepting to raw boolean
    simp only [GBA.toSpec] at hj
    have hi_gba : i.val < (constructGBA φ st).acceptSets.size := by
      simp only [constructGBA, buildAcceptSets, Array.size_map]; exact i.isLt
    rw [GBA.isAccepting_eq_contains _ hi_gba] at hj
    simp only [constructGBA] at hj
    dsimp only [] at hacc_eq
    rw [hacc_eq] at hj
    -- hj : (!FSet.contains ... || FSet.contains ...) = true
    simp only [expandOASpec]
    rcases Bool.or_eq_true_iff.mp hj with h | h
    · -- !FSet.contains = true, i.e., FSet.contains = false
      left
      rw [Bool.not_eq_true'] at h
      intro ⟨node', hnode', h'⟩
      rw [hnode] at hnode'; cases hnode'
      -- h and h' are about the same boolean (defeq) but with different indexing
      exact absurd h' (h ▸ Bool.noConfusion)
    · -- η ∈ old
      right
      exact ⟨node, hnode, h⟩

/-! ### Direction 2: expandOASpec accepts → GBA.toSpec accepts

Given a run σ : Nat → NodeData α in the abstract automaton, project it to σ' : Nat → Nat in the computational GBA. -/

/-- Every word `expandOASpec` accepts is also accepted by `constructGBA`. -/
theorem expandOASpec_refines_constructGBA_toSpec
    {φ : NNF α} {st : ExpandState α S}
    (hcg : createGraph φ = some st)
    {ξ : OmegaWord α}
    (hacc : (expandOASpec φ st.toNodes φ.untilSubformulasDedup).accepts ξ) :
    (constructGBA φ st).toSpec.accepts ξ := by
  obtain ⟨σ, hrun, hcompat, haccRun⟩ := hacc
  have hname := createGraph_nameConsistent φ hcg
  -- Each σ n is in st.toNodes, so there's a corresponding ExpansionNode
  have h_node : ∀ n, ∃ node : ExpansionNode α S,
      st.nodes[(σ n).name]? = some node ∧
      (∀ k, (σ n).incoming k ↔ node.incoming.contains k) ∧
      (∀ ψ, (σ n).old ψ ↔ FSet.contains node.old ψ) ∧
      (∀ ψ, (σ n).next ψ ↔ FSet.contains node.next ψ) := by
    intro n
    have hmem : st.toNodes (σ n) := by
      cases n with
      | zero => exact hrun.1.1
      | succ n => exact (hrun.2 n).2.1
    exact hmem
  -- Define the Nat run
  let σ' : Nat → Nat := fun n => (σ n).name
  refine ⟨σ', ?_, ?_, ?_⟩
  · -- isRun
    constructor
    · -- initial
      simp only [GBA.toSpec, GBA.isInitial, constructGBA]
      obtain ⟨node, hnode, hinc_iff, _, _⟩ := h_node 0
      exact (buildInitialStates_correct hname _).mpr
        ⟨node, hnode, (hinc_iff expandInit).mp hrun.1.2⟩
    · -- transitions
      intro n
      simp only [GBA.toSpec, constructGBA]
      obtain ⟨node', hnode', hinc_iff', _, _⟩ := h_node (n + 1)
      have htrans := (hrun.2 n).2.2
      exact (buildSuccessors_mem_iff hname _ _).mpr
        ⟨node', hnode', (hinc_iff' (σ n).name).mp htrans⟩
  · -- runCompatible
    intro n
    simp only [GBA.toSpec, constructGBA]
    obtain ⟨node, hnode, _, hold_iff, _⟩ := h_node n
    obtain ⟨pos, neg, hlab⟩ := buildLabeling_some hname hnode
    rw [hlab]
    have hcompat_n := hcompat n
    constructor
    · intro a hpos
      have heq := buildLabeling_pos_correct hname hnode hlab a
      exact hcompat_n.1 a ((hold_iff (.prop a)).mpr (heq ▸ hpos))
    · intro a hneg
      have heq := buildLabeling_neg_correct hname hnode hlab a
      exact hcompat_n.2 a ((hold_iff (.nprop a)).mpr (heq ▸ hneg))
  · -- isAcceptingRun
    intro i n
    have hnum := constructGBA_numAcceptSets φ st
    let i' : Fin φ.untilSubformulasDedup.length := ⟨i.val, hnum ▸ i.isLt⟩
    obtain ⟨j, hj⟩ := haccRun i' n
    refine ⟨j, ?_⟩
    obtain ⟨node, hnode, _, hold_iff, _⟩ := h_node (n + j)
    simp only [expandOASpec] at hj
    -- First prove the boolean expression
    have hbool : (!FSet.contains node.old
        (.until (φ.untilSubformulasDedup[i']).1 (φ.untilSubformulasDedup[i']).2) ||
        FSet.contains node.old (φ.untilSubformulasDedup[i']).2) = true := by
      cases hU : FSet.contains node.old
          (.until (φ.untilSubformulasDedup[i']).1 (φ.untilSubformulasDedup[i']).2) with
      | false => simp
      | true =>
        simp only [Bool.not_true, Bool.false_or]
        have h_until_old := (hold_iff _).mpr hU
        rcases hj with h | h
        · exact absurd h_until_old h
        · exact (hold_iff _).mp h
    -- Connect to GBA acceptance
    simp only [GBA.toSpec]
    have hi_gba : i.val < (constructGBA φ st).acceptSets.size := by
      simp only [constructGBA, buildAcceptSets, Array.size_map]; exact i'.isLt
    rw [GBA.isAccepting_eq_contains _ hi_gba]
    simp only [constructGBA]
    have hacc_eq := buildAcceptSets_correct hname φ.untilSubformulasDedup i' hnode
    dsimp only [] at hacc_eq
    rw [hacc_eq]
    exact hbool

/-! ### Combined bridge -/

/-- The computational GBA and abstract automaton accept the same words. -/
theorem constructGBA_iff_expandOASpec
    {φ : NNF α} {st : ExpandState α S}
    (hcg : createGraph φ = some st)
    (ξ : OmegaWord α) :
    (constructGBA φ st).toSpec.accepts ξ ↔
      (expandOASpec φ st.toNodes φ.untilSubformulasDedup).accepts ξ :=
  ⟨constructGBA_toSpec_refines_expandOASpec hcg,
   expandOASpec_refines_constructGBA_toSpec hcg⟩

/-! ### Well-formedness of constructGBA -/

omit [LawfulBEq α] [LawfulHashable α] in
/-- `constructGBA`'s output is well-formed: initial states and successors of known states are themselves known states. -/
theorem constructGBA_wellFormed {φ : NNF α} {st : ExpandState α S}
    (hcg : createGraph φ = some st) :
    (constructGBA φ st).WellFormed := by
  have hname := createGraph_nameConsistent φ hcg
  have hcontains : ∀ {q : Nat} {node : ExpansionNode α S}, st.nodes[q]? = some node →
      (constructGBA φ st).states.contains q = true := by
    intro q node hq
    simp only [constructGBA]
    rw [buildStates_mem_iff, Std.HashMap.contains_eq_isSome_getElem?, hq]; rfl
  refine ⟨?_, ?_⟩
  · -- initial_mem
    intro q hq
    simp only [GBA.isInitial, constructGBA] at hq
    obtain ⟨node, hnode, _⟩ := (buildInitialStates_correct hname q).mp hq
    exact hcontains hnode
  · -- succ_mem
    intro q q' _ hq'
    simp only [GBA.getSuccessors, constructGBA] at hq'
    obtain ⟨node, hnode, _⟩ := (buildSuccessors_mem_iff hname q q').mp hq'
    exact hcontains hnode

/-! ### Canonical labeling for constructGBA -/

/-- `canonicalLabel`, applied to `constructGBA`'s own `labeling` map, always satisfies `labelCompat` at any state
    with a stored node. -/
theorem constructGBA_canonicalLabel_compat (φ : NNF α) {st : ExpandState α S}
    (hcg : createGraph φ = some st) {q : Nat} {node : ExpansionNode α S}
    (hnode : st.nodes[q]? = some node) :
    (constructGBA φ st).toSpec.labelCompat q
      (canonicalLabel (constructGBA φ st).labeling q) := by
  have hname := createGraph_nameConsistent φ hcg
  obtain ⟨pos, neg, hlab⟩ := buildLabeling_some hname hnode
  have hlab' : (constructGBA φ st).labeling[q]? = some (pos, neg) := by
    simp only [constructGBA]; exact hlab
  show (GBA.toSpec (constructGBA φ st)).labelCompat q _
  simp only [GBA.toSpec, hlab']
  exact canonicalLabel_compat hlab' (buildLabeling_disjoint φ hcg hnode hlab)

end LTLLib
