/-
  Soundness of the LTL-to-GBA construction.

  Core theorem: For a valid node run σ labeled by ξ,
  if ψ ∈ old(σ n) then NNF.satisfies (ξ.drop n) ψ.

  Top-level: If the expand result satisfies ExpandSpec and there is
  a valid accepting run σ through the nodes labeled by ξ, then ξ satisfies φ.
-/

import LTLLib.LTLtoGBA.Invariants
import LTLLib.LTLtoGBA.Construction
import LTLLib.LTL.Semantics
import LTLLib.AbstractSpec.Acceptance
import Mathlib.Order.Nat

namespace LTLLib

open NNF TLA

variable {α : Type u}

/-! ### Helper lemmas for temporal propagation -/

/-- One step of until propagation: if until(μ,η) ∈ old and η ∉ old,
    then μ ∈ old and until carries to the next state. -/
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
  have := spec.until_propag _ (h_nodes n) _ _ h_old
  rcases this with h | ⟨hμ, h_next⟩
  · exact absurd h h_no_eta
  · exact ⟨hμ, spec.successor_old _ (h_nodes n) _ (h_nodes (n+1)) (h_succ n) _ h_next⟩

/-- One step of release propagation: if release(μ,ψ) ∈ old and μ ∉ old,
    then ψ ∈ old and release carries to the next state. -/
private theorem release_step
    {φ : NNF α} {nodes : NodeData α → Prop}
    (spec : ExpandSpec φ nodes)
    {σ : Nat → NodeData α}
    (h_nodes : ∀ n, nodes (σ n))
    (h_succ : ∀ n, (σ (n + 1)).incoming (σ n).name)
    {μ ψ : NNF α} {n : Nat}
    (h_old : (σ n).old (.release μ ψ))
    (h_no_mu : ¬(σ n).old μ) :
    (σ n).old ψ ∧ (σ (n + 1)).old (.release μ ψ) := by
  have ⟨hψ, h_or⟩ := spec.release_propag _ (h_nodes n) _ _ h_old
  rcases h_or with hμ | h_next
  · exact absurd hμ h_no_mu
  · exact ⟨hψ, spec.successor_old _ (h_nodes n) _ (h_nodes (n+1)) (h_succ n) _ h_next⟩

/-! ### Core soundness theorem -/

/-- Core soundness lemma: formulas in old are satisfied.
    For any position n, every formula in old(σ n) is satisfied
    by the suffix ξ.drop n. -/
theorem old_implies_satisfied
    {φ : NNF α} {nodes : NodeData α → Prop}
    (spec : ExpandSpec φ nodes)
    {σ : Nat → NodeData α} {ξ : OmegaWord α}
    (h_nodes : ∀ n, nodes (σ n))
    (h_succ : ∀ n, (σ (n + 1)).incoming (σ n).name)
    (h_label_pos : ∀ n a, (σ n).old (.prop a) → (ξ n) a)
    (h_label_neg : ∀ n a, (σ n).old (.nprop a) → ¬(ξ n) a)
    (h_accept : ∀ μ η, NNF.IsSubformula (.until μ η) φ →
      ∀ n, ∃ j, ¬(σ (n + j)).old (.until μ η) ∨ (σ (n + j)).old η) :
    ∀ (ψ : NNF α), ∀ n, (σ n).old ψ → NNF.satisfies (ξ.drop n) ψ := by
  intro ψ
  induction ψ with
  | tt =>
    intro n _
    dsimp [NNF.satisfies, NNF.toPred]
    tunfold_simp
  | ff =>
    intro n h
    exact absurd h (spec.no_false _ (h_nodes n))
  | prop a =>
    intro n h
    show (ξ.drop n 0) a
    simp [exec.drop]
    exact h_label_pos n a h
  | nprop a =>
    intro n h
    show ¬(ξ.drop n 0) a
    simp [exec.drop]
    exact h_label_neg n a h
  | and μ ψ ih_μ ih_ψ =>
    intro n h
    have ⟨hμ, hψ⟩ := spec.and_propag _ (h_nodes n) _ _ h
    dsimp [NNF.satisfies, NNF.toPred] at ih_μ ih_ψ ⊢
    tunfold_simp
    exact ⟨ih_μ n hμ, ih_ψ n hψ⟩
  | or μ ψ ih_μ ih_ψ =>
    intro n h
    dsimp [NNF.satisfies, NNF.toPred] at ih_μ ih_ψ ⊢
    tunfold_simp
    rcases spec.or_propag _ (h_nodes n) _ _ h with hμ | hψ
    · exact Or.inl (ih_μ n hμ)
    · exact Or.inr (ih_ψ n hψ)
  | next ψ ih =>
    intro n h
    have h_next := spec.next_propag _ (h_nodes n) _ h
    have h_old := spec.successor_old _ (h_nodes n) _ (h_nodes (n+1)) (h_succ n) _ h_next
    dsimp [NNF.satisfies, NNF.toPred] at ih ⊢
    tunfold_simp
    exact ih (n + 1) h_old
  | «until» μ η ih_μ ih_η =>
    intro n h_old
    dsimp [NNF.satisfies, NNF.toPred] at ih_μ ih_η ⊢
    tunfold_simp
    have hsub := spec.old_subformula _ (h_nodes n) _ h_old
    have hex := h_accept μ η hsub n
    classical
    let j₀ := Nat.find hex
    have hj₀_spec := Nat.find_spec hex
    have hj₀_min : ∀ k < j₀, ¬(¬(σ (n + k)).old (.until μ η) ∨ (σ (n + k)).old η) :=
      fun k hk => Nat.find_min hex hk
    have h_before : ∀ k < j₀, (σ (n + k)).old (.until μ η) ∧ ¬(σ (n + k)).old η := by
      intro k hk
      have := hj₀_min k hk
      push_neg at this
      exact this
    have h_until_stays : ∀ k, k ≤ j₀ → (σ (n + k)).old (.until μ η) := by
      intro k hk
      induction k with
      | zero => simpa
      | succ k ih_k =>
        have hk_lt : k < j₀ := by omega
        have ⟨h_u, h_ne⟩ := h_before k hk_lt
        have h_step := (until_step spec h_nodes h_succ h_u h_ne).2
        rwa [show n + k + 1 = n + (k + 1) from by omega] at h_step
    have h_eta_j0 : (σ (n + j₀)).old η := by
      rcases hj₀_spec with h | h
      · exact absurd (h_until_stays j₀ (le_refl j₀)) h
      · exact h
    have h_mu_before : ∀ k < j₀, (σ (n + k)).old μ := by
      intro k hk
      exact (until_step spec h_nodes h_succ
        (h_until_stays k (le_of_lt hk)) (h_before k hk).2).1
    refine ⟨j₀, ?_, ?_⟩
    · exact ih_η (n + j₀) h_eta_j0
    · intro i hi
      exact ih_μ (n + i) (h_mu_before i hi)
  | «release» μ ψ ih_μ ih_ψ =>
    intro n h_old
    dsimp [NNF.satisfies, NNF.toPred, tla_release] at ih_μ ih_ψ ⊢
    intro j
    classical
    by_cases h : ∃ i, i < j ∧ (σ (n + i)).old μ
    · right
      obtain ⟨i, hi, hμ⟩ := h
      exact ⟨i, hi, by simp only [exec.drop_drop]; exact ih_μ (n + i) hμ⟩
    · left
      push_neg at h
      have h_rel : ∀ k, k ≤ j → (σ (n + k)).old (.release μ ψ) := by
        intro k hk
        induction k with
        | zero => simpa
        | succ k ih_k =>
          have hk_lt : k < j := by omega
          have h_rel_k := ih_k (by omega)
          have h_no_mu := h k hk_lt
          have h_step := (release_step spec h_nodes h_succ h_rel_k h_no_mu).2
          rwa [show n + k + 1 = n + (k + 1) from by omega] at h_step
      have h_rel_j := h_rel j (le_refl j)
      have ⟨hψ, _⟩ := spec.release_propag _ (h_nodes (n + j)) _ _ h_rel_j
      simp only [exec.drop_drop]; exact ih_ψ (n + j) hψ

/-! ### Top-level soundness (L4_9) -/

/-- Top-level soundness: If the expand result satisfies ExpandSpec
    and there exists a valid accepting run σ through the nodes labeled by ξ,
    then ξ satisfies φ. -/
theorem soundness
    {φ : NNF α} {nodes : NodeData α → Prop}
    (spec : ExpandSpec φ nodes)
    {σ : Nat → NodeData α} {ξ : OmegaWord α}
    (h_nodes : ∀ n, nodes (σ n))
    (h_succ : ∀ n, (σ (n + 1)).incoming (σ n).name)
    (h_init : (σ 0).incoming expandInit)
    (h_label_pos : ∀ n a, (σ n).old (.prop a) → (ξ n) a)
    (h_label_neg : ∀ n a, (σ n).old (.nprop a) → ¬(ξ n) a)
    (h_accept : ∀ μ η, NNF.IsSubformula (.until μ η) φ →
      ∀ n, ∃ j, ¬(σ (n + j)).old (.until μ η) ∨ (σ (n + j)).old η)
    : NNF.satisfies ξ φ := by
  have h_phi := spec.initial_old _ (h_nodes 0) h_init
  have h := old_implies_satisfied spec h_nodes h_succ h_label_pos h_label_neg h_accept φ 0 h_phi
  simp only [NNF.satisfies] at h ⊢
  have : ξ.drop 0 = ξ := by funext n; simp [exec.drop]
  rw [this] at h
  exact h

/-! ### Concrete soundness via createGraph -/

/-- Concrete soundness: if createGraph succeeds, the expansion nodes satisfy
    the abstract soundness hypotheses. This is a direct corollary of
    `createGraph_spec` + `soundness`. -/
theorem concrete_soundness
    {S : Type v} [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)]
    {φ : NNF α} {st : ExpandState α S}
    (hcg : createGraph φ = some st)
    {σ : Nat → NodeData α} {ξ : OmegaWord α}
    (h_nodes : ∀ n, st.toNodes (σ n))
    (h_succ : ∀ n, (σ (n + 1)).incoming (σ n).name)
    (h_init : (σ 0).incoming expandInit)
    (h_label_pos : ∀ n a, (σ n).old (.prop a) → (ξ n) a)
    (h_label_neg : ∀ n a, (σ n).old (.nprop a) → ¬(ξ n) a)
    (h_accept : ∀ μ η, NNF.IsSubformula (.until μ η) φ →
      ∀ n, ∃ j, ¬(σ (n + j)).old (.until μ η) ∨ (σ (n + j)).old η)
    : NNF.satisfies ξ φ :=
  soundness (createGraph_spec φ hcg) h_nodes h_succ h_init h_label_pos h_label_neg h_accept

/-! ### Abstract automaton from ExpandSpec

Instead of reasoning about `constructGBA` (which requires HashMap/HashSet
correctness lemmas), we define the automaton specification abstractly from
`NodeData` predicates. The acceptance condition indexes over until-subformulas
of φ via `IsSubformula`. -/

/-- Abstract automaton induced by ExpandSpec nodes.
    States are `NodeData α` values. Transitions are via the `incoming` relation.
    Label compatibility checks positive/negative atoms in `old`.
    Acceptance sets correspond to until-subformulas of φ: a state is accepting
    for (μ U η) iff the until obligation is either absent or satisfied. -/
def expandOASpec (_φ : NNF α) (nodes : NodeData α → Prop)
    (untils : List (NNF α × NNF α)) :
    OASpec (NodeData α) α untils.length where
  trans q q' := nodes q ∧ nodes q' ∧ q'.incoming q.name
  initial q := nodes q ∧ q.incoming expandInit
  labelCompat q v :=
    (∀ a, q.old (.prop a) → v a) ∧ (∀ a, q.old (.nprop a) → ¬v a)
  acceptSet i q :=
    let (μ, η) := untils[i]
    ¬q.old (.until μ η) ∨ q.old η

/-- Soundness of the abstract automaton: if the abstract automaton
    induced by `ExpandSpec` nodes accepts ξ, then ξ satisfies φ. -/
theorem expandOASpec_soundness
    {φ : NNF α} {nodes : NodeData α → Prop}
    (spec : ExpandSpec φ nodes)
    {untils : List (NNF α × NNF α)}
    (h_untils : ∀ μ η, NNF.IsSubformula (.until μ η) φ →
      ∃ i : Fin untils.length, untils[i] = (μ, η))
    {ξ : OmegaWord α}
    (hacc : (expandOASpec φ nodes untils).accepts ξ)
    : NNF.satisfies ξ φ := by
  obtain ⟨σ, hrun, hcompat, haccRun⟩ := hacc
  have h_nodes : ∀ n, nodes (σ n) := by
    intro n
    cases n with
    | zero => exact hrun.1.1
    | succ n => exact (hrun.2 n).2.1
  apply soundness spec h_nodes
  · -- h_succ: successor relationship via incoming
    intro n
    exact (hrun.2 n).2.2
  · -- h_init: initial state has expandInit in incoming
    exact hrun.1.2
  · -- h_label_pos
    intro n a hold
    exact (hcompat n).1 a hold
  · -- h_label_neg
    intro n a hold
    exact (hcompat n).2 a hold
  · -- h_accept: for each until-subformula, the acceptance condition holds i.o.
    intro μ η hsub n
    obtain ⟨i, hi⟩ := h_untils μ η hsub
    obtain ⟨j, hj⟩ := haccRun i n
    refine ⟨j, ?_⟩
    simp only [expandOASpec] at hj
    have : untils.get ⟨↑i, i.isLt⟩ = (μ, η) := hi
    rw [this] at hj
    exact hj

/-! ### untilSubformulas completeness -/

/-- Helper: the fold function used in `untilSubformulas`. -/
private abbrev untilFoldFn (α : Type u) :=
  fun (acc : List (NNF α × NNF α)) (f : NNF α) =>
    match f with | .until a b => (a, b) :: acc | _ => acc

/-- The fold preserves accumulator elements. -/
private theorem fold_until_mono (φ : NNF α)
    (acc : List (NNF α × NNF α)) (x : NNF α × NNF α)
    (hx : x ∈ acc) :
    x ∈ φ.fold (untilFoldFn α) acc := by
  induction φ generalizing acc with
  | tt | ff | prop _ | nprop _ => exact hx
  | next ψ ih => exact ih _ hx
  | and ψ₁ ψ₂ ih₁ ih₂ | or ψ₁ ψ₂ ih₁ ih₂ | «release» ψ₁ ψ₂ ih₁ ih₂ =>
    exact ih₂ _ (ih₁ _ hx)
  | «until» ψ₁ ψ₂ ih₁ ih₂ =>
    exact ih₂ _ (ih₁ _ (.tail _ hx))

/-- For any accumulator, if ψ is a subformula and ψ = until μ η,
    then (μ, η) appears in the fold result. -/
private theorem fold_until_complete (φ : NNF α) (acc : List (NNF α × NNF α))
    (μ η : NNF α) (hsub : NNF.IsSubformula (.until μ η) φ) :
    (μ, η) ∈ φ.fold (untilFoldFn α) acc := by
  induction φ generalizing acc with
  | tt | ff | prop _ | nprop _ => cases hsub
  | next ψ ih =>
    cases hsub with
    | next_sub h => exact ih _ h
  | and ψ₁ ψ₂ ih₁ ih₂ =>
    cases hsub with
    | and_left h => exact fold_until_mono ψ₂ _ _ (ih₁ _ h)
    | and_right h => exact ih₂ _ h
  | or ψ₁ ψ₂ ih₁ ih₂ =>
    cases hsub with
    | or_left h => exact fold_until_mono ψ₂ _ _ (ih₁ _ h)
    | or_right h => exact ih₂ _ h
  | «until» ψ₁ ψ₂ ih₁ ih₂ =>
    cases hsub with
    | refl =>
      show (μ, η) ∈ η.fold (untilFoldFn α) (μ.fold (untilFoldFn α) ((μ, η) :: acc))
      exact fold_until_mono η _ _ (fold_until_mono μ _ _ (.head _))
    | until_left h =>
      show (μ, η) ∈ ψ₂.fold (untilFoldFn α) (ψ₁.fold (untilFoldFn α) ((ψ₁, ψ₂) :: acc))
      exact fold_until_mono ψ₂ _ _ (ih₁ _ h)
    | until_right h =>
      show (μ, η) ∈ ψ₂.fold (untilFoldFn α) (ψ₁.fold (untilFoldFn α) ((ψ₁, ψ₂) :: acc))
      exact ih₂ _ h
  | «release» ψ₁ ψ₂ ih₁ ih₂ =>
    cases hsub with
    | release_left h => exact fold_until_mono ψ₂ _ _ (ih₁ _ h)
    | release_right h => exact ih₂ _ h

/-- Every until-subformula (in the IsSubformula sense) appears in
    `φ.untilSubformulas`. -/
theorem untilSubformulas_complete (φ : NNF α) (μ η : NNF α)
    (hsub : NNF.IsSubformula (.until μ η) φ) :
    (μ, η) ∈ φ.untilSubformulas :=
  fold_until_complete φ [] μ η hsub

/-- `untilSubformulas_complete` as an index lookup, matching the
    `h_untils` hypothesis of `expandOASpec_soundness`. -/
theorem untilSubformulas_index (φ : NNF α) (μ η : NNF α)
    (hsub : NNF.IsSubformula (.until μ η) φ) :
    ∃ i : Fin φ.untilSubformulas.length,
      φ.untilSubformulas[i] = (μ, η) := by
  have hmem := untilSubformulas_complete φ μ η hsub
  exact List.mem_iff_get.mp hmem

/-! ### Concrete soundness via expandOASpec

Instantiates `expandOASpec_soundness` with `createGraph_spec` and
`φ.untilSubformulas` as the until-subformula list. -/

theorem gba_abstract_soundness
    {S : Type v} [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)]
    {φ : NNF α} {st : ExpandState α S}
    (hcg : createGraph φ = some st)
    {ξ : OmegaWord α}
    (hacc : (expandOASpec φ st.toNodes φ.untilSubformulas).accepts ξ)
    : NNF.satisfies ξ φ :=
  expandOASpec_soundness (createGraph_spec φ hcg)
    (fun μ η hsub => untilSubformulas_index φ μ η hsub) hacc

end LTLLib
