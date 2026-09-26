/-
  Soundness of the LTL-to-GBA construction: any valid accepting run through `ExpandSpec`-satisfying nodes labeled by an
  ω-word ξ implies ξ ⊨ φ.

  Defines:
  - `old_implies_satisfied`: for a valid node run σ labeled by ξ, ψ ∈ old(σ n) → ξ.drop n ⊨ ψ
  - `soundness`: top-level soundness for `ExpandSpec` nodes
  - `concrete_soundness`: soundness corollary via `createGraph`
  - `expandOASpec_soundness`: soundness of the `expandOASpec` abstract automaton
  - `gba_abstract_soundness`: `expandOASpec_soundness` corollary via `createGraph`

  ### Sections
  - Helper lemmas for temporal propagation
  - Core soundness theorem
  - Top-level soundness
  - Concrete soundness via createGraph
  - Soundness of the abstract automaton
  - Concrete soundness via expandOASpec
-/

import LTLLib.LTLtoGBA.Invariants
import LTLLib.LTLtoGBA.ToGBA
import LTLLib.LTLtoGBA.AbstractSpec.ExpansionSpec
import LTLLib.LTL.Semantics
import LTLLib.LTL.Subformulas
import LTLLib.AbstractSpec.Acceptance
import Mathlib.Order.Nat

namespace LTLLib

open NNF Lentil

variable {α : Type u}

/-! ### Helper lemmas for temporal propagation -/

/-- One step of until propagation: if until(μ,η) ∈ old and η ∉ old, then μ ∈ old and until carries to the next state. -/
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

/-- One step of release propagation: if release(μ,ψ) ∈ old and μ ∉ old, then ψ ∈ old and release carries next. -/
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

/-- Every formula in old(σ n) is satisfied by the suffix ξ.drop n. -/
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
    rw [NNF.satisfies_next, exec.drop_drop]
    exact ih (n + 1) h_old
  | «until» μ η ih_μ ih_η =>
    intro n h_old
    simp only [NNF.satisfies_until, exec.drop_drop]
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
    rw [NNF.satisfies_release]
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

/-! ### Top-level soundness -/

/-- If there is a valid accepting run through `ExpandSpec` nodes labeled by ξ, then ξ satisfies φ. -/
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

/-- If `createGraph` succeeds and there is a valid accepting run through the resulting nodes labeled by ξ, then ξ ⊨ φ. -/
theorem concrete_soundness
    {S : Type v} [FSet (NNF α) S] [Hashable (NNF α)] [BEq (NNF α)] [LawfulBEq (NNF α)]
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

/-! ### Soundness of the abstract automaton

`expandOASpec` (see `LTLLib.LTLtoGBA.AbstractSpec.ExpansionSpec`) packages `ExpandSpec` nodes as an `OASpec`, an
automaton abstraction independent of `constructGBA`'s own representation. -/

/-- If the abstract automaton induced by `ExpandSpec` nodes accepts ξ, then ξ satisfies φ. -/
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
    rw [hi] at hj
    exact hj

/-! ### Concrete soundness via expandOASpec -/

/-- Concrete soundness of the abstract automaton via `createGraph`, using `φ.untilSubformulasDedup` as the until-subformula list. -/
theorem gba_abstract_soundness
    {S : Type v} [FSet (NNF α) S] [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {φ : NNF α} {st : ExpandState α S}
    (hcg : createGraph φ = some st)
    {ξ : OmegaWord α}
    (hacc : (expandOASpec φ st.toNodes φ.untilSubformulasDedup).accepts ξ)
    : NNF.satisfies ξ φ :=
  expandOASpec_soundness (createGraph_spec φ hcg)
    (fun μ η hsub => untilSubformulasDedup_index φ μ η hsub) hacc

end LTLLib
