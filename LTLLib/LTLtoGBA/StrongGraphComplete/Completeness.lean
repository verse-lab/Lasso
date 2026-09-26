/-
  Superseded: `StrongGraphComplete` is never discharged for `createGraph`'s actual output (see `LTLtoGBA/Completeness.lean`
  for the property `createGraph` really establishes and the live proof chain). Kept for reference, nothing outside this
  folder imports it.

  Completeness of the LTL-to-GBA construction: if ξ ⊨ φ and the node graph is complete, then the abstract automaton
  accepts ξ.

  Defines:
  - `StrongGraphComplete`: hypothesis that the node graph contains a run matching every ξ ⊨ φ
  - `expandOASpec_completeness_strong`: `StrongGraphComplete` + ξ ⊨ φ → `expandOASpec` accepts ξ
  - `gba_abstract_completeness_strong`: `expandOASpec_completeness_strong` corollary via `createGraph`

  ### Sections
  - Graph completeness hypothesis
  - Helper: satisfies unfolding for until
  - Core completeness theorem
  - Top-level completeness
-/

import LTLLib.LTLtoGBA.Soundness
import LTLLib.LTL.Semantics
import LTLLib.LTLtoGBA.Invariants
import LTLLib.LTLtoGBA.ToGBA
import LTLLib.AbstractSpec.Acceptance

namespace LTLLib

open NNF Lentil

variable {α : Type u}

/-! ### Graph completeness hypothesis

`StrongGraphComplete` is assumed, not proved, here: establishing it for `createGraph`'s output requires showing the
expand algorithm explores all consistent branches of formula decomposition. -/

/-- Graph completeness: every ξ ⊨ φ has a matching run through the node graph. -/
def StrongGraphComplete (φ : NNF α) (nodes : NodeData α → Prop) : Prop :=
  ∀ ξ : OmegaWord α, NNF.satisfies ξ φ →
    ∃ σ : Nat → NodeData α,
      (∀ n, nodes (σ n)) ∧ -- σ stays within the node graph
      (σ 0).incoming expandInit ∧ -- σ starts at the initial node
      (∀ n, (σ (n + 1)).incoming (σ n).name) ∧ -- σ follows graph transitions
      (∀ n ψ, (σ n).old ψ ↔ -- old(σ n) is exactly the subformulas ξ.drop n satisfies
        (NNF.IsSubformula ψ φ ∧ NNF.satisfies (ξ.drop n) ψ))

/-! ### Helper: satisfies unfolding for until -/

/-- Characterize `NNF.satisfies` for until formulas without TLA unfolding. -/
private theorem satisfies_until_iff (ξ : OmegaWord α) (μ η : NNF α) :
    NNF.satisfies ξ (.until μ η) ↔
    ∃ j, NNF.satisfies (ξ.drop j) η ∧ ∀ i, i < j → NNF.satisfies (ξ.drop i) μ := by
  exact NNF.satisfies_until ξ μ η

/-- Characterize `NNF.satisfies` for prop. -/
private theorem satisfies_prop_iff (ξ : OmegaWord α) (a : α) :
    NNF.satisfies ξ (.prop a) ↔ (ξ 0) a := by
  dsimp [NNF.satisfies, NNF.toPred]
  tunfold_simp

/-- Characterize `NNF.satisfies` for nprop. -/
private theorem satisfies_nprop_iff (ξ : OmegaWord α) (a : α) :
    NNF.satisfies ξ (.nprop a) ↔ ¬(ξ 0) a := by
  dsimp [NNF.satisfies, NNF.toPred]
  tunfold_simp

/-! ### Core completeness theorem -/

/-- Completeness: if ξ satisfies φ and the node graph is complete, then the abstract automaton accepts ξ. -/
theorem expandOASpec_completeness_strong
    {φ : NNF α} {nodes : NodeData α → Prop}
    {untils : List (NNF α × NNF α)}
    (h_complete : StrongGraphComplete φ nodes)
    {ξ : OmegaWord α}
    (hsat : NNF.satisfies ξ φ)
    : (expandOASpec φ nodes untils).accepts ξ := by
  obtain ⟨σ, h_nodes, h_init, h_succ, h_old_iff⟩ := h_complete ξ hsat
  refine ⟨σ, ?_, ?_, ?_⟩
  · -- isRun: initial state and transitions
    exact ⟨⟨h_nodes 0, h_init⟩, fun n => ⟨h_nodes n, h_nodes (n + 1), h_succ n⟩⟩
  · -- runCompatible: label compatibility at each position
    intro n
    constructor
    · -- positive atoms: prop a ∈ old(σ n) → ξ(n)(a)
      intro a hold
      have ⟨_, hsat'⟩ := (h_old_iff n (.prop a)).mp hold
      rw [satisfies_prop_iff] at hsat'
      simp [exec.drop] at hsat'
      exact hsat'
    · -- negative atoms: nprop a ∈ old(σ n) → ¬ξ(n)(a)
      intro a hold
      have ⟨_, hsat'⟩ := (h_old_iff n (.nprop a)).mp hold
      rw [satisfies_nprop_iff] at hsat'
      simp [exec.drop] at hsat'
      exact hsat'
  · -- isAcceptingRun: each acceptance set is visited infinitely often
    intro i n
    classical
    by_cases h : (σ n).old (.until (untils[i]).1 (untils[i]).2)
    · -- extract the until's satisfaction witness j and locate it in old(σ(n + j))
      have ⟨hsub, hsat_u⟩ := (h_old_iff n _).mp h
      rw [satisfies_until_iff] at hsat_u
      obtain ⟨j, heta_sat, _⟩ := hsat_u
      have h_eta_sub : IsSubformula (untils[i]).2 φ :=
        .trans (.until_right .refl) hsub
      -- (ξ.drop n).drop j = ξ.drop (n + j)
      have heta_sat' : NNF.satisfies (ξ.drop (n + j)) (untils[i]).2 := by
        rw [← exec.drop_drop]
        exact heta_sat
      have h_in_old := (h_old_iff (n + j) (untils[i]).2).mpr ⟨h_eta_sub, heta_sat'⟩
      refine ⟨j, ?_⟩
      simp only [expandOASpec]
      right
      exact h_in_old
    · -- j = 0 trivially satisfies acceptance when the until isn't in old(σ n)
      refine ⟨0, ?_⟩
      simp only [expandOASpec, Nat.add_zero]
      left
      exact h

/-! ### Top-level completeness -/

/-- Top-level completeness, instantiated with `createGraph`'s node set and `untilSubformulas`. -/
theorem gba_abstract_completeness_strong
    {S : Type v} [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)]
    {φ : NNF α} {st : ExpandState α S}
    (h_complete : StrongGraphComplete φ st.toNodes)
    {ξ : OmegaWord α}
    (hsat : NNF.satisfies ξ φ)
    : (expandOASpec φ st.toNodes φ.untilSubformulasDedup).accepts ξ :=
  expandOASpec_completeness_strong h_complete hsat

end LTLLib
