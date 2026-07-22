/-
  Completeness of the LTL-to-GBA construction.

  Core theorem (L4_10): If ξ satisfies φ and the node graph is complete
  (contains nodes matching all satisfiable types), then the abstract
  automaton accepts ξ.

  The graph completeness hypothesis (`GraphComplete`) states that for any
  ω-word satisfying φ, there exists a run through the nodes where each
  node's `old` set captures exactly the subformulas satisfied at that position.

  Corresponds to Lemma 4.10 in LTL_to_GBA.thy.
-/

import LTLLib.LTLtoGBA.Soundness

namespace LTLLib

open NNF TLA

variable {α : Type u}

/-! ### Graph completeness hypothesis

The key hypothesis for completeness: the node graph produced by `createGraph`
is "complete" — for any ω-word satisfying φ, there exists a run through the
nodes such that each node's `old` set captures exactly the subformulas
satisfied at that position.

This property is stated abstractly and used as a hypothesis. Proving it
from `createGraph` requires showing that the expand algorithm explores all
consistent branches of formula decomposition. -/

/-- Graph completeness: for any ξ ⊨ φ, there exists a run σ through
    the nodes such that old(σ n) = {ψ | IsSubformula ψ φ ∧ ξ.drop(n) ⊨ ψ}. -/
def GraphComplete (φ : NNF α) (nodes : NodeData α → Prop) : Prop :=
  ∀ ξ : OmegaWord α, NNF.satisfies ξ φ →
    ∃ σ : Nat → NodeData α,
      (∀ n, nodes (σ n)) ∧
      (σ 0).incoming expandInit ∧
      (∀ n, (σ (n + 1)).incoming (σ n).name) ∧
      (∀ n ψ, (σ n).old ψ ↔
        (NNF.IsSubformula ψ φ ∧ NNF.satisfies (ξ.drop n) ψ))

/-! ### Helper: satisfies unfolding for until -/

/-- Characterize `NNF.satisfies` for until formulas without TLA unfolding. -/
private theorem satisfies_until_iff (ξ : OmegaWord α) (μ η : NNF α) :
    NNF.satisfies ξ (.until μ η) ↔
    ∃ j, NNF.satisfies (ξ.drop j) η ∧ ∀ i, i < j → NNF.satisfies (ξ.drop i) μ := by
  simp only [NNF.satisfies, NNF.toPred, tla_until]

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

/-- Completeness (L4_10): if ξ satisfies φ and the node graph is complete,
    then the abstract automaton accepts ξ. -/
theorem expandOASpec_completeness
    {φ : NNF α} {nodes : NodeData α → Prop}
    {untils : List (NNF α × NNF α)}
    (h_complete : GraphComplete φ nodes)
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
    · -- The until formula IS in old(σ n) → use semantics to find witness
      have ⟨hsub, hsat_u⟩ := (h_old_iff n _).mp h
      rw [satisfies_until_iff] at hsat_u
      obtain ⟨j, heta_sat, _⟩ := hsat_u
      -- η is a subformula of φ (via transitivity)
      have h_eta_sub : IsSubformula (untils[i]).2 φ :=
        .trans (.until_right .refl) hsub
      -- Convert ξ.drop n |.drop j to ξ.drop (n + j)
      have heta_sat' : NNF.satisfies (ξ.drop (n + j)) (untils[i]).2 := by
        show (untils[i]).2.toPred (ξ.drop (n + j))
        rw [← exec.drop_drop]
        exact heta_sat
      -- By h_old_iff backward: η ∈ old(σ(n + j))
      have h_in_old := (h_old_iff (n + j) (untils[i]).2).mpr ⟨h_eta_sub, heta_sat'⟩
      refine ⟨j, ?_⟩
      simp only [expandOASpec]
      right
      exact h_in_old
    · -- The until formula NOT in old(σ n)
      refine ⟨0, ?_⟩
      simp only [expandOASpec, Nat.add_zero]
      left
      exact h

/-! ### Top-level completeness -/

/-- Top-level completeness combining with `createGraph` and `untilSubformulas`. -/
theorem gba_abstract_completeness
    {S : Type v} [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)]
    {φ : NNF α} {st : ExpandState α S}
    (h_complete : GraphComplete φ st.toNodes)
    {ξ : OmegaWord α}
    (hsat : NNF.satisfies ξ φ)
    : (expandOASpec φ st.toNodes φ.untilSubformulas).accepts ξ :=
  expandOASpec_completeness h_complete hsat

/-! ### Combined correctness -/

/-- Full correctness of the abstract automaton: accepts ξ iff ξ ⊨ φ.
    Requires both `ExpandSpec` (soundness) and `GraphComplete` (completeness). -/
theorem expandOASpec_correct
    {φ : NNF α} {nodes : NodeData α → Prop}
    (spec : ExpandSpec φ nodes)
    {untils : List (NNF α × NNF α)}
    (h_untils : ∀ μ η, NNF.IsSubformula (.until μ η) φ →
      ∃ i : Fin untils.length, untils[i] = (μ, η))
    (h_complete : GraphComplete φ nodes)
    (ξ : OmegaWord α)
    : (expandOASpec φ nodes untils).accepts ξ ↔ NNF.satisfies ξ φ :=
  ⟨expandOASpec_soundness spec h_untils,
   expandOASpec_completeness h_complete⟩

/-- Full correctness via `createGraph`. -/
theorem gba_abstract_correct
    {S : Type v} [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)]
    {φ : NNF α} {st : ExpandState α S}
    (hcg : createGraph φ = some st)
    (h_complete : GraphComplete φ st.toNodes)
    (ξ : OmegaWord α)
    : (expandOASpec φ st.toNodes φ.untilSubformulas).accepts ξ ↔
      NNF.satisfies ξ φ :=
  expandOASpec_correct (createGraph_spec φ hcg)
    (fun μ η hsub => untilSubformulas_index φ μ η hsub)
    h_complete ξ

end LTLLib
