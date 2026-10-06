module

/-
  Superseded: depends on `StrongGraphComplete`, which is never discharged for `createGraph`'s actual output. See
  `LTLtoGBA/Correctness.lean` for the live unconditional result. Kept for reference and checked by
  `LTLLibTests.HistoricalTheorems`; not re-exported by the public library root.

  Correctness of the LTL-to-GBA construction: the `expandOASpec` abstract automaton accepts ξ iff ξ ⊨ φ, given both
  soundness and completeness of the node graph.

  Defines:
  - `expandOASpec_correct_strong`: abstract correctness, given `ExpandSpec` + `StrongGraphComplete`
  - `gba_abstract_correct_strong`: `expandOASpec_correct_strong` corollary via `createGraph`
-/
public import LTLLib.LTLtoGBA.StrongGraphComplete.Completeness
public import LTLLib.LTL.Subformulas

public section

namespace LTLLib

/-- Full correctness of the abstract automaton: accepts ξ iff ξ ⊨ φ, given soundness and graph completeness. -/
theorem expandOASpec_correct_strong
    {φ : NNF α} {nodes : NodeData α → Prop}
    (spec : ExpandSpec φ nodes)
    {untils : List (NNF α × NNF α)}
    (h_untils : ∀ μ η, NNF.IsSubformula (.until μ η) φ →
      ∃ i : Fin untils.length, untils[i] = (μ, η))
    (h_complete : StrongGraphComplete φ nodes)
    (ξ : OmegaWord α)
    : (expandOASpec φ nodes untils).accepts ξ ↔ NNF.satisfies ξ φ :=
  ⟨expandOASpec_soundness spec h_untils,
   expandOASpec_completeness_strong h_complete⟩

/-- Full correctness via `createGraph`, given graph completeness. -/
theorem gba_abstract_correct_strong
    [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {S : Type v} [FSet (NNF α) S] [BEq (NNF α)] [LawfulBEq (NNF α)]
    {φ : NNF α} {st : ExpandState α S}
    (hcg : createGraph φ = some st)
    (h_complete : StrongGraphComplete φ st.toNodes)
    (ξ : OmegaWord α)
    : (expandOASpec φ st.toNodes φ.untilSubformulasDedup).accepts ξ ↔
      NNF.satisfies ξ φ :=
  expandOASpec_correct_strong (createGraph_spec φ hcg)
    (fun μ η hsub => NNF.untilSubformulasDedup_index φ μ η hsub)
    h_complete ξ

end LTLLib
