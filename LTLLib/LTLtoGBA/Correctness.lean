/-
  Correctness of the LTL-to-GBA construction.

  Core theorem: accepts ξ iff ξ ⊨ φ.

  Combines Soundess + Completeness.
-/
import LTLLib.LTLtoGBA.Completeness

namespace LTLLib

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
