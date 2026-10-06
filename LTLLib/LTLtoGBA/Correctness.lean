module

/-
  Full, unconditional correctness of the LTL-to-GBA construction: `constructGBA` accepts exactly the ω-words satisfying `φ`.

  Defines:
  - `constructGBA_correct`: `constructGBA` accepts exactly the words satisfying `φ`. Unconditional, needs only `createGraph φ = some st`
-/

public import LTLLib.LTLtoGBA.Completeness
public import LTLLib.LTLtoGBA.Soundness

public section

namespace LTLLib

open NNF

variable {α : Type u} {S : Type v} [FSet (NNF α) S] [Hashable (NNF α)]

/-- `constructGBA` accepts exactly the ω-words satisfying `φ`, unconditionally. -/
theorem constructGBA_correct
    [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {φ : NNF α} {st : ExpandState α S}
    (hcg : createGraph φ = some st)
    (ξ : OmegaWord α) :
    (constructGBA φ st).toSpec.accepts ξ ↔ NNF.satisfies ξ φ := by
  rw [constructGBA_iff_expandOASpec hcg]
  exact ⟨expandOASpec_soundness (createGraph_spec φ hcg)
           (fun μ η hsub => untilSubformulasDedup_index φ μ η hsub),
         expandOASpec_completeness (createGraph_spec φ hcg)
           (createGraph_graphComplete φ hcg)⟩

end LTLLib
