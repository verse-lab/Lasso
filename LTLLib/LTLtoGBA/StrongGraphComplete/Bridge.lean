module

/-
  Superseded: `constructGBA_correct_strong` depends on `StrongGraphComplete`, which is never discharged for
  `createGraph`'s actual output. See `LTLtoGBA/Bridge.lean` (`constructGBA_iff_expandOASpec`) and
  `LTLtoGBA/Correctness.lean` (`constructGBA_correct`) for the live unconditional result. Kept for reference, nothing
  outside this folder imports it.

  Defines, for `createGraph φ = some st`:
  - `constructGBA_correct_strong`: `constructGBA` accepts exactly the words satisfying φ, given `StrongGraphComplete`
-/

public import LTLLib.LTLtoGBA.Bridge
public import LTLLib.LTLtoGBA.StrongGraphComplete.Correctness

public section

namespace LTLLib

open NNF

variable {α : Type u} {S : Type v} [FSet (NNF α) S]
  [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]

/-- The computational GBA accepts exactly the words satisfying φ, given graph completeness. -/
theorem constructGBA_correct_strong
    {φ : NNF α} {st : ExpandState α S}
    (hcg : createGraph φ = some st)
    (h_complete : StrongGraphComplete φ st.toNodes)
    (ξ : OmegaWord α) :
    (constructGBA φ st).toSpec.accepts ξ ↔ NNF.satisfies ξ φ := by
  rw [constructGBA_iff_expandOASpec hcg]
  exact gba_abstract_correct_strong hcg h_complete ξ

end LTLLib
