module

import LTLLib.LTLtoGBA.StrongGraphComplete.Bridge
import LTLLibTests.GuardAxioms

/-
  These superseded results still require their explicit StrongGraphComplete hypotheses.
  This checks proof dependencies, not whether createGraph satisfies those hypotheses.
-/
open LTLLib

#guard_axioms
  expandOASpec_completeness_strong, gba_abstract_completeness_strong,
  expandOASpec_correct_strong, gba_abstract_correct_strong, constructGBA_correct_strong
  ⊆ [propext, Classical.choice, Quot.sound]
