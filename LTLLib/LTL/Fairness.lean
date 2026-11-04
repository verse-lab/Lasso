module

/-
  Fairness combinators for LTL formulas: unconditional, weak (justice), and strong (compassion) fairness, plus
  helpers for combining and assuming multiple fairness constraints.

  These expand into standard LTL formulas and require no special handling in the TGBA construction.
  Fairness-encoded formulas can however produce larger automata.

  `BoolFormula.weakFairMark` is the alternative for a propositional weak fairness assumption, which
  `modelCheckTGBAFair` carries as a generalized Büchi mark instead of translating.

  Sections:
  - Formula combinators
  - Weak fairness as a mark
-/

public import LTLLib.LTL.Propositional
public import LTLLib.LTL.Syntax

public section

namespace LTLLib

/-! ## Formula combinators -/

namespace Formula

/-- Unconditional fairness: □◇taken. `taken` happens infinitely often, unconditionally.
Equivalent to `weakFairness ⊤ taken`. -/
@[expose] def unconditionalFairness (taken : Formula α) : Formula α :=
  .always (.eventually taken)

/-- Weak fairness (justice): □(◇¬enabled ∨ ◇taken).
If `enabled` is continuously true, then `taken` must eventually become true.
Equivalently `□(◇¬enabled ∨ ◇taken)`, or `◇□enabled → □◇taken`.
  (The `□◇` form used as it holds only on Until-subformula and fairness is usually an assumption,
  so it is positive in the negated formula). -/
@[expose] def weakFairness (enabled taken : Formula α) : Formula α :=
  .always (.eventually (.or enabled.not taken))

/-- Strong fairness (compassion): □◇enabled → □◇taken.
If `enabled` is true infinitely often, then `taken` must be true infinitely often. -/
@[expose] def strongFairness (enabled taken : Formula α) : Formula α :=
  .implies (.always (.eventually enabled)) (.always (.eventually taken))

/-- Conjunction of multiple fairness constraints. -/
def fairnessConjunction (constraints : List (Formula α)) : Formula α :=
  match constraints with
  | [] => .tt
  | c :: cs => cs.foldl .and c

/-- Conjunction of weak fairness assumptions for every (enabled, taken) pair. -/
def allWeakFair (pairs : List (Formula α × Formula α)) : Formula α :=
  fairnessConjunction (pairs.map fun (e, t) => weakFairness e t)

/-- Conjunction of strong fairness assumptions for every (enabled, taken) pair. -/
def allStrongFair (pairs : List (Formula α × Formula α)) : Formula α :=
  fairnessConjunction (pairs.map fun (e, t) => strongFairness e t)

/-- `fairness₁ ∧ fairness₂ ∧ ... → property`: `property` need only hold under the given fairness assumptions. -/
def underFairness (fairnessAssumptions : List (Formula α)) (property : Formula α)
    : Formula α :=
  .implies (fairnessConjunction fairnessAssumptions) property

end Formula

/-! ## Weak fairness as a mark -/

namespace BoolFormula

/-- Weak fairness `◇□E → □◇T` for propositional `E` and `T`, as the single conjunct `¬E ∨ T` whose `□◇` form
is the assumption. [SLDP09] Definition 1 for the notion, generalised from actions to predicates, with the
collapse `◇□E → □◇T ≡ GF ¬E ∨ GF T ≡ GF(¬E ∨ T)` read off [LSFZ16] Theorem 1's distribution of `GF` over `∨`. -/
@[expose] def weakFairMark {α} (enabled taken : BoolFormula α) : BoolFormula α := .or enabled.neg taken

/-- `□◇(¬E ∨ T)` is exactly weak fairness, which is why one generalized Büchi mark suffices for it. -/
theorem satisfies_weakFairMark {α} (ξ : OmegaWord α) (e t : BoolFormula α) :
    (alwaysEventually (weakFairMark e t)).satisfies ξ ↔
      ((eventuallyAlways e).satisfies ξ → (alwaysEventually t).satisfies ξ) := by
  rw [satisfies_alwaysEventually, satisfies_eventuallyAlways, satisfies_alwaysEventually]
  simp only [weakFairMark, holds, holds_neg]
  constructor
  · rintro h ⟨N, hN⟩ n
    obtain ⟨j, hj⟩ := h (n + N)
    rcases hj with hne | ht
    · exact absurd (by rw [show n + N + j = N + (n + j) by omega]; exact hN (n + j)) hne
    · exact ⟨N + j, by rw [show n + (N + j) = n + N + j by omega]; exact ht⟩
  · intro h n
    by_cases hen : ∃ N, ∀ k, holds (ξ (N + k)) e
    · obtain ⟨j, hj⟩ := h hen n
      exact ⟨j, Or.inr hj⟩
    · have hex : ∃ k, ¬ holds (ξ (n + k)) e :=
        Classical.byContradiction fun hc =>
          hen ⟨n, fun k => Classical.byContradiction fun hk => hc ⟨k, hk⟩⟩
      obtain ⟨k, hk⟩ := hex
      exact ⟨k, Or.inl hk⟩

end BoolFormula

end LTLLib
