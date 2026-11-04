module

/-
  Checks `[ltl| φ]`: each connective gives its constructor of `Formula`, `⌜ a ⌝` is the atom `a`,
  a plain term is a formula, and a formula without a counterpart is an error.
-/
import Lasso

open Lasso

example : [ltl| □ ◇ ⌜ "p" ⌝] = (Formula.always (.eventually (.atom "p")) : Formula String) := rfl

example (φ ψ : Formula Nat) :
    [ltl| (¬ φ ∧ ◯ ψ) ∨ (⊤ → ⊥) ∨ (φ ↔ ψ)] = .or (.and (.not φ) (.next ψ)) (.or (.implies .tt .ff) (.iff φ ψ)) :=
  rfl

example (φ ψ : Formula Nat) : [ltl| (φ 𝑈 ψ) ∧ (φ 𝑅 ψ)] = .and (.until φ ψ) (.release φ ψ) := rfl

-- `↝` and `⇒` unfold as in Lentil
example (φ ψ : Formula Nat) : [ltl| φ ↝ ψ] = .always (.implies φ (.eventually ψ)) := rfl
example (φ ψ : Formula Nat) : [ltl| φ ⇒ ψ] = .always (.implies φ ψ) := rfl

/-- error: `[ltl| …]` has no counterpart for this formula -/
#guard_msgs in
example (φ : Formula Nat) : Formula Nat := [ltl| 𝒲ℱ φ]
