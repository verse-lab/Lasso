module

/-
  `Nat` helpers that core Lean does not provide.

  Declared under `LTLLib.Nat`, so inside `namespace LTLLib` the name `Nat.le_induction` resolves here.

  Key theorems:
  - `Nat.le_induction`: induction on `n` starting from `m ≤ n`
-/


public section
namespace LTLLib.Nat

/-- Induction on `n` for `m ≤ n`: prove `P m`, then `P n → P (n + 1)` for every `n ≥ m`. -/
@[elab_as_elim]
theorem le_induction {m : Nat} {P : ∀ n, m ≤ n → Prop} (base : P m (Nat.le_refl m))
    (succ : ∀ n hmn, P n hmn → P (n + 1) (Nat.le_succ_of_le hmn)) : ∀ n hmn, P n hmn := by
  intro n hmn
  induction hmn with
  | refl => exact base
  | step hmn ih => exact succ _ hmn ih

end LTLLib.Nat
