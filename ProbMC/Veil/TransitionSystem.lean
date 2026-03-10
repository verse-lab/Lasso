/-
Adapted from Veil (veil-dev-clean-3/Veil/Core/Tools/ModelChecker/TransitionSystem.lean).
Only the relational transition system core is included; executable/enumerable parts
and Veil-specific imports are removed.
-/

namespace Veil

structure TransitionSystem (ρ : Type) (σ : Type) (l : outParam Type) where

/-- A relational transition system is parametrised by:
  - `ρ` - the type of the background theory (immutable state) it operates in
  - `σ` - the type of the state it operates on
  - `l` - the type of the transition labels (including the names of the
  transitions and the parameters they take)
  - `assumptions` - the set of acceptable background theories
  - `init` - the set of initial states, indexed by background theory they
  operate in
  - `tr` - the transition relation

A relational transition system might or might be executable, depending on
whether `assumptions`, `init`, and `tr` are decidable.
-/
@[grind]
structure RelationalTransitionSystem (ρ : Type) (σ : Type) (l : outParam Type)
    extends TransitionSystem ρ σ l where
  /-- The set of acceptable background theories -/
  assumptions : ρ → Prop
  /-- The set of initial states, indexed by background theory -/
  init : ρ → σ → Prop
  /-- The transition relation -/
  tr : ρ → σ → l → σ → Prop

attribute [grind] RelationalTransitionSystem.assumptions
  RelationalTransitionSystem.init RelationalTransitionSystem.tr

structure LawfulRelationalTransitionSystem (ρ : Type) (σ : Type) (l : outParam Type)
    extends RelationalTransitionSystem ρ σ l where
  /-- The initial states satisfy the assumptions -/
  initSatisfiesAssumptions : ∀ (th : ρ) (s : σ), init th s → assumptions th

namespace RelationalTransitionSystem

/-- A version of the transition relation that "hides" which particular
transition was taken. -/
@[grind]
def next (sys : RelationalTransitionSystem ρ σ l) (th : ρ) (s s' : σ) : Prop :=
  ∃ label, sys.tr th s label s'

/-- Reachability relation, indexed by background theory -/
@[grind cases, grind intro]
inductive reachable (sys : RelationalTransitionSystem ρ σ l) (th : ρ) : σ → Prop where
  | init : ∀ (s : σ), sys.assumptions th → sys.init th s → sys.reachable th s
  | step : ∀ (s s' : σ), sys.reachable th s → sys.next th s s' → sys.reachable th s'

/-- Assumptions hold in all reachable states. -/
@[grind .]
theorem reachable_assumptions (sys : RelationalTransitionSystem ρ σ l) (th : ρ) (s : σ)
    (h : reachable sys th s) : sys.assumptions th := by
  induction h with
  | init s has hinit => assumption
  | step s s' h2 hn ih => assumption

end RelationalTransitionSystem

end Veil
