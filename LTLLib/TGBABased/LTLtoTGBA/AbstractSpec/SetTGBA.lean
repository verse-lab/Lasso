module

/-
  Transition-based generalised Büchi automata (TGBA) whose states are `FinSet Q` for a VWAA state type `Q`. Each transition
  carries a guard, a target and a mark set, and acceptance requires every final to be marked infinitely often.
  Also defines the `T_f` condition (`inTf`) and the product-transition predicate (`prodTrans`) that the soundness (S) and
  completeness (C) conditions are built from, following `[GO01]` Definition 5 and `[HOL4-ltl]`'s `acc_cond` and `d_gen`.

  Defines:
  - `SetTGBA`: guard/target/marks transitions, initial states and finals
  - `SetTGBA.Run`, `SetTGBA.Run.ValidFrom`: an infinite state-and-mark sequence, and its validity on a word
  - `SetTGBA.AcceptingRun`, `SetTGBA.AcceptsFrom`, `SetTGBA.Accepts`: acceptance
  - `SetTGBA.Reachable`, `SetTGBA.IsReachable`: states reachable from the initials
  - `VWAA.inTf`: the `T_f` mark condition, `[HOL4-ltl]`'s `acc_cond`
  - `VWAA.prodTrans`: the product-transition predicate, `[HOL4-ltl]`'s `d_gen`

  References:
  - `[GO01]` Gastin, Oddoux. Fast LTL to Büchi Automata Translation. CAV'01, LNCS 2102, Definition 5.
  - `[HOL4-ltl]` Jantsch, Norrish. Verifying the LTL to Büchi Automata Translation via Very Weak Alternating
    Automata. ITP'18, `waa2baScript` definitions `acc_cond`, `d_gen`, `gba_trans`.

  Sections:
  - The automaton
  - Runs
  - Acceptance
  - Reachability
  - T_f condition
  - Product transitions
-/
public import LTLLib.TGBABased.LTLtoTGBA.AbstractSpec.VWAA
public import LTLLib.Data.FinSet

public section

namespace LTLLib

universe u v

/-! ## The automaton -/

/-- A TGBA whose states are `FinSet Q`, each transition a `(guard, target, marks)` triple with `marks ⊆ finals`. -/
structure SetTGBA (Q : Type v) (α : Type u) where
  -- alternatives from each state: guard, target, marks
  trans : FinSet Q → List (((α → Prop) → Prop) × FinSet Q × FinSet Q)
  -- alternatives for the starting state
  initial : List (FinSet Q)
  -- acceptance conditions indexed by `Q` elements, a transition marks a subset of these
  finals : FinSet Q

/-! ## Runs -/

/-- A run: `state i` is the TGBA state at step `i`, `mark i` is the mark set of the transition taken. -/
structure SetTGBA.Run (Q : Type v) where
  state : Nat → FinSet Q
  mark : Nat → FinSet Q

variable {Q : Type v} {α : Type u}

/-- `r` is a run of `T` on `ξ` starting from `e`: the state at 0 is `e`, and at every step a listed
transition is taken whose guard the current letter satisfies. -/
structure SetTGBA.Run.ValidFrom (r : SetTGBA.Run Q) (T : SetTGBA Q α) (e : FinSet Q)
    (ξ : OmegaWord α) : Prop where
  init : r.state 0 = e
  step : ∀ i, ∃ g, (g, r.state (i + 1), r.mark i) ∈ T.trans (r.state i) ∧ g (ξ i)

/-! ## Acceptance -/

/-- Generalised Büchi acceptance: for each final f, the mark set contains f on infinitely many steps. -/
@[expose] def SetTGBA.AcceptingRun (T : SetTGBA Q α) (r : SetTGBA.Run Q) : Prop :=
  ∀ f ∈ T.finals, ¬ FinitePred fun i => f ∈ r.mark i

/-- `T` accepts `ξ` from state `e`: some valid run from `e` is accepting. -/
@[expose] def SetTGBA.AcceptsFrom (T : SetTGBA Q α) (e : FinSet Q) (ξ : OmegaWord α) : Prop :=
  ∃ r : SetTGBA.Run Q, r.ValidFrom T e ξ ∧ T.AcceptingRun r

/-- The language of `T`: some initial alternative accepts. -/
@[expose] def SetTGBA.Accepts (T : SetTGBA Q α) (ξ : OmegaWord α) : Prop :=
  ∃ e ∈ T.initial, T.AcceptsFrom e ξ

/-! ## Reachability -/

/-- `e'` is reachable from `e₀` in `T` in zero or more steps (ignoring guards and letters). -/
inductive SetTGBA.Reachable (T : SetTGBA Q α) : FinSet Q → FinSet Q → Prop where
  | refl {e} : Reachable T e e
  | step {e₀ e e' : FinSet Q} (hreach : Reachable T e₀ e)
      (htrans : ∃ g m, (g, e', m) ∈ T.trans e) : Reachable T e₀ e'

/-- `e` is reachable in `T` from some initial state. -/
@[expose] def SetTGBA.IsReachable (T : SetTGBA Q α) (e : FinSet Q) : Prop :=
  ∃ e₀ ∈ T.initial, T.Reachable e₀ e

/-! ## T_f condition -/

/-- `[GO01]` Definition 5's `T_f`, `[HOL4-ltl]`'s `acc_cond`: final `f` may be marked at letter `v` and target `e'` when
`f ∉ e'`, or some non-looping transition of `f` enabled at `v` has its target inside `e'`. -/
@[expose] def VWAA.inTf (A : VWAA Q α) (v : α → Prop) (e' : FinSet Q) (f : Q) : Prop :=
  f ∉ e' ∨ ∃ g O, (g, O) ∈ A.trans f ∧ g v ∧ f ∉ O ∧ O ⊆ e'

theorem VWAA.inTf_of_not_mem {A : VWAA Q α} {v : α → Prop} {e' : FinSet Q} {f : Q}
    (hf : f ∉ e') : A.inTf v e' f := Or.inl hf


/-! ## Product transitions -/

/-- Pointwise form of `[HOL4-ltl]`'s `d_gen`: every `q ∈ e` has a component transition enabled at letter `v`, and the
union of their targets lies inside `e'`. -/
@[expose] def VWAA.prodTrans (A : VWAA Q α) (e : FinSet Q) (v : α → Prop) (e' : FinSet Q) : Prop :=
  ∃ (gf : Q → (α → Prop) → Prop) (Of : Q → FinSet Q),
    (∀ q ∈ e, (gf q, Of q) ∈ A.trans q ∧ gf q v) ∧
    e.biUnion Of ⊆ e'

@[simp] theorem VWAA.prodTrans_empty (A : VWAA Q α) (v : α → Prop) (e' : FinSet Q) :
    A.prodTrans ∅ v e' := ⟨fun _ => fun _ => False, fun _ => ∅, by simp, by simp⟩

end LTLLib
