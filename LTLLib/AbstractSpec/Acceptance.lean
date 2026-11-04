module

/-
  Edge-indexed abstract automaton specification, the proof-level counterpart of a `TGBA`, with each
  acceptance mark carried by an edge rather than by a state.

  Defines:
  - `TOASpec`: proof-level automaton with `k` edge-indexed acceptance marks

  Sections:
  - Edge-indexed automaton specification
-/
public import Lentil
public import LTLLib.LTL.Semantics

public section

namespace LTLLib

open Lentil

/-! ## Edge-indexed automaton specification -/

/-- Abstract specification of an ω-automaton whose `k` acceptance marks are carried by edges. -/
structure TOASpec (State : Type u) (Edge : Type u') (α : Type v) (k : Nat) where
  src : Edge → State
  dst : Edge → State
  valid : Edge → Prop -- This edge belongs to the automaton.
  initial : State → Prop
  labelCompat : Edge → (α → Prop) → Prop
  acceptMark : Fin k → Edge → Prop

namespace TOASpec

variable {State : Type u} {Edge : Type u'} {α : Type v} {k : Nat} (A : TOASpec State Edge α k)

/-- An infinite edge-run: starts at an initial state, every edge is valid, and consecutive edges share a state. -/
@[expose] def isRun (σ : exec Edge) : Prop :=
  A.initial (A.src (σ 0)) ∧ ∀ n, A.valid (σ n) ∧ A.dst (σ n) = A.src (σ (n + 1))

/-- A run is compatible with an ω-word if each edge is label-compatible with the corresponding position. -/
@[expose] def runCompatible (σ : exec Edge) (ξ : OmegaWord α) : Prop :=
  ∀ n, A.labelCompat (σ n) (ξ n)

/-- A run is accepting if every mark is carried by some edge infinitely often. -/
@[expose] def isAcceptingRun (σ : exec Edge) : Prop :=
  ∀ i : Fin k, ∀ n, ∃ j, A.acceptMark i (σ (n + j))

/-- The automaton accepts an ω-word if there exists a run that is valid, compatible, and accepting. -/
@[expose] def accepts (ξ : OmegaWord α) : Prop :=
  ∃ σ : exec Edge, A.isRun σ ∧ A.runCompatible σ ξ ∧ A.isAcceptingRun σ

end TOASpec

end LTLLib
