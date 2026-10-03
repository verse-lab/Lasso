module

/-
  Edge-indexed abstract automaton specification, and its relationship to the state-indexed `OASpec`
  (`AbstractSpec/Acceptance.lean`), whose states' marks and labels are pushed onto their outgoing edges.

  Defines:
  - `TOASpec`: proof-level automaton with `k` edge-indexed acceptance marks
  - `OASpec.toTOASpec`: the state-to-edge pushdown, edges being related state pairs

  Proves:
  - `OASpec.toTOASpec_accepts`: the pushdown accepts exactly the same ω-words as the original

  Sections:
  - Edge-indexed automaton specification
  - State-to-edge pushdown
  - Pushdown correctness
-/
public import LTLLib.AbstractSpec.Acceptance

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

/-! ## State-to-edge pushdown -/

/-- Push a state-indexed automaton's acceptance and label onto its outgoing edges. Edges are related state
pairs `(q, q')`, and both label and acceptance are read off the source `q`. -/
@[expose] def OASpec.toTOASpec {State : Type u} {α : Type v} {k : Nat} (A : OASpec State α k) :
    TOASpec State (State × State) α k where
  src e := e.1
  dst e := e.2
  valid e := A.trans e.1 e.2
  initial := A.initial
  labelCompat e v := A.labelCompat e.1 v
  acceptMark i e := A.acceptSet i e.1

/-! ## Pushdown correctness -/

/-- The pushdown accepts exactly the same ω-words as the original automaton. -/
theorem OASpec.toTOASpec_accepts {State : Type u} {α : Type v} {k : Nat} (A : OASpec State α k)
    (ξ : OmegaWord α) : A.toTOASpec.accepts ξ ↔ A.accepts ξ := by
  constructor
  · rintro ⟨σ, hrun, hcompat, hacc⟩
    refine ⟨fun n => (σ n).1, ⟨hrun.1, fun n => ?_⟩, hcompat, hacc⟩
    show A.trans (σ n).1 (σ (n + 1)).1
    have hvalid : A.trans (σ n).1 (σ n).2 := (hrun.2 n).1
    have heq : (σ n).2 = (σ (n + 1)).1 := (hrun.2 n).2
    exact heq ▸ hvalid
  · rintro ⟨σ, hrun, hcompat, hacc⟩
    exact ⟨fun n => (σ n, σ (n + 1)), ⟨hrun.1, fun n => ⟨hrun.2 n, rfl⟩⟩, hcompat, hacc⟩

end LTLLib
