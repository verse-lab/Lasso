module

/-
  Spec-level (computation-independent) description of a valid LTL-to-GBA expansion result, and the abstract automaton it induces.

  Defines:
  - `NodeData`: spec-level representation of a finished expansion node
  - `ExpandSpec`: the invariants a valid expansion result must satisfy
  - `expandOASpec`: the `OASpec` automaton induced by `ExpandSpec` nodes

  ## Sections
  - Expansion specification
  - Abstract automaton from ExpandSpec
-/

public import LTLLib.LTL.Subformulas
public import LTLLib.AbstractSpec.Acceptance

public section

namespace LTLLib

open NNF

variable {α : Type u}

/-! ## Expansion specification

`ExpandSpec φ nodes` describes the invariants that the output of `expand` (applied to the initial node for formula φ) must
satisfy, stated abstractly over spec-level node data. -/

/-- The special "init" node name, used as the incoming marker for initial states. -/
@[expose] def expandInit : Nat := 0

/-- Spec-level representation of a finished node. -/
structure NodeData (α : Type u) where
  name : Nat
  incoming : Nat → Prop  -- predicate on node names marking incoming edges
  old : NNF α → Prop     -- formulas already satisfied at this node
  next : NNF α → Prop    -- formulas deferred to the successor node

/-- The abstract specification of a valid expansion result for formula φ.
`nodes` is a predicate selecting the finished nodes. -/
structure ExpandSpec {α : Type u} (φ : NNF α) (nodes : NodeData α → Prop) : Prop where
  literal_consistent :
    ∀ q, nodes q → ∀ a, q.old (.prop a) → ¬ q.old (.nprop a)

  no_false :
    ∀ q, nodes q → ¬ q.old .ff

  and_propag :
    ∀ q, nodes q → ∀ μ ψ, q.old (.and μ ψ) → q.old μ ∧ q.old ψ

  or_propag :
    ∀ q, nodes q → ∀ μ ψ, q.old (.or μ ψ) → q.old μ ∨ q.old ψ

  next_propag :
    ∀ q, nodes q → ∀ ψ, q.old (.next ψ) → q.next ψ

  -- Either ψ holds now, or μ holds and the until obligation carries forward via next.
  until_propag :
    ∀ q, nodes q → ∀ μ ψ, q.old (.until μ ψ) →
      q.old ψ ∨ (q.old μ ∧ q.next (.until μ ψ))

  -- ψ must hold now, as μ holding releases the obligation, otherwise it carries forward via next.
  release_propag :
    ∀ q, nodes q → ∀ μ ψ, q.old (.release μ ψ) →
      q.old ψ ∧ (q.old μ ∨ q.next (.release μ ψ))

  old_subformula :
    ∀ q, nodes q → ∀ ψ, q.old ψ → NNF.IsSubformula ψ φ

  next_subformula :
    ∀ q, nodes q → ∀ ψ, q.next ψ → NNF.IsSubformula ψ φ

  -- q' is a successor of q when q.name ∈ q'.incoming.
  successor_old :
    ∀ q, nodes q → ∀ q', nodes q' → q'.incoming q.name →
      ∀ ψ, q.next ψ → q'.old ψ

  -- Nodes reachable from the expandInit marker must contain φ.
  initial_old :
    ∀ q, nodes q → q.incoming expandInit → q.old φ

/-! ## Abstract automaton from ExpandSpec

The automaton specification is defined abstractly from `NodeData` predicates, independent of `constructGBA`'s own
representation. The acceptance condition indexes over until-subformulas of φ via `IsSubformula`. -/

/-- Abstract automaton induced by ExpandSpec nodes: transitions via `incoming`, label compatibility from `old`'s
atoms, and acceptance sets indexed by until-subformulas of φ (accepting for `μ U η` iff absent from `old` or `old η`
already holds). -/
@[expose] def expandOASpec (_φ : NNF α) (nodes : NodeData α → Prop)
    (untils : List (NNF α × NNF α)) :
    OASpec (NodeData α) α untils.length where
  trans q q' := nodes q ∧ nodes q' ∧ q'.incoming q.name
  initial q := nodes q ∧ q.incoming 0  -- 0 = expandInit
  labelCompat q v :=
    (∀ a, q.old (.prop a) → v a) ∧ (∀ a, q.old (.nprop a) → ¬v a)
  acceptSet i q :=
    let (μ, η) := untils[i]
    ¬q.old (.until μ η) ∨ q.old η

end LTLLib
