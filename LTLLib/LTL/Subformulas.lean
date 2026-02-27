/-
  Subformula operations for NNF formulas.

  Provides a generic fold (`NNF.fold`) that traverses all subformulas
  in pre-order with an accumulator, plus derived operations:
  `subformulas`, `untilSubformulas`, and their dedup variants.

  The fold is a paramorphism-style traversal (each node sees the original
  formula, not just recursive results). Corresponds loosely to `universe`
  from Uniplate / SYB generic programming.

  `untilSubformulas` corresponds to `until_frmlsr` in the CAVA LTL framework,
  used in LTL_to_GBA.thy for defining acceptance conditions (one per
  Until-subformula).
-/

import Std
import LTLLib.LTL.Syntax

namespace LTLLib

namespace NNF

/-- Generic pre-order fold over all subformulas with a left accumulator.

Visits every node in the formula tree exactly once. At each node,
`f` receives the current accumulator and the subformula at that node.
Children are visited left-to-right after the parent.

Complexity: O(n) where n = number of nodes.

This is the accumulator-based generalization of Uniplate's `universe`:
  `universe φ = φ.fold (fun acc f => f :: acc) [] |>.reverse` -/
def fold (f : β → NNF α → β) (init : β) : NNF α → β
  | φ@(.tt) | φ@(.ff) | φ@(.prop _) | φ@(.nprop _) => f init φ
  | φ@(.next ψ) => ψ.fold f (f init φ)
  | φ@(.and ψ₁ ψ₂) | φ@(.or ψ₁ ψ₂) | φ@(.until ψ₁ ψ₂) | φ@(.release ψ₁ ψ₂) =>
    ψ₂.fold f (ψ₁.fold f (f init φ))

/-- Compute the list of all subformulas (pre-order).
Corresponds to `subfrmlsr` in the CAVA LTL framework. -/
def subformulas (φ : NNF α) : List (NNF α) :=
  φ.fold (fun acc f => f :: acc) []

/-- Extract all Until-subformulas as (left, right) pairs.
Corresponds to `until_frmlsr φ` in the CAVA LTL framework:
  `{(μ, η) | μ U⁼ η ∈ subfrmlsr φ}`.
Used for defining acceptance conditions: one accepting set per Until-subformula. -/
def untilSubformulas (φ : NNF α) : List (NNF α × NNF α) :=
  φ.fold (fun acc f =>
    match f with | .until a b => (a, b) :: acc | _ => acc) []

/-- Deduplicated subformulas. -/
def subformulasDedup [BEq α] [Hashable α] (φ : NNF α) : List (NNF α) :=
  (φ.fold (fun state f =>
    if state.2.contains f then state
    else (f :: state.1, state.2.insert f))
    ([], Std.HashSet.emptyWithCapacity (16 : Nat))).1

/-- Deduplicated Until-subformulas. -/
def untilSubformulasDedup [BEq α] [Hashable α] (φ : NNF α) : List (NNF α × NNF α) :=
  (φ.fold (fun state f =>
    match f with
    | .until a b =>
      let pair := (a, b)
      if state.2.contains pair then state
      else (pair :: state.1, state.2.insert pair)
    | _ => state)
    ([], Std.HashSet.emptyWithCapacity (8 : Nat))).1

end NNF

end LTLLib
