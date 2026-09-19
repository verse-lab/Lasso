/-
  Disjunctive hoisting. A kept conjunct `ψ ∨ γ` whose `∨`-chain contains a fairness `γ` that `fnf` flattens is not a
  fairness itself, so `rehoist` keeps it whole and the translator builds `γ` along with `ψ`. Since `A ∧ (ψ ∨ γ)` holds
  iff `A ∧ ψ` or `A ∧ γ` does, the emptiness question splits into one per choice of side, keep `ψ` or hoist `γ`, and
  `branches` enumerates these combinations.

  Mixed conjuncts after NNF and `simplify`, from the assumption or the negated specification alike:
  - `p → GF q` as `¬p ∨ GF q`, fairness only from an initial condition
  - `G w → GF c` as `F ¬w ∨ GF c`, justice from time 0 (`FG w → GF c` is a fairness and hoisted whole)
  - `G ¬crash → GF act` as `F crash ∨ GF act`, fair unless the process crashes
  - `G(p ∨ GF q)` as `G p ∨ GF q`, and `X`, `U`, `R` with a fairness in the right operand, by `simplify`'s lifting
  - `(GF a) U b` as `F b ∧ (b ∨ GF a)`, `(GF a) R b` as `b ∧ (G b ∨ GF a)`, by `simplify`'s left-operand rewrites
  - `F ¬p ∨ GF q ∨ FG r`, whose fairness side `GF q ∨ FG r` is one hoisted conjunct with two options, not crossed
  Not touched: fairness under `∧` inside a `∨`, e.g. `¬p ∨ (q ∧ GF r)`, and fairness `fnf` does not flatten, e.g.
  `GF(a ∧ X b)` or `¬p ∨ GF(a ∧ X b)`. Those conjuncts stay kept whole.

  Defines:
  - `mixedSplit`: a conjunct's disjuncts that stay, and the fair normal form of its disjuncts that can be hoisted
  - `branches`: every combination of sides, as the normal forms to hoist and the conjuncts to keep, all-hoisted first

  Proves:
  - `mixedSplit_correct`: a conjunct holds iff one of its staying disjuncts or one of its hoisted fair disjuncts does
  - `branches_correct`: the conjuncts hold iff, for some combination, its hoisted normal forms and kept conjuncts do

  Sections:
  - Mixed conjuncts
  - Combinations
-/
import LTLLib.TGBABased.FairRouter
import LTLLib.TGBABased.LTLtoTGBA.Preprocess.Rules

namespace LTLLib

variable {α : Type u} [DecidableEq α]

/-! ## Mixed conjuncts -/

/-- The disjuncts of `c`'s `∨`-chain that stay, and the fair normal form of those `fnf` flattens, `none` when none do. -/
def mixedSplit (c : NNF α) : Option (List (NNF α) × List (NNF.FairDisjunct α)) :=
  let leaves := (collectOrFairness c).1
  if leaves.any fun l => (hoistConjunct l).isSome then
    some (leaves.filter (fun l => (hoistConjunct l).isNone) ++ (collectOrFairness c).2.toList,
      (leaves.filterMap hoistConjunct).flatten)
  else none

private theorem exists_leaf_iff (leaves : List (NNF α)) (ξ : OmegaWord α) :
    (∃ f ∈ leaves, f.satisfies ξ) ↔
      (∃ f ∈ leaves.filter (fun l => (hoistConjunct l).isNone), f.satisfies ξ) ∨
        ∃ d ∈ (leaves.filterMap hoistConjunct).flatten, NNF.FairDisjunct.holds ξ d := by
  simp only [List.mem_filter, List.mem_flatten, List.mem_filterMap]
  constructor
  · rintro ⟨f, hf, hsat⟩
    cases hh : hoistConjunct f with
    | none => exact Or.inl ⟨f, ⟨hf, by simp [hh]⟩, hsat⟩
    | some ds =>
      obtain ⟨d, hd, hhold⟩ := (hoistConjunct_correct hh ξ).mp hsat
      exact Or.inr ⟨d, ⟨ds, ⟨f, hf, hh⟩, hd⟩, hhold⟩
  · rintro (⟨f, ⟨hf, -⟩, hsat⟩ | ⟨d, ⟨ds, ⟨f, hf, hh⟩, hd⟩, hhold⟩)
    · exact ⟨f, hf, hsat⟩
    · exact ⟨f, hf, (hoistConjunct_correct hh ξ).mpr ⟨d, hd, hhold⟩⟩

theorem mixedSplit_correct {c : NNF α} {stay : List (NNF α)} {ds : List (NNF.FairDisjunct α)}
    (h : mixedSplit c = some (stay, ds)) (ξ : OmegaWord α) :
    c.satisfies ξ ↔ (∃ p ∈ stay, p.satisfies ξ) ∨ ∃ d ∈ ds, NNF.FairDisjunct.holds ξ d := by
  unfold mixedSplit at h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [(collectOrFairness_spec c).2 ξ, exists_leaf_iff]
    simp only [List.mem_append, Option.mem_toList]
    constructor
    · rintro ((h | h) | ⟨r, hr, hsat⟩)
      · exact Or.inl (by obtain ⟨f, hf, hs⟩ := h; exact ⟨f, Or.inl hf, hs⟩)
      · exact Or.inr h
      · exact Or.inl ⟨r, Or.inr hr, hsat⟩
    · rintro (⟨p, hp | hp, hsat⟩ | h)
      · exact Or.inl (Or.inl ⟨p, hp, hsat⟩)
      · exact Or.inr ⟨p, hp, hsat⟩
      · exact Or.inl (Or.inr h)
  · exact absurd h (by simp)

/-! ## Combinations -/

/-- Every combination of sides of the mixed conjuncts of `cs`, as the normal forms to hoist and the conjuncts to keep.
The combination hoisting every fairness side comes first. -/
def branches : List (NNF α) → List (List (List (NNF.FairDisjunct α)) × List (NNF α))
  | [] => [([], [])]
  | c :: cs =>
    match mixedSplit c with
    | none => (branches cs).map fun b => (b.1, c :: b.2)
    | some (stay, ds) =>
      (branches cs).map (fun b => (ds :: b.1, b.2)) ++
        if stay.isEmpty then [] else (branches cs).map fun b => (b.1, orAll stay :: b.2)

theorem branches_correct (ξ : OmegaWord α) (cs : List (NNF α)) :
    (∀ c ∈ cs, c.satisfies ξ) ↔
      ∃ b ∈ branches cs, (∀ ds ∈ b.1, ∃ d ∈ ds, NNF.FairDisjunct.holds ξ d) ∧ ∀ c ∈ b.2, c.satisfies ξ := by
  induction cs with
  | nil => simp [branches]
  | cons c cs ih =>
    rw [List.forall_mem_cons, ih]
    rcases hms : mixedSplit c with _ | ⟨stay, ds⟩
    · simp only [branches, hms, List.mem_map, exists_exists_and_eq_and, List.forall_mem_cons]
      constructor
      · rintro ⟨hc, b, hb, h1, h2⟩
        exact ⟨b, hb, h1, hc, h2⟩
      · rintro ⟨b, hb, h1, hc, h2⟩
        exact ⟨hc, b, hb, h1, h2⟩
    · rw [mixedSplit_correct hms ξ]
      cases stay with
      | nil =>
        simp only [branches, hms, List.isEmpty_nil, if_true, List.append_nil, List.mem_map, exists_exists_and_eq_and,
          List.forall_mem_cons, List.not_mem_nil, false_and, exists_false, false_or]
        constructor
        · rintro ⟨hds, b, hb, h1, h2⟩
          exact ⟨b, hb, ⟨hds, h1⟩, h2⟩
        · rintro ⟨b, hb, ⟨hds, h1⟩, h2⟩
          exact ⟨hds, b, hb, h1, h2⟩
      | cons s0 stay =>
        simp only [branches, hms, List.isEmpty_cons, Bool.false_eq_true, if_false, List.mem_append, or_and_right,
          exists_or, List.mem_map, exists_exists_and_eq_and, List.forall_mem_cons, satisfies_orAll]
        constructor
        · rintro (⟨hp, b, hb, h1, h2⟩ | ⟨hds, b, hb, h1, h2⟩)
          · exact Or.inr ⟨b, hb, h1, hp, h2⟩
          · exact Or.inl ⟨b, hb, ⟨hds, h1⟩, h2⟩
        · rintro (⟨b, hb, ⟨hds, h1⟩, h2⟩ | ⟨b, hb, h1, hp, h2⟩)
          · exact Or.inr ⟨hds, b, hb, h1, h2⟩
          · exact Or.inl ⟨hp, b, hb, h1, h2⟩

end LTLLib
