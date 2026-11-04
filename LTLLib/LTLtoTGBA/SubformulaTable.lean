module

/-
  Every subformula of a formula, indexed by a `Nat` id (`[HOL4-ltl]`'s `unique_node_formula` dedup, done once). Every
  VWAA and TGBA state built from it is a set of ids, canonically hashable and comparable, unlike a set of `NNF` trees.

  Defines:
  - `SubformulaTable`: the id assignment, `build`, `idOf`, `formulaOf`

  Proves:
  - `idOf_formulaOf`, `formulaOf_idOf`: `idOf` and `formulaOf` are mutual inverses on the range `build` produces
  - `formulaOf_isSubformula`, `idOf_lt_size`: every id in that range names a subformula, and every subformula has one

  References:
  - `[HOL4-ltl]` Jantsch, Norrish. Verifying the LTL to Büchi Automata Translation via Very Weak Alternating
    Automata. ITP'18, and its HOL4 formalisation `examples/logic/ltl`.

  Sections:
  - The table
  - Invariants
-/
public import LTLLib.LTL.Subformulas

public section

namespace LTLLib

variable {α : Type u} [BEq α] [Hashable α]

/-! ## The table -/

/-- `formulas[i]` is the formula with id `i`, `index` its inverse. -/
structure SubformulaTable (α : Type u) [BEq α] [Hashable α] where
  formulas : Array (NNF α)
  index : Std.HashMap (NNF α) Nat

namespace SubformulaTable

/-- Every subformula of `φ`, ids assigned in `subformulasDedup`'s root-first order. -/
@[expose] def build (φ : NNF α) : SubformulaTable α :=
  let formulas := φ.subformulasDedup.toArray
  let index := (formulas.foldl (init := (Std.HashMap.emptyWithCapacity formulas.size, 0))
    fun (m, i) f => (m.insert f i, i + 1)).1
  { formulas, index }

/-- The id of `φ`, `0` if `φ` is not in the table. -/
@[expose] def idOf (t : SubformulaTable α) (φ : NNF α) : Nat := t.index.getD φ 0

/-- The formula with id `i`, `default` if `i` is out of range. -/
@[expose] def formulaOf (t : SubformulaTable α) (i : Nat) : NNF α := t.formulas.getD i default

/-! ## Invariants

`[HOL4-ltl]`'s `unique_node_formula` and reachable-subformula invariants. -/

private theorem size_eq (φ : NNF α) : (build φ).formulas.size = φ.subformulasDedup.length := by
  simp [build]

/-- The formula at a valid id is exactly `subformulasDedup`'s entry there. -/
theorem formulaOf_getElem? (φ : NNF α) (i : Nat) (hi : i < (build φ).formulas.size) :
    φ.subformulasDedup[i]? = some ((build φ).formulaOf i) := by
  have hi' : i < φ.subformulasDedup.length := by rwa [size_eq] at hi
  simp [formulaOf, build, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_eq_getElem hi']

private theorem formulaOf_of_getElem? (φ : NNF α) (j : Nat) (ψ : NNF α)
    (hget : φ.subformulasDedup[j]? = some ψ) :
    (build φ).formulaOf j = ψ := by
  simp [formulaOf, build, Array.getD_eq_getD_getElem?, List.getElem?_toArray, hget]

/-- Every formula the table assigns an id to is a subformula of `φ`. -/
theorem formulaOf_isSubformula (φ : NNF α) (i : Nat) (hi : i < (build φ).formulas.size) :
    NNF.IsSubformula ((build φ).formulaOf i) φ :=
  NNF.subformulasDedup_sound φ _ (List.mem_of_getElem? (formulaOf_getElem? φ i hi))

section Invariants

variable [LawfulBEq α] [LawfulHashable α]

private theorem buildIndex_notMem {β} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β]
    (l : List β) (f : β) (hf : f ∉ l) (m0 : Std.HashMap β Nat) (base : Nat) :
    (l.foldl (init := (m0, base)) fun (m, i) g => (m.insert g i, i + 1)).1.getD f 0
      = m0.getD f 0 := by
  induction l generalizing m0 base with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih (fun h => hf (List.mem_cons_of_mem _ h)), Std.HashMap.getD_insert]
    have hne : ¬ (hd == f) := by
      simp only [beq_iff_eq]
      exact fun h => hf (h ▸ List.mem_cons_self ..)
    simp [hne]

/-- Folding an increasing index assignment over a duplicate-free list maps the entry at position `j` to `base + j`. -/
theorem buildIndex_get {β} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β] :
    ∀ (l : List β), l.Nodup →
    ∀ (m0 : Std.HashMap β Nat) (base j : Nat) (f : β), l[j]? = some f →
      (l.foldl (init := (m0, base)) fun (m, i) g => (m.insert g i, i + 1)).1.getD f 0
        = base + j
  | [], _, _, _, _, _, hget => by simp at hget
  | hd :: tl, hnodup, m0, base, j, f, hget => by
    match j, hget with
    | 0, hget =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      have hnotmem : hd ∉ tl := (List.nodup_cons.mp hnodup).1
      simp only [List.foldl_cons]
      rw [buildIndex_notMem tl hd hnotmem (m0.insert hd base) (base + 1)]
      simp
    | j + 1, hget =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [List.foldl_cons]
      exact (buildIndex_get tl (List.nodup_cons.mp hnodup).2
        (m0.insert hd base) (base + 1) j f hget).trans (by omega)

/-- The table's `idOf` agrees with the position `subformulasDedup` assigns, `[HOL4-ltl]`'s
`unique_node_formula`. -/
private theorem idOf_eq_of_getElem? (φ : NNF α) (f : NNF α) (j : Nat)
    (hget : φ.subformulasDedup[j]? = some f) :
    (build φ).idOf f = j := by
  have h : (φ.subformulasDedup.toArray.foldl
      (init := (Std.HashMap.emptyWithCapacity φ.subformulasDedup.toArray.size, 0))
      fun (m, i) g => (m.insert g i, i + 1)).1.getD f 0 = 0 + j := by
    rw [← Array.foldl_toList]
    exact buildIndex_get φ.subformulasDedup (NNF.subformulasDedup_nodup φ)
      (Std.HashMap.emptyWithCapacity φ.subformulasDedup.toArray.size) 0 j f hget
  simpa [build, idOf] using h

/-- The formula at a valid id `i` maps back to `i`. -/
theorem idOf_formulaOf (φ : NNF α) (i : Nat) (hi : i < (build φ).formulas.size) :
    (build φ).idOf ((build φ).formulaOf i) = i :=
  idOf_eq_of_getElem? φ _ i (formulaOf_getElem? φ i hi)

/-- Every subformula of `φ` gets an id inside the table's range. -/
theorem idOf_lt_size (φ : NNF α) (ψ : NNF α) (hsub : NNF.IsSubformula ψ φ) :
    (build φ).idOf ψ < (build φ).formulas.size := by
  obtain ⟨j, hget⟩ := List.mem_iff_getElem?.mp (NNF.subformulasDedup_complete φ ψ hsub)
  rw [idOf_eq_of_getElem? φ ψ j hget, size_eq]
  exact (List.getElem?_eq_some_iff.mp hget).1

/-- The id of a subformula of `φ` maps back to it. -/
theorem formulaOf_idOf (φ : NNF α) (ψ : NNF α) (hsub : NNF.IsSubformula ψ φ) :
    (build φ).formulaOf ((build φ).idOf ψ) = ψ := by
  obtain ⟨j, hget⟩ := List.mem_iff_getElem?.mp (NNF.subformulasDedup_complete φ ψ hsub)
  rw [idOf_eq_of_getElem? φ ψ j hget]
  exact formulaOf_of_getElem? φ j ψ hget

end Invariants

end SubformulaTable

end LTLLib
