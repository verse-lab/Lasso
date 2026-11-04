module

/-
  Building blocks for the paper rewrite rules. `collectAndFairness`/`collectOrFairness` walk a whole `∧`/`∨`-chain in
  one call, collecting every alternating (`[BKŘS12]` ξ-grammar, `NNF.isFairness`) leaf and what is left over, so the
  rewrite pass reaches the rules' normal form in a single bottom-up pass. The `U`/`R` merge rules of `[SB00]` §3 and
  the nested `U`/`R` merges under an implication of `[BKŘS12]` §4 are not implemented.

  Defines:
  - `andAll`, `orAll`: the conjunction/disjunction of a list, `⊤`/`⊥` on the empty list
  - `collectAndFairness`, `collectOrFairness`: every alternating leaf of a `∧`/`∨`-chain, and the remainder

  Proves:
  - `satisfies_andAll`, `satisfies_orAll`: a folded list's language
  - `satisfies_drop_of_isFairness`: an alternating formula is prefix invariant, `[BKŘS12]` Lemma 2
  - `collectAndFairness_spec`, `collectOrFairness_spec`: the leaves are alternating, and together with the remainder
    they denote the chain

  References:
  - `[SB00]` Somenzi, Bloem. Efficient Büchi Automata from LTL Formulae. CAV'00, §3.
  - `[EH00]` Etessami, Holzmann. Optimizing Büchi Automata. CONCUR'00, Lemma 3.
  - `[BKŘS12]` Babiak, Křetínský, Řehák, Strejček. LTL to Büchi Automata Translation: Fast and More
    Deterministic. TACAS'12, §4.

  Sections:
  - Folding a list of formulas
  - Collecting alternating leaves of a chain
  - Semantics
-/
public import LTLLib.LTLtoTGBA.Preprocess.Implication

public section

namespace LTLLib

variable {α : Type u}

/-! ## Folding a list of formulas -/

/-- The conjunction of `fs`, `⊤` on the empty list, `x` itself rather than `x ∧ ⊤` on a singleton. -/
@[expose] def andAll : List (NNF α) → NNF α
  | [] => .tt
  | [x] => x
  | x :: rest => .and x (andAll rest)

/-- The disjunction of `fs`, `⊥` on the empty list, `x` itself rather than `x ∨ ⊥` on a singleton. -/
@[expose] def orAll : List (NNF α) → NNF α
  | [] => .ff
  | [x] => x
  | x :: rest => .or x (orAll rest)

/-! ## Collecting alternating leaves of a chain -/

/-- Every alternating leaf reachable through a chain of `∧`, and what is left over once they are removed. -/
@[expose] def collectAndFairness : NNF α → List (NNF α) × Option (NNF α)
  | .and a b =>
    let (fa, ra) := collectAndFairness a
    let (fb, rb) := collectAndFairness b
    (fa ++ fb, match ra, rb with
      | some x, some y => some (.and x y)
      | some x, none => some x
      | none, some y => some y
      | none, none => none)
  | φ => if φ.isFairness then ([φ], none) else ([], some φ)

/-- Every alternating leaf reachable through a chain of `∨`, and what is left over once they are removed. -/
@[expose] def collectOrFairness : NNF α → List (NNF α) × Option (NNF α)
  | .or a b =>
    let (fa, ra) := collectOrFairness a
    let (fb, rb) := collectOrFairness b
    (fa ++ fb, match ra, rb with
      | some x, some y => some (.or x y)
      | some x, none => some x
      | none, some y => some y
      | none, none => none)
  | φ => if φ.isFairness then ([φ], none) else ([], some φ)

/-! ## Semantics -/

/-- `andAll` holds exactly when every conjunct does. -/
theorem satisfies_andAll (fs : List (NNF α)) (ξ : OmegaWord α) :
    (andAll fs).satisfies ξ ↔ ∀ f ∈ fs, f.satisfies ξ := by
  induction fs with
  | nil => simp [andAll, NNF.satisfies_tt]
  | cons x rest ih =>
    cases rest with
    | nil => simp [andAll]
    | cons y rest' =>
      simp only [andAll] at ih ⊢
      rw [NNF.satisfies_and, ih]
      simp

/-- `orAll` holds exactly when some disjunct does. -/
theorem satisfies_orAll (fs : List (NNF α)) (ξ : OmegaWord α) :
    (orAll fs).satisfies ξ ↔ ∃ f ∈ fs, f.satisfies ξ := by
  induction fs with
  | nil => simp [orAll, NNF.satisfies_ff]
  | cons x rest ih =>
    cases rest with
    | nil => simp [orAll]
    | cons y rest' =>
      simp only [orAll] at ih ⊢
      rw [NNF.satisfies_or, ih]
      simp

/-- `[BKŘS12]` Lemma 2: an alternating formula holds at a suffix exactly when it holds at the whole word. -/
theorem satisfies_drop_of_isFairness {γ : NNF α} (h : γ.isFairness = true) (ξ : OmegaWord α) (k : Nat) :
    γ.satisfies (ξ.drop k) ↔ γ.satisfies ξ := by
  simp only [NNF.isFairness, Bool.and_eq_true] at h
  exact ⟨NNF.isPureEventuality_sound γ h.1 ξ k, NNF.isPurelyUniversal_sound γ h.2 ξ k⟩

/-- The leaves `collectAndFairness` returns are alternating, and with the remainder they denote the chain. -/
theorem collectAndFairness_spec (φ : NNF α) :
    (∀ f ∈ (collectAndFairness φ).1, f.isFairness = true) ∧
      ∀ ξ : OmegaWord α, φ.satisfies ξ ↔
        (∀ f ∈ (collectAndFairness φ).1, f.satisfies ξ) ∧ ∀ r ∈ (collectAndFairness φ).2, r.satisfies ξ := by
  induction φ
  case and a b iha ihb =>
    obtain ⟨hfa, hsa⟩ := iha
    obtain ⟨hfb, hsb⟩ := ihb
    rcases hca : collectAndFairness a with ⟨fa, ra⟩
    rcases hcb : collectAndFairness b with ⟨fb, rb⟩
    rw [hca] at hfa hsa
    rw [hcb] at hfb hsb
    unfold collectAndFairness
    rw [hca, hcb]
    refine ⟨fun f hf => ?_, fun ξ => ?_⟩
    · rcases List.mem_append.mp hf with hf | hf
      · exact hfa f hf
      · exact hfb f hf
    · rw [NNF.satisfies_and, hsa ξ, hsb ξ]
      cases ra <;> cases rb <;> simp [NNF.satisfies_and] <;> grind
  all_goals
    unfold collectAndFairness
    split <;> simp_all

/-- The leaves `collectOrFairness` returns are alternating, and with the remainder they denote the chain. -/
theorem collectOrFairness_spec (φ : NNF α) :
    (∀ f ∈ (collectOrFairness φ).1, f.isFairness = true) ∧
      ∀ ξ : OmegaWord α, φ.satisfies ξ ↔
        (∃ f ∈ (collectOrFairness φ).1, f.satisfies ξ) ∨ ∃ r ∈ (collectOrFairness φ).2, r.satisfies ξ := by
  induction φ
  case or a b iha ihb =>
    obtain ⟨hfa, hsa⟩ := iha
    obtain ⟨hfb, hsb⟩ := ihb
    rcases hca : collectOrFairness a with ⟨fa, ra⟩
    rcases hcb : collectOrFairness b with ⟨fb, rb⟩
    rw [hca] at hfa hsa
    rw [hcb] at hfb hsb
    unfold collectOrFairness
    rw [hca, hcb]
    refine ⟨fun f hf => ?_, fun ξ => ?_⟩
    · rcases List.mem_append.mp hf with hf | hf
      · exact hfa f hf
      · exact hfb f hf
    · rw [NNF.satisfies_or, hsa ξ, hsb ξ]
      cases ra <;> cases rb <;> simp [NNF.satisfies_or] <;> grind
  all_goals
    unfold collectOrFairness
    split <;> simp_all

end LTLLib
