module

/-
  The fair normal form of [LSFZ16, Theorem 1]: every fairness in `LTL(F, G)` is equivalent to a disjunction
  `⋁ᵢ (FG lᵢ ∧ ⋀ⱼ GF lᵢⱼ)` with every `l` propositional. Each disjunct is one `modelCheckTGBADisjunct` call.

  Two mutually recursive functions push the modalities inward, `gfPush ψ` returning a formula equivalent to
  `GF ψ` and `fgPush ψ` one equivalent to `FG ψ`, then `toDNF` reads the result off as disjuncts. The pushing
  is well-founded rather than fuel-bounded, on a measure where `∧` multiplies and every other node adds, so
  distributing `∧` over `∨` strictly decreases it.

  The rewrite rules are [LSFZ16] Appendix A's, which states them in the `GF`/`FG`-prefixed form where they are
  genuine equivalences. Appendix B's abbreviated forms, writing `G` for `FG` and `F` for `GF`, hold only over
  cyclic words and must not be used.

  Key definitions:
  - `dsize`: the distribution measure the recursion terminates on
  - `gfPush`, `fgPush`: the modality pushing
  - `FairDisjunct`, `toDNF`, `fnf`: the normal form and its extraction
  - `crossDNF`, `crossAllDNF`: conjoining normal forms, one disjunct per combination, folded and filtered
  - `FairDisjunct.stronger`, `dropSubsumed`, `normalise`: the syntactic implication between disjuncts, and the
    pass that drops repeated marks and every disjunct another one already covers

  Key theorems:
  - `gf_eventually` through `fg_or_eventually`: the ten rewrite equivalences
  - `gfPush_correct`, `fgPush_correct`: the pushing preserves meaning
  - `toDNF_correct`: the extraction denotes the disjunction it claims
  - `holds_crossAllDNF`: crossing a list of normal forms denotes their conjunction
  - `holds_of_stronger`, `holds_dropSubsumed`, `holds_normalise`: the syntactic implication is one, and
    normalising leaves the disjunction alone
  - `fnf_correct`: for a fairness, `φ` and its fair normal form agree

  References:
  - [LSFZ16] Li, Song, Feng, Zhang. Verify LTL with Fairness Assumptions Efficiently. arXiv:1606.08116, 2016.
    Theorem 1 for the normal form, Appendix A for the equivalences, Example 3 for the worked flattening.

  Sections:
  - Distribution measure
  - Suffix form of the two modalities
  - Collapsing nested modalities
  - Distributing over the matching connective
  - Absorbing a guarded operand
  - Distributing over the mismatched connective
  - Raw shapes used by the pushing
  - Pushing the modalities inward
  - Pushing correctness
  - Fair normal form
-/
public import LTLLib.LTL.FairClass
public import LTLLib.LTL.Propositional

public section

namespace LTLLib

open Lentil

namespace NNF

variable {α : Type u}

/-- `□◇φ`. -/
abbrev gf (φ : NNF α) : NNF α := .always (.eventually φ)

/-- `◇□φ`. -/
abbrev fg (φ : NNF α) : NNF α := .eventually (.always φ)

/-! ## Distribution measure -/

/-- `∧` multiplies and every other node adds, so distributing `∧` over `∨` strictly decreases it. Every leaf
is at least `2`, which is what makes the product dominate each factor. -/
def dsize : NNF α → Nat
  | .tt | .ff | .prop _ | .nprop _ => 2
  | .and φ ψ => dsize φ * dsize ψ
  | .or φ ψ => dsize φ + dsize ψ + 1
  | .next φ => dsize φ + 1
  | .until φ ψ => dsize φ + dsize ψ + 1
  | .release φ ψ => dsize φ + dsize ψ + 1

theorem two_le_dsize (φ : NNF α) : 2 ≤ dsize φ := by
  induction φ with
  | and φ ψ ihφ ihψ =>
    show 2 ≤ dsize φ * dsize ψ
    have : 1 * dsize ψ ≤ dsize φ * dsize ψ := Nat.mul_le_mul (by omega) (Nat.le_refl _)
    omega
  | _ => simp [dsize] <;> omega

theorem dsize_pos (φ : NNF α) : 0 < dsize φ := by have := two_le_dsize φ; omega

private theorem lt_mul_left {a b c : Nat} (h : a < b) (hc : 1 ≤ c) : a < b * c := by
  have : b * 1 ≤ b * c := Nat.mul_le_mul (Nat.le_refl b) hc
  omega

private theorem lt_mul_right {a b c : Nat} (h : a < c) (hb : 1 ≤ b) : a < b * c := by
  have : 1 * c ≤ b * c := Nat.mul_le_mul hb (Nat.le_refl c)
  omega

private theorem self_lt_mul_right {a b : Nat} (ha : 0 < a) (hb : 2 ≤ b) : a < a * b := by
  have : a * 2 ≤ a * b := Nat.mul_le_mul (Nat.le_refl a) hb
  omega

private theorem self_lt_mul_left {a b : Nat} (ha : 0 < a) (hb : 2 ≤ b) : a < b * a := by
  have : 2 * a ≤ b * a := Nat.mul_le_mul hb (Nat.le_refl a)
  omega

private theorem dsize_lt_and_left (φ ψ : NNF α) : dsize φ < dsize φ * dsize ψ :=
  self_lt_mul_right (dsize_pos φ) (two_le_dsize ψ)

private theorem dsize_lt_and_right (φ ψ : NNF α) : dsize ψ < dsize φ * dsize ψ :=
  self_lt_mul_left (dsize_pos ψ) (two_le_dsize φ)

/-! ## Suffix form of the two modalities -/

/-- `□◇φ` holds exactly when `φ` holds at arbitrarily late suffixes. -/
theorem satisfies_gf (ξ : OmegaWord α) (φ : NNF α) :
    (gf φ).satisfies ξ ↔ ∀ n, ∃ m, φ.satisfies (ξ.drop (n + m)) := by
  simp only [gf, satisfies_always, satisfies_eventually, exec.drop_drop]

/-- `◇□φ` holds exactly when `φ` holds from some suffix onwards. -/
theorem satisfies_fg (ξ : OmegaWord α) (φ : NNF α) :
    (fg φ).satisfies ξ ↔ ∃ n, ∀ m, φ.satisfies (ξ.drop (n + m)) := by
  simp only [fg, satisfies_always, satisfies_eventually, exec.drop_drop]

/-- `□◇` and `◇□` only read the formula's meaning, so equivalent operands give equivalent results. -/
theorem gf_congr {φ ψ : NNF α} (h : ∀ ζ : OmegaWord α, φ.satisfies ζ ↔ ψ.satisfies ζ)
    (ξ : OmegaWord α) : (gf φ).satisfies ξ ↔ (gf ψ).satisfies ξ := by
  simp only [satisfies_gf]
  exact forall_congr' fun n => exists_congr fun m => h _

theorem fg_congr {φ ψ : NNF α} (h : ∀ ζ : OmegaWord α, φ.satisfies ζ ↔ ψ.satisfies ζ)
    (ξ : OmegaWord α) : (fg φ).satisfies ξ ↔ (fg ψ).satisfies ξ := by
  simp only [satisfies_fg]
  exact exists_congr fun n => forall_congr' fun m => h _

/-! ## Collapsing nested modalities

[LSFZ16] Section III-A case 1, `GFF ≡ GF`, `GFG ≡ FG`, `FGG ≡ FG` and `FGF ≡ GF`.
-/

/-- Transport a satisfaction along an index equality, keeping `omega` in charge of the arithmetic. -/
private theorem drop_congr {φ : NNF α} {ξ : OmegaWord α} {i j : Nat} (h : i = j) :
    φ.satisfies (ξ.drop i) ↔ φ.satisfies (ξ.drop j) := by rw [h]

private theorem not_forall_nat {P : Nat → Prop} (h : ¬ ∀ m, P m) : ∃ m, ¬ P m := by
  by_contra hc
  exact h fun m => Classical.byContradiction fun hm => hc ⟨m, hm⟩

private theorem not_forall_exists {P : Nat → Nat → Prop} (h : ¬ ∀ n, ∃ m, P n m) :
    ∃ n, ∀ m, ¬ P n m := by
  by_contra hc
  exact h fun n => Classical.byContradiction fun hn => hc ⟨n, fun m hm => hn ⟨m, hm⟩⟩

/-- `GF F ψ ≡ GF ψ`. -/
theorem gf_eventually (ξ : OmegaWord α) (ψ : NNF α) :
    (gf (.eventually ψ)).satisfies ξ ↔ (gf ψ).satisfies ξ := by
  rw [satisfies_gf, satisfies_gf]
  simp only [satisfies_eventually, exec.drop_drop]
  constructor
  · intro h n
    obtain ⟨m, k, hk⟩ := h n
    exact ⟨m + k, (drop_congr (by omega)).mp hk⟩
  · intro h n
    obtain ⟨m, hm⟩ := h n
    exact ⟨m, 0, (drop_congr (by omega)).mp hm⟩

/-- `GF G ψ ≡ FG ψ`. -/
theorem gf_always (ξ : OmegaWord α) (ψ : NNF α) :
    (gf (.always ψ)).satisfies ξ ↔ (fg ψ).satisfies ξ := by
  rw [satisfies_gf, satisfies_fg]
  simp only [satisfies_always, exec.drop_drop]
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h 0
    exact ⟨m, fun k => (drop_congr (by omega)).mp (hm k)⟩
  · rintro ⟨N, hN⟩ n
    exact ⟨N, fun k => (drop_congr (by omega)).mp (hN (n + k))⟩

/-- `FG G ψ ≡ FG ψ`. -/
theorem fg_always (ξ : OmegaWord α) (ψ : NNF α) :
    (fg (.always ψ)).satisfies ξ ↔ (fg ψ).satisfies ξ := by
  rw [satisfies_fg, satisfies_fg]
  simp only [satisfies_always, exec.drop_drop]
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun m => (drop_congr (by omega)).mp (hN m 0)⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, fun m k => (drop_congr (by omega)).mp (hN (m + k))⟩

/-- `FG F ψ ≡ GF ψ`. -/
theorem fg_eventually (ξ : OmegaWord α) (ψ : NNF α) :
    (fg (.eventually ψ)).satisfies ξ ↔ (gf ψ).satisfies ξ := by
  rw [satisfies_fg, satisfies_gf]
  simp only [satisfies_eventually, exec.drop_drop]
  constructor
  · rintro ⟨N, hN⟩ n
    obtain ⟨k, hk⟩ := hN n
    exact ⟨N + k, (drop_congr (by omega)).mp hk⟩
  · intro h
    refine ⟨0, fun m => ?_⟩
    obtain ⟨k, hk⟩ := h m
    exact ⟨k, (drop_congr (by omega)).mp hk⟩

/-! ## Distributing over the matching connective

[LSFZ16] Section III-A case 2. `GF` distributes over `∨` and `FG` over `∧`.
-/

/-- `GF(ψ₁ ∨ ψ₂) ≡ GF ψ₁ ∨ GF ψ₂`. -/
theorem gf_or (ξ : OmegaWord α) (ψ₁ ψ₂ : NNF α) :
    (gf (.or ψ₁ ψ₂)).satisfies ξ ↔ (gf ψ₁).satisfies ξ ∨ (gf ψ₂).satisfies ξ := by
  rw [satisfies_gf, satisfies_gf, satisfies_gf]
  simp only [satisfies_or]
  constructor
  · intro h
    -- Only one of the two can fail to recur, so contraposing on the first gives the second.
    by_cases h1 : ∀ n, ∃ m, ψ₁.satisfies (ξ.drop (n + m))
    · exact Or.inl h1
    · obtain ⟨n₁, hn₁⟩ := not_forall_exists h1
      refine Or.inr fun n => ?_
      obtain ⟨m, hm | hm⟩ := h (n + n₁)
      · exact absurd ((drop_congr (by omega)).mp hm) (hn₁ (n + m))
      · exact ⟨n₁ + m, (drop_congr (by omega)).mp hm⟩
  · rintro (h | h) n
    · exact (h n).imp fun _ => Or.inl
    · exact (h n).imp fun _ => Or.inr

/-- `FG(ψ₁ ∧ ψ₂) ≡ FG ψ₁ ∧ FG ψ₂`. -/
theorem fg_and (ξ : OmegaWord α) (ψ₁ ψ₂ : NNF α) :
    (fg (.and ψ₁ ψ₂)).satisfies ξ ↔ (fg ψ₁).satisfies ξ ∧ (fg ψ₂).satisfies ξ := by
  rw [satisfies_fg, satisfies_fg, satisfies_fg]
  simp only [satisfies_and]
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨⟨N, fun m => (hN m).1⟩, ⟨N, fun m => (hN m).2⟩⟩
  · rintro ⟨⟨N₁, h₁⟩, ⟨N₂, h₂⟩⟩
    exact ⟨N₁ + N₂, fun m =>
      ⟨(drop_congr (by omega)).mp (h₁ (N₂ + m)), (drop_congr (by omega)).mp (h₂ (N₁ + m))⟩⟩

/-! ## Absorbing a guarded operand

[LSFZ16] Section III-A case 3, the four rules that pull an `F` or `G` operand out of the modality.
-/

/-- `GF(ψ₁ ∧ F ψ₂) ≡ GF ψ₁ ∧ GF ψ₂`. -/
theorem gf_and_eventually (ξ : OmegaWord α) (ψ₁ ψ₂ : NNF α) :
    (gf (.and ψ₁ (.eventually ψ₂))).satisfies ξ ↔ (gf ψ₁).satisfies ξ ∧ (gf ψ₂).satisfies ξ := by
  rw [satisfies_gf, satisfies_gf, satisfies_gf]
  simp only [satisfies_and, satisfies_eventually, exec.drop_drop]
  constructor
  · intro h
    refine ⟨fun n => (h n).imp fun _ hm => hm.1, fun n => ?_⟩
    obtain ⟨m, -, k, hk⟩ := h n
    exact ⟨m + k, (drop_congr (by omega)).mp hk⟩
  · rintro ⟨h1, h2⟩ n
    obtain ⟨m, hm⟩ := h1 n
    obtain ⟨k, hk⟩ := h2 (n + m)
    exact ⟨m, hm, k, (drop_congr (by omega)).mp hk⟩

/-- `GF(ψ₁ ∧ G ψ₂) ≡ GF ψ₁ ∧ FG ψ₂`. -/
theorem gf_and_always (ξ : OmegaWord α) (ψ₁ ψ₂ : NNF α) :
    (gf (.and ψ₁ (.always ψ₂))).satisfies ξ ↔ (gf ψ₁).satisfies ξ ∧ (fg ψ₂).satisfies ξ := by
  rw [satisfies_gf, satisfies_gf, satisfies_fg]
  simp only [satisfies_and, satisfies_always, exec.drop_drop]
  constructor
  · intro h
    refine ⟨fun n => (h n).imp fun _ hm => hm.1, ?_⟩
    obtain ⟨m, -, hk⟩ := h 0
    exact ⟨m, fun k => (drop_congr (by omega)).mp (hk k)⟩
  · rintro ⟨h1, N, hN⟩ n
    obtain ⟨m, hm⟩ := h1 (n + N)
    exact ⟨N + m, (drop_congr (by omega)).mp hm,
      fun k => (drop_congr (by omega)).mp (hN (n + m + k))⟩

/-- `FG(ψ₁ ∨ G ψ₂) ≡ FG ψ₁ ∨ FG ψ₂`. -/
theorem fg_or_always (ξ : OmegaWord α) (ψ₁ ψ₂ : NNF α) :
    (fg (.or ψ₁ (.always ψ₂))).satisfies ξ ↔ (fg ψ₁).satisfies ξ ∨ (fg ψ₂).satisfies ξ := by
  rw [satisfies_fg, satisfies_fg, satisfies_fg]
  simp only [satisfies_or, satisfies_always, exec.drop_drop]
  constructor
  · rintro ⟨N, hN⟩
    by_cases h1 : ∀ m, ψ₁.satisfies (ξ.drop (N + m))
    · exact Or.inl ⟨N, h1⟩
    · obtain ⟨m₀, hm₀⟩ := not_forall_nat h1
      refine Or.inr ⟨N + m₀, fun k => ?_⟩
      rcases hN m₀ with h | h
      · exact absurd h hm₀
      · exact (drop_congr (by omega)).mp (h k)
  · rintro (⟨N, h⟩ | ⟨N, h⟩)
    · exact ⟨N, fun m => Or.inl (h m)⟩
    · exact ⟨N, fun m => Or.inr fun k => (drop_congr (by omega)).mp (h (m + k))⟩

/-- `FG(ψ₁ ∨ F ψ₂) ≡ FG ψ₁ ∨ GF ψ₂`. -/
theorem fg_or_eventually (ξ : OmegaWord α) (ψ₁ ψ₂ : NNF α) :
    (fg (.or ψ₁ (.eventually ψ₂))).satisfies ξ ↔ (fg ψ₁).satisfies ξ ∨ (gf ψ₂).satisfies ξ := by
  rw [satisfies_fg, satisfies_fg, satisfies_gf]
  simp only [satisfies_or, satisfies_eventually, exec.drop_drop]
  constructor
  · rintro ⟨N, hN⟩
    by_cases h2 : ∀ n, ∃ m, ψ₂.satisfies (ξ.drop (n + m))
    · exact Or.inr h2
    · obtain ⟨n₀, hn₀⟩ := not_forall_exists h2
      refine Or.inl ⟨N + n₀, fun m => ?_⟩
      rcases hN (n₀ + m) with h | ⟨k, hk⟩
      · exact (drop_congr (by omega)).mp h
      · exact absurd ((drop_congr (by omega)).mp hk) (hn₀ (N + m + k))
  · rintro (⟨N, h⟩ | h)
    · exact ⟨N, fun m => Or.inl (h m)⟩
    · refine ⟨0, fun m => Or.inr ?_⟩
      obtain ⟨k, hk⟩ := h m
      exact ⟨k, (drop_congr (by omega)).mp hk⟩

/-! ## Distributing over the mismatched connective

[LSFZ16] Section III-A case 4, the DNF and CNF step, taken one distribution at a time.
-/

/-- `GF((α ∨ β) ∧ γ) ≡ GF(α ∧ γ) ∨ GF(β ∧ γ)`. -/
theorem gf_and_or_left (ξ : OmegaWord α) (a b c : NNF α) :
    (gf (.and (.or a b) c)).satisfies ξ ↔
      (gf (.and a c)).satisfies ξ ∨ (gf (.and b c)).satisfies ξ := by
  rw [gf_congr (φ := .and (.or a b) c) (ψ := .or (.and a c) (.and b c))
    (fun ζ => by simp only [satisfies_and, satisfies_or]; grind), gf_or]

/-- `GF(α ∧ (β ∨ γ)) ≡ GF(α ∧ β) ∨ GF(α ∧ γ)`. -/
theorem gf_and_or_right (ξ : OmegaWord α) (a b c : NNF α) :
    (gf (.and a (.or b c))).satisfies ξ ↔
      (gf (.and a b)).satisfies ξ ∨ (gf (.and a c)).satisfies ξ := by
  rw [gf_congr (φ := .and a (.or b c)) (ψ := .or (.and a b) (.and a c))
    (fun ζ => by simp only [satisfies_and, satisfies_or]; grind), gf_or]

/-- `FG((α ∧ β) ∨ γ) ≡ FG(α ∨ γ) ∧ FG(β ∨ γ)`. -/
theorem fg_or_and_left (ξ : OmegaWord α) (a b c : NNF α) :
    (fg (.or (.and a b) c)).satisfies ξ ↔
      (fg (.or a c)).satisfies ξ ∧ (fg (.or b c)).satisfies ξ := by
  rw [fg_congr (φ := .or (.and a b) c) (ψ := .and (.or a c) (.or b c))
    (fun ζ => by simp only [satisfies_and, satisfies_or]; grind), fg_and]

/-- `FG(α ∨ (β ∧ γ)) ≡ FG(α ∨ β) ∧ FG(α ∨ γ)`. -/
theorem fg_or_and_right (ξ : OmegaWord α) (a b c : NNF α) :
    (fg (.or a (.and b c))).satisfies ξ ↔
      (fg (.or a b)).satisfies ξ ∧ (fg (.or a c)).satisfies ξ := by
  rw [fg_congr (φ := .or a (.and b c)) (ψ := .and (.or a b) (.or a c))
    (fun ζ => by simp only [satisfies_and, satisfies_or]; grind), fg_and]

/-! ## Raw shapes used by the pushing

`F` and `G` are `⊤ U ψ` and `⊥ R ψ`, so these restate the rules in the form the recursion matches on, and
supply the two commuted variants.
-/

theorem gf_untilTop (ξ : OmegaWord α) (ψ : NNF α) :
    (gf (.until .tt ψ)).satisfies ξ ↔ (gf ψ).satisfies ξ := gf_eventually ξ ψ

theorem gf_releaseBot (ξ : OmegaWord α) (ψ : NNF α) :
    (gf (.release .ff ψ)).satisfies ξ ↔ (fg ψ).satisfies ξ := gf_always ξ ψ

theorem fg_releaseBot (ξ : OmegaWord α) (ψ : NNF α) :
    (fg (.release .ff ψ)).satisfies ξ ↔ (fg ψ).satisfies ξ := fg_always ξ ψ

theorem fg_untilTop (ξ : OmegaWord α) (ψ : NNF α) :
    (fg (.until .tt ψ)).satisfies ξ ↔ (gf ψ).satisfies ξ := fg_eventually ξ ψ

theorem gf_and_untilTop_right (ξ : OmegaWord α) (ψ₁ χ : NNF α) :
    (gf (.and ψ₁ (.until .tt χ))).satisfies ξ ↔ (gf ψ₁).satisfies ξ ∧ (gf χ).satisfies ξ :=
  gf_and_eventually ξ ψ₁ χ

theorem gf_and_releaseBot_right (ξ : OmegaWord α) (ψ₁ χ : NNF α) :
    (gf (.and ψ₁ (.release .ff χ))).satisfies ξ ↔ (gf ψ₁).satisfies ξ ∧ (fg χ).satisfies ξ :=
  gf_and_always ξ ψ₁ χ

theorem gf_and_untilTop_left (ξ : OmegaWord α) (χ ψ₂ : NNF α) :
    (gf (.and (.until .tt χ) ψ₂)).satisfies ξ ↔ (gf χ).satisfies ξ ∧ (gf ψ₂).satisfies ξ := by
  rw [gf_congr (φ := .and (.until .tt χ) ψ₂) (ψ := .and ψ₂ (.until .tt χ))
    (fun ζ => by simp only [satisfies_and]; grind), gf_and_untilTop_right]
  grind

theorem gf_and_releaseBot_left (ξ : OmegaWord α) (χ ψ₂ : NNF α) :
    (gf (.and (.release .ff χ) ψ₂)).satisfies ξ ↔ (fg χ).satisfies ξ ∧ (gf ψ₂).satisfies ξ := by
  rw [gf_congr (φ := .and (.release .ff χ) ψ₂) (ψ := .and ψ₂ (.release .ff χ))
    (fun ζ => by simp only [satisfies_and]; grind), gf_and_releaseBot_right]
  grind

theorem fg_or_releaseBot_right (ξ : OmegaWord α) (ψ₁ χ : NNF α) :
    (fg (.or ψ₁ (.release .ff χ))).satisfies ξ ↔ (fg ψ₁).satisfies ξ ∨ (fg χ).satisfies ξ :=
  fg_or_always ξ ψ₁ χ

theorem fg_or_untilTop_right (ξ : OmegaWord α) (ψ₁ χ : NNF α) :
    (fg (.or ψ₁ (.until .tt χ))).satisfies ξ ↔ (fg ψ₁).satisfies ξ ∨ (gf χ).satisfies ξ :=
  fg_or_eventually ξ ψ₁ χ

theorem fg_or_releaseBot_left (ξ : OmegaWord α) (χ ψ₂ : NNF α) :
    (fg (.or (.release .ff χ) ψ₂)).satisfies ξ ↔ (fg χ).satisfies ξ ∨ (fg ψ₂).satisfies ξ := by
  rw [fg_congr (φ := .or (.release .ff χ) ψ₂) (ψ := .or ψ₂ (.release .ff χ))
    (fun ζ => by simp only [satisfies_or]; grind), fg_or_releaseBot_right]
  grind

theorem fg_or_untilTop_left (ξ : OmegaWord α) (χ ψ₂ : NNF α) :
    (fg (.or (.until .tt χ) ψ₂)).satisfies ξ ↔ (gf χ).satisfies ξ ∨ (fg ψ₂).satisfies ξ := by
  rw [fg_congr (φ := .or (.until .tt χ) ψ₂) (ψ := .or ψ₂ (.until .tt χ))
    (fun ζ => by simp only [satisfies_or]; grind), fg_or_untilTop_right]
  grind

/-! ## Pushing the modalities inward -/

mutual

/-- A formula equivalent to `□◇ψ` with the modalities pushed in as far as the rules reach. -/
@[expose] def gfPush : NNF α → NNF α
  | .or ψ₁ ψ₂ => .or (gfPush ψ₁) (gfPush ψ₂)
  | .until .tt ψ' => gfPush ψ'
  | .release .ff ψ' => fgPush ψ'
  | .and ψ₁ (.until .tt χ) => .and (gfPush ψ₁) (gfPush χ)
  | .and ψ₁ (.release .ff χ) => .and (gfPush ψ₁) (fgPush χ)
  | .and (.until .tt χ) ψ₂ => .and (gfPush χ) (gfPush ψ₂)
  | .and (.release .ff χ) ψ₂ => .and (fgPush χ) (gfPush ψ₂)
  | .and (.or a b) c => .or (gfPush (.and a c)) (gfPush (.and b c))
  | .and a (.or b c) => .or (gfPush (.and a b)) (gfPush (.and a c))
  | ψ => gf ψ
termination_by ψ => dsize ψ
decreasing_by
  all_goals simp_wf
  all_goals simp only [dsize]
  all_goals
    first
      | omega
      | exact (Nat.mul_lt_mul_left (dsize_pos _)).mpr (by omega)
      | exact (Nat.mul_lt_mul_right (dsize_pos _)).mpr (by omega)
      | (refine lt_mul_left ?_ (dsize_pos _); omega)
      | (refine lt_mul_right ?_ (dsize_pos _); omega)
      | (refine self_lt_mul_right (dsize_pos _) ?_; omega)
      | (refine self_lt_mul_left (dsize_pos _) ?_; omega)

/-- A formula equivalent to `◇□ψ` with the modalities pushed in as far as the rules reach. -/
def fgPush : NNF α → NNF α
  | .and ψ₁ ψ₂ => .and (fgPush ψ₁) (fgPush ψ₂)
  | .release .ff ψ' => fgPush ψ'
  | .until .tt ψ' => gfPush ψ'
  | .or ψ₁ (.release .ff χ) => .or (fgPush ψ₁) (fgPush χ)
  | .or ψ₁ (.until .tt χ) => .or (fgPush ψ₁) (gfPush χ)
  | .or (.release .ff χ) ψ₂ => .or (fgPush χ) (fgPush ψ₂)
  | .or (.until .tt χ) ψ₂ => .or (gfPush χ) (fgPush ψ₂)
  | .or (.and a b) c => .and (fgPush (.or a c)) (fgPush (.or b c))
  | .or a (.and b c) => .and (fgPush (.or a b)) (fgPush (.or a c))
  | ψ => fg ψ
termination_by ψ => dsize ψ
decreasing_by
  all_goals simp_wf
  all_goals simp only [dsize]
  all_goals
    first
      | omega
      | exact (Nat.mul_lt_mul_left (dsize_pos _)).mpr (by omega)
      | exact (Nat.mul_lt_mul_right (dsize_pos _)).mpr (by omega)
      | (refine lt_mul_left ?_ (dsize_pos _); omega)
      | (refine lt_mul_right ?_ (dsize_pos _); omega)
      | (refine self_lt_mul_right (dsize_pos _) ?_; first | omega | exact two_le_dsize _)
      | (refine self_lt_mul_left (dsize_pos _) ?_; first | omega | exact two_le_dsize _)
      | (refine Nat.add_lt_add_right (Nat.add_lt_add_right ?_ _) _
         first | exact dsize_lt_and_left _ _ | exact dsize_lt_and_right _ _)
      | (refine Nat.add_lt_add_right (Nat.add_lt_add_left ?_ _) _
         first | exact dsize_lt_and_left _ _ | exact dsize_lt_and_right _ _)

end

/-! ## Pushing correctness -/

/-- One case of either pushing function's correctness: unfold the arm, discharge the arm's own side
conditions, rewrite the recursive calls by their induction hypotheses, then apply the arm's rule. -/
local syntax "push_step" : tactic

local macro_rules
  | `(tactic| push_step) => `(tactic|
      (intros
       first | rw [gfPush] | rw [fgPush]
       all_goals
         first
           | assumption
           | (simp only [satisfies_and, satisfies_or, *]
              first
                | rfl
                | rw [gf_or] | rw [gf_untilTop] | rw [gf_releaseBot]
                | rw [gf_and_untilTop_right] | rw [gf_and_releaseBot_right]
                | rw [gf_and_untilTop_left] | rw [gf_and_releaseBot_left]
                | rw [gf_and_or_left] | rw [gf_and_or_right]
                | rw [fg_and] | rw [fg_releaseBot] | rw [fg_untilTop]
                | rw [fg_or_releaseBot_right] | rw [fg_or_untilTop_right]
                | rw [fg_or_releaseBot_left] | rw [fg_or_untilTop_left]
                | rw [fg_or_and_left] | rw [fg_or_and_right])))

/-- `gfPush ψ` means `□◇ψ`. -/
theorem gfPush_correct (ψ : NNF α) :
    ∀ ξ : OmegaWord α, (gfPush ψ).satisfies ξ ↔ (gf ψ).satisfies ξ := by
  induction ψ using gfPush.induct
    (motive2 := fun ψ => ∀ ξ : OmegaWord α, (fgPush ψ).satisfies ξ ↔ (fg ψ).satisfies ξ) with
  | _ => push_step

/-- `fgPush ψ` means `◇□ψ`. -/
theorem fgPush_correct (ψ : NNF α) :
    ∀ ξ : OmegaWord α, (fgPush ψ).satisfies ξ ↔ (fg ψ).satisfies ξ := by
  induction ψ using fgPush.induct
    (motive1 := fun ψ => ∀ ξ : OmegaWord α, (gfPush ψ).satisfies ξ ↔ (gf ψ).satisfies ξ) with
  | _ => push_step

/-! ## Fair normal form -/

/-- One fair-normal-form disjunct, the `FG` part and the list of `GF` parts, all propositional. -/
abbrev FairDisjunct (α : Type u) := BoolFormula α × List (BoolFormula α)

/-- A disjunct denotes `◇□f ∧ ⋀ g ∈ gs, □◇g`, which is exactly what one emptiness check decides. -/
@[expose] def FairDisjunct.holds (ξ : OmegaWord α) (d : FairDisjunct α) : Prop :=
  (BoolFormula.eventuallyAlways d.1).satisfies ξ ∧
  ∀ g ∈ d.2, (BoolFormula.alwaysEventually g).satisfies ξ

private def memBy {β : Type v} [DecidableEq β] (b : β) (l : List β) : Bool :=
  l.any fun c => decide (b = c)

private theorem memBy_iff {β : Type v} [DecidableEq β] {b : β} {l : List β} :
    memBy b l = true ↔ b ∈ l := by simp [memBy]

/-- `d` implies `e`, read off the syntax: every conjunct of `e`'s region is one of `d`'s, and every mark of
`e` is one of `d`'s. A disjunct that implies another one contributes nothing to the disjunction. -/
def FairDisjunct.stronger [DecidableEq α] (d e : FairDisjunct α) : Bool :=
  e.1.conjuncts.all (fun c => memBy c d.1.conjuncts) && e.2.all (fun g => memBy g d.2)

private def dedupList {β : Type v} [DecidableEq β] : List β → List β
  | [] => []
  | b :: bs => if memBy b bs then dedupList bs else b :: dedupList bs

private theorem mem_dedupList {β : Type v} [DecidableEq β] (b : β) :
    ∀ bs : List β, b ∈ dedupList bs ↔ b ∈ bs
  | [] => by simp [dedupList]
  | c :: bs => by
    rw [dedupList]
    split
    · next h =>
      rw [mem_dedupList b bs, List.mem_cons]
      have := memBy_iff.mp h
      grind
    · rw [List.mem_cons, List.mem_cons, mem_dedupList b bs]

/-- Drop every disjunct that another one already covers. The first of a group is kept, so identical disjuncts
collapse and a disjunct strengthening an earlier one goes. -/
def dropSubsumed [DecidableEq α] : List (FairDisjunct α) → List (FairDisjunct α)
  | [] => []
  | d :: ds => d :: dropSubsumed (ds.filter fun e => !e.stronger d)
termination_by ds => ds.length
decreasing_by
  try simp only [List.length_unattach]
  exact Nat.lt_succ_of_le (Nat.le_trans (List.length_filter_le _ _) (by simp))

/-- Merge two disjuncts, `none` when the merged region folds to `⊥` and no run can take it. -/
def mergePair [DecidableEq α] (d e : FairDisjunct α) : Option (FairDisjunct α) :=
  match (BoolFormula.and d.1 e.1).simplify with
  | .ff => none
  | region => some (region, d.2 ++ e.2)

/-- Conjoin two normal forms, one disjunct per pair. The `FG` parts merge into one because `FG` distributes
over `∧`, and the `GF` parts accumulate. One pass and nothing quadratic, since this also crosses a whole
assumption, where the list reaches one disjunct per combination. -/
def crossDNF [DecidableEq α] (ds es : List (FairDisjunct α)) : List (FairDisjunct α) :=
  ds.flatMap fun d => es.filterMap (mergePair d)

/-- Drop the marks a disjunct repeats and the disjuncts another one covers. Quadratic, so it runs once per
conjunct of the assumption, where the list is the size of the formula. -/
def normalise [DecidableEq α] (ds : List (FairDisjunct α)) : List (FairDisjunct α) :=
  dropSubsumed (ds.map fun d => (d.1, dedupList d.2))

/-- Conjoin a list of normal forms, `⊤` when empty. -/
@[expose] def crossAllDNF [DecidableEq α] : List (List (FairDisjunct α)) → List (FairDisjunct α)
  | [] => [(.tt, [])]
  | ds :: dss => crossDNF ds (crossAllDNF dss)

/-- Read `◇□l` off a pushed formula. -/
@[expose] def asFGPart : NNF α → Option (BoolFormula α)
  | .release φ l => if φ.isBot then l.asBool? else none
  | _ => none

/-- Read `□◇l` off a pushed formula. -/
@[expose] def asGFPart : NNF α → Option (BoolFormula α)
  | .until φ l => if φ.isTop then l.asBool? else none
  | _ => none

theorem asFGPart_eq {ψ : NNF α} {f : BoolFormula α} (h : asFGPart ψ = some f) :
    ψ = .always f.toNNF := by
  cases ψ with
  | release φ l =>
    simp only [asFGPart] at h
    split at h
    · rename_i hb
      rw [eq_ff_of_isBot hb, asBool?_toNNF h]; rfl
    · exact absurd h (by simp)
  | _ => simp [asFGPart] at h

theorem asGFPart_eq {ψ : NNF α} {g : BoolFormula α} (h : asGFPart ψ = some g) :
    ψ = .eventually g.toNNF := by
  cases ψ with
  | «until» φ l =>
    simp only [asGFPart] at h
    split at h
    · rename_i ht
      rw [eq_tt_of_isTop ht, asBool?_toNNF h]; rfl
    · exact absurd h (by simp)
  | _ => simp [asGFPart] at h

/-- Read a pushed formula off as disjuncts, `none` when it is not a Boolean combination of `FG l` and `GF l`. -/
def toDNF [DecidableEq α] : NNF α → Option (List (FairDisjunct α))
  | .tt => some [(.tt, [])]
  | .ff => some []
  | .or φ ψ => (toDNF φ).bind fun a => (toDNF ψ).map fun b => a ++ b
  | .and φ ψ => (toDNF φ).bind fun a => (toDNF ψ).map fun b => crossDNF a b
  | .until φ ψ => if φ.isTop then (asFGPart ψ).map fun f => [(f, [])] else none
  | .release φ ψ => if φ.isBot then (asGFPart ψ).map fun g => [(.tt, [g])] else none
  | _ => none

private theorem holds_top (ξ : OmegaWord α) :
    (BoolFormula.eventuallyAlways (.tt : BoolFormula α)).satisfies ξ := by
  simp [BoolFormula.eventuallyAlways, BoolFormula.toNNF, satisfies_eventually, satisfies_always,
    satisfies_tt]

/-- `◇□` reads a folded formula the same way, the folding being an equivalence at every position. -/
private theorem satisfies_eventuallyAlways_simplify [DecidableEq α] (ξ : OmegaWord α)
    (b : BoolFormula α) :
    (BoolFormula.eventuallyAlways b.simplify).satisfies ξ ↔
      (BoolFormula.eventuallyAlways b).satisfies ξ := by
  simp only [BoolFormula.satisfies_eventuallyAlways, BoolFormula.holds_simplify]

private theorem holds_merge [DecidableEq α] (ξ : OmegaWord α) (d₁ d₂ : FairDisjunct α) :
    FairDisjunct.holds ξ ((BoolFormula.and d₁.1 d₂.1).simplify, d₁.2 ++ d₂.2) ↔
      FairDisjunct.holds ξ d₁ ∧ FairDisjunct.holds ξ d₂ := by
  have hfg : (BoolFormula.eventuallyAlways (BoolFormula.and d₁.1 d₂.1).simplify).satisfies ξ ↔
      (BoolFormula.eventuallyAlways d₁.1).satisfies ξ ∧
      (BoolFormula.eventuallyAlways d₂.1).satisfies ξ := by
    rw [satisfies_eventuallyAlways_simplify]
    exact fg_and ξ d₁.1.toNNF d₂.1.toNNF
  simp only [FairDisjunct.holds, hfg, List.mem_append]
  grind

private theorem holds_dedupMarks [DecidableEq α] (ξ : OmegaWord α) (d : FairDisjunct α) :
    FairDisjunct.holds ξ (d.1, dedupList d.2) ↔ FairDisjunct.holds ξ d := by
  simp only [FairDisjunct.holds]
  constructor
  · exact fun h => ⟨h.1, fun g hg => h.2 g ((mem_dedupList g d.2).mpr hg)⟩
  · exact fun h => ⟨h.1, fun g hg => h.2 g ((mem_dedupList g d.2).mp hg)⟩

/-- A disjunct whose region is `⊥` holds of no word, which is what lets the crossing drop it. -/
private theorem not_holds_of_isFalse {ξ : OmegaWord α} {d : FairDisjunct α}
    (h : d.1.isFalse = true) : ¬ FairDisjunct.holds ξ d := by
  have hd1 : d.1 = .ff := by cases hd : d.1 <;> simp_all [BoolFormula.isFalse]
  rintro ⟨hfg, -⟩
  rw [hd1] at hfg
  obtain ⟨n, hn⟩ := (BoolFormula.satisfies_eventuallyAlways ξ .ff).mp hfg
  exact hn 0

/-- The syntactic test really is an implication between disjuncts. -/
theorem holds_of_stronger [DecidableEq α] {ξ : OmegaWord α} {d e : FairDisjunct α}
    (h : d.stronger e = true) (hd : FairDisjunct.holds ξ d) : FairDisjunct.holds ξ e := by
  rw [FairDisjunct.stronger, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  refine ⟨?_, fun g hg => hd.2 g (memBy_iff.mp (h.2 g hg))⟩
  obtain ⟨n, hn⟩ := (BoolFormula.satisfies_eventuallyAlways ξ d.1).mp hd.1
  exact (BoolFormula.satisfies_eventuallyAlways ξ e.1).mpr
    ⟨n, fun k => BoolFormula.holds_of_conjuncts_subset
      (fun c hc => memBy_iff.mp (h.1 c hc)) (hn k)⟩

private theorem mem_of_mem_dropSubsumed [DecidableEq α] :
    ∀ (ds : List (FairDisjunct α)) {d : FairDisjunct α}, d ∈ dropSubsumed ds → d ∈ ds
  | [], _, h => by simp [dropSubsumed] at h
  | d₀ :: ds, d, h => by
    rw [dropSubsumed, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _
        (List.mem_filter.mp (mem_of_mem_dropSubsumed _ h)).1
termination_by ds => ds.length
decreasing_by
  try simp only [List.length_unattach]
  exact Nat.lt_succ_of_le (Nat.le_trans (List.length_filter_le _ _) (by simp))

/-- Dropping the covered disjuncts leaves the disjunction alone. -/
theorem holds_dropSubsumed [DecidableEq α] (ξ : OmegaWord α) :
    ∀ ds : List (FairDisjunct α),
      (∃ d ∈ dropSubsumed ds, FairDisjunct.holds ξ d) ↔ ∃ d ∈ ds, FairDisjunct.holds ξ d
  | [] => by simp [dropSubsumed]
  | d₀ :: ds => by
    rw [dropSubsumed]
    constructor
    · rintro ⟨d, hd, hh⟩
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨d, List.mem_cons_self .., hh⟩
      · exact ⟨d, List.mem_cons_of_mem _
          (List.mem_filter.mp (mem_of_mem_dropSubsumed _ hd)).1, hh⟩
    · rintro ⟨d, hd, hh⟩
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ⟨d, List.mem_cons_self .., hh⟩
      · by_cases hs : d.stronger d₀ = true
        · exact ⟨d₀, List.mem_cons_self .., holds_of_stronger hs hh⟩
        · obtain ⟨d', hd', hh'⟩ :=
            (holds_dropSubsumed ξ (ds.filter fun e => !e.stronger d₀)).mpr
              ⟨d, List.mem_filter.mpr ⟨hd, by simp [hs]⟩, hh⟩
          exact ⟨d', List.mem_cons_of_mem _ hd', hh'⟩
termination_by ds => ds.length
decreasing_by
  try simp only [List.length_unattach]
  exact Nat.lt_succ_of_le (Nat.le_trans (List.length_filter_le _ _) (by simp))

/-- Crossing two normal forms denotes their conjunction. -/
theorem holds_crossDNF [DecidableEq α] (ξ : OmegaWord α) (ds es : List (FairDisjunct α)) :
    (∃ d ∈ crossDNF ds es, FairDisjunct.holds ξ d) ↔
      (∃ d ∈ ds, FairDisjunct.holds ξ d) ∧ (∃ e ∈ es, FairDisjunct.holds ξ e) := by
  rw [crossDNF]
  constructor
  · rintro ⟨d, hd, hh⟩
    obtain ⟨d₁, hd₁, hmem⟩ := List.mem_flatMap.mp hd
    obtain ⟨d₂, hd₂, heq⟩ := List.mem_filterMap.mp hmem
    rw [mergePair] at heq
    split at heq
    · exact absurd heq (by simp)
    · obtain rfl : d = _ := (Option.some.inj heq).symm
      obtain ⟨h₁, h₂⟩ := (holds_merge ξ d₁ d₂).mp hh
      exact ⟨⟨d₁, hd₁, h₁⟩, ⟨d₂, hd₂, h₂⟩⟩
  · rintro ⟨⟨d₁, hd₁, h₁⟩, ⟨d₂, hd₂, h₂⟩⟩
    have hh := (holds_merge ξ d₁ d₂).mpr ⟨h₁, h₂⟩
    have hmp : mergePair d₁ d₂ = some ((BoolFormula.and d₁.1 d₂.1).simplify, d₁.2 ++ d₂.2) := by
      rw [mergePair]
      split
      · next hff =>
        exact absurd (hff ▸ hh)
          (not_holds_of_isFalse (d := (BoolFormula.ff, d₁.2 ++ d₂.2)) (by simp [BoolFormula.isFalse]))
      · rfl
    exact ⟨_, List.mem_flatMap.mpr ⟨d₁, hd₁, List.mem_filterMap.mpr ⟨d₂, hd₂, hmp⟩⟩, hh⟩

/-- Normalising leaves the disjunction alone. -/
theorem holds_normalise [DecidableEq α] (ξ : OmegaWord α) (ds : List (FairDisjunct α)) :
    (∃ d ∈ normalise ds, FairDisjunct.holds ξ d) ↔ ∃ d ∈ ds, FairDisjunct.holds ξ d := by
  rw [normalise, holds_dropSubsumed]
  constructor
  · rintro ⟨d, hd, hh⟩
    obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
    exact ⟨d', hd', (holds_dedupMarks ξ d').mp hh⟩
  · rintro ⟨d, hd, hh⟩
    exact ⟨_, List.mem_map.mpr ⟨d, hd, rfl⟩, (holds_dedupMarks ξ d).mpr hh⟩

/-- Crossing a list of normal forms denotes their conjunction. -/
theorem holds_crossAllDNF [DecidableEq α] (ξ : OmegaWord α) (dss : List (List (FairDisjunct α))) :
    (∃ d ∈ crossAllDNF dss, FairDisjunct.holds ξ d) ↔
      ∀ ds ∈ dss, ∃ d ∈ ds, FairDisjunct.holds ξ d := by
  induction dss with
  | nil =>
    simp only [crossAllDNF, List.mem_singleton, List.not_mem_nil, false_implies, implies_true,
      iff_true]
    exact ⟨_, rfl, holds_top ξ, by simp⟩
  | cons ds dss ih =>
    rw [crossAllDNF, holds_crossDNF, ih]
    constructor
    · rintro ⟨h₁, h₂⟩ ds' hds'
      rcases List.mem_cons.mp hds' with rfl | hm
      · exact h₁
      · exact h₂ ds' hm
    · exact fun h => ⟨h ds (by simp), fun ds' hm => h ds' (by simp [hm])⟩

/-- The extraction denotes the disjunction it claims. -/
theorem toDNF_correct [DecidableEq α] : ∀ (φ : NNF α) {ds : List (FairDisjunct α)}, toDNF φ = some ds →
    ∀ ξ : OmegaWord α, φ.satisfies ξ ↔ ∃ d ∈ ds, FairDisjunct.holds ξ d := by
  intro φ
  induction φ with
  | tt =>
    intro ds h ξ
    simp only [toDNF, Option.some.injEq] at h
    subst h
    simp only [satisfies_tt, List.mem_singleton, FairDisjunct.holds, true_iff]
    exact ⟨_, rfl, holds_top ξ, by simp⟩
  | ff =>
    intro ds h ξ
    simp only [toDNF, Option.some.injEq] at h
    subst h
    simp [satisfies_ff]
  | prop a => intro ds h; simp [toDNF] at h
  | nprop a => intro ds h; simp [toDNF] at h
  | next φ _ => intro ds h; simp [toDNF] at h
  | and φ ψ ihφ ihψ =>
    intro ds h ξ
    simp only [toDNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [satisfies_and, ihφ ha ξ, ihψ hb ξ]
    exact (holds_crossDNF ξ a b).symm
  | or φ ψ ihφ ihψ =>
    intro ds h ξ
    simp only [toDNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [satisfies_or, ihφ ha ξ, ihψ hb ξ]
    simp only [List.mem_append]
    grind
  | «until» φ ψ _ _ =>
    intro ds h ξ
    rw [toDNF] at h
    split at h
    · rename_i ht
      obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [eq_tt_of_isTop ht, asFGPart_eq hf]
      simp only [FairDisjunct.holds]
      constructor
      · intro hs
        exact ⟨(f, []), List.mem_singleton_self _, hs, by simp⟩
      · rintro ⟨d, hd, h1, -⟩
        rw [List.mem_singleton] at hd
        subst hd
        exact h1
    · exact absurd h (by simp)
  | release φ ψ _ _ =>
    intro ds h ξ
    rw [toDNF] at h
    split at h
    · rename_i hb
      obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [eq_ff_of_isBot hb, asGFPart_eq hg]
      simp only [FairDisjunct.holds]
      constructor
      · intro hs
        refine ⟨(.tt, [g]), List.mem_singleton_self _, holds_top ξ, fun g' hg' => ?_⟩
        rw [List.mem_singleton] at hg'
        subst hg'
        exact hs
      · rintro ⟨d, hd, -, h2⟩
        rw [List.mem_singleton] at hd
        subst hd
        exact h2 g (List.mem_singleton_self _)
    · exact absurd h (by simp)

/-- The fair normal form of `φ`, `none` when the flattening does not land in the fragment. -/
@[expose] def fnf [DecidableEq α] (φ : NNF α) : Option (List (FairDisjunct α)) :=
  (toDNF (gfPush φ)).map normalise

/-- [LSFZ16, Theorem 1]. A fairness is equivalent to the disjunction of its fair normal form. -/
theorem fnf_correct [DecidableEq α] {φ : NNF α} (hfair : φ.isFairness = true)
    {ds : List (FairDisjunct α)} (h : fnf φ = some ds) (ξ : OmegaWord α) :
    φ.satisfies ξ ↔ ∃ d ∈ ds, FairDisjunct.holds ξ d := by
  rw [fnf, Option.map_eq_some_iff] at h
  obtain ⟨ds', hds', rfl⟩ := h
  rw [holds_normalise, ← isFairness_alwaysEventually hfair ξ, ← gfPush_correct φ ξ]
  exact toDNF_correct (gfPush φ) hds' ξ

end NNF

end LTLLib
