/-
  The bottom-up rewrite pass: constant folding and idempotence, absorption under syntactic implication (`[SB00]` §3),
  `φ U e ≡ e` and `φ R u ≡ u` for a pure eventuality `e` and a purely universal `u` (`[EH00]` Lemma 3.4-3.5), `X γ ≡ γ`
  for an alternating `γ` (`[BKŘS12]` §4, whose `U`/`R`/`F`/`G` cases follow from `[EH00]`), and lifting an alternating
  conjunct out of `F`, `X`, `φ U`, or a disjunct out of `G`, `X`, `φ R` (`[BKŘS12]` Lemma 2). The `[SB00]` §3 shape
  rules close each node: `G F a ∨ G F b ≡ G F (a ∨ b)`, `F G a ∧ F G b ≡ F G (a ∧ b)`, `X` distributing out of `∧`,
  `∨`, `U`, `R`, `F X ≡ X F` and `G X ≡ X G`, while `X G F ≡ G F`, `X F G ≡ F G`, `F G F ≡ G F` and `G F G ≡ F G`
  already follow from the rules above. An alternating left operand of `U` or `R` moves to the top of a disjunction,
  `γ U b ≡ F b ∧ (b ∨ γ)` and `γ R ψ ≡ ψ ∧ (G ψ ∨ γ)` (the latter LTL3BA's `rewrite_V`).

  `G(φ ∧ ψ) ≡ Gφ ∧ Gψ` (`[BKŘS12]` §4) is applied only where it exposes an alternating conjunct, since unconditionally
  it duplicates `G` without shrinking anything. Every child is simplified before its parent's rules are tried, as in
  `[LTL2BA-1.3]`'s `bin_simpler`, and one pass reaches the rules' normal form since `collectAndFairness` and
  `collectOrFairness` walk a whole `∧`/`∨`-chain at once.

  Defines:
  - `simplifyAnd`, `simplifyOr`, `simplifyNext`, `simplifyUntil`, `simplifyRelease`: the rules at one node, operands
    already simplified
  - `untilLift`, `releaseLift`: the lifting and shape rules at a `U`/`R` node
  - `andShapes`, `orShapes`, `untilShapes`, `releaseShapes`: the shape rules at one node
  - `simplify`: one bottom-up pass of the rules

  Proves:
  - `until_of_isPureEventuality`, `release_of_isPurelyUniversal`: `[EH00]` Lemma 3.4, 3.5
  - `until_of_synImpl`: `[SB00]` §3, `φ ⇒ ψ` gives `φ U ψ ≡ ψ`
  - `until_and_of_prefixInvariant`, `release_or_of_prefixInvariant`, `always_and_of_prefixInvariant`: lifting a
    prefix-invariant conjunct or disjunct out of `U`, `R`, `G`
  - `until_left_prefixInvariant`, `release_left_prefixInvariant`: `γ U b ≡ F b ∧ (b ∨ γ)` and `γ R ψ ≡ ψ ∧ (G ψ ∨ γ)`
    for a prefix-invariant `γ`
  - `gf_or_gf`, `fg_and_fg`, `until_next_next`, `release_next_next`, `eventually_next`, `always_next`: the `[SB00]` §3
    shape rules
  - `satisfies_simplifyAnd`, `satisfies_simplifyOr`, `satisfies_simplifyNext`, `satisfies_simplifyUntil`,
    `satisfies_simplifyRelease`: every rule preserves the node's language
  - `simplify_correct`: the pass preserves every formula's language

  References:
  - `[SB00]` Somenzi, Bloem. Efficient Büchi Automata from LTL Formulae. CAV'00, §3.
  - `[EH00]` Etessami, Holzmann. Optimizing Büchi Automata. CONCUR'00, Lemma 3.
  - `[BKŘS12]` Babiak, Křetínský, Řehák, Strejček. LTL to Büchi Automata Translation: Fast and More
    Deterministic. TACAS'12, §4, Lemma 2.

  Sections:
  - The rules
  - The pass
  - Paper equivalences
  - Correctness of the rules
  - Correctness of the pass
-/
import LTLLib.TGBABased.LTLtoTGBA.Preprocess.Rules

namespace LTLLib

variable {α : Type u}

/-! ## The rules -/

/-- Shape rules at an `∧` node: `F G a ∧ F G b ≡ F G (a ∧ b)` and `X a ∧ X b ≡ X (a ∧ b)`. -/
def andShapes (a b : NNF α) : NNF α :=
  match a, b with
  | .until .tt (.release .ff a'), .until .tt (.release .ff b') => .until .tt (.release .ff (.and a' b'))
  | .next a', .next b' => .next (.and a' b')
  | _, _ => .and a b

/-- Shape rules at an `∨` node: `G F a ∨ G F b ≡ G F (a ∨ b)` and `X a ∨ X b ≡ X (a ∨ b)`. -/
def orShapes (a b : NNF α) : NNF α :=
  match a, b with
  | .release .ff (.until .tt a'), .release .ff (.until .tt b') => .release .ff (.until .tt (.or a' b'))
  | .next a', .next b' => .next (.or a' b')
  | _, _ => .or a b

/-- Shape rules at a `U` node: `X a U X b ≡ X (a U b)` and `F X b ≡ X F b`. -/
def untilShapes (a b : NNF α) : NNF α :=
  match a, b with
  | .next a', .next b' => .next (.until a' b')
  | .tt, .next b' => .next (.until .tt b')
  | _, _ => .until a b

/-- Shape rules at an `R` node: `X a R X b ≡ X (a R b)` and `G X b ≡ X G b`. -/
def releaseShapes (a b : NNF α) : NNF α :=
  match a, b with
  | .next a', .next b' => .next (.release a' b')
  | .ff, .next b' => .next (.release .ff b')
  | _, _ => .release a b

section Rules

variable [BEq α]

/-- `a ∧ b` with simplified operands: constants, idempotence, absorption under `synImpl`, shape rules. -/
def simplifyAnd (a b : NNF α) : NNF α :=
  if a.isBot || b.isBot then .ff
  else if a.isTop then b
  else if b.isTop then a
  else if a == b then a
  else if synImpl a b then a  -- a ∧ b ≡ a when a ⇒ b
  else if synImpl b a then b
  else andShapes a b

/-- `a ∨ b` with simplified operands: constants, idempotence, absorption under `synImpl`, shape rules. -/
def simplifyOr (a b : NNF α) : NNF α :=
  if a.isTop || b.isTop then .tt
  else if a.isBot then b
  else if b.isBot then a
  else if a == b then a
  else if synImpl a b then b  -- a ∨ b ≡ b when a ⇒ b
  else if synImpl b a then a
  else orShapes a b

end Rules

/-- `X a` with a simplified operand: constants, `X γ ≡ γ`, and lifting of alternating conjuncts or disjuncts. -/
def simplifyNext (a : NNF α) : NNF α :=
  if a.isTop then .tt
  else if a.isBot then .ff
  else if a.isFairness then a  -- X γ ≡ γ for an alternating γ
  else match collectAndFairness a with
    | (fs, rem) =>
      if !fs.isEmpty then
        match rem with
        | none => andAll fs
        | some r => .and (.next r) (andAll fs)  -- X(φ ∧ γ) ≡ Xφ ∧ γ
      else match collectOrFairness a with
        | (fs2, rem2) =>
          if fs2.isEmpty then .next a
          else match rem2 with
            | none => orAll fs2
            | some r => .or (.next r) (orAll fs2)  -- X(φ ∨ γ) ≡ Xφ ∨ γ

/-- Lifting of alternating conjuncts and the shape rules at `a U b`. -/
def untilLift (a b : NNF α) : NNF α :=
  match collectAndFairness b with
    | (fs, rem) =>
      if fs.isEmpty then untilShapes a b
      else match rem with
        | none => andAll fs
        -- φ U (ψ ∧ γ) ≡ (φ U ψ) ∧ γ, includes F(φ ∧ γ) ≡ Fφ ∧ γ at a = ⊤
        | some r => .and (if r.isPureEventuality then r else .until a r) (andAll fs)

/-- `a U b` with simplified operands: `φ U e ≡ e`, absorption under `synImpl`, an alternating left operand moved out,
then `untilLift`. -/
def simplifyUntil [BEq α] (a b : NNF α) : NNF α :=
  if b.isPureEventuality then b  -- φ U e ≡ e, includes F e ≡ e at a = ⊤
  else if synImpl a b then b  -- a U b ≡ b when a ⇒ b
  -- γ U b ≡ F b ∧ (b ∨ γ) for an alternating γ, which leaves γ at the top of a disjunction
  else if a.isFairness && !a.isTop && !a.isBot then simplifyAnd (untilLift .tt b) (simplifyOr b a)
  else untilLift a b

/-- Lifting of alternating disjuncts, and under `G` of alternating conjuncts, and the shape rules at `a R b`. -/
def releaseLift (a b : NNF α) : NNF α :=
  match collectOrFairness b with
    | (fs, rem) =>
      if !fs.isEmpty then
        match rem with
        | none => orAll fs
        -- φ R (ψ ∨ γ) ≡ (φ R ψ) ∨ γ, includes G(φ ∨ γ) ≡ Gφ ∨ γ at a = ⊥
        | some r => .or (if r.isPurelyUniversal then r else .release a r) (orAll fs)
      else if a.isBot then
        match collectAndFairness b with
        | (fs2, rem2) =>
          if fs2.isEmpty then releaseShapes a b
          else match rem2 with
            | none => andAll fs2
            -- G distributes over ∧ where it exposes an alternating conjunct: G(φ ∧ γ) ≡ Gφ ∧ γ
            | some r => .and (andAll fs2) (.release .ff r)
      else releaseShapes a b

/-- `a R b` with simplified operands: `φ R u ≡ u`, an alternating left operand moved out, then `releaseLift`. -/
def simplifyRelease [BEq α] (a b : NNF α) : NNF α :=
  if b.isPurelyUniversal then b  -- φ R u ≡ u, includes G u ≡ u at a = ⊥
  -- γ R ψ ≡ ψ ∧ (G ψ ∨ γ) for an alternating γ, LTL3BA's `rewrite_V`, which leaves γ at the top of a disjunction
  else if a.isFairness && !a.isTop && !a.isBot then simplifyAnd b (simplifyOr (releaseLift .ff b) a)
  else releaseLift a b

/-! ## The pass -/

/-- One bottom-up pass of the rules. -/
def simplify [BEq α] : NNF α → NNF α
  | .and a b => simplifyAnd (simplify a) (simplify b)
  | .or a b => simplifyOr (simplify a) (simplify b)
  | .next a => simplifyNext (simplify a)
  | .until a b => simplifyUntil (simplify a) (simplify b)
  | .release a b => simplifyRelease (simplify a) (simplify b)
  | φ => φ

/-! ## Paper equivalences -/

/-- `[EH00]` Lemma 3.4: `φ U e ≡ e` for a pure eventuality `e`. -/
theorem until_of_isPureEventuality (a : NNF α) {b : NNF α} (hb : b.isPureEventuality = true)
    (ξ : OmegaWord α) : (NNF.until a b).satisfies ξ ↔ b.satisfies ξ := by
  rw [NNF.satisfies_until]
  exact ⟨fun ⟨i, hi, _⟩ => NNF.isPureEventuality_sound b hb ξ i hi,
    fun h => ⟨0, by rwa [exec_drop_zero], fun j hj => absurd hj (Nat.not_lt_zero j)⟩⟩

/-- `[EH00]` Lemma 3.5: `φ R u ≡ u` for a purely universal `u`. -/
theorem release_of_isPurelyUniversal (a : NNF α) {b : NNF α} (hb : b.isPurelyUniversal = true)
    (ξ : OmegaWord α) : (NNF.release a b).satisfies ξ ↔ b.satisfies ξ := by
  rw [NNF.satisfies_release]
  refine ⟨fun h => ?_, fun h j => Or.inl (NNF.isPurelyUniversal_sound b hb ξ j h)⟩
  rcases h 0 with h0 | ⟨i, hi, -⟩
  · rwa [exec_drop_zero] at h0
  · exact absurd hi (Nat.not_lt_zero i)

/-- `[SB00]` §3: `φ ⇒ ψ` gives `φ U ψ ≡ ψ`. -/
theorem until_of_synImpl [BEq α] [LawfulBEq α] {a b : NNF α} (h : synImpl a b = true) (ξ : OmegaWord α) :
    (NNF.until a b).satisfies ξ ↔ b.satisfies ξ := by
  rw [NNF.satisfies_until]
  refine ⟨fun ⟨i, hi, hbefore⟩ => ?_, fun hb => ⟨0, by rwa [exec_drop_zero], fun j hj => absurd hj (Nat.not_lt_zero j)⟩⟩
  cases i with
  | zero => rwa [exec_drop_zero] at hi
  | succ i =>
    have h0 := hbefore 0 (Nat.succ_pos i)
    rw [exec_drop_zero] at h0
    exact synImpl_sound a b h ξ h0

/-- `φ U γ ≡ γ` for a prefix-invariant `γ`. -/
theorem until_of_prefixInvariant (a : NNF α) {γ : NNF α}
    (hγ : ∀ (ξ : OmegaWord α) (k : Nat), γ.satisfies (ξ.drop k) ↔ γ.satisfies ξ) (ξ : OmegaWord α) :
    (NNF.until a γ).satisfies ξ ↔ γ.satisfies ξ := by
  rw [NNF.satisfies_until]
  exact ⟨fun ⟨i, hi, _⟩ => (hγ ξ i).mp hi,
    fun h => ⟨0, by rwa [exec_drop_zero], fun j hj => absurd hj (Nat.not_lt_zero j)⟩⟩

/-- `φ U (ψ ∧ γ) ≡ (φ U ψ) ∧ γ` for a prefix-invariant `γ`. -/
theorem until_and_of_prefixInvariant (a r : NNF α) {γ : NNF α}
    (hγ : ∀ (ξ : OmegaWord α) (k : Nat), γ.satisfies (ξ.drop k) ↔ γ.satisfies ξ) (ξ : OmegaWord α) :
    (NNF.until a (NNF.and r γ)).satisfies ξ ↔ (NNF.until a r).satisfies ξ ∧ γ.satisfies ξ := by
  simp only [NNF.satisfies_until, NNF.satisfies_and]
  constructor
  · rintro ⟨i, ⟨hr, hg⟩, hbefore⟩
    exact ⟨⟨i, hr, hbefore⟩, (hγ ξ i).mp hg⟩
  · rintro ⟨⟨i, hr, hbefore⟩, hg⟩
    exact ⟨i, ⟨hr, (hγ ξ i).mpr hg⟩, hbefore⟩

/-- `φ R γ ≡ γ` for a prefix-invariant `γ`. -/
theorem release_of_prefixInvariant (a : NNF α) {γ : NNF α}
    (hγ : ∀ (ξ : OmegaWord α) (k : Nat), γ.satisfies (ξ.drop k) ↔ γ.satisfies ξ) (ξ : OmegaWord α) :
    (NNF.release a γ).satisfies ξ ↔ γ.satisfies ξ := by
  rw [NNF.satisfies_release]
  refine ⟨fun h => ?_, fun h j => Or.inl ((hγ ξ j).mpr h)⟩
  rcases h 0 with h0 | ⟨i, hi, -⟩
  · rwa [exec_drop_zero] at h0
  · exact absurd hi (Nat.not_lt_zero i)

/-- `φ R (ψ ∨ γ) ≡ (φ R ψ) ∨ γ` for a prefix-invariant `γ`. -/
theorem release_or_of_prefixInvariant (a r : NNF α) {γ : NNF α}
    (hγ : ∀ (ξ : OmegaWord α) (k : Nat), γ.satisfies (ξ.drop k) ↔ γ.satisfies ξ) (ξ : OmegaWord α) :
    (NNF.release a (NNF.or r γ)).satisfies ξ ↔ (NNF.release a r).satisfies ξ ∨ γ.satisfies ξ := by
  simp only [NNF.satisfies_release, NNF.satisfies_or]
  constructor
  · intro h
    by_cases hg : γ.satisfies ξ
    · exact Or.inr hg
    · refine Or.inl fun j => ?_
      rcases h j with (hr | hg') | hb
      · exact Or.inl hr
      · exact absurd ((hγ ξ j).mp hg') hg
      · exact Or.inr hb
  · rintro (h | hg) j
    · rcases h j with hr | hb
      · exact Or.inl (Or.inl hr)
      · exact Or.inr hb
    · exact Or.inl (Or.inr ((hγ ξ j).mpr hg))

/-- `γ U b ≡ F b ∧ (b ∨ γ)` for a prefix-invariant `γ`. -/
theorem until_left_prefixInvariant (b : NNF α) {γ : NNF α}
    (hγ : ∀ (ξ : OmegaWord α) (k : Nat), γ.satisfies (ξ.drop k) ↔ γ.satisfies ξ) (ξ : OmegaWord α) :
    (NNF.until γ b).satisfies ξ ↔ (NNF.until .tt b).satisfies ξ ∧ (NNF.or b γ).satisfies ξ := by
  simp only [NNF.satisfies_until, NNF.satisfies_or, NNF.satisfies_tt]
  constructor
  · rintro ⟨i, hb, hbefore⟩
    refine ⟨⟨i, hb, fun _ _ => trivial⟩, ?_⟩
    cases i with
    | zero => left; rwa [exec_drop_zero] at hb
    | succ i =>
      right
      have h0 := hbefore 0 (Nat.succ_pos i)
      rwa [exec_drop_zero] at h0
  · rintro ⟨⟨i, hb, -⟩, hb0 | hg⟩
    · exact ⟨0, by rwa [exec_drop_zero], fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · exact ⟨i, hb, fun j _ => (hγ ξ j).mpr hg⟩

/-- `γ R ψ ≡ ψ ∧ (G ψ ∨ γ)` for a prefix-invariant `γ`. -/
theorem release_left_prefixInvariant (b : NNF α) {γ : NNF α}
    (hγ : ∀ (ξ : OmegaWord α) (k : Nat), γ.satisfies (ξ.drop k) ↔ γ.satisfies ξ) (ξ : OmegaWord α) :
    (NNF.release γ b).satisfies ξ ↔ b.satisfies ξ ∧ (NNF.or (NNF.release .ff b) γ).satisfies ξ := by
  simp only [NNF.satisfies_release, NNF.satisfies_or, NNF.satisfies_ff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rcases h 0 with h0 | ⟨i, hi, -⟩
      · rwa [exec_drop_zero] at h0
      · exact absurd hi (Nat.not_lt_zero i)
    · by_cases hg : γ.satisfies ξ
      · exact Or.inr hg
      · refine Or.inl fun j => Or.inl ?_
        rcases h j with hb | ⟨i, -, hgi⟩
        · exact hb
        · exact absurd ((hγ ξ i).mp hgi) hg
  · rintro ⟨hb0, hG | hg⟩ j
    · rcases hG j with hb | ⟨_, _, hf⟩
      · exact Or.inl hb
      · exact hf.elim
    · cases j with
      | zero => exact Or.inl (by rwa [exec_drop_zero])
      | succ j => exact Or.inr ⟨0, Nat.succ_pos j, (hγ ξ 0).mpr hg⟩

/-- `G(ψ ∧ γ) ≡ Gψ ∧ γ` for a prefix-invariant `γ`. -/
theorem always_and_of_prefixInvariant (r : NNF α) {γ : NNF α}
    (hγ : ∀ (ξ : OmegaWord α) (k : Nat), γ.satisfies (ξ.drop k) ↔ γ.satisfies ξ) (ξ : OmegaWord α) :
    (NNF.release .ff (NNF.and r γ)).satisfies ξ ↔ (NNF.release .ff r).satisfies ξ ∧ γ.satisfies ξ := by
  simp only [NNF.satisfies_release, NNF.satisfies_and, NNF.satisfies_ff]
  constructor
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · rcases h j with ⟨hr, -⟩ | ⟨_, _, hf⟩
      · exact Or.inl hr
      · exact hf.elim
    · rcases h 0 with ⟨-, hg⟩ | ⟨_, _, hf⟩
      · rwa [exec_drop_zero] at hg
      · exact hf.elim
  · rintro ⟨h, hg⟩ j
    rcases h j with hr | ⟨_, _, hf⟩
    · exact Or.inl ⟨hr, (hγ ξ j).mpr hg⟩
    · exact hf.elim

/-- A conjunction of alternating formulas is prefix invariant. -/
theorem andAll_prefixInvariant {fs : List (NNF α)} (hfs : ∀ f ∈ fs, f.isFairness = true)
    (ξ : OmegaWord α) (k : Nat) : (andAll fs).satisfies (ξ.drop k) ↔ (andAll fs).satisfies ξ := by
  rw [satisfies_andAll, satisfies_andAll]
  exact forall₂_congr fun f hf => satisfies_drop_of_isFairness (hfs f hf) ξ k

/-- A disjunction of alternating formulas is prefix invariant. -/
theorem orAll_prefixInvariant {fs : List (NNF α)} (hfs : ∀ f ∈ fs, f.isFairness = true)
    (ξ : OmegaWord α) (k : Nat) : (orAll fs).satisfies (ξ.drop k) ↔ (orAll fs).satisfies ξ := by
  rw [satisfies_orAll, satisfies_orAll]
  exact exists_congr fun f => and_congr_right fun hf => satisfies_drop_of_isFairness (hfs f hf) ξ k

/-- `[SB00]` §3: `F G a ∧ F G b ≡ F G (a ∧ b)`. -/
theorem fg_and_fg (a b : NNF α) (ξ : OmegaWord α) :
    (NNF.eventually (NNF.always (NNF.and a b))).satisfies ξ ↔
      (NNF.eventually (NNF.always a)).satisfies ξ ∧ (NNF.eventually (NNF.always b)).satisfies ξ := by
  simp only [NNF.satisfies_eventually, NNF.satisfies_always, NNF.satisfies_and, Lentil.exec.drop_drop]
  constructor
  · rintro ⟨i, h⟩
    exact ⟨⟨i, fun k => (h k).1⟩, ⟨i, fun k => (h k).2⟩⟩
  · rintro ⟨⟨i, ha⟩, ⟨j, hb⟩⟩
    refine ⟨i + j, fun k => ⟨?_, ?_⟩⟩
    · have h := ha (j + k)
      rwa [show i + (j + k) = i + j + k by omega] at h
    · have h := hb (i + k)
      rwa [show j + (i + k) = i + j + k by omega] at h

/-- `[SB00]` §3: `G F a ∨ G F b ≡ G F (a ∨ b)`. -/
theorem gf_or_gf (a b : NNF α) (ξ : OmegaWord α) :
    (NNF.always (NNF.eventually (NNF.or a b))).satisfies ξ ↔
      (NNF.always (NNF.eventually a)).satisfies ξ ∨ (NNF.always (NNF.eventually b)).satisfies ξ := by
  simp only [NNF.satisfies_eventually, NNF.satisfies_always, NNF.satisfies_or, Lentil.exec.drop_drop]
  constructor
  · intro h
    by_cases ha : ∀ k, ∃ m, a.satisfies (ξ.drop (k + m))
    · exact Or.inl ha
    · -- `a` stops holding from some `i` on, so every later witness of `a ∨ b` is one of `b`
      obtain ⟨i, hi⟩ := Classical.not_forall.mp ha
      refine Or.inr fun k => ?_
      obtain ⟨m, hm⟩ := h (i + k)
      rcases hm with hm | hm
      · exact absurd ⟨k + m, by rwa [show i + (k + m) = i + k + m by omega]⟩ hi
      · exact ⟨i + m, by rwa [show k + (i + m) = i + k + m by omega]⟩
  · rintro (h | h) k
    · obtain ⟨m, hm⟩ := h k
      exact ⟨m, Or.inl hm⟩
    · obtain ⟨m, hm⟩ := h k
      exact ⟨m, Or.inr hm⟩

/-- `[SB00]` §3: `X a U X b ≡ X (a U b)`. -/
theorem until_next_next (a b : NNF α) (ξ : OmegaWord α) :
    (NNF.until (.next a) (.next b)).satisfies ξ ↔ (NNF.next (NNF.until a b)).satisfies ξ := by
  simp only [NNF.satisfies_until, NNF.satisfies_next, Lentil.exec.drop_drop, Nat.add_comm]

/-- `[SB00]` §3: `F X b ≡ X F b`. -/
theorem eventually_next (b : NNF α) (ξ : OmegaWord α) :
    (NNF.until .tt (.next b)).satisfies ξ ↔ (NNF.next (NNF.until .tt b)).satisfies ξ := by
  simp only [NNF.satisfies_until, NNF.satisfies_next, NNF.satisfies_tt, Lentil.exec.drop_drop, Nat.add_comm]

/-- `[SB00]` §3: `X a R X b ≡ X (a R b)`. -/
theorem release_next_next (a b : NNF α) (ξ : OmegaWord α) :
    (NNF.release (.next a) (.next b)).satisfies ξ ↔ (NNF.next (NNF.release a b)).satisfies ξ := by
  simp only [NNF.satisfies_release, NNF.satisfies_next, Lentil.exec.drop_drop, Nat.add_comm]

/-- `[SB00]` §3: `G X b ≡ X G b`. -/
theorem always_next (b : NNF α) (ξ : OmegaWord α) :
    (NNF.release .ff (.next b)).satisfies ξ ↔ (NNF.next (NNF.release .ff b)).satisfies ξ := by
  simp only [NNF.satisfies_release, NNF.satisfies_next, NNF.satisfies_ff, Lentil.exec.drop_drop, Nat.add_comm]

theorem satisfies_andShapes (a b : NNF α) (ξ : OmegaWord α) :
    (andShapes a b).satisfies ξ ↔ a.satisfies ξ ∧ b.satisfies ξ := by
  unfold andShapes
  split
  · exact fg_and_fg _ _ ξ
  · exact Iff.rfl
  · exact Iff.rfl

theorem satisfies_orShapes (a b : NNF α) (ξ : OmegaWord α) :
    (orShapes a b).satisfies ξ ↔ a.satisfies ξ ∨ b.satisfies ξ := by
  unfold orShapes
  split
  · exact gf_or_gf _ _ ξ
  · exact Iff.rfl
  · exact Iff.rfl

theorem satisfies_untilShapes (a b : NNF α) (ξ : OmegaWord α) :
    (untilShapes a b).satisfies ξ ↔ (NNF.until a b).satisfies ξ := by
  unfold untilShapes
  split
  · exact (until_next_next _ _ ξ).symm
  · exact (eventually_next _ ξ).symm
  · exact Iff.rfl

theorem satisfies_releaseShapes (a b : NNF α) (ξ : OmegaWord α) :
    (releaseShapes a b).satisfies ξ ↔ (NNF.release a b).satisfies ξ := by
  unfold releaseShapes
  split
  · exact (release_next_next _ _ ξ).symm
  · exact (always_next _ ξ).symm
  · exact Iff.rfl

/-! ## Correctness of the rules -/

/-- A `∧`-chain is the conjunction of its alternating leaves and its remainder. -/
private theorem satisfies_of_collectAnd {b : NNF α} {fs : List (NNF α)} {rem : Option (NNF α)}
    (hc : collectAndFairness b = (fs, rem)) (ξ : OmegaWord α) :
    b.satisfies ξ ↔ (andAll fs).satisfies ξ ∧ ∀ r ∈ rem, r.satisfies ξ := by
  have h := (collectAndFairness_spec b).2 ξ
  rw [hc] at h
  rw [h, satisfies_andAll]

/-- A `∨`-chain is the disjunction of its alternating leaves and its remainder. -/
private theorem satisfies_of_collectOr {b : NNF α} {fs : List (NNF α)} {rem : Option (NNF α)}
    (hc : collectOrFairness b = (fs, rem)) (ξ : OmegaWord α) :
    b.satisfies ξ ↔ (orAll fs).satisfies ξ ∨ ∃ r ∈ rem, r.satisfies ξ := by
  have h := (collectOrFairness_spec b).2 ξ
  rw [hc] at h
  rw [h, satisfies_orAll]

section Lawful

variable [BEq α] [LawfulBEq α]

theorem satisfies_simplifyAnd (a b : NNF α) (ξ : OmegaWord α) :
    (simplifyAnd a b).satisfies ξ ↔ a.satisfies ξ ∧ b.satisfies ξ := by
  unfold simplifyAnd
  split
  next h =>
    rcases Bool.or_eq_true _ _ |>.mp h with h | h
    · rw [NNF.eq_ff_of_isBot h]; simp [NNF.satisfies_ff]
    · rw [NNF.eq_ff_of_isBot h]; simp [NNF.satisfies_ff]
  next =>
    split
    next h => rw [NNF.eq_tt_of_isTop h]; simp [NNF.satisfies_tt]
    next =>
      split
      next h => rw [NNF.eq_tt_of_isTop h]; simp [NNF.satisfies_tt]
      next =>
        split
        next h => rw [beq_iff_eq.mp h]; simp
        next =>
          split
          next h => exact ⟨fun ha => ⟨ha, synImpl_sound a b h ξ ha⟩, fun h => h.1⟩
          next =>
            split
            next h => exact ⟨fun hb => ⟨synImpl_sound b a h ξ hb, hb⟩, fun h => h.2⟩
            next => exact satisfies_andShapes a b ξ

theorem satisfies_simplifyOr (a b : NNF α) (ξ : OmegaWord α) :
    (simplifyOr a b).satisfies ξ ↔ a.satisfies ξ ∨ b.satisfies ξ := by
  unfold simplifyOr
  split
  next h =>
    rcases Bool.or_eq_true _ _ |>.mp h with h | h
    · rw [NNF.eq_tt_of_isTop h]; simp [NNF.satisfies_tt]
    · rw [NNF.eq_tt_of_isTop h]; simp [NNF.satisfies_tt]
  next =>
    split
    next h => rw [NNF.eq_ff_of_isBot h]; simp [NNF.satisfies_ff]
    next =>
      split
      next h => rw [NNF.eq_ff_of_isBot h]; simp [NNF.satisfies_ff]
      next =>
        split
        next h => rw [beq_iff_eq.mp h]; simp
        next =>
          split
          next h => exact ⟨Or.inr, fun h' => h'.elim (synImpl_sound a b h ξ) id⟩
          next =>
            split
            next h => exact ⟨Or.inl, fun h' => h'.elim id (synImpl_sound b a h ξ)⟩
            next => exact satisfies_orShapes a b ξ

end Lawful

theorem satisfies_simplifyNext (a : NNF α) (ξ : OmegaWord α) :
    (simplifyNext a).satisfies ξ ↔ a.satisfies (ξ.drop 1) := by
  unfold simplifyNext
  split
  next h => rw [NNF.eq_tt_of_isTop h]; simp [NNF.satisfies_tt]
  next =>
    split
    next h => rw [NNF.eq_ff_of_isBot h]; simp [NNF.satisfies_ff]
    next =>
      split
      next h => exact (satisfies_drop_of_isFairness h ξ 1).symm
      next =>
        rcases hc : collectAndFairness a with ⟨fs, rem⟩
        have hfs := (collectAndFairness_spec a).1
        rw [hc] at hfs
        dsimp only
        split
        next hne =>
          rw [satisfies_of_collectAnd hc (ξ.drop 1), andAll_prefixInvariant hfs ξ 1]
          cases rem with
          | none => simp
          | some r => rw [NNF.satisfies_and, NNF.satisfies_next]; simp [and_comm]
        next =>
          rcases hc2 : collectOrFairness a with ⟨fs2, rem2⟩
          have hfs2 := (collectOrFairness_spec a).1
          rw [hc2] at hfs2
          dsimp only
          split
          next => exact NNF.satisfies_next ξ a
          next =>
            rw [satisfies_of_collectOr hc2 (ξ.drop 1), orAll_prefixInvariant hfs2 ξ 1]
            cases rem2 with
            | none => simp
            | some r => rw [NNF.satisfies_or, NNF.satisfies_next]; simp [or_comm]

theorem satisfies_untilLift (a b : NNF α) (ξ : OmegaWord α) :
    (untilLift a b).satisfies ξ ↔ (NNF.until a b).satisfies ξ := by
  unfold untilLift
  rcases hc : collectAndFairness b with ⟨fs, rem⟩
  have hfs := (collectAndFairness_spec b).1
  rw [hc] at hfs
  dsimp only
  split
  next => exact satisfies_untilShapes a b ξ
  next =>
    -- `b ≡ r ∧ γ` pointwise, `γ := andAll fs` prefix invariant, so the `γ` part lifts out of the `U`
    have hγ := andAll_prefixInvariant hfs
    have hb : ∀ ξ', b.satisfies ξ' ↔ (andAll fs).satisfies ξ' ∧ ∀ r ∈ rem, r.satisfies ξ' :=
      fun ξ' => satisfies_of_collectAnd hc ξ'
    cases rem with
    | none =>
      simp only [Option.not_mem_none, false_imp_iff, implies_true, and_true] at hb
      rw [show (NNF.until a b).satisfies ξ ↔ (NNF.until a (andAll fs)).satisfies ξ by
        simp only [NNF.satisfies_until, hb]]
      exact (until_of_prefixInvariant a hγ ξ).symm
    | some r =>
      simp only [Option.mem_def, Option.some.injEq, forall_eq'] at hb
      rw [show (NNF.until a b).satisfies ξ ↔ (NNF.until a (NNF.and r (andAll fs))).satisfies ξ by
        simp only [NNF.satisfies_until, NNF.satisfies_and, hb, and_comm],
        until_and_of_prefixInvariant a r hγ ξ, NNF.satisfies_and]
      split
      next hr => rw [until_of_isPureEventuality a hr ξ]
      next => rfl

theorem satisfies_simplifyUntil [BEq α] [LawfulBEq α] (a b : NNF α) (ξ : OmegaWord α) :
    (simplifyUntil a b).satisfies ξ ↔ (NNF.until a b).satisfies ξ := by
  unfold simplifyUntil
  split
  next h => exact (until_of_isPureEventuality a h ξ).symm
  next =>
    split
    next h => exact (until_of_synImpl h ξ).symm
    next =>
      split
      next hfair =>
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfair
        rw [satisfies_simplifyAnd, satisfies_untilLift, satisfies_simplifyOr,
          until_left_prefixInvariant b (satisfies_drop_of_isFairness hfair.1.1) ξ, NNF.satisfies_or]
      next => exact satisfies_untilLift a b ξ

theorem satisfies_releaseLift (a b : NNF α) (ξ : OmegaWord α) :
    (releaseLift a b).satisfies ξ ↔ (NNF.release a b).satisfies ξ := by
  unfold releaseLift
  rcases hc : collectOrFairness b with ⟨fs, rem⟩
  have hfs := (collectOrFairness_spec b).1
  rw [hc] at hfs
  dsimp only
  split
  next hne =>
    -- `b ≡ r ∨ δ` pointwise, `δ := orAll fs` prefix invariant, so the `δ` part lifts out of the `R`
    have hδ := orAll_prefixInvariant hfs
    have hb : ∀ ξ', b.satisfies ξ' ↔ (orAll fs).satisfies ξ' ∨ ∃ r ∈ rem, r.satisfies ξ' :=
      fun ξ' => satisfies_of_collectOr hc ξ'
    cases rem with
    | none =>
      simp only [Option.not_mem_none, false_and, exists_false, or_false] at hb
      rw [show (NNF.release a b).satisfies ξ ↔ (NNF.release a (orAll fs)).satisfies ξ by
        simp only [NNF.satisfies_release, hb]]
      exact (release_of_prefixInvariant a hδ ξ).symm
    | some r =>
      simp only [Option.mem_def, Option.some.injEq, exists_eq_left'] at hb
      rw [show (NNF.release a b).satisfies ξ ↔ (NNF.release a (NNF.or r (orAll fs))).satisfies ξ by
        simp only [NNF.satisfies_release, NNF.satisfies_or, hb, or_comm],
        release_or_of_prefixInvariant a r hδ ξ, NNF.satisfies_or]
      split
      next hr => rw [release_of_isPurelyUniversal a hr ξ]
      next => rfl
  next =>
    split
    next hbot =>
      rcases hc2 : collectAndFairness b with ⟨fs2, rem2⟩
      have hfs2 := (collectAndFairness_spec b).1
      rw [hc2] at hfs2
      dsimp only
      rw [NNF.eq_ff_of_isBot hbot]
      split
      next => exact satisfies_releaseShapes .ff b ξ
      next =>
        have hγ := andAll_prefixInvariant hfs2
        have hb : ∀ ξ', b.satisfies ξ' ↔ (andAll fs2).satisfies ξ' ∧ ∀ r ∈ rem2, r.satisfies ξ' :=
          fun ξ' => satisfies_of_collectAnd hc2 ξ'
        cases rem2 with
        | none =>
          simp only [Option.not_mem_none, false_imp_iff, implies_true, and_true] at hb
          rw [show (NNF.release .ff b).satisfies ξ ↔ (NNF.release .ff (andAll fs2)).satisfies ξ by
            simp only [NNF.satisfies_release, hb]]
          exact (release_of_prefixInvariant .ff hγ ξ).symm
        | some r =>
          simp only [Option.mem_def, Option.some.injEq, forall_eq'] at hb
          rw [show (NNF.release .ff b).satisfies ξ ↔ (NNF.release .ff (NNF.and r (andAll fs2))).satisfies ξ by
            simp only [NNF.satisfies_release, NNF.satisfies_and, hb, and_comm],
            always_and_of_prefixInvariant r hγ ξ, NNF.satisfies_and, and_comm]
    next => exact satisfies_releaseShapes a b ξ

theorem satisfies_simplifyRelease [BEq α] [LawfulBEq α] (a b : NNF α) (ξ : OmegaWord α) :
    (simplifyRelease a b).satisfies ξ ↔ (NNF.release a b).satisfies ξ := by
  unfold simplifyRelease
  split
  next h => exact (release_of_isPurelyUniversal a h ξ).symm
  next =>
    split
    next hfair =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfair
      rw [satisfies_simplifyAnd, satisfies_simplifyOr, satisfies_releaseLift,
        release_left_prefixInvariant b (satisfies_drop_of_isFairness hfair.1.1) ξ, NNF.satisfies_or]
    next => exact satisfies_releaseLift a b ξ

/-! ## Correctness of the pass -/

/-- The rewrite pass preserves every formula's language. -/
theorem simplify_correct [BEq α] [LawfulBEq α] (φ : NNF α) (ξ : OmegaWord α) :
    (simplify φ).satisfies ξ ↔ φ.satisfies ξ := by
  induction φ generalizing ξ with
  | and a b iha ihb => rw [simplify, satisfies_simplifyAnd, iha, ihb, NNF.satisfies_and]
  | or a b iha ihb => rw [simplify, satisfies_simplifyOr, iha, ihb, NNF.satisfies_or]
  | next a iha => rw [simplify, satisfies_simplifyNext, iha, NNF.satisfies_next]
  | «until» a b iha ihb =>
    rw [simplify, satisfies_simplifyUntil]
    simp only [NNF.satisfies_until, iha, ihb]
  | «release» a b iha ihb =>
    rw [simplify, satisfies_simplifyRelease]
    simp only [NNF.satisfies_release, iha, ihb]
  | tt => rfl
  | ff => rfl
  | prop _ => rfl
  | nprop _ => rfl

end LTLLib
