/-
  Syntactic implication between NNF formulas: `[SB00]` §3's relation with duals, case for case `[LTL2BA-1.3]`'s
  `implies`, plus `[BKŘS12]` §4's three `X`-rules. The equality test is plain structural equality rather than
  `[LTL2BA-1.3]`'s associativity-commutativity-aware `sameform`, a sound but weaker approximation.

  Defines:
  - `NNF.size`: node count, the termination measure
  - `isG`, `isF`: the syntactic shapes `ff R ψ` and `tt U ψ`
  - `synImpl`: syntactic implication

  Proves:
  - `synImpl_sound`: a syntactic implication is a semantic one

  References:
  - `[SB00]` Somenzi, Bloem. Efficient Büchi Automata from LTL Formulae. CAV'00, §3.
  - `[BKŘS12]` Babiak, Křetínský, Řehák, Strejček. LTL to Büchi Automata Translation: Fast and More
    Deterministic. TACAS'12, §4.

  Sections:
  - Node count
  - Syntactic shapes
  - Syntactic implication
  - Soundness
-/
import LTLLib.LTL.FairClass

namespace LTLLib

variable {α : Type u}

/-! ## Node count -/

/-- Node count, `synImpl`'s termination measure (`sizeOf` is proof-only, not compiled). -/
def NNF.size : NNF α → Nat
  | .tt | .ff | .prop _ | .nprop _ => 1
  | .next φ => φ.size + 1
  | .and φ ψ | .or φ ψ | .until φ ψ | .release φ ψ => φ.size + ψ.size + 1

/-! ## Syntactic shapes -/

/-- `ψ` is syntactically `G ψ' = ff R ψ'`. -/
def NNF.isG : NNF α → Bool
  | .release .ff _ => true
  | _ => false

/-- `ψ` is syntactically `F ψ' = tt U ψ'`. -/
def NNF.isF : NNF α → Bool
  | .until .tt _ => true
  | _ => false

theorem NNF.eq_of_isG {φ : NNF α} (h : φ.isG = true) : ∃ ψ, φ = .release .ff ψ := by
  unfold NNF.isG at h
  split at h
  · exact ⟨_, rfl⟩
  · exact absurd h (by simp)

theorem NNF.eq_of_isF {φ : NNF α} (h : φ.isF = true) : ∃ ψ, φ = .until .tt ψ := by
  unfold NNF.isF at h
  split at h
  · exact ⟨_, rfl⟩
  · exact absurd h (by simp)

/-! ## Syntactic implication -/

variable [BEq α]

/-- `a` syntactically implies `b`. -/
def synImpl (a b : NNF α) : Bool :=
  a == b ||
  NNF.isTop b ||
  NNF.isBot a ||
  (match b with | .and b1 b2 => synImpl a b1 && synImpl a b2 | _ => false) ||
  (match a with | .or a1 a2 => synImpl a1 b && synImpl a2 b | _ => false) ||
  (match a with | .and a1 a2 => synImpl a1 b || synImpl a2 b | _ => false) ||
  (match b with | .or b1 b2 => synImpl a b1 || synImpl a b2 | _ => false) ||
  (match b with | .until _ b2 => synImpl a b2 | _ => false) ||
  (match a with | .release _ a2 => synImpl a2 b | _ => false) ||
  (match a with | .until a1 a2 => synImpl a1 b && synImpl a2 b | _ => false) ||
  (match b with | .release b1 b2 => synImpl a b1 && synImpl a b2 | _ => false) ||
  (match a, b with
    | .until a1 a2, .until b1 b2 => synImpl a1 b1 && synImpl a2 b2
    | .release a1 a2, .release b1 b2 => synImpl a1 b1 && synImpl a2 b2
    | _, _ => false) ||
  (match b with | .next b1 => a.isG && synImpl a b1 | _ => false) ||
  (match a with | .next a1 => b.isF && synImpl a1 b | _ => false) ||
  (match a, b with | .next a1, .next b1 => synImpl a1 b1 | _, _ => false)
termination_by a.size + b.size
decreasing_by all_goals simp_all [NNF.size] <;> omega

/-! ## Soundness -/

section Soundness

variable [LawfulBEq α]

/-- `[SB00]` §3, `[BKŘS12]` §4: whenever `a` syntactically implies `b`, every word satisfying `a` satisfies `b`. -/
theorem synImpl_sound (a b : NNF α) (h : synImpl a b = true) (ξ : OmegaWord α) (ha : a.satisfies ξ) :
    b.satisfies ξ := by
  unfold synImpl at h
  simp only [Bool.or_eq_true, or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [← beq_iff_eq.mp h]; exact ha
  · rw [NNF.eq_tt_of_isTop h]; exact (NNF.satisfies_tt ξ).mpr trivial
  · rw [NNF.eq_ff_of_isBot h] at ha; exact ha.elim
  · -- b = b1 ∧ b2, a implies both
    split at h
    · rename_i b1 b2
      simp only [Bool.and_eq_true] at h
      exact (NNF.satisfies_and ξ b1 b2).mpr ⟨synImpl_sound a b1 h.1 ξ ha, synImpl_sound a b2 h.2 ξ ha⟩
    · exact absurd h (by simp)
  · -- a = a1 ∨ a2, both imply b
    split at h
    · rename_i a1 a2
      simp only [Bool.and_eq_true] at h
      rcases (NNF.satisfies_or ξ a1 a2).mp ha with ha | ha
      · exact synImpl_sound a1 b h.1 ξ ha
      · exact synImpl_sound a2 b h.2 ξ ha
    · exact absurd h (by simp)
  · -- a = a1 ∧ a2, one implies b
    split at h
    · rename_i a1 a2
      have ha' := (NNF.satisfies_and ξ a1 a2).mp ha
      rcases Bool.or_eq_true _ _ |>.mp h with h | h
      · exact synImpl_sound a1 b h ξ ha'.1
      · exact synImpl_sound a2 b h ξ ha'.2
    · exact absurd h (by simp)
  · -- b = b1 ∨ b2, a implies one
    split at h
    · rename_i b1 b2
      rcases Bool.or_eq_true _ _ |>.mp h with h | h
      · exact (NNF.satisfies_or ξ b1 b2).mpr (Or.inl (synImpl_sound a b1 h ξ ha))
      · exact (NNF.satisfies_or ξ b1 b2).mpr (Or.inr (synImpl_sound a b2 h ξ ha))
    · exact absurd h (by simp)
  · -- b = b1 U b2, a implies b2, the witness is position 0
    split at h
    · rename_i b1 b2
      refine (NNF.satisfies_until ξ b1 b2).mpr ⟨0, ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      rw [exec_drop_zero]
      exact synImpl_sound a b2 h ξ ha
    · exact absurd h (by simp)
  · -- a = a1 R a2, a2 implies b, a2 holds at position 0
    split at h
    · rename_i a1 a2
      have ha2 : a2.satisfies ξ := by
        rcases (NNF.satisfies_release ξ a1 a2).mp ha 0 with h0 | ⟨i, hi, -⟩
        · rwa [exec_drop_zero] at h0
        · exact absurd hi (Nat.not_lt_zero i)
      exact synImpl_sound a2 b h ξ ha2
    · exact absurd h (by simp)
  · -- a = a1 U a2, both imply b, whichever holds at position 0
    split at h
    · rename_i a1 a2
      simp only [Bool.and_eq_true] at h
      obtain ⟨i, hi, hbefore⟩ := (NNF.satisfies_until ξ a1 a2).mp ha
      cases i with
      | zero => rw [exec_drop_zero] at hi; exact synImpl_sound a2 b h.2 ξ hi
      | succ i =>
        have h0 := hbefore 0 (Nat.succ_pos i)
        rw [exec_drop_zero] at h0
        exact synImpl_sound a1 b h.1 ξ h0
    · exact absurd h (by simp)
  · -- b = b1 R b2, a implies both, b2 holds at 0 and b1 releases it from there
    split at h
    · rename_i b1 b2
      simp only [Bool.and_eq_true] at h
      refine (NNF.satisfies_release ξ b1 b2).mpr fun j => ?_
      cases j with
      | zero => exact Or.inl (by rw [exec_drop_zero]; exact synImpl_sound a b2 h.2 ξ ha)
      | succ j => exact Or.inr ⟨0, Nat.succ_pos j, by rw [exec_drop_zero]; exact synImpl_sound a b1 h.1 ξ ha⟩
    · exact absurd h (by simp)
  · -- U against U, R against R, componentwise at every suffix
    split at h
    · rename_i a1 a2 b1 b2
      simp only [Bool.and_eq_true] at h
      obtain ⟨i, hi, hbefore⟩ := (NNF.satisfies_until ξ a1 a2).mp ha
      exact (NNF.satisfies_until ξ b1 b2).mpr ⟨i, synImpl_sound a2 b2 h.2 _ hi,
        fun j hj => synImpl_sound a1 b1 h.1 _ (hbefore j hj)⟩
    · rename_i a1 a2 b1 b2
      simp only [Bool.and_eq_true] at h
      refine (NNF.satisfies_release ξ b1 b2).mpr fun j => ?_
      rcases (NNF.satisfies_release ξ a1 a2).mp ha j with h2 | ⟨i, hi, h1⟩
      · exact Or.inl (synImpl_sound a2 b2 h.2 _ h2)
      · exact Or.inr ⟨i, hi, synImpl_sound a1 b1 h.1 _ h1⟩
    · exact absurd h (by simp)
  · -- b = X b1 and a = G a', which holds one step later too
    split at h
    · rename_i b1
      simp only [Bool.and_eq_true] at h
      obtain ⟨a', rfl⟩ := NNF.eq_of_isG h.1
      refine (NNF.satisfies_next ξ b1).mpr (synImpl_sound _ b1 h.2 _ ?_)
      refine (NNF.satisfies_release _ .ff a').mpr fun j => Or.inl ?_
      rcases (NNF.satisfies_release ξ .ff a').mp ha (1 + j) with h2 | ⟨i, -, hff⟩
      · rwa [Lentil.exec.drop_drop]
      · exact hff.elim
    · exact absurd h (by simp)
  · -- a = X a1 and b = F b', which a1's implication one step later witnesses
    split at h
    · rename_i a1
      simp only [Bool.and_eq_true] at h
      obtain ⟨b', rfl⟩ := NNF.eq_of_isF h.1
      have h1 := synImpl_sound a1 _ h.2 _ ((NNF.satisfies_next ξ a1).mp ha)
      obtain ⟨i, hi, -⟩ := (NNF.satisfies_until _ .tt b').mp h1
      refine (NNF.satisfies_until ξ .tt b').mpr ⟨1 + i, by rw [Lentil.exec.drop_drop] at hi; exact hi, fun _ _ => trivial⟩
    · exact absurd h (by simp)
  · -- X against X
    split at h
    · rename_i a1 b1
      exact (NNF.satisfies_next ξ b1).mpr (synImpl_sound a1 b1 h _ ((NNF.satisfies_next ξ a1).mp ha))
    · exact absurd h (by simp)
termination_by a.size + b.size
decreasing_by all_goals (simp_wf; subst_vars; (try simp only [NNF.size]); omega)

end Soundness

end LTLLib
