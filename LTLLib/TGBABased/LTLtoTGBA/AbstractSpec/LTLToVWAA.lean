/-
  The abstract LTL to VWAA construction, `[BKŘS12]` §5's δ without suspension, stated directly in `Prop` and `FinSet`.
  States are all `NNF α` nodes rather than only `[TV21]`'s elementary subformulae, `rank` is formula size, and `until` and
  `release` self-loop to the formula itself, which very weakness allows.

  Defines:
  - `NNF.rank`: formula size, the very weak rank
  - `NNF.isUntil`: whether a state is an `until` node, the co-Büchi final condition
  - `NNF.vwaaTrans`: δ, one list of (guard, target set) pairs per formula, `[BKŘS12]` §5
  - `ltlVWAA`: the `VWAA (NNF α) α` assembled from the above
  - `NNF.satTrans`: the canonical one-step transition choice for a satisfied formula
  - `NNF.satLevel`, `NNF.satRun`: the run built by iterating `satTrans` from a singleton level 0

  Proves:
  - `ltlVWAA_correct`: `ltlVWAA` accepts `ξ` from `{ψ}` exactly when `ψ` is satisfied
  - `vwaaTrans_veryWeak`: every successor is the state itself or strictly lower ranked
  - `satTrans_spec`: `satTrans`'s choice is a transition whose guard holds now and whose targets hold one step later
  - `one_step_complete`: the converse, a transition with its targets satisfied gives the source satisfied
  - `satRun_validFrom`, `satRun_accepting`, `acceptsFrom_of_satisfies`: completeness
  - `sound_until`, `sound_release`, `sound`: soundness
  - `ltlVWAA_reachable_subformula`: every state reachable from `{φ}` is a subformula of `φ`

  References:
  - `[BKŘS12]` Babiak, Křetínský, Řehák, Strejček. LTL to Büchi Automata Translation: Fast and More
    Deterministic. TACAS'12, §5.
  - `[TV21]` Tsay, Vardi. From Linear Temporal Logics to Büchi Automata. LNCS 13030, Construction 1, section
    4.1, Lemma 4 and 5's congruences for the one-step choice and its converse.

  Sections:
  - Rank
  - The transition function
  - Very weakness
  - The automaton
  - The canonical one-step choice
  - One-step contraction
  - Completeness
  - Soundness
-/
import LTLLib.LTL.Semantics
import LTLLib.LTL.Subformulas
import LTLLib.TGBABased.LTLtoTGBA.AbstractSpec.VWAA
import LTLLib.TGBABased.LTLtoTGBA.AbstractSpec.VWAARuns
import LTLLib.TGBABased.LTLtoTGBA.AbstractSpec.VWAAReduce
import LTLLib.Tactic.Set
import LTLLib.Data.FinSet

namespace LTLLib

variable {α : Type u}

/-! ## Rank -/

/-- Formula size, the very weak rank (`[TV21]` Lemma 3's C2, in rank form). -/
def NNF.rank : NNF α → Nat
  | .tt | .ff | .prop _ | .nprop _ => 1
  | .next φ => φ.rank + 1
  | .and φ ψ | .or φ ψ | .until φ ψ | .release φ ψ => φ.rank + ψ.rank + 1

/-! ## The transition function -/

/-- Whether `q` is an `until` node, the co-Büchi final condition of `[BKŘS12]` §5. -/
def NNF.isUntil : NNF α → Prop
  | .until _ _ => True
  | _ => False

/-- `[BKŘS12]` §5's δ without suspension: `next ψ` targets `{ψ}`, and `until`/`release`'s self-loop targets the formula
itself. -/
def NNF.vwaaTrans : NNF α → List (((α → Prop) → Prop) × FinSet (NNF α))
  | .tt => [(fun _ => True, ∅)]
  | .ff => []
  | .prop a => [(fun v => v a, ∅)]
  | .nprop a => [(fun v => ¬ v a, ∅)]
  | .and φ ψ => φ.vwaaTrans.flatMap fun p => ψ.vwaaTrans.map fun q => (fun v => p.1 v ∧ q.1 v, p.2 ∪ q.2)
  | .or φ ψ => φ.vwaaTrans ++ ψ.vwaaTrans
  | .next ψ => [(fun _ => True, {ψ})]
  | .until φ ψ => ψ.vwaaTrans ++ φ.vwaaTrans.map fun p => (p.1, p.2 ∪ {NNF.until φ ψ})
  | .release φ ψ =>
    let alts := φ.vwaaTrans ++ [(fun _ => True, {NNF.release φ ψ})]
    ψ.vwaaTrans.flatMap fun p => alts.map fun q => (fun v => p.1 v ∧ q.1 v, p.2 ∪ q.2)

/-! ## Very weakness -/

/-- Every target of `vwaaTrans` is a (reflexive) subformula of the source. -/
theorem NNF.vwaaTrans_subformula (q : NNF α) (g : (α → Prop) → Prop) (O : FinSet (NNF α))
    (h : (g, O) ∈ q.vwaaTrans) (q' : NNF α) (hq' : q' ∈ O) : NNF.IsSubformula q' q := by
  induction q generalizing g O with
  | tt =>
    simp only [NNF.vwaaTrans, List.mem_singleton] at h
    injection h with _ hO; subst hO; simp at hq'
  | ff => simp [NNF.vwaaTrans] at h
  | prop a =>
    simp only [NNF.vwaaTrans, List.mem_singleton] at h
    injection h with _ hO; subst hO; simp at hq'
  | nprop a =>
    simp only [NNF.vwaaTrans, List.mem_singleton] at h
    injection h with _ hO; subst hO; simp at hq'
  | next ψ =>
    simp only [NNF.vwaaTrans, List.mem_singleton] at h
    injection h with _ hO; subst hO
    rw [FinSet.mem_singleton] at hq'; subst hq'
    exact .next_sub .refl
  | and φ ψ ihφ ihψ =>
    simp only [NNF.vwaaTrans, List.mem_flatMap, List.mem_map] at h
    obtain ⟨⟨g1, t1⟩, h1, ⟨g2, t2⟩, h2, heq⟩ := h
    injection heq with _ hO; subst hO
    rcases FinSet.mem_union.mp hq' with hq' | hq'
    · exact .and_left (ihφ g1 t1 h1 hq')
    · exact .and_right (ihψ g2 t2 h2 hq')
  | or φ ψ ihφ ihψ =>
    simp only [NNF.vwaaTrans, List.mem_append] at h
    rcases h with h | h
    · exact .or_left (ihφ g O h hq')
    · exact .or_right (ihψ g O h hq')
  | «until» φ ψ ihφ ihψ =>
    simp only [NNF.vwaaTrans, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨⟨g1, t1⟩, h1, heq⟩
    · exact .until_right (ihψ g O h hq')
    · injection heq with _ hOeq
      rw [← hOeq] at hq'
      rcases FinSet.mem_union.mp hq' with hq' | hq'
      · exact .until_left (ihφ g1 t1 h1 hq')
      · rw [FinSet.mem_singleton] at hq'; subst hq'; exact .refl
  | «release» φ ψ ihφ ihψ =>
    simp only [NNF.vwaaTrans, List.mem_flatMap, List.mem_map] at h
    obtain ⟨⟨g1, t1⟩, h1, ⟨g2, t2⟩, h2, heq⟩ := h
    injection heq with _ hOeq
    rw [← hOeq] at hq'
    rcases FinSet.mem_union.mp hq' with hq' | hq'
    · exact .release_right (ihψ g1 t1 h1 hq')
    · rcases List.mem_append.mp h2 with h2 | h2
      · exact .release_left (ihφ g2 t2 h2 hq')
      · rw [List.mem_singleton] at h2
        injection h2 with _ hOeq2
        dsimp only at hq'
        rw [hOeq2, FinSet.mem_singleton] at hq'
        subst hq'
        exact .refl

/-- Every successor of `q` in `q.vwaaTrans` is `q` itself or ranks strictly lower, `[TV21]` Lemma 3's C2. -/
theorem NNF.vwaaTrans_veryWeak (q : NNF α) (g : (α → Prop) → Prop) (O : FinSet (NNF α))
    (h : (g, O) ∈ q.vwaaTrans) (q' : NNF α) (hq' : q' ∈ O) : q' = q ∨ q'.rank < q.rank := by
  induction q generalizing g O with
  | tt =>
    simp only [NNF.vwaaTrans, List.mem_singleton] at h
    injection h with _ hO; subst hO; simp at hq'
  | ff => simp [NNF.vwaaTrans] at h
  | prop a =>
    simp only [NNF.vwaaTrans, List.mem_singleton] at h
    injection h with _ hO; subst hO; simp at hq'
  | nprop a =>
    simp only [NNF.vwaaTrans, List.mem_singleton] at h
    injection h with _ hO; subst hO; simp at hq'
  | next ψ =>
    simp only [NNF.vwaaTrans, List.mem_singleton] at h
    injection h with _ hO; subst hO
    right; rw [FinSet.mem_singleton] at hq'; subst hq'; simp only [NNF.rank]; omega
  | and φ ψ ihφ ihψ =>
    simp only [NNF.vwaaTrans, List.mem_flatMap, List.mem_map] at h
    obtain ⟨⟨g1, t1⟩, h1, ⟨g2, t2⟩, h2, heq⟩ := h
    injection heq with _ hO; subst hO
    rcases FinSet.mem_union.mp hq' with hq' | hq'
    · rcases ihφ g1 t1 h1 hq' with rfl | hlt <;> (right; simp only [NNF.rank]; omega)
    · rcases ihψ g2 t2 h2 hq' with rfl | hlt <;> (right; simp only [NNF.rank]; omega)
  | or φ ψ ihφ ihψ =>
    simp only [NNF.vwaaTrans, List.mem_append] at h
    rcases h with h | h
    · rcases ihφ g O h hq' with rfl | hlt <;> (right; simp only [NNF.rank]; omega)
    · rcases ihψ g O h hq' with rfl | hlt <;> (right; simp only [NNF.rank]; omega)
  | «until» φ ψ ihφ ihψ =>
    simp only [NNF.vwaaTrans, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨⟨g0, t0⟩, h0, heq⟩
    · rcases ihψ g O h hq' with rfl | hlt <;> (right; simp only [NNF.rank]; omega)
    · injection heq with _ hO; subst hO
      rcases FinSet.mem_union.mp hq' with hq' | hq'
      · rcases ihφ g0 t0 h0 hq' with rfl | hlt <;> (right; simp only [NNF.rank]; omega)
      · left; simpa using hq'
  | «release» φ ψ ihφ ihψ =>
    simp only [NNF.vwaaTrans, List.mem_flatMap, List.mem_map] at h
    obtain ⟨⟨g1, t1⟩, h1, ⟨g2, t2⟩, h2, heq⟩ := h
    injection heq with _ hO; subst hO
    rcases FinSet.mem_union.mp hq' with hq' | hq'
    · rcases ihψ g1 t1 h1 hq' with rfl | hlt <;> (right; simp only [NNF.rank]; omega)
    · rcases List.mem_append.mp h2 with h2 | h2
      · rcases ihφ g2 t2 h2 hq' with rfl | hlt <;> (right; simp only [NNF.rank]; omega)
      · simp only [List.mem_singleton] at h2
        injection h2 with _ hO; subst hO
        left; simpa using hq'

/-! ## The automaton -/

/-- The VWAA of `φ`, with the single initial level `{φ}`. -/
def ltlVWAA (φ : NNF α) : VWAA (NNF α) α where
  trans := NNF.vwaaTrans
  initial := [{φ}]
  final := NNF.isUntil
  rank := NNF.rank
  veryWeak := NNF.vwaaTrans_veryWeak

/-- Every `VWAA.Reachable` state of `ltlVWAA φ` from `{φ}` is a subformula of `φ`. -/
theorem ltlVWAA_reachable_subformula (φ : NNF α) :
    ∀ q, VWAA.Reachable (ltlVWAA φ) {φ} q → NNF.IsSubformula q φ := by
  intro q hq
  induction hq with
  | base q hq => rw [FinSet.mem_singleton] at hq; subst hq; exact .refl
  | step p hp g O hgO q hq ih => exact (NNF.vwaaTrans_subformula p g O hgO q hq).trans ih

/-! ## The canonical one-step choice -/

open Classical in
/-- The canonical one-step transition choice, taking at `or`/`until`/`release` whichever alternative the word satisfies.
`until`'s self-loop is taken only while its right operand does not hold. -/
noncomputable def NNF.satTrans (ξ : OmegaWord α) : NNF α → ((α → Prop) → Prop) × FinSet (NNF α)
  | .tt => (fun _ => True, ∅)
  | .ff => (fun _ => True, ∅)
  | .prop a => (fun v => v a, ∅)
  | .nprop a => (fun v => ¬ v a, ∅)
  | .and φ ψ =>
    (fun v => (NNF.satTrans ξ φ).1 v ∧ (NNF.satTrans ξ ψ).1 v, (NNF.satTrans ξ φ).2 ∪ (NNF.satTrans ξ ψ).2)
  | .or φ ψ => if φ.satisfies ξ then NNF.satTrans ξ φ else NNF.satTrans ξ ψ
  | .next ψ => (fun _ => True, {ψ})
  | .until φ ψ =>
    if ψ.satisfies ξ then NNF.satTrans ξ ψ
    else ((NNF.satTrans ξ φ).1, (NNF.satTrans ξ φ).2 ∪ {NNF.until φ ψ})
  | .release φ ψ =>
    if φ.satisfies ξ then
      (fun v => (NNF.satTrans ξ ψ).1 v ∧ (NNF.satTrans ξ φ).1 v, (NNF.satTrans ξ ψ).2 ∪ (NNF.satTrans ξ φ).2)
    else (fun v => (NNF.satTrans ξ ψ).1 v ∧ True, (NNF.satTrans ξ ψ).2 ∪ {NNF.release φ ψ})

/-- `satTrans`'s choice is a transition of `q.vwaaTrans` whose guard holds now and whose targets hold one step later,
`[TV21]` Lemma 5's expansion congruence turned into a construction. -/
theorem NNF.satTrans_spec (q : NNF α) (ξ : OmegaWord α) (hq : q.satisfies ξ) :
    NNF.satTrans ξ q ∈ q.vwaaTrans ∧ (NNF.satTrans ξ q).1 (ξ 0) ∧
      ∀ q' ∈ (NNF.satTrans ξ q).2, q'.satisfies (ξ.drop 1) := by
  induction q generalizing ξ with
  | tt => refine ⟨?_, trivial, ?_⟩ <;> simp [NNF.satTrans, NNF.vwaaTrans]
  | ff => simp [NNF.satisfies_ff] at hq
  | prop a =>
    rw [NNF.satisfies_prop] at hq
    refine ⟨?_, hq, ?_⟩ <;> simp [NNF.satTrans, NNF.vwaaTrans]
  | nprop a =>
    rw [NNF.satisfies_nprop] at hq
    refine ⟨?_, hq, ?_⟩ <;> simp [NNF.satTrans, NNF.vwaaTrans]
  | and φ ψ ihφ ihψ =>
    rw [NNF.satisfies_and] at hq
    obtain ⟨hmemφ, hgφ, hOφ⟩ := ihφ ξ hq.1
    obtain ⟨hmemψ, hgψ, hOψ⟩ := ihψ ξ hq.2
    refine ⟨?_, ⟨hgφ, hgψ⟩, ?_⟩
    · simp only [NNF.satTrans, NNF.vwaaTrans]
      exact List.mem_flatMap.mpr ⟨NNF.satTrans ξ φ, hmemφ, List.mem_map.mpr ⟨NNF.satTrans ξ ψ, hmemψ, rfl⟩⟩
    · intro q' hq'
      simp only [NNF.satTrans] at hq'
      rcases FinSet.mem_union.mp hq' with hq' | hq'
      · exact hOφ q' hq'
      · exact hOψ q' hq'
  | or φ ψ ihφ ihψ =>
    rw [NNF.satisfies_or] at hq
    unfold NNF.satTrans
    by_cases hφ : φ.satisfies ξ
    · rw [if_pos hφ]
      obtain ⟨hmem, hg, hO⟩ := ihφ ξ hφ
      exact ⟨by simp [NNF.vwaaTrans, hmem], hg, hO⟩
    · rw [if_neg hφ]
      have hψ : ψ.satisfies ξ := hq.resolve_left hφ
      obtain ⟨hmem, hg, hO⟩ := ihψ ξ hψ
      exact ⟨by simp [NNF.vwaaTrans, hmem], hg, hO⟩
  | next ψ =>
    rw [NNF.satisfies_next] at hq
    refine ⟨?_, trivial, ?_⟩ <;> simp [NNF.satTrans, NNF.vwaaTrans, hq]
  | «until» φ ψ ihφ ihψ =>
    unfold NNF.satTrans
    by_cases hψ : ψ.satisfies ξ
    · rw [if_pos hψ]
      obtain ⟨hmem, hg, hO⟩ := ihψ ξ hψ
      exact ⟨by simp [NNF.vwaaTrans, hmem], hg, hO⟩
    · rw [if_neg hψ]
      rw [NNF.satisfies_until] at hq
      obtain ⟨i, hψi, hφlt⟩ := hq
      have hipos : 0 < i := by
        rcases Nat.eq_zero_or_pos i with rfl | h
        · rw [exec_drop_zero] at hψi; exact absurd hψi hψ
        · exact h
      have hφ0 : φ.satisfies ξ := by have := hφlt 0 hipos; rwa [exec_drop_zero] at this
      obtain ⟨hmem, hg, hO⟩ := ihφ ξ hφ0
      refine ⟨?_, hg, ?_⟩
      · simp only [NNF.vwaaTrans]
        exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨NNF.satTrans ξ φ, hmem, rfl⟩))
      · intro q' hq'
        rcases FinSet.mem_union.mp hq' with hq' | hq'
        · exact hO q' hq'
        · rw [FinSet.mem_singleton] at hq'; subst hq'
          rw [NNF.satisfies_until]
          refine ⟨i - 1, ?_, ?_⟩
          · rw [NNF.satisfies_drop_drop]
            have : 1 + (i - 1) = i := by omega
            rwa [this]
          · intro j hj
            rw [NNF.satisfies_drop_drop]
            exact hφlt (1 + j) (by omega)
  | «release» φ ψ ihφ ihψ =>
    rw [NNF.satisfies_release] at hq
    have hψ0 : ψ.satisfies ξ := by
      rcases hq 0 with h | ⟨i, hi, -⟩
      · rwa [exec_drop_zero] at h
      · omega
    obtain ⟨hmemψ, hgψ, hOψ⟩ := ihψ ξ hψ0
    unfold NNF.satTrans
    by_cases hφ0 : φ.satisfies ξ
    · rw [if_pos hφ0]
      obtain ⟨hmemφ, hgφ, hOφ⟩ := ihφ ξ hφ0
      refine ⟨?_, ⟨hgψ, hgφ⟩, ?_⟩
      · simp only [NNF.vwaaTrans]
        exact List.mem_flatMap.mpr ⟨NNF.satTrans ξ ψ, hmemψ,
          List.mem_map.mpr ⟨NNF.satTrans ξ φ, List.mem_append.mpr (Or.inl hmemφ), rfl⟩⟩
      · intro q' hq'
        rcases FinSet.mem_union.mp hq' with hq' | hq'
        · exact hOψ q' hq'
        · exact hOφ q' hq'
    · rw [if_neg hφ0]
      refine ⟨?_, ⟨hgψ, trivial⟩, ?_⟩
      · simp only [NNF.vwaaTrans]
        exact List.mem_flatMap.mpr ⟨NNF.satTrans ξ ψ, hmemψ,
          List.mem_map.mpr ⟨(fun _ => True, {NNF.release φ ψ}), List.mem_append.mpr (Or.inr (by simp)), rfl⟩⟩
      · intro q' hq'
        rcases FinSet.mem_union.mp hq' with hq' | hq'
        · exact hOψ q' hq'
        · rw [FinSet.mem_singleton] at hq'; subst hq'
          rw [NNF.satisfies_release]
          intro j
          rcases hq (1 + j) with h | ⟨i', hi', hφi'⟩
          · left; rw [NNF.satisfies_drop_drop]; exact h
          · have hi'pos : 0 < i' := by
              rcases Nat.eq_zero_or_pos i' with rfl | hpos
              · rw [exec_drop_zero] at hφi'; exact absurd hφi' hφ0
              · exact hpos
            right
            refine ⟨i' - 1, by omega, ?_⟩
            rw [NNF.satisfies_drop_drop]
            have : 1 + (i' - 1) = i' := by omega
            rwa [this]

/-! ## One-step contraction -/

/-- The converse of `satTrans_spec`: a transition whose guard holds now and whose targets, self-loop included, hold one
step later has its source satisfied now. -/
theorem NNF.one_step_complete (q : NNF α) (ξ : OmegaWord α) (g : (α → Prop) → Prop) (O : FinSet (NNF α))
    (hmem : (g, O) ∈ q.vwaaTrans) (hg : g (ξ 0)) (hO : ∀ q' ∈ O, q'.satisfies (ξ.drop 1)) :
    q.satisfies ξ := by
  induction q generalizing ξ g O with
  | tt => rw [NNF.satisfies_tt]; trivial
  | ff => simp [NNF.vwaaTrans] at hmem
  | prop a =>
    simp only [NNF.vwaaTrans, List.mem_singleton] at hmem
    injection hmem with hgeq _; subst hgeq
    rw [NNF.satisfies_prop]; exact hg
  | nprop a =>
    simp only [NNF.vwaaTrans, List.mem_singleton] at hmem
    injection hmem with hgeq _; subst hgeq
    rw [NNF.satisfies_nprop]; exact hg
  | and φ ψ ihφ ihψ =>
    simp only [NNF.vwaaTrans, List.mem_flatMap, List.mem_map] at hmem
    obtain ⟨⟨g1, O1⟩, hmem1, ⟨g2, O2⟩, hmem2, heq⟩ := hmem
    injection heq with hgeq hOeq; subst hgeq; subst hOeq
    rw [NNF.satisfies_and]
    exact ⟨ihφ ξ g1 O1 hmem1 hg.1 fun q' hq' => hO q' (FinSet.mem_union.mpr (Or.inl hq')),
      ihψ ξ g2 O2 hmem2 hg.2 fun q' hq' => hO q' (FinSet.mem_union.mpr (Or.inr hq'))⟩
  | or φ ψ ihφ ihψ =>
    simp only [NNF.vwaaTrans, List.mem_append] at hmem
    rw [NNF.satisfies_or]
    rcases hmem with hmem | hmem
    · exact Or.inl (ihφ ξ g O hmem hg hO)
    · exact Or.inr (ihψ ξ g O hmem hg hO)
  | next ψ =>
    simp only [NNF.vwaaTrans, List.mem_singleton] at hmem
    injection hmem with _ hOeq; subst hOeq
    rw [NNF.satisfies_next]
    exact hO ψ (by simp)
  | «until» φ ψ ihφ ihψ =>
    simp only [NNF.vwaaTrans, List.mem_append, List.mem_map] at hmem
    rw [NNF.satisfies_until]
    rcases hmem with hmem | ⟨⟨g0, O0⟩, hmem0, heq⟩
    · have hψ : ψ.satisfies ξ := ihψ ξ g O hmem hg hO
      exact ⟨0, by rwa [exec_drop_zero], fun j hj => absurd hj (by omega)⟩
    · injection heq with hgeq hOeq; subst hgeq; subst hOeq
      have hO0 : ∀ q' ∈ O0, q'.satisfies (ξ.drop 1) := fun q' hq' => hO q' (FinSet.mem_union.mpr (Or.inl hq'))
      have hquntil : (NNF.until φ ψ).satisfies (ξ.drop 1) :=
        hO (NNF.until φ ψ) (FinSet.mem_union.mpr (Or.inr (by simp)))
      have hφ : φ.satisfies ξ := ihφ ξ g0 O0 hmem0 hg hO0
      rw [NNF.satisfies_until] at hquntil
      obtain ⟨i', hψi', hφlt'⟩ := hquntil
      refine ⟨i' + 1, ?_, ?_⟩
      · rw [NNF.satisfies_drop_drop] at hψi'
        have heq2 : 1 + i' = i' + 1 := by omega
        rwa [heq2] at hψi'
      · intro j hj
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · rwa [exec_drop_zero]
        · have hj' : j - 1 < i' := by omega
          have hstep := hφlt' (j - 1) hj'
          rw [NNF.satisfies_drop_drop] at hstep
          have heq3 : 1 + (j - 1) = j := by omega
          rwa [heq3] at hstep
  | «release» φ ψ ihφ ihψ =>
    simp only [NNF.vwaaTrans, List.mem_flatMap, List.mem_map] at hmem
    obtain ⟨⟨g1, O1⟩, hmem1, ⟨g2, O2⟩, hmem2, heq⟩ := hmem
    injection heq with hgeq hOeq; subst hgeq; subst hOeq
    have hψ : ψ.satisfies ξ :=
      ihψ ξ g1 O1 hmem1 hg.1 fun q' hq' => hO q' (FinSet.mem_union.mpr (Or.inl hq'))
    rw [NNF.satisfies_release]
    rcases List.mem_append.mp hmem2 with hmem2 | hmem2
    · have hφ : φ.satisfies ξ :=
        ihφ ξ g2 O2 hmem2 hg.2 fun q' hq' => hO q' (FinSet.mem_union.mpr (Or.inr hq'))
      intro j
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · left; rwa [exec_drop_zero]
      · right; exact ⟨0, hjpos, by rwa [exec_drop_zero]⟩
    · simp only [List.mem_singleton] at hmem2
      injection hmem2 with _ hO2eq; subst hO2eq
      have hqrelease : (NNF.release φ ψ).satisfies (ξ.drop 1) :=
        hO (NNF.release φ ψ) (FinSet.mem_union.mpr (Or.inr (by simp)))
      rw [NNF.satisfies_release] at hqrelease
      intro j
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · left; rwa [exec_drop_zero]
      · rcases hqrelease (j - 1) with h | ⟨i, hi, hφi⟩
        · left
          rw [NNF.satisfies_drop_drop] at h
          have heq2 : 1 + (j - 1) = j := by omega
          rwa [heq2] at h
        · right
          refine ⟨i + 1, by omega, ?_⟩
          rw [NNF.satisfies_drop_drop] at hφi
          have heq3 : 1 + i = i + 1 := by omega
          rwa [heq3] at hφi

/-! ## Completeness -/

/-- The levels of the run built by iterating `satTrans`'s choice from `{ψ}`. -/
noncomputable def NNF.satLevel (ξ : OmegaWord α) (ψ : NNF α) : Nat → FinSet (NNF α)
  | 0 => {ψ}
  | i + 1 => (NNF.satLevel ξ ψ i).biUnion fun q => (NNF.satTrans (ξ.drop i) q).2

/-- The run built by iterating `satTrans`'s choice from `{ψ}`, `[TV21]` Lemma 5's expansion congruence turned
into a run. -/
noncomputable def NNF.satRun (ξ : OmegaWord α) (ψ : NNF α) : VWAA.Run (NNF α) where
  level := NNF.satLevel ξ ψ
  succ i q := (NNF.satTrans (ξ.drop i) q).2

/-- Every state alive on a level of `satRun` satisfies the word from that level on. -/
theorem NNF.satRun_live (ξ : OmegaWord α) (ψ : NNF α) (hψ : ψ.satisfies ξ) :
    ∀ i q, q ∈ (NNF.satRun ξ ψ).level i → q.satisfies (ξ.drop i) := by
  intro i
  induction i with
  | zero =>
    intro q hq
    simp only [NNF.satRun, NNF.satLevel, FinSet.mem_singleton] at hq
    subst hq; rwa [exec_drop_zero]
  | succ i ih =>
    intro q hq
    simp only [NNF.satRun, NNF.satLevel, FinSet.mem_biUnion] at hq
    obtain ⟨p, hp, hq⟩ := hq
    have hp' := ih p hp
    have hstep := (NNF.satTrans_spec p (ξ.drop i) hp').2.2 q hq
    rwa [NNF.satisfies_drop_drop] at hstep

/-- `satRun` is a run of `ltlVWAA φ` on `ξ` from `{ψ}`. -/
theorem NNF.satRun_validFrom (ξ : OmegaWord α) (ψ φ : NNF α) (hψ : ψ.satisfies ξ) :
    (NNF.satRun ξ ψ).ValidFrom (ltlVWAA φ) {ψ} ξ where
  init := rfl
  step i q hq := by
    have hq' := NNF.satRun_live ξ ψ hψ i q hq
    obtain ⟨hmem, hg, -⟩ := NNF.satTrans_spec q (ξ.drop i) hq'
    have hzero : (ξ.drop i) 0 = ξ i := by show ξ (0 + i) = ξ i; rw [Nat.zero_add]
    exact ⟨(NNF.satTrans (ξ.drop i) q).1, hmem, hzero ▸ hg⟩
  succ_sub i q hq := by
    intro q' hq'
    simp only [NNF.satRun, NNF.satLevel, FinSet.mem_biUnion]
    exact ⟨q, hq, hq'⟩
  no_orphan i q hq := by
    simp only [NNF.satRun, NNF.satLevel, FinSet.mem_biUnion] at hq
    obtain ⟨p, hp, hq⟩ := hq
    exact ⟨p, hp, hq⟩

/-- `satRun` is accepting, no branch settles in an `until` state forever. -/
theorem NNF.satRun_accepting (ξ : OmegaWord α) (ψ φ : NNF α) (hψ : ψ.satisfies ξ) :
    (ltlVWAA φ).AcceptingRun (NNF.satRun ξ ψ) := by
  have hv := NNF.satRun_validFrom ξ ψ φ hψ
  rw [acceptingRun_iff hv]
  intro b q hb hst hfin
  obtain ⟨φ', ψ', rfl⟩ : ∃ φ' ψ', q = NNF.until φ' ψ' := by
    match q, hfin with
    | .until φ' ψ', _ => exact ⟨φ', ψ', rfl⟩
    | .tt, hfin => simp [ltlVWAA, NNF.isUntil] at hfin
    | .ff, hfin => simp [ltlVWAA, NNF.isUntil] at hfin
    | .prop _, hfin => simp [ltlVWAA, NNF.isUntil] at hfin
    | .nprop _, hfin => simp [ltlVWAA, NNF.isUntil] at hfin
    | .and _ _, hfin => simp [ltlVWAA, NNF.isUntil] at hfin
    | .or _ _, hfin => simp [ltlVWAA, NNF.isUntil] at hfin
    | .next _, hfin => simp [ltlVWAA, NNF.isUntil] at hfin
    | .release _ _, hfin => simp [ltlVWAA, NNF.isUntil] at hfin
  obtain ⟨N, hstab⟩ := hst
  have hlive : ∀ m, N ≤ m → (NNF.until φ' ψ').satisfies (ξ.drop m) := by
    intro m hm
    have hmem : b m ∈ (NNF.satRun ξ ψ).level m := mem_level_of_infBranch hv hb m
    rw [hstab m hm] at hmem
    exact NNF.satRun_live ξ ψ hψ m _ hmem
  have hself : ∀ m, N ≤ m → NNF.until φ' ψ' ∈ (NNF.satTrans (ξ.drop m) (NNF.until φ' ψ')).2 := by
    intro m hm
    have hstep := hb.2 m
    simp only [NNF.satRun] at hstep
    rw [hstab m hm, hstab (m + 1) (by omega)] at hstep
    exact hstep
  have hnotψ : ∀ m, N ≤ m → ¬ ψ'.satisfies (ξ.drop m) := by
    intro m hm hψ'm
    have hmem := hself m hm
    unfold NNF.satTrans at hmem
    rw [if_pos hψ'm] at hmem
    have hmem' : NNF.satTrans (ξ.drop m) ψ' ∈ ψ'.vwaaTrans := (NNF.satTrans_spec ψ' (ξ.drop m) hψ'm).1
    rcases NNF.vwaaTrans_veryWeak ψ' _ _ hmem' (NNF.until φ' ψ') hmem with heq | hlt
    · have hrk : (NNF.until φ' ψ').rank = ψ'.rank := by rw [heq]
      simp only [NNF.rank] at hrk; omega
    · simp only [NNF.rank] at hlt; omega
  obtain ⟨i, hψi, -⟩ := (NNF.satisfies_until (ξ.drop N) φ' ψ').mp (hlive N (Nat.le_refl _))
  rw [NNF.satisfies_drop_drop] at hψi
  exact hnotψ (N + i) (by omega) hψi

/-- Completeness: a satisfied formula's canonical run witnesses `acceptsFrom`. -/
theorem NNF.acceptsFrom_of_satisfies (ψ φ : NNF α) (ξ : OmegaWord α) (hψ : ψ.satisfies ξ) :
    (ltlVWAA φ).AcceptsFrom {ψ} ξ :=
  ⟨NNF.satRun ξ ψ, NNF.satRun_validFrom ξ ψ φ hψ, NNF.satRun_accepting ξ ψ φ hψ⟩

/-! ## Soundness -/

open Classical in
/-- The `until` case of soundness: given soundness for lower ranks, an alive `until` state satisfies the word from its
level on. -/
theorem NNF.sound_until (φ : NNF α) {r : VWAA.Run (NNF α)} {S : FinSet (NNF α)} {ξ : OmegaWord α}
    (hv : r.ValidFrom (ltlVWAA φ) S ξ) (hacc : (ltlVWAA φ).AcceptingRun r) (φ' ψ' : NNF α)
    (hlower : ∀ q', q'.rank < (NNF.until φ' ψ').rank → ∀ j, q' ∈ r.level j → q'.satisfies (ξ.drop j))
    (i : Nat) (hi : NNF.until φ' ψ' ∈ r.level i) : (NNF.until φ' ψ').satisfies (ξ.drop i) := by
  have hstep_cases : ∀ j, NNF.until φ' ψ' ∈ r.level j →
      (NNF.until φ' ψ' ∉ r.succ j (NNF.until φ' ψ') ∧ (NNF.until φ' ψ').satisfies (ξ.drop j)) ∨
      (NNF.until φ' ψ' ∈ r.succ j (NNF.until φ' ψ') ∧
        ((NNF.until φ' ψ').satisfies (ξ.drop (j + 1)) → (NNF.until φ' ψ').satisfies (ξ.drop j))) := by
    intro j hj
    obtain ⟨g, hmem, hg⟩ := hv.step j (NNF.until φ' ψ') hj
    have hsub := hv.succ_sub j (NNF.until φ' ψ') hj
    have hzero : (ξ.drop j) 0 = ξ j := by show ξ (0 + j) = ξ j; rw [Nat.zero_add]
    rcases List.mem_append.mp hmem with hmemψ | hmemφ
    · left
      have hnotloop : NNF.until φ' ψ' ∉ r.succ j (NNF.until φ' ψ') := by
        intro hmemq
        rcases NNF.vwaaTrans_veryWeak ψ' g (r.succ j (NNF.until φ' ψ')) hmemψ (NNF.until φ' ψ') hmemq with
          heq2 | hlt2
        · have hrk : (NNF.until φ' ψ').rank = ψ'.rank := by rw [heq2]
          simp only [NNF.rank] at hrk; omega
        · simp only [NNF.rank] at hlt2; omega
      refine ⟨hnotloop, NNF.one_step_complete (NNF.until φ' ψ') (ξ.drop j) g
        (r.succ j (NNF.until φ' ψ')) hmem (hzero ▸ hg) ?_⟩
      intro q' hq'
      have hqalive : q' ∈ r.level (j + 1) := hsub hq'
      have hrk : q'.rank < (NNF.until φ' ψ').rank := by
        rcases NNF.vwaaTrans_veryWeak ψ' g (r.succ j (NNF.until φ' ψ')) hmemψ q' hq' with heq2 | hlt2
        · rw [heq2]; simp only [NNF.rank]; omega
        · simp only [NNF.rank] at hlt2 ⊢; omega
      have hsat := hlower q' hrk (j + 1) hqalive
      rwa [← NNF.satisfies_drop_drop] at hsat
    · obtain ⟨p, hp, heq⟩ := List.mem_map.mp hmemφ
      injection heq with hgeq hOeq
      right
      have hqmem : NNF.until φ' ψ' ∈ r.succ j (NNF.until φ' ψ') := by
        rw [← hOeq]; exact FinSet.mem_union_right _ (FinSet.mem_singleton_self _)
      refine ⟨hqmem, fun hnext => NNF.one_step_complete (NNF.until φ' ψ') (ξ.drop j) g
        (r.succ j (NNF.until φ' ψ')) hmem (hzero ▸ hg) ?_⟩
      intro q' hq'
      rw [← hOeq] at hq'
      rcases FinSet.mem_union.mp hq' with hq' | hq'
      · have hqalive : q' ∈ r.level (j + 1) := hsub (hOeq ▸ FinSet.mem_union_left _ hq')
        have hrk : q'.rank < (NNF.until φ' ψ').rank := by
          rcases NNF.vwaaTrans_veryWeak φ' p.1 p.2 hp q' hq' with heq2 | hlt2
          · rw [heq2]; simp only [NNF.rank]; omega
          · simp only [NNF.rank] at hlt2 ⊢; omega
        have hsat := hlower q' hrk (j + 1) hqalive
        rwa [← NNF.satisfies_drop_drop] at hsat
      · rw [FinSet.mem_singleton] at hq'
        rw [hq', NNF.satisfies_drop_drop]
        exact hnext
  have hnotforever : ¬ ∀ m, NNF.until φ' ψ' ∈ r.level (i + m) ∧
      NNF.until φ' ψ' ∈ r.succ (i + m) (NNF.until φ' ψ') := by
    intro hforever
    obtain ⟨p, hpi, hp0, hpstep⟩ := exists_path_to hv i (NNF.until φ' ψ') hi
    set b : Nat → NNF α := fun k => if k ≤ i then p k else NNF.until φ' ψ' with hb_def
    have hb : r.InfBranch b := by
      refine ⟨?_, ?_⟩
      · show b 0 ∈ r.level 0
        simp only [hb_def, if_pos (Nat.zero_le i)]
        exact hp0
      · intro k
        show b (k + 1) ∈ r.succ k (b k)
        rcases Nat.lt_or_ge k i with hk | hk
        · simp only [hb_def, if_pos (Nat.le_of_lt hk), if_pos (show k + 1 ≤ i by omega)]
          exact hpstep k hk
        · rcases Nat.lt_or_ge i k with hk' | hk'
          · simp only [hb_def, if_neg (show ¬ k ≤ i by omega), if_neg (show ¬ k + 1 ≤ i by omega)]
            have hboth := hforever (k - i)
            have heqk : i + (k - i) = k := by omega
            rw [heqk] at hboth
            exact hboth.2
          · have hk'' : k = i := by omega
            subst hk''
            simp only [hb_def, if_pos (Nat.le_refl _), if_neg (show ¬ k + 1 ≤ k by omega), hpi]
            have hboth := hforever 0
            simpa using hboth.2
    have hstab : VWAA.StabilizesAt b (NNF.until φ' ψ') := by
      refine ⟨i, fun m hm => ?_⟩
      simp only [hb_def]
      rcases Nat.lt_or_ge i m with hm' | hm'
      · rw [if_neg (show ¬ m ≤ i by omega)]
      · have : m = i := by omega
        rw [this, if_pos (Nat.le_refl _), hpi]
    exact (acceptingRun_iff hv).mp hacc b (NNF.until φ' ψ') hb hstab trivial
  rw [not_forall] at hnotforever
  obtain ⟨N, hNspec⟩ := hnotforever
  have hex : ∃ m, ¬ (NNF.until φ' ψ' ∈ r.level (i + m) ∧ NNF.until φ' ψ' ∈ r.succ (i + m) (NNF.until φ' ψ')) :=
    ⟨N, hNspec⟩
  clear hNspec N
  obtain ⟨N, -, hNspec, hNmin⟩ := LentilLib.Nat.find_min
    (p := fun m => ¬ (NNF.until φ' ψ' ∈ r.level (i + m) ∧ NNF.until φ' ψ' ∈ r.succ (i + m) (NNF.until φ' ψ')))
    _ hex.choose_spec
  have hnotN_lt : ∀ k, k < N → NNF.until φ' ψ' ∈ r.level (i + k) ∧
      NNF.until φ' ψ' ∈ r.succ (i + k) (NNF.until φ' ψ') := by
    intro k hk
    by_contra hcon
    exact hNmin k hk hcon
  have halive : ∀ m', m' ≤ N → NNF.until φ' ψ' ∈ r.level (i + m') := by
    intro m'
    induction m' with
    | zero => intro _; simpa using hi
    | succ k ih =>
      intro hm'
      have hk : k ≤ N := by omega
      have hkalive := ih hk
      have hkN : k < N := by omega
      have hboth := hnotN_lt k hkN
      have hnext := hv.succ_sub (i + k) (NNF.until φ' ψ') hkalive hboth.2
      have heqidx : i + (k + 1) = i + k + 1 := by omega
      rwa [heqidx]
  have hNalive : NNF.until φ' ψ' ∈ r.level (i + N) := halive N (Nat.le_refl _)
  have hNnotloop : NNF.until φ' ψ' ∉ r.succ (i + N) (NNF.until φ' ψ') := by
    intro h
    exact hNspec ⟨hNalive, h⟩
  have hsatN : (NNF.until φ' ψ').satisfies (ξ.drop (i + N)) := by
    rcases hstep_cases (i + N) hNalive with ⟨_, hsat⟩ | ⟨hloopmem, -⟩
    · exact hsat
    · exact absurd hloopmem hNnotloop
  have hback : ∀ k, k ≤ N → (NNF.until φ' ψ').satisfies (ξ.drop (i + N - k)) := by
    intro k
    induction k with
    | zero => intro _; simpa using hsatN
    | succ k ih =>
      intro hk
      have hk' : k ≤ N := by omega
      have hprev := ih hk'
      have hkN : N - k - 1 < N := by omega
      have hboth := hnotN_lt (N - k - 1) hkN
      rcases hstep_cases (i + (N - k - 1)) hboth.1 with ⟨hnotloop, -⟩ | ⟨-, himp⟩
      · exact absurd hboth.2 hnotloop
      · have heqidx1 : i + (N - k - 1) + 1 = i + N - k := by omega
        have hnext : (NNF.until φ' ψ').satisfies (ξ.drop (i + (N - k - 1) + 1)) := by
          rw [heqidx1]; exact hprev
        have := himp hnext
        have heqidx2 : i + (N - k - 1) = i + N - (k + 1) := by omega
        rwa [heqidx2] at this
  have hfinal := hback N (Nat.le_refl _)
  have heqidxN : i + N - N = i := by omega
  rwa [heqidxN] at hfinal

/-- The `release` case of soundness: given soundness for lower ranks, an alive `release` state satisfies the word from its
level on. -/
theorem NNF.sound_release (φ : NNF α) {r : VWAA.Run (NNF α)} {S : FinSet (NNF α)} {ξ : OmegaWord α}
    (hv : r.ValidFrom (ltlVWAA φ) S ξ) (φ' ψ' : NNF α)
    (hlower : ∀ q', q'.rank < (NNF.release φ' ψ').rank → ∀ j, q' ∈ r.level j → q'.satisfies (ξ.drop j))
    (i : Nat) (hi : NNF.release φ' ψ' ∈ r.level i) : (NNF.release φ' ψ').satisfies (ξ.drop i) := by
  have hstep : ∀ j, NNF.release φ' ψ' ∈ r.level j →
      ψ'.satisfies (ξ.drop j) ∧ (φ'.satisfies (ξ.drop j) ∨ NNF.release φ' ψ' ∈ r.level (j + 1)) := by
    intro j hj
    obtain ⟨g, hmem, hg⟩ := hv.step j (NNF.release φ' ψ') hj
    have hsub := hv.succ_sub j (NNF.release φ' ψ') hj
    have hzero : (ξ.drop j) 0 = ξ j := by show ξ (0 + j) = ξ j; rw [Nat.zero_add]
    obtain ⟨p, hp, hmem2⟩ := List.mem_flatMap.mp hmem
    obtain ⟨q2, hq2, heq⟩ := List.mem_map.mp hmem2
    injection heq with hgeq hOeq
    have hgv : p.1 (ξ j) ∧ q2.1 (ξ j) := by
      have hg' : g (ξ j) := hg
      rw [← hgeq] at hg'
      exact hg'
    have hg1 : p.1 ((ξ.drop j) 0) := by rw [hzero]; exact hgv.1
    have hg2 : q2.1 ((ξ.drop j) 0) := by rw [hzero]; exact hgv.2
    have hψsat : ψ'.satisfies (ξ.drop j) := by
      apply NNF.one_step_complete ψ' (ξ.drop j) p.1 p.2 hp hg1
      intro q' hq'
      have hqalive : q' ∈ r.level (j + 1) := hsub (hOeq ▸ FinSet.mem_union_left _ hq')
      have hrk : q'.rank < (NNF.release φ' ψ').rank := by
        rcases NNF.vwaaTrans_veryWeak ψ' p.1 p.2 hp q' hq' with heq2 | hlt2
        · rw [heq2]; simp only [NNF.rank]; omega
        · simp only [NNF.rank] at hlt2 ⊢; omega
      have hsat := hlower q' hrk (j + 1) hqalive
      rwa [← NNF.satisfies_drop_drop] at hsat
    refine ⟨hψsat, ?_⟩
    rcases List.mem_append.mp hq2 with hq2' | hq2'
    · left
      apply NNF.one_step_complete φ' (ξ.drop j) q2.1 q2.2 hq2' hg2
      intro q' hq'
      have hqalive : q' ∈ r.level (j + 1) := hsub (hOeq ▸ FinSet.mem_union_right _ hq')
      have hrk : q'.rank < (NNF.release φ' ψ').rank := by
        rcases NNF.vwaaTrans_veryWeak φ' q2.1 q2.2 hq2' q' hq' with heq2 | hlt2
        · rw [heq2]; simp only [NNF.rank]; omega
        · simp only [NNF.rank] at hlt2 ⊢; omega
      have hsat := hlower q' hrk (j + 1) hqalive
      rwa [← NNF.satisfies_drop_drop] at hsat
    · right
      rw [List.mem_singleton] at hq2'
      have hqmem : NNF.release φ' ψ' ∈ r.succ j (NNF.release φ' ψ') := by
        rw [← hOeq, hq2']
        exact FinSet.mem_union_right _ (FinSet.mem_singleton_self _)
      exact hsub hqmem
  have hQ : ∀ j', (NNF.release φ' ψ' ∈ r.level (i + j') ∧ ψ'.satisfies (ξ.drop (i + j'))) ∨
      ∃ k, k < j' ∧ φ'.satisfies (ξ.drop (i + k)) := by
    intro j'
    induction j' with
    | zero =>
      left
      have hstep0 := hstep i hi
      simpa using And.intro hi hstep0.1
    | succ j' ih =>
      rcases ih with ⟨halive, hψsat⟩ | ⟨k, hk, hφsat⟩
      · have hnext := hstep (i + j') halive
        rcases hnext.2 with hφ | hnextalive
        · right; exact ⟨j', by omega, hφ⟩
        · left
          have heqidx : i + j' + 1 = i + (j' + 1) := by omega
          rw [heqidx] at hnextalive
          have hψnext := (hstep (i + (j' + 1)) hnextalive).1
          exact ⟨hnextalive, hψnext⟩
      · right; exact ⟨k, by omega, hφsat⟩
  rw [NNF.satisfies_release]
  intro j
  rcases hQ j with ⟨-, hψsat⟩ | ⟨k, hk, hφsat⟩
  · left; rwa [NNF.satisfies_drop_drop]
  · right; exact ⟨k, hk, by rwa [NNF.satisfies_drop_drop]⟩

/-- Soundness: every state alive on a level of an accepting run satisfies the word from that level on. -/
theorem NNF.sound (φ : NNF α) {r : VWAA.Run (NNF α)} {S : FinSet (NNF α)} {ξ : OmegaWord α}
    (hv : r.ValidFrom (ltlVWAA φ) S ξ) (hacc : (ltlVWAA φ).AcceptingRun r) :
    ∀ q i, q ∈ r.level i → q.satisfies (ξ.drop i) := by
  have main : ∀ n q, q.rank ≤ n → ∀ i, q ∈ r.level i → q.satisfies (ξ.drop i) := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n IH =>
      intro q hqn i hqi
      have hlower : ∀ q', q'.rank < q.rank → ∀ j, q' ∈ r.level j → q'.satisfies (ξ.drop j) := by
        intro q' hq'rank j hq'j
        exact IH q'.rank (by omega) q' (Nat.le_refl _) j hq'j
      have hzero : (ξ.drop i) 0 = ξ i := by show ξ (0 + i) = ξ i; rw [Nat.zero_add]
      cases q with
      | tt => rw [NNF.satisfies_tt]; trivial
      | ff =>
        obtain ⟨g, hmem, -⟩ := hv.step i NNF.ff hqi
        cases hmem
      | prop a =>
        obtain ⟨g, hmem, hg⟩ := hv.step i (NNF.prop a) hqi
        have hmem' := List.mem_singleton.mp hmem
        injection hmem' with hgeq _
        rw [hgeq] at hg
        rw [NNF.satisfies_prop, hzero]; exact hg
      | nprop a =>
        obtain ⟨g, hmem, hg⟩ := hv.step i (NNF.nprop a) hqi
        have hmem' := List.mem_singleton.mp hmem
        injection hmem' with hgeq _
        rw [hgeq] at hg
        rw [NNF.satisfies_nprop, hzero]; exact hg
      | and φ' ψ' =>
        obtain ⟨g, hmem, hg⟩ := hv.step i (NNF.and φ' ψ') hqi
        have hsub := hv.succ_sub i (NNF.and φ' ψ') hqi
        obtain ⟨p, hp, hmem2⟩ := List.mem_flatMap.mp hmem
        obtain ⟨p2, hp2, heq⟩ := List.mem_map.mp hmem2
        injection heq with hgeq hOeq
        apply NNF.one_step_complete (NNF.and φ' ψ') (ξ.drop i) g (r.succ i (NNF.and φ' ψ')) hmem (hzero ▸ hg)
        intro q' hq'
        rw [← hOeq] at hq'
        rcases FinSet.mem_union.mp hq' with hq' | hq'
        · have hqalive : q' ∈ r.level (i + 1) := hsub (hOeq ▸ FinSet.mem_union_left _ hq')
          have hrk : q'.rank < (NNF.and φ' ψ').rank := by
            rcases NNF.vwaaTrans_veryWeak φ' p.1 p.2 hp q' hq' with heq2 | hlt2
            · rw [heq2]; simp only [NNF.rank]; omega
            · simp only [NNF.rank] at hlt2 ⊢; omega
          have hsat := hlower q' hrk (i + 1) hqalive
          rwa [← NNF.satisfies_drop_drop] at hsat
        · have hqalive : q' ∈ r.level (i + 1) := hsub (hOeq ▸ FinSet.mem_union_right _ hq')
          have hrk : q'.rank < (NNF.and φ' ψ').rank := by
            rcases NNF.vwaaTrans_veryWeak ψ' p2.1 p2.2 hp2 q' hq' with heq2 | hlt2
            · rw [heq2]; simp only [NNF.rank]; omega
            · simp only [NNF.rank] at hlt2 ⊢; omega
          have hsat := hlower q' hrk (i + 1) hqalive
          rwa [← NNF.satisfies_drop_drop] at hsat
      | or φ' ψ' =>
        obtain ⟨g, hmem, hg⟩ := hv.step i (NNF.or φ' ψ') hqi
        have hsub := hv.succ_sub i (NNF.or φ' ψ') hqi
        apply NNF.one_step_complete (NNF.or φ' ψ') (ξ.drop i) g (r.succ i (NNF.or φ' ψ')) hmem (hzero ▸ hg)
        intro q' hq'
        have hqalive : q' ∈ r.level (i + 1) := hsub hq'
        rcases List.mem_append.mp hmem with hmem' | hmem'
        · have hrk : q'.rank < (NNF.or φ' ψ').rank := by
            rcases NNF.vwaaTrans_veryWeak φ' g (r.succ i (NNF.or φ' ψ')) hmem' q' hq' with heq2 | hlt2
            · rw [heq2]; simp only [NNF.rank]; omega
            · simp only [NNF.rank] at hlt2 ⊢; omega
          have hsat := hlower q' hrk (i + 1) hqalive
          rwa [← NNF.satisfies_drop_drop] at hsat
        · have hrk : q'.rank < (NNF.or φ' ψ').rank := by
            rcases NNF.vwaaTrans_veryWeak ψ' g (r.succ i (NNF.or φ' ψ')) hmem' q' hq' with heq2 | hlt2
            · rw [heq2]; simp only [NNF.rank]; omega
            · simp only [NNF.rank] at hlt2 ⊢; omega
          have hsat := hlower q' hrk (i + 1) hqalive
          rwa [← NNF.satisfies_drop_drop] at hsat
      | next ψ' =>
        obtain ⟨g, hmem, hg⟩ := hv.step i (NNF.next ψ') hqi
        have hsub := hv.succ_sub i (NNF.next ψ') hqi
        have hmem' := List.mem_singleton.mp hmem
        injection hmem' with _ hOeq
        have hqalive : ψ' ∈ r.level (i + 1) := hsub (hOeq ▸ FinSet.mem_singleton_self ψ')
        have hrk : ψ'.rank < (NNF.next ψ').rank := by simp only [NNF.rank]; omega
        rw [NNF.satisfies_next, NNF.satisfies_drop_drop]
        exact hlower ψ' hrk (i + 1) hqalive
      | «until» φ' ψ' => exact NNF.sound_until φ hv hacc φ' ψ' hlower i hqi
      | «release» φ' ψ' => exact NNF.sound_release φ hv φ' ψ' hlower i hqi
  intro q i hqi
  exact main q.rank q (Nat.le_refl _) i hqi

/-- `ltlVWAA` accepts `ξ` from `{ψ}` exactly when `ψ` is satisfied, the correctness of `[BKŘS12]` §5's construction. -/
theorem NNF.ltlVWAA_correct (φ ψ : NNF α) (ξ : OmegaWord α) :
    (ltlVWAA φ).AcceptsFrom {ψ} ξ ↔ ψ.satisfies ξ := by
  constructor
  · rintro ⟨r, hv, hacc⟩
    exact NNF.sound φ hv hacc ψ 0 (by simpa using hv.init ▸ FinSet.mem_singleton_self ψ)
  · exact NNF.acceptsFrom_of_satisfies ψ φ ξ

end LTLLib
