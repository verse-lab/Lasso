module

/-
  Three instances of `SoundComplete`, following `[GO01]` Step 2 and Remark 3: the plain product `δ''` with `T_f` marks,
  on-the-fly dominance, and OR-merging transitions with equal target and marks.

  The product's transition table has two layers, the per-state alternatives (`combos`) and an optional non-looping
  escape witness per final state (`candidates`). `CompleteTrans` quantifies over every target `prodTrans` allows, not
  only the least one, so a single fixed target per combination does not suffice.

  Defines:
  - `combos`: the product transitions over a list of states
  - `candidates`: every non-looping alternative of a final state, `[GO01]`'s `T_f` witnesses
  - `productSetTGBA`: the product `SetTGBA`, one transition per combination and escape subset
  - `SoundCompleteEverywhere`: `SoundComplete`'s two obligations at every state, not only reachable ones
  - `Dominates`: `[GO01]` Step 2's `≼`, guard at least as broad, target no larger, marks no fewer

  Proves:
  - `productSetTGBA_soundComplete`: the product is sound and complete for `A`, `[GO01]` Theorem 2
  - `soundCompleteEverywhere_of_dominance`: dropping a dominated transition preserves correctness
  - `soundCompleteEverywhere_of_merge`: OR-merging transitions with equal target and marks preserves correctness

  References:
  - `[GO01]` Gastin, Oddoux. Fast LTL to Büchi Automata Translation. CAV'01, LNCS 2102, Theorem 2 Step 2,
    Remark 3.

  Sections:
  - Product transition enumeration
  - Escape witnesses
  - The product instance
  - Soundness
  - Completeness
  - Correctness everywhere
  - On-the-fly dominance
  - OR-merging equal transitions
-/
public import Lasso.LTLtoTGBA.AbstractSpec.VWAAToTGBA
public import Lasso.Data.FinSet
meta import Lasso.Tactic.Set

public section

namespace Lasso

universe u v

variable {Q : Type v} {α : Type u}

/-! ## Product transition enumeration -/

/-- One alternative per state of `l`, guard the conjunction and target the union of the choices, `[GO01]`'s plain
product transition. -/
def combos (A : VWAA Q α) : List Q → List (((α → Prop) → Prop) × FinSet Q)
  | [] => [(fun _ => True, ∅)]
  | q :: qs => (A.trans q).flatMap fun (g, O) =>
      (combos A qs).map fun (g', O') => (fun v => g v ∧ g' v, O ∪ O')

-- The combo built from a specific per-state choice.
private def canonicalCombo (gf : Q → (α → Prop) → Prop) (Of : Q → FinSet Q) :
    List Q → ((α → Prop) → Prop) × FinSet Q
  | [] => (fun _ => True, ∅)
  | q :: qs => (fun v => gf q v ∧ (canonicalCombo gf Of qs).1 v, Of q ∪ (canonicalCombo gf Of qs).2)

private theorem canonicalCombo_mem {A : VWAA Q α} {gf : Q → (α → Prop) → Prop} {Of : Q → FinSet Q} :
    ∀ l, (∀ q ∈ l, (gf q, Of q) ∈ A.trans q) → canonicalCombo gf Of l ∈ combos A l
  | [], _ => List.mem_singleton.mpr rfl
  | q :: qs, h => by
      simp only [combos, canonicalCombo, List.mem_flatMap, List.mem_map]
      exact ⟨(gf q, Of q), h q (List.mem_cons_self ..),
        (canonicalCombo gf Of qs), canonicalCombo_mem qs fun p hp => h p (List.mem_cons_of_mem _ hp), rfl⟩

private theorem canonicalCombo_guard {gf : Q → (α → Prop) → Prop} {Of : Q → FinSet Q} :
    ∀ l v, (canonicalCombo gf Of l).1 v ↔ ∀ q ∈ l, gf q v
  | [], _ => by simp [canonicalCombo]
  | q :: qs, v => by simp [canonicalCombo, canonicalCombo_guard qs v]

private theorem canonicalCombo_target {gf : Q → (α → Prop) → Prop} {Of : Q → FinSet Q} :
    ∀ l, (canonicalCombo gf Of l).2 = l.foldr (fun q acc => Of q ∪ acc) ∅
  | [] => rfl
  | q :: qs => by simp [canonicalCombo, canonicalCombo_target qs]

-- Two per-state target choices agreeing on `l` fold to the same union.
private theorem foldr_union_congr {Of Of' : Q → FinSet Q} {l : List Q} (h : ∀ x ∈ l, Of x = Of' x) :
    l.foldr (fun q acc => Of q ∪ acc) ∅ = l.foldr (fun q acc => Of' q ∪ acc) ∅ := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rw [h x (List.mem_cons_self ..), ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- Full spec of `combos`: over a `Nodup` list, membership is exactly a per-state choice matching
`A.trans`, guard the pointwise conjunction, target the union. `Nodup` is essential, a state repeated in `l`
could otherwise take two different alternatives at its two occurrences, which no single `gf`/`Of` can
represent. -/
theorem mem_combos_iff {A : VWAA Q α} : ∀ (l : List Q), l.Nodup → ∀ (g : (α → Prop) → Prop) (B : FinSet Q),
    (g, B) ∈ combos A l ↔
      ∃ (gf : Q → (α → Prop) → Prop) (Of : Q → FinSet Q),
        (∀ q ∈ l, (gf q, Of q) ∈ A.trans q) ∧ (∀ v, g v ↔ ∀ q ∈ l, gf q v) ∧
        B = l.foldr (fun q acc => Of q ∪ acc) ∅
  | [], _, g, B => by
      constructor
      · intro hmem
        simp only [combos, List.mem_singleton, Prod.mk.injEq] at hmem
        obtain ⟨hg, hB⟩ := hmem
        exact ⟨fun _ _ => False, fun _ => ∅, fun q hq => (List.not_mem_nil hq).elim,
          fun v => by simp [hg], hB⟩
      · rintro ⟨gf, Of, -, hg, hB⟩
        simp only [combos, List.mem_singleton, Prod.mk.injEq]
        exact ⟨funext fun v => propext (by simpa using hg v), hB⟩
  | q :: qs, hnd, g, B => by
      have hqqs : q ∉ qs := (List.nodup_cons.mp hnd).1
      have hndqs : qs.Nodup := (List.nodup_cons.mp hnd).2
      constructor
      · intro hmem
        simp only [combos, List.mem_flatMap, List.mem_map] at hmem
        obtain ⟨⟨g0, O0⟩, hmem0, ⟨g', B'⟩, hmem', heq⟩ := hmem
        obtain ⟨gf', Of', hall', hg', hB'⟩ := (mem_combos_iff qs hndqs g' B').mp hmem'
        obtain ⟨hgeq, hBeq⟩ := Prod.mk.injEq .. |>.mp heq
        classical
        refine ⟨fun x => if x = q then g0 else gf' x, fun x => if x = q then O0 else Of' x, ?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · simpa using hmem0
          · have hxq : x ≠ q := fun h => hqqs (h ▸ hx)
            simpa [hxq] using hall' x hx
        · intro v
          rw [← hgeq]
          simp only [List.mem_cons]
          rw [hg' v]
          constructor
          · rintro ⟨h0, htl⟩; rintro y (rfl | hy)
            · simpa using h0
            · have hyq : y ≠ q := fun h => hqqs (h ▸ hy)
              simpa [hyq] using htl y hy
          · intro h
            refine ⟨by simpa using h q (Or.inl rfl), fun y hy => ?_⟩
            have hyq : y ≠ q := fun h => hqqs (h ▸ hy)
            simpa [hyq] using h y (Or.inr hy)
        · rw [← hBeq]
          show O0 ∪ B' = List.foldr (fun x acc => (if x = q then O0 else Of' x) ∪ acc) ∅ (q :: qs)
          simp only [List.foldr_cons]
          congr 1
          rw [hB']
          apply foldr_union_congr
          intro x hx
          have hxq : x ≠ q := fun h => hqqs (h ▸ hx)
          simp [hxq]
      · rintro ⟨gf, Of, hall, hg, hB⟩
        have hcanon : canonicalCombo gf Of (q :: qs) ∈ combos A (q :: qs) :=
          canonicalCombo_mem _ hall
        have hgeq : (canonicalCombo gf Of (q :: qs)).1 = g := by
          funext v
          exact propext (by rw [canonicalCombo_guard, hg v])
        have hBeq : (canonicalCombo gf Of (q :: qs)).2 = B := by
          rw [hB]; exact canonicalCombo_target _
        have hpair : (g, B) = canonicalCombo gf Of (q :: qs) := by rw [← hgeq, ← hBeq]
        rw [hpair]; exact hcanon

private theorem mem_foldr_union_iff {l : List Q} {Of : Q → FinSet Q} {x : Q} :
    x ∈ l.foldr (fun q acc => Of q ∪ acc) ∅ ↔ ∃ q ∈ l, x ∈ Of q := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldr_cons, FinSet.mem_union, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨q, hq, hxq⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨q, Or.inr hq, hxq⟩
    · rintro ⟨q, rfl | hq, hxq⟩
      · exact Or.inl hxq
      · exact Or.inr ⟨q, hq, hxq⟩

private theorem biUnion_eq_foldr_toList (e : FinSet Q) (Of : Q → FinSet Q) :
    e.biUnion Of = e.toList.foldr (fun q acc => Of q ∪ acc) ∅ :=
  FinSet.ext fun x => by rw [FinSet.mem_biUnion, mem_foldr_union_iff]; simp [FinSet.mem_toList]

/-! ## Escape witnesses -/

/-- Every non-looping alternative of a final state `f`, with its guard and target, `[GO01]`'s `T_f` witnesses. Ranges
over every final in `AF`, so a final pulled into a target by another final's witness still has a candidate. -/
@[expose] noncomputable def candidates (A : VWAA Q α) (AF : FinSet Q) : List (Q × ((α → Prop) → Prop) × FinSet Q) :=
  AF.toList.flatMap fun f => ((A.trans f).filter fun p => decide (f ∉ p.2)).map fun p => (f, p.1, p.2)

theorem mem_candidates_iff {A : VWAA Q α} {AF : FinSet Q} {f : Q} {g : (α → Prop) → Prop} {O : FinSet Q} :
    (f, g, O) ∈ candidates A AF ↔ f ∈ AF ∧ (g, O) ∈ A.trans f ∧ f ∉ O := by
  simp only [candidates, List.mem_flatMap, List.mem_map, List.mem_filter, FinSet.mem_toList,
    decide_eq_true_eq]
  constructor
  · rintro ⟨f', hf', ⟨g', O'⟩, ⟨hmem, hnin⟩, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact ⟨hf', hmem, hnin⟩
  · rintro ⟨hf, hmem, hnin⟩
    exact ⟨f, hf, (g, O), ⟨hmem, hnin⟩, rfl⟩

/-! ## The product instance -/

-- The guard, target and marks contributed by an activated escape subset `S`.
private def escGuard (S : List (Q × ((α → Prop) → Prop) × FinSet Q)) : (α → Prop) → Prop :=
  fun v => ∀ p ∈ S, p.2.1 v

private def escTarget (S : List (Q × ((α → Prop) → Prop) × FinSet Q)) : FinSet Q :=
  (S.map fun p => p.2.2).foldr (· ∪ ·) ∅

private def escMarks (S : List (Q × ((α → Prop) → Prop) × FinSet Q)) : FinSet Q :=
  (S.map Prod.fst).toFinSet

private theorem mem_escTarget_iff {S : List (Q × ((α → Prop) → Prop) × FinSet Q)} {x : Q} :
    x ∈ escTarget S ↔ ∃ p ∈ S, x ∈ p.2.2 := by
  unfold escTarget
  induction S with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.foldr_cons, FinSet.mem_union, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨q, hq, hxq⟩)
      · exact ⟨p, Or.inl rfl, h⟩
      · exact ⟨q, Or.inr hq, hxq⟩
    · rintro ⟨q, rfl | hq, hxq⟩
      · exact Or.inl hxq
      · exact Or.inr ⟨q, hq, hxq⟩

private theorem mem_escMarks_iff {S : List (Q × ((α → Prop) → Prop) × FinSet Q)} {f : Q} :
    f ∈ escMarks S ↔ ∃ p ∈ S, p.1 = f := by
  unfold escMarks; simp [List.mem_toFinSet, List.mem_map, eq_comm]

/-- The product transitions at state `e`, one per combination and escape subset. -/
noncomputable def productSetTrans (A : VWAA Q α) (AF : FinSet Q) (e : FinSet Q) :
    List (((α → Prop) → Prop) × FinSet Q × FinSet Q) :=
  (combos A e.toList).flatMap fun p =>
    (candidates A AF).sublists.map fun S =>
      (fun v => p.1 v ∧ escGuard S v, p.2 ∪ escTarget S, (AF \ (p.2 ∪ escTarget S)) ∪ escMarks S)

private theorem mem_productSetTrans_iff {A : VWAA Q α} {AF : FinSet Q} {e : FinSet Q}
    {g : (α → Prop) → Prop} {e' m : FinSet Q} :
    (g, e', m) ∈ productSetTrans A AF e ↔
      ∃ g0 B, (g0, B) ∈ combos A e.toList ∧ ∃ S ∈ (candidates A AF).sublists,
        g = (fun v => g0 v ∧ escGuard S v) ∧ e' = B ∪ escTarget S ∧ m = (AF \ (B ∪ escTarget S)) ∪ escMarks S := by
  simp only [productSetTrans, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨g0, B⟩, hmemc, S, hS, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2, h3⟩ := heq
    exact ⟨g0, B, hmemc, S, hS, h1.symm, h2.symm, h3.symm⟩
  · rintro ⟨g0, B, hmemc, S, hS, h1, h2, h3⟩
    exact ⟨(g0, B), hmemc, S, hS, by rw [h1, h2, h3]⟩

/-- `[GO01]` Step 2's product TGBA. -/
noncomputable def productSetTGBA (A : VWAA Q α) (AF : FinSet Q) : SetTGBA Q α where
  trans := productSetTrans A AF
  initial := A.initial
  finals := AF

/-! ## Soundness -/

/-- Every product transition satisfies (S). -/
theorem productSetTGBA_soundTrans (A : VWAA Q α) (AF : FinSet Q) (e : FinSet Q) :
    ∀ g e' m, (g, e', m) ∈ productSetTrans A AF e → SoundTrans A e g e' m := by
  intro g e' m hmem v hgv
  obtain ⟨g0, B, hmemc, S, hS, hgeq, he'eq, hmeq⟩ := mem_productSetTrans_iff.mp hmem
  subst hgeq; subst he'eq; subst hmeq
  have hg0v : g0 v := hgv.1
  have hescv : escGuard S v := hgv.2
  obtain ⟨gf, Of, hall, hgiff, hBeq⟩ := (mem_combos_iff e.toList e.nodup_toList g0 B).mp hmemc
  have hgfv : ∀ q ∈ e.toList, gf q v := (hgiff v).mp hg0v
  refine ⟨⟨gf, Of, fun q hq => ⟨hall q (FinSet.mem_toList.mpr hq), hgfv q (FinSet.mem_toList.mpr hq)⟩, ?_⟩, ?_⟩
  · intro x hx
    rw [FinSet.mem_biUnion] at hx
    obtain ⟨q, hq, hxq⟩ := hx
    apply FinSet.mem_union_left
    rw [hBeq]
    exact mem_foldr_union_iff.mpr ⟨q, FinSet.mem_toList.mpr hq, hxq⟩
  · intro f hf
    rcases FinSet.mem_union.mp hf with hf1 | hf2
    · exact Or.inl (FinSet.mem_sdiff.mp hf1).2
    · obtain ⟨p, hpS, hpf⟩ := mem_escMarks_iff.mp hf2
      have hpcand : p ∈ candidates A AF := (List.mem_sublists.mp hS).subset hpS
      obtain ⟨-, hfmem, hfnin⟩ := mem_candidates_iff.mp hpcand
      rw [hpf] at hfmem hfnin
      refine Or.inr ⟨p.2.1, p.2.2, hfmem, hescv p hpS, hfnin, fun x hx => ?_⟩
      exact FinSet.mem_union_right _ (mem_escTarget_iff.mpr ⟨p, hpS, hx⟩)

/-! ## Completeness -/

/-- The product satisfies (C). -/
theorem productSetTGBA_completeTrans (A : VWAA Q α) (AF : FinSet Q) (e : FinSet Q) : CompleteTrans (productSetTGBA A AF) A e := by
  classical
  intro v e' hprod
  obtain ⟨gf, Of, hall, hsub⟩ := hprod
  have hcanonMem : (canonicalCombo gf Of e.toList).1 v ↔ ∀ q ∈ e.toList, gf q v := canonicalCombo_guard e.toList v
  have hmemc : canonicalCombo gf Of e.toList ∈ combos A e.toList :=
    canonicalCombo_mem _ fun q hq => (hall q (FinSet.mem_toList.mp hq)).1
  set g0 := (canonicalCombo gf Of e.toList).1 with hg0def
  set B := (canonicalCombo gf Of e.toList).2 with hBdef
  have hBeq : B = e.toList.foldr (fun q acc => Of q ∪ acc) ∅ := canonicalCombo_target e.toList
  have hBsub : B ⊆ e' := by rw [hBeq, ← biUnion_eq_foldr_toList]; exact hsub
  set S : List (Q × ((α → Prop) → Prop) × FinSet Q) :=
    (candidates A AF).filter fun p => decide (p.2.1 v ∧ p.2.2 ⊆ e') with hSdef
  have hSsub : S ∈ (candidates A AF).sublists := List.mem_sublists.mpr List.filter_sublist
  have hSmem : ∀ p ∈ S, p ∈ candidates A AF ∧ p.2.1 v ∧ p.2.2 ⊆ e' := by
    intro p hp
    have := List.mem_filter.mp hp
    exact ⟨this.1, decide_eq_true_eq.mp this.2⟩
  refine ⟨fun v' => g0 v' ∧ escGuard S v', B ∪ escTarget S, (AF \ (B ∪ escTarget S)) ∪ escMarks S,
    mem_productSetTrans_iff.mpr ⟨g0, B, hmemc, S, hSsub, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · refine ⟨hcanonMem.mpr fun q hq => (hall q (FinSet.mem_toList.mp hq)).2, fun p hp => (hSmem p hp).2.1⟩
  · apply FinSet.union_subset hBsub
    intro x hx
    obtain ⟨p, hpS, hxp⟩ := mem_escTarget_iff.mp hx
    exact (hSmem p hpS).2.2 hxp
  · intro f hfAF hinTf
    by_cases hftgt : f ∈ B ∪ escTarget S
    · refine FinSet.mem_union_right _ ?_
      rw [mem_escMarks_iff]
      rcases hinTf with hfe' | ⟨g, O, hmemA, hgv, hfnO, hOsub⟩
      · exact absurd (FinSet.union_subset hBsub (fun x hx => (mem_escTarget_iff.mp hx).elim
          fun p hp => (hSmem p hp.1).2.2 hp.2) hftgt) hfe'
      · refine ⟨(f, g, O), ?_, rfl⟩
        rw [hSdef, List.mem_filter, decide_eq_true_eq]
        exact ⟨mem_candidates_iff.mpr ⟨hfAF, hmemA, hfnO⟩, hgv, hOsub⟩
    · exact FinSet.mem_union_left _ (FinSet.mem_sdiff.mpr ⟨hfAF, hftgt⟩)

/-- The product is sound and complete for `A`, `[GO01]` Theorem 2. -/
theorem productSetTGBA_soundComplete (A : VWAA Q α) (AF : FinSet Q) (hAF : ∀ q, q ∈ AF ↔ A.final q) :
    SoundComplete (productSetTGBA A AF) A where
  finals_iff := hAF
  sound := fun e _ g e' m hmem => productSetTGBA_soundTrans A AF e g e' m hmem
  complete := fun e _ => productSetTGBA_completeTrans A AF e

/-- The product accepts from every reachable state exactly what `A` accepts, `[GO01]` Theorem 2. -/
theorem productSetTGBA_correct (A : VWAA Q α) (AF : FinSet Q) (hAF : ∀ q, q ∈ AF ↔ A.final q) {e : FinSet Q}
    {ξ : OmegaWord α} (hreach : (productSetTGBA A AF).IsReachable e) :
    (productSetTGBA A AF).AcceptsFrom e ξ ↔ A.AcceptsFrom e ξ :=
  vwaaToTgba_correct (productSetTGBA_soundComplete A AF hAF) hreach

/-! ## Correctness everywhere -/

/-- `SoundComplete`'s two per-state obligations, at every state rather than only reachable ones. -/
structure SoundCompleteEverywhere (T : SetTGBA Q α) (A : VWAA Q α) : Prop where
  finals_iff : ∀ f, f ∈ T.finals ↔ A.final f
  sound : ∀ e g e' m, (g, e', m) ∈ T.trans e → SoundTrans A e g e' m
  complete : ∀ e, CompleteTrans T A e

theorem SoundCompleteEverywhere.soundComplete {T : SetTGBA Q α} {A : VWAA Q α}
    (h : SoundCompleteEverywhere T A) : SoundComplete T A where
  finals_iff := h.finals_iff
  sound := fun e _ => h.sound e
  complete := fun e _ => h.complete e

/-- The product satisfies both obligations at every state. -/
theorem productSetTGBA_soundCompleteEverywhere (A : VWAA Q α) (AF : FinSet Q) (hAF : ∀ q, q ∈ AF ↔ A.final q) :
    SoundCompleteEverywhere (productSetTGBA A AF) A where
  finals_iff := hAF
  sound := productSetTGBA_soundTrans A AF
  complete := productSetTGBA_completeTrans A AF

/-! ## On-the-fly dominance -/

/-- `[GO01]` Step 2's `≼`: `t1`'s guard is at least as broad, its target no larger, and its marks no fewer. -/
@[expose] def Dominates (t1 t2 : ((α → Prop) → Prop) × FinSet Q × FinSet Q) : Prop :=
  (∀ v, t2.1 v → t1.1 v) ∧ t1.2.1 ⊆ t2.2.1 ∧ t2.2.2 ⊆ t1.2.2

/-- Dropping transitions that each have a surviving dominator preserves correctness. -/
theorem soundCompleteEverywhere_of_dominance {T : SetTGBA Q α} {A : VWAA Q α}
    (h : SoundCompleteEverywhere T A) (T' : SetTGBA Q α) (hfin : T'.finals = T.finals)
    (hsub : ∀ e, T'.trans e ⊆ T.trans e)
    (hdom : ∀ e, ∀ t ∈ T.trans e, t ∉ T'.trans e → ∃ t' ∈ T'.trans e, Dominates t' t) :
    SoundCompleteEverywhere T' A where
  finals_iff := fun f => by rw [hfin]; exact h.finals_iff f
  sound := fun e g e' m hmem => h.sound e g e' m (hsub e hmem)
  complete := by
    intro e v e' hprod
    obtain ⟨g, e'', m, hmem, hgv, hsub', hmarks⟩ := h.complete e v e' hprod
    by_cases hmemT' : (g, e'', m) ∈ T'.trans e
    · exact ⟨g, e'', m, hmemT', hgv, hsub', fun f hf hinTf => hmarks f (by rw [← hfin]; exact hf) hinTf⟩
    · obtain ⟨t', hmemT', hg1, he1, hm1⟩ := hdom e (g, e'', m) hmem hmemT'
      exact ⟨t'.1, t'.2.1, t'.2.2, hmemT', hg1 v hgv, he1.trans hsub',
        fun f hf hinTf => hm1 (hmarks f (by rw [← hfin]; exact hf) hinTf)⟩

/-! ## OR-merging equal transitions -/

/-- OR-merging transitions that share a target and marks preserves correctness: every original is dominated by a
survivor, and whenever a survivor's guard fires, some original with its exact target and marks fires too. -/
theorem soundCompleteEverywhere_of_merge {T : SetTGBA Q α} {A : VWAA Q α}
    (h : SoundCompleteEverywhere T A) (T' : SetTGBA Q α) (hfin : T'.finals = T.finals)
    (hcover : ∀ e, ∀ t ∈ T.trans e, ∃ t' ∈ T'.trans e, Dominates t' t)
    (hjust : ∀ e, ∀ t' ∈ T'.trans e, ∀ v, t'.1 v → ∃ t ∈ T.trans e, t.1 v ∧ t.2 = t'.2) :
    SoundCompleteEverywhere T' A where
  finals_iff := fun f => by rw [hfin]; exact h.finals_iff f
  sound := by
    intro e g e' m hmem v hgv
    obtain ⟨t, hmemt, hgtv, heq⟩ := hjust e (g, e', m) hmem v hgv
    have he' : t.2.1 = e' := congrArg Prod.fst heq
    have hm' : t.2.2 = m := congrArg Prod.snd heq
    have := h.sound e t.1 t.2.1 t.2.2 hmemt v hgtv
    rwa [he', hm'] at this
  complete := by
    intro e v e' hprod
    obtain ⟨g, e'', m, hmem, hgv, hsub, hmarks⟩ := h.complete e v e' hprod
    obtain ⟨t', hmemt', hg1, he1, hm1⟩ := hcover e (g, e'', m) hmem
    exact ⟨t'.1, t'.2.1, t'.2.2, hmemt', hg1 v hgv, he1.trans hsub,
      fun f hf hinTf => hm1 (hmarks f (by rw [← hfin]; exact hf) hinTf)⟩
