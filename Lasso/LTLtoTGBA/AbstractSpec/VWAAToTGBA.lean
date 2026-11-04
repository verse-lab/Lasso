module

/-
  Generalised `[GO01]` Theorem 2, `[HOL4-ltl]`'s `GBA_CORRECT`: a TGBA `T` built from a VWAA `A` over the same states
  accepts exactly what `A` accepts, provided every reachable state of `T` meets soundness (S) and completeness (C).
  Both conditions are letterwise, quantifying over individual letters rather than guards, so every concrete construction
  (the product with `T_f` marks, on-the-fly dominance, OR-merging, letterwise label splitting) is an instance with a short
  proof. Marks computed exactly as `T_f` are the most (S) allows and the least (C) demands.

  Defines:
  - `SoundTrans`, `CompleteTrans`: the (S) and (C) conditions at one state
  - `SoundComplete`: (S) and (C) at every reachable state, with the finals matching
  - `CompleteTransTight`, `SoundCompleteTight`: the tight (C) that `[GO01]`'s own proof uses, `[BKŘS12]` §6's modified `T_f`

  Proves:
  - `vwaaToTgba_correct`: under `SoundComplete`, `T.AcceptsFrom e ξ ↔ A.AcceptsFrom e ξ` at every reachable `e`
  - `vwaaToTgba_correct'`: the same under `SoundCompleteTight`

  References:
  - `[GO01]` Gastin, Oddoux. Fast LTL to Büchi Automata Translation. CAV'01, LNCS 2102, Theorem 2.
  - `[BKŘS12]` Babiak, Křetínský, Řehák, Strejček. LTL to Büchi Automata Translation: Fast and More
    Deterministic. TACAS'12, §6 (modified acceptance sets).
  - `[HOL4-ltl]` Jantsch, Norrish. ITP'18, `waa2baScript` theorems `WAA_IN_GBA`, `GBA_IN_WAA`,
    `GBA_CORRECT`.

  Sections:
  - Soundness and completeness conditions
  - TGBA → VWAA direction
  - VWAA → TGBA direction
  - Main equivalence
  - VWAA → TGBA direction, tight completeness
-/
public import Lasso.LTLtoTGBA.AbstractSpec.SetTGBA
public import Lasso.LTLtoTGBA.AbstractSpec.VWAARuns
public import Lasso.Data.FinSet

public section

namespace Lasso

universe u v

variable {Q : Type v} {α : Type u}
variable {A : VWAA Q α} {T : SetTGBA Q α}

/-! ## Soundness and completeness conditions -/

/-- (S) for a transition `(g, e', m)` at `e`: at every letter `v` with `g v`, `e` has a product transition into `e'`,
and every mark satisfies `T_f` at `v`. -/
@[expose] def SoundTrans (A : VWAA Q α) (e : FinSet Q) (g : (α → Prop) → Prop) (e' : FinSet Q)
    (m : FinSet Q) : Prop :=
  ∀ v, g v → A.prodTrans e v e' ∧ ∀ f ∈ m, A.inTf v e' f

/-- (C) at `e`: every product transition at letter `v` to `e'` is refined by an enabled TGBA transition with target inside
`e'` that marks every final satisfying `T_f` at the product target `e'`, `[HOL4-ltl]`'s `D_GEN_HAS_MIN` plus `gba_trans`. -/
@[expose] def CompleteTrans (T : SetTGBA Q α) (A : VWAA Q α) (e : FinSet Q) : Prop :=
  ∀ (v : α → Prop) (e' : FinSet Q), A.prodTrans e v e' →
    ∃ g e'' m, (g, e'', m) ∈ T.trans e ∧ g v ∧ e'' ⊆ e' ∧
      ∀ f ∈ T.finals, A.inTf v e' f → f ∈ m

/-- The combined hypothesis: every reachable state meets (S) and (C), and TGBA finals match VWAA finals. -/
structure SoundComplete (T : SetTGBA Q α) (A : VWAA Q α) : Prop where
  -- finals of T are exactly the co-Büchi final states of A
  finals_iff : ∀ f, f ∈ T.finals ↔ A.final f
  -- every reachable state satisfies (S) on all its transitions
  sound : ∀ e, T.IsReachable e →
    ∀ g e' m, (g, e', m) ∈ T.trans e → SoundTrans A e g e' m
  -- every reachable state satisfies (C)
  complete : ∀ e, T.IsReachable e → CompleteTrans T A e

/-! ## TGBA → VWAA direction -/

-- Level sequence for the VWAA run built from a per-step successor choice.
private def buildLevel (Of : Nat → Q → FinSet Q) (e₀ : FinSet Q) : Nat → FinSet Q
  | 0 => e₀
  | i + 1 => (buildLevel Of e₀ i).biUnion (Of i)

-- `[HOL4-ltl]` `GBA_IN_WAA`, `[GO01]` Theorem 2 ⊆ direction.
private theorem tgba_to_vwaa (hfinals : ∀ f, f ∈ T.finals ↔ A.final f)
    (hsound : ∀ e, T.IsReachable e → ∀ g e' m, (g, e', m) ∈ T.trans e → SoundTrans A e g e' m)
    {e : FinSet Q} {ξ : OmegaWord α} (hreach : T.IsReachable e) (hacc : T.AcceptsFrom e ξ) :
    A.AcceptsFrom e ξ := by
  obtain ⟨r, hrv, hracc⟩ := hacc
  -- Reachability propagates along the run
  have hri : ∀ i, T.IsReachable (r.state i) := by
    intro i; induction i with
    | zero => rwa [hrv.init]
    | succ i ih =>
      obtain ⟨g, htrans, _⟩ := hrv.step i
      obtain ⟨e₀, he₀, hre₀⟩ := ih
      exact ⟨e₀, he₀, hre₀.step ⟨g, _, htrans⟩⟩
  -- (S) at each step: prodTrans and mark justification
  have hS : ∀ i, A.prodTrans (r.state i) (ξ i) (r.state (i + 1)) ∧
      ∀ f ∈ r.mark i, A.inTf (ξ i) (r.state (i + 1)) f := fun i =>
    hsound _ (hri i) _ _ _ (hrv.step i).choose_spec.1 (ξ i) (hrv.step i).choose_spec.2
  -- Non-looping witness for marked finals staying alive
  have hNL : ∀ i f, f ∈ T.finals → f ∈ r.mark i → f ∈ r.state (i + 1) →
      ∃ g O, (g, O) ∈ A.trans f ∧ g (ξ i) ∧ f ∉ O ∧ O ⊆ r.state (i + 1) := by
    intro i f _ hfm hfe
    exact ((hS i).2 f hfm).resolve_left (fun h => h hfe)
  -- Per-step choice of successors: non-looping for marked finals staying alive, default otherwise
  have hchoice : ∀ i, ∃ (Of : Q → FinSet Q),
      (∀ q ∈ r.state i, ∃ g, (g, Of q) ∈ A.trans q ∧ g (ξ i)) ∧
      (∀ q ∈ r.state i, Of q ⊆ r.state (i + 1)) ∧
      (∀ f ∈ T.finals ∩ r.mark i, f ∈ r.state (i + 1) → f ∉ Of f) := by
    intro i
    obtain ⟨gf, Of, hcomp, hbU⟩ := (hS i).1
    -- For each q, pick a non-looping witness if q is a marked final staying alive
    have hoverride : ∀ q ∈ T.finals ∩ r.mark i, q ∈ r.state (i+1) →
        ∃ Of_q : FinSet Q, (∃ g, (g, Of_q) ∈ A.trans q ∧ g (ξ i)) ∧ Of_q ⊆ r.state (i+1) ∧ q ∉ Of_q := by
      intro q hq hq'
      obtain ⟨g, O, hmem, hg, hfO, hOe⟩ := hNL i q
        (FinSet.mem_of_mem_inter_left hq) (FinSet.mem_of_mem_inter_right hq) hq'
      exact ⟨O, ⟨g, hmem, hg⟩, hOe, hfO⟩
    classical
    refine ⟨fun q =>
      if hq : q ∈ T.finals ∩ r.mark i ∧ q ∈ r.state (i + 1) then
        Classical.choose (hoverride q hq.1 hq.2)
      else Of q, ?_, ?_, ?_⟩
    · intro q hq
      by_cases hcase : q ∈ T.finals ∩ r.mark i ∧ q ∈ r.state (i + 1)
      · simp only [dif_pos hcase]
        exact (Classical.choose_spec (hoverride q hcase.1 hcase.2)).1
      · simp only [dif_neg hcase]
        exact ⟨gf q, (hcomp q hq).1, (hcomp q hq).2⟩
    · intro q hq
      by_cases hcase : q ∈ T.finals ∩ r.mark i ∧ q ∈ r.state (i + 1)
      · simp only [dif_pos hcase]
        exact (Classical.choose_spec (hoverride q hcase.1 hcase.2)).2.1
      · simp only [dif_neg hcase]
        exact (FinSet.subset_biUnion_of_mem Of hq).trans hbU
    · intro f hfm hfe
      have hcase : f ∈ T.finals ∩ r.mark i ∧ f ∈ r.state (i + 1) :=
        ⟨hfm, hfe⟩
      simp only [dif_pos hcase]
      exact (Classical.choose_spec (hoverride f hcase.1 hcase.2)).2.2
  let Of : Nat → Q → FinSet Q := fun i => Classical.choose (hchoice i)
  have hOf : ∀ i, (∀ q ∈ r.state i, ∃ g, (g, Of i q) ∈ A.trans q ∧ g (ξ i)) ∧
      (∀ q ∈ r.state i, Of i q ⊆ r.state (i + 1)) ∧
      (∀ f ∈ T.finals ∩ r.mark i, f ∈ r.state (i + 1) → f ∉ Of i f) :=
    fun i => Classical.choose_spec (hchoice i)
  -- The VWAA run
  have hlev_sub : ∀ i, buildLevel Of (r.state 0) i ⊆ r.state i := by
    intro i; induction i with
    | zero => exact FinSet.Subset.refl _
    | succ i ih =>
      intro q hq
      simp only [buildLevel, FinSet.mem_biUnion] at hq
      obtain ⟨p, hp, hpq⟩ := hq
      exact (hOf i).2.1 p (ih hp) hpq
  let rv : VWAA.Run Q := { level := buildLevel Of (r.state 0), succ := Of }
  have hrv_valid : rv.ValidFrom A e ξ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- init
      simp only [rv, buildLevel, hrv.init]
    · -- step
      intro i q hq
      exact (hOf i).1 q (hlev_sub i hq)
    · -- succ_sub
      intro i q hq
      show Of i q ⊆ buildLevel Of (r.state 0) (i + 1)
      simp only [buildLevel]
      exact FinSet.subset_biUnion_of_mem (Of i) hq
    · -- no_orphan
      intro i q hq
      simp only [rv, buildLevel] at hq
      exact FinSet.mem_biUnion.mp hq
  refine ⟨rv, hrv_valid, ?_⟩
  -- Acceptance: no branch stabilises at a final
  rw [acceptingRun_iff hrv_valid]
  intro b q hb hstab hfin
  have hqT : q ∈ T.finals := (hfinals q).mpr hfin
  obtain ⟨N, hstabN⟩ := hstab
  -- Some step n > N marks q, since the TGBA run is accepting
  obtain ⟨n, hqmn, hn⟩ := FinitePred.exists_gt_of_not (hracc q hqT) N
  have hbn : b n = q := hstabN n (by omega)
  have hbn1 : b (n + 1) = q := hstabN (n + 1) (by omega)
  -- b is a branch: q ∈ rv.level n
  have hqln := mem_level_of_infBranch hrv_valid hb n
  rw [hbn] at hqln
  -- b(n+1) = q ∈ rv.succ n (b n) = Of n q
  have hqIn : q ∈ Of n q := by
    have h := hb.2 n; rw [hbn, hbn1] at h; exact h
  -- Of n q ⊆ r.state (n+1), so q ∈ r.state (n+1)
  have hqSub : q ∈ r.state (n + 1) := (hOf n).2.1 q (hlev_sub n hqln) hqIn
  -- Non-looping override: q ∉ Of n q
  exact (hOf n).2.2 q (FinSet.mem_inter.mpr ⟨hqT, hqmn⟩) hqSub hqIn

/-! ## VWAA → TGBA direction -/

-- `[HOL4-ltl]` `WAA_IN_GBA`, `[GO01]` Theorem 2 ⊇ direction.
private theorem vwaa_to_tgba (hsc : SoundComplete T A) {e : FinSet Q} {ξ : OmegaWord α}
    (hreach : T.IsReachable e) (hacc : A.AcceptsFrom e ξ) : T.AcceptsFrom e ξ := by
  obtain ⟨rv, hrv, hracc⟩ := hacc
  -- Step lemma: from any reachable ei ⊆ rv.level i, (C) yields the next TGBA step
  have hstep : ∀ i (ei : FinSet Q), ei ⊆ rv.level i → T.IsReachable ei →
      ∃ g ei1 mi, (g, ei1, mi) ∈ T.trans ei ∧ g (ξ i) ∧ ei1 ⊆ rv.level (i + 1) ∧
        T.IsReachable ei1 ∧ ∀ f ∈ T.finals, A.inTf (ξ i) (rv.level (i + 1)) f → f ∈ mi := by
    intro i ei hei_sub hei_reach
    have hprod : A.prodTrans ei (ξ i) (rv.level (i + 1)) := by
      classical
      exact ⟨fun q => if hq : q ∈ rv.level i then Classical.choose (hrv.step i q hq)
                      else fun _ => False,
             rv.succ i,
             fun q hq => by simp only [dif_pos (hei_sub hq)];
                            exact Classical.choose_spec (hrv.step i q (hei_sub hq)),
             FinSet.biUnion_subset.mpr fun q hq => hrv.succ_sub i q (hei_sub hq)⟩
    obtain ⟨g, ei1, mi, htrans, hg, hsub, hmarks⟩ :=
      hsc.complete ei hei_reach (ξ i) (rv.level (i + 1)) hprod
    obtain ⟨e₀, he₀, hre₀⟩ := hei_reach
    exact ⟨g, ei1, mi, htrans, hg, hsub, ⟨e₀, he₀, hre₀.step ⟨g, mi, htrans⟩⟩, hmarks⟩
  -- The TGBA state sequence, each state inside its VWAA level and reachable
  classical
  let S : ∀ n, {ei : FinSet Q // ei ⊆ rv.level n ∧ T.IsReachable ei} := fun n =>
    Nat.rec ⟨e, hrv.init ▸ FinSet.Subset.refl _, hreach⟩
      (fun n prev =>
        ⟨Classical.choose (Classical.choose_spec
            (hstep n prev.val prev.property.1 prev.property.2)),
         (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
            (hstep n prev.val prev.property.1 prev.property.2)))).2.2.1,
         (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
            (hstep n prev.val prev.property.1 prev.property.2)))).2.2.2.1⟩)
      n
  let eT : Nat → FinSet Q := fun n => (S n).val
  -- The witness `hstep` produces at step n
  let stepSpec := fun n => Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (hstep n (S n).val (S n).property.1 (S n).property.2)))
  let mT : Nat → FinSet Q := fun n =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec
      (hstep n (S n).val (S n).property.1 (S n).property.2)))
  let r : SetTGBA.Run Q := { state := eT, mark := mT }
  have hrv_valid : r.ValidFrom T e ξ :=
    ⟨rfl, fun i => ⟨Classical.choose (hstep i (S i).val (S i).property.1 (S i).property.2),
                     (stepSpec i).1, (stepSpec i).2.1⟩⟩
  -- Acceptance: for each f ∈ T.finals, {i | f ∈ mT i} is infinite
  refine ⟨r, hrv_valid, fun f hfT => ?_⟩
  -- Suppose for contradiction that f is marked only finitely often
  intro hfin_c
  -- From some step N on, f is never marked
  have ⟨N, hN⟩ : ∃ N, ∀ i > N, f ∉ mT i := by
    obtain ⟨N, hN⟩ := FinitePred.nat_iff.mp hfin_c
    exact ⟨N, fun i hi hfm => absurd (hN i hfm) (by omega)⟩
  have hmarks_cond : ∀ i ff, ff ∈ T.finals → A.inTf (ξ i) (rv.level (i + 1)) ff → ff ∈ mT i :=
    fun i => (stepSpec i).2.2.2.2
  -- f ∈ rv.level (i+1) whenever i > N: else `inTf` would trivially hold and mark f
  have hf_alive : ∀ i, N < i → f ∈ rv.level (i + 1) := fun i hi => by
    by_contra hf; exact hN i hi (hmarks_cond i f hfT (Or.inl hf))
  -- f ∈ rv.level (N + 2 + k) for every k
  have hf_all : ∀ k, f ∈ rv.level (N + 2 + k) := by
    intro k; induction k with
    | zero => exact hf_alive (N + 1) (by omega)
    | succ k ih =>
      -- ¬inTf at rv.level (N+2+k) forces f ∈ rv.succ (N+2+k) f
      have hloop : f ∈ rv.succ (N + 2 + k) f := by
        obtain ⟨gf, hmem, hg⟩ := hrv.step (N + 2 + k) f ih
        by_contra hfl
        exact hN (N + 2 + k) (by omega) (hmarks_cond (N + 2 + k) f hfT
          (Or.inr ⟨gf, rv.succ (N + 2 + k) f, hmem, hg, hfl,
            hrv.succ_sub (N + 2 + k) f ih⟩))
      exact hrv.succ_sub _ f ih hloop
  -- f loops at every step from N + 2 on
  have hf_loop : ∀ k, f ∈ rv.succ (N + 2 + k) f := fun k => by
    obtain ⟨gf, hmem, hg⟩ := hrv.step (N + 2 + k) f (hf_all k)
    by_contra hfl
    exact hN (N + 2 + k) (by omega) (hmarks_cond (N + 2 + k) f hfT
      (Or.inr ⟨gf, rv.succ (N + 2 + k) f, hmem, hg, hfl,
        hrv.succ_sub (N + 2 + k) f (hf_all k)⟩))
  -- Path from level 0 to f at level N + 2, then a stuck constant tail: a VWAA branch stuck at final f
  obtain ⟨p, hp_end, hp_start, hp_step⟩ := exists_path_to hrv (N + 2) f (hf_all 0)
  let branch : Nat → Q := fun i => if i ≤ N + 2 then p i else f
  have hbranch : rv.InfBranch branch := ⟨by simp [branch, hp_start], fun i => by
    simp only [branch]
    by_cases hi : i + 1 ≤ N + 2
    · rw [if_pos hi, if_pos (by omega)]; exact hp_step i (by omega)
    · rw [if_neg hi]
      by_cases hi2 : i ≤ N + 2
      · have heqi : i = N + 2 := by omega
        rw [if_pos hi2, heqi, hp_end]; exact hf_loop 0
      · rw [if_neg hi2]
        have heq : i = N + 2 + (i - N - 2) := by omega
        exact heq ▸ hf_loop (i - N - 2)⟩
  have hstab : VWAA.StabilizesAt branch f :=
    ⟨N + 3, fun m hm => if_neg (show ¬(m ≤ N + 2) from by omega)⟩
  -- Contradicts A.AcceptingRun rv, `[GO01]`'s Claim in contrapositive form
  rw [acceptingRun_iff hrv] at hracc
  exact hracc branch f hbranch hstab ((hsc.finals_iff f).mp hfT)

/-! ## Main equivalence -/

/-- `[GO01]` Theorem 2, generalised: a TGBA meeting (S) and (C) at every reachable state accepts from `e` exactly what the
underlying VWAA accepts. -/
theorem vwaaToTgba_correct (hsc : SoundComplete T A) {e : FinSet Q} {ξ : OmegaWord α}
    (hreach : T.IsReachable e) : T.AcceptsFrom e ξ ↔ A.AcceptsFrom e ξ :=
  ⟨tgba_to_vwaa hsc.finals_iff hsc.sound hreach, vwaa_to_tgba hsc hreach⟩

/-! ## VWAA → TGBA direction, tight completeness -/

/-- (C-tight) at `e`: every component choice `(gf, Of)` has an enabled TGBA transition refining `e.biUnion Of` that marks
every final of `e` whose chosen component does not loop (`[BKŘS12]` §6's modified `T_f`) and every final its target drops. -/
@[expose] def CompleteTransTight (T : SetTGBA Q α) (A : VWAA Q α) (e : FinSet Q) : Prop :=
  ∀ (v : α → Prop) (gf : Q → (α → Prop) → Prop) (Of : Q → FinSet Q),
    (∀ q ∈ e, (gf q, Of q) ∈ A.trans q ∧ gf q v) →
    ∃ g e'' m, (g, e'', m) ∈ T.trans e ∧ g v ∧ e'' ⊆ e.biUnion Of ∧
      (∀ f ∈ T.finals, f ∈ e → f ∉ Of f → f ∈ m) ∧ (∀ f ∈ T.finals, f ∉ e'' → f ∈ m)

/-- `SoundComplete` with (C) replaced by (C-tight). -/
structure SoundCompleteTight (T : SetTGBA Q α) (A : VWAA Q α) : Prop where
  finals_iff : ∀ f, f ∈ T.finals ↔ A.final f
  sound : ∀ e, T.IsReachable e → ∀ g e' m, (g, e', m) ∈ T.trans e → SoundTrans A e g e' m
  completeTight : ∀ e, T.IsReachable e → CompleteTransTight T A e

-- `[HOL4-ltl]` `WAA_IN_GBA`, `[GO01]` Theorem 2 ⊇ direction, under (C-tight).
private theorem vwaa_to_tgba' (hsc : SoundCompleteTight T A) {e : FinSet Q} {ξ : OmegaWord α}
    (hreach : T.IsReachable e) (hacc : A.AcceptsFrom e ξ) : T.AcceptsFrom e ξ := by
  obtain ⟨rv, hrv, hracc⟩ := hacc
  have hstep : ∀ i (ei : FinSet Q), ei ⊆ rv.level i → T.IsReachable ei →
      ∃ g ei1 mi, (g, ei1, mi) ∈ T.trans ei ∧ g (ξ i) ∧ ei1 ⊆ ei.biUnion (rv.succ i) ∧
        T.IsReachable ei1 ∧ (∀ f ∈ T.finals, f ∈ ei → f ∉ rv.succ i f → f ∈ mi) ∧
        (∀ f ∈ T.finals, f ∉ ei1 → f ∈ mi) := by
    intro i ei hei_sub hei_reach
    classical
    obtain ⟨g, ei1, mi, htrans, hg, hsub, hmarks, hmarks2⟩ := hsc.completeTight ei hei_reach (ξ i)
      (fun q => if hq : q ∈ ei then Classical.choose (hrv.step i q (hei_sub hq)) else fun _ => False)
      (rv.succ i)
      (fun q hq => by simp only [dif_pos hq]; exact Classical.choose_spec (hrv.step i q (hei_sub hq)))
    obtain ⟨e₀, he₀, hre₀⟩ := hei_reach
    exact ⟨g, ei1, mi, htrans, hg, hsub, ⟨e₀, he₀, hre₀.step ⟨g, mi, htrans⟩⟩, hmarks, hmarks2⟩
  -- The TGBA state sequence, each state inside its VWAA level and reachable
  classical
  let S : ∀ n, {ei : FinSet Q // ei ⊆ rv.level n ∧ T.IsReachable ei} := fun n =>
    Nat.rec ⟨e, hrv.init ▸ FinSet.Subset.refl _, hreach⟩
      (fun n prev =>
        ⟨Classical.choose (Classical.choose_spec
            (hstep n prev.val prev.property.1 prev.property.2)),
         (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
            (hstep n prev.val prev.property.1 prev.property.2)))).2.2.1.trans
          (FinSet.biUnion_subset.mpr fun q hq => hrv.succ_sub n q (prev.property.1 hq)),
         (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
            (hstep n prev.val prev.property.1 prev.property.2)))).2.2.2.1⟩)
      n
  let eT : Nat → FinSet Q := fun n => (S n).val
  let stepSpec := fun n => Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (hstep n (S n).val (S n).property.1 (S n).property.2)))
  let mT : Nat → FinSet Q := fun n =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec
      (hstep n (S n).val (S n).property.1 (S n).property.2)))
  let r : SetTGBA.Run Q := { state := eT, mark := mT }
  have hrv_valid : r.ValidFrom T e ξ :=
    ⟨rfl, fun i => ⟨Classical.choose (hstep i (S i).val (S i).property.1 (S i).property.2),
                     (stepSpec i).1, (stepSpec i).2.1⟩⟩
  refine ⟨r, hrv_valid, fun f hfT => ?_⟩
  -- Suppose for contradiction that f is marked only finitely often
  intro hfin_c
  have ⟨N, hN⟩ : ∃ N, ∀ i > N, f ∉ mT i := by
    obtain ⟨N, hN⟩ := FinitePred.nat_iff.mp hfin_c
    exact ⟨N, fun i hi hfm => absurd (hN i hfm) (by omega)⟩
  have hmarks_cond : ∀ i ff, ff ∈ T.finals → ff ∈ eT i → ff ∉ rv.succ i ff → ff ∈ mT i :=
    fun i => (stepSpec i).2.2.2.2.1
  have hmarks_cond2 : ∀ i ff, ff ∈ T.finals → ff ∉ eT (i + 1) → ff ∈ mT i :=
    fun i => (stepSpec i).2.2.2.2.2
  -- f ∈ eT (i+1) whenever i > N: dropping it from the committed target would mark it immediately
  have hf_alive : ∀ i, N < i → f ∈ eT (i + 1) := fun i hi => by
    by_contra hf; exact hN i hi (hmarks_cond2 i f hfT hf)
  -- f is alive from N + 2 on
  have hf_all : ∀ i, N + 2 ≤ i → f ∈ eT i := by
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = N + 2 + j := ⟨i - N - 2, by omega⟩
    have heq : N + 2 + j = N + 1 + j + 1 := by omega
    rw [heq]
    exact hf_alive (N + 1 + j) (by omega)
  -- f loops at every step from N + 2 on: a non-looping own component would have marked it
  have hf_loop : ∀ i, N + 2 ≤ i → f ∈ rv.succ i f := fun i hi => by
    by_contra hloop
    exact hN i (by omega) (hmarks_cond i f hfT (hf_all i hi) hloop)
  -- Path from level 0 to f at level N + 2, then a stuck constant tail: a VWAA branch stuck at final f
  obtain ⟨p, hp_end, hp_start, hp_step⟩ :=
    exists_path_to hrv (N + 2) f ((S (N + 2)).property.1 (hf_all (N + 2) (Nat.le_refl _)))
  let branch : Nat → Q := fun i => if i ≤ N + 2 then p i else f
  have hbranch : rv.InfBranch branch := ⟨by simp [branch, hp_start], fun i => by
    simp only [branch]
    by_cases hi : i + 1 ≤ N + 2
    · rw [if_pos hi, if_pos (by omega)]; exact hp_step i (by omega)
    · rw [if_neg hi]
      by_cases hi2 : i ≤ N + 2
      · have heqi : i = N + 2 := by omega
        rw [if_pos hi2, heqi, hp_end]; exact hf_loop (N + 2) (Nat.le_refl _)
      · rw [if_neg hi2]; exact hf_loop i (by omega)⟩
  have hstab : VWAA.StabilizesAt branch f :=
    ⟨N + 3, fun m hm => if_neg (show ¬(m ≤ N + 2) from by omega)⟩
  -- Contradicts A.AcceptingRun rv, `[GO01]`'s Claim in contrapositive form
  rw [acceptingRun_iff hrv] at hracc
  exact hracc branch f hbranch hstab ((hsc.finals_iff f).mp hfT)

/-- `[GO01]` Theorem 2 under (C-tight): a TGBA meeting (S) and (C-tight) at every reachable state accepts from `e` exactly
what the underlying VWAA accepts. -/
theorem vwaaToTgba_correct' (hsc : SoundCompleteTight T A) {e : FinSet Q} {ξ : OmegaWord α}
    (hreach : T.IsReachable e) : T.AcceptsFrom e ξ ↔ A.AcceptsFrom e ξ :=
  ⟨tgba_to_vwaa hsc.finals_iff hsc.sound hreach, vwaa_to_tgba' hsc hreach⟩

end Lasso
