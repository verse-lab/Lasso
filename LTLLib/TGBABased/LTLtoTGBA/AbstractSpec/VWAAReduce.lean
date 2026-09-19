/-
  VWAA reductions. One letterwise simulation theorem carries `AcceptsFrom` across any transition change meeting a local,
  per-letter condition, and the optimisations of `[BKŘS12]` §5 and `[GO01]` §6 are instances of it. It generalises
  `[HOL4-ltl]`'s `reduced_run` from plain restriction to an arbitrary letterwise simulation, shrinking the original run
  level by level so that every branch of the new run is a branch of the original.

  Defines:
  - `VWAA.TransSim`: `B` simulates `A` letterwise, `[BKŘS12]` §5's local completeness condition
  - `VWAA.ListSim`, `VWAA.TargetsIn`: `TransSim` and target inclusion on a single transition list
  - `VWAA.lprod`: `[BKŘS12]`'s `⊗` on transition lists
  - `VWAA.Reachable`: the states `A` can reach from a level-0 set, ignoring letters
  - `VWAA.RelabelsFrom`: `B` is `A` relabeled along `e`, with left inverse `d`, on the states reachable from `S`

  Proves:
  - `VWAA.veryWeak_of_subset`: very weakness transfers along any target-shrinking transition change
  - `VWAA.ListSim.lprod`, `VWAA.ListSim.append`: `ListSim` is a congruence for `⊗` and `++`
  - `VWAA.acceptsFrom_congr`: `TransSim` in both directions carries `AcceptsFrom` across
  - `VWAA.transSim_of_target_iff`: merging alternatives that share a target, `[BKŘS12]` §5
  - `VWAA.transSim_split`: splitting away a target strictly contained in another alternative's, `[BKŘS12]` §5
  - `VWAA.transSim_drop`: dropping an alternative dominated by another, `[GO01]` §6, `[HOL4-ltl]` `REDUCE_TRANS_CORRECT`
  - `VWAA.acceptsFrom_congr_of_reachable`: changing transitions off the reachable states, `[HOL4-ltl]` `REDUCE_STATE_CORRECT`
  - `VWAA.acceptsFrom_relabel`: relabeling preserves the language

  References:
  - `[BKŘS12]` Babiak, Křetínský, Řehák, Strejček. LTL to Büchi Automata Translation: Fast and More
    Deterministic. TACAS'12, LNCS 7214, §5.
  - `[GO01]` Gastin, Oddoux. Fast LTL to Büchi Automata Translation. CAV'01, LNCS 2102, §6.
  - `[HOL4-ltl]` Jantsch, Norrish. Verifying the LTL to Büchi Automata Translation via Very Weak Alternating
    Automata. ITP'18, and its HOL4 `alterAScript`.

  Sections:
  - Transition lists
  - Letterwise simulation
  - Run shrinking
  - Acceptance agrees
  - Merging transitions to the same target
  - Splitting away a subsumed target
  - Dropping a dominated transition
  - Restricting to reachable states
  - State relabeling
-/
import LTLLib.TGBABased.LTLtoTGBA.AbstractSpec.VWAA
import LTLLib.TGBABased.LTLtoTGBA.AbstractSpec.VWAARuns

namespace LTLLib

universe u v w

variable {Q : Type v} {α : Type u}

/-! ## Transition lists -/

/-- `B` letterwise simulates `A` as lists of alternatives, `VWAA.TransSim` read at a single state. -/
structure VWAA.ListSim (B A : List (((α → Prop) → Prop) × Finset Q)) : Prop where
  sound : ∀ g' O' v, (g', O') ∈ B → g' v → ∃ g O, (g, O) ∈ A ∧ g v ∧ O ⊆ O'
  complete : ∀ g O v, (g, O) ∈ A → g v → ∃ g' O', (g', O') ∈ B ∧ g' v ∧ O' ⊆ O

/-- Every target of `B` already occurs as a target of `A`. -/
def VWAA.TargetsIn (B A : List (((α → Prop) → Prop) × Finset Q)) : Prop := ∀ p ∈ B, ∃ q ∈ A, q.2 = p.2

namespace VWAA.ListSim

theorem refl (A : List (((α → Prop) → Prop) × Finset Q)) : VWAA.ListSim A A where
  sound g O _ h hv := ⟨g, O, h, hv, Finset.Subset.refl _⟩
  complete g O _ h hv := ⟨g, O, h, hv, Finset.Subset.refl _⟩

theorem trans {A B C : List (((α → Prop) → Prop) × Finset Q)} (h1 : VWAA.ListSim C B)
    (h2 : VWAA.ListSim B A) : VWAA.ListSim C A where
  sound g O v h hv := by
    obtain ⟨g1, O1, h1', hv1, hs1⟩ := h1.sound g O v h hv
    obtain ⟨g2, O2, h2', hv2, hs2⟩ := h2.sound g1 O1 v h1' hv1
    exact ⟨g2, O2, h2', hv2, hs2.trans hs1⟩
  complete g O v h hv := by
    obtain ⟨g1, O1, h1', hv1, hs1⟩ := h2.complete g O v h hv
    obtain ⟨g2, O2, h2', hv2, hs2⟩ := h1.complete g1 O1 v h1' hv1
    exact ⟨g2, O2, h2', hv2, hs2.trans hs1⟩

theorem append {A1 A2 B1 B2 : List (((α → Prop) → Prop) × Finset Q)} (h1 : VWAA.ListSim B1 A1)
    (h2 : VWAA.ListSim B2 A2) : VWAA.ListSim (B1 ++ B2) (A1 ++ A2) where
  sound g O v h hv := by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨g', O', h', hv', hs⟩ := h1.sound g O v h hv
      exact ⟨g', O', List.mem_append_left _ h', hv', hs⟩
    · obtain ⟨g', O', h', hv', hs⟩ := h2.sound g O v h hv
      exact ⟨g', O', List.mem_append_right _ h', hv', hs⟩
  complete g O v h hv := by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨g', O', h', hv', hs⟩ := h1.complete g O v h hv
      exact ⟨g', O', List.mem_append_left _ h', hv', hs⟩
    · obtain ⟨g', O', h', hv', hs⟩ := h2.complete g O v h hv
      exact ⟨g', O', List.mem_append_right _ h', hv', hs⟩

end VWAA.ListSim

namespace VWAA.TargetsIn

theorem refl (A : List (((α → Prop) → Prop) × Finset Q)) : VWAA.TargetsIn A A := fun p hp => ⟨p, hp, rfl⟩

theorem trans {A B C : List (((α → Prop) → Prop) × Finset Q)} (h1 : VWAA.TargetsIn C B)
    (h2 : VWAA.TargetsIn B A) : VWAA.TargetsIn C A := by
  intro p hp
  obtain ⟨q, hq, hqp⟩ := h1 p hp
  obtain ⟨r, hr, hrq⟩ := h2 q hq
  exact ⟨r, hr, hrq.trans hqp⟩

theorem append {A1 A2 B1 B2 : List (((α → Prop) → Prop) × Finset Q)} (h1 : VWAA.TargetsIn B1 A1)
    (h2 : VWAA.TargetsIn B2 A2) : VWAA.TargetsIn (B1 ++ B2) (A1 ++ A2) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨q, hq, hqp⟩ := h1 p hp; exact ⟨q, List.mem_append_left _ hq, hqp⟩
  · obtain ⟨q, hq, hqp⟩ := h2 p hp; exact ⟨q, List.mem_append_right _ hq, hqp⟩

end VWAA.TargetsIn

variable [DecidableEq Q]

/-- `[BKŘS12]` §5's `⊗`: every combination of an alternative from each side, guards conjoined and targets unioned. -/
def VWAA.lprod (xs ys : List (((α → Prop) → Prop) × Finset Q)) : List (((α → Prop) → Prop) × Finset Q) :=
  xs.flatMap fun p => ys.map fun q => (fun v => p.1 v ∧ q.1 v, p.2 ∪ q.2)

theorem VWAA.mem_lprod {xs ys : List (((α → Prop) → Prop) × Finset Q)} {p : ((α → Prop) → Prop) × Finset Q} :
    p ∈ VWAA.lprod xs ys ↔ ∃ p1 ∈ xs, ∃ p2 ∈ ys, p = (fun v => p1.1 v ∧ p2.1 v, p1.2 ∪ p2.2) := by
  unfold VWAA.lprod
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨p1, h1, p2, h2, rfl⟩; exact ⟨p1, h1, p2, h2, rfl⟩
  · rintro ⟨p1, h1, p2, h2, rfl⟩; exact ⟨p1, h1, p2, h2, rfl⟩

namespace VWAA.ListSim

theorem lprod {A1 A2 B1 B2 : List (((α → Prop) → Prop) × Finset Q)} (h1 : VWAA.ListSim B1 A1)
    (h2 : VWAA.ListSim B2 A2) : VWAA.ListSim (VWAA.lprod B1 B2) (VWAA.lprod A1 A2) where
  sound g O v h hv := by
    obtain ⟨⟨g1, O1⟩, hm1, ⟨g2, O2⟩, hm2, heq⟩ := VWAA.mem_lprod.mp h
    injection heq with hg hO
    subst hg hO
    obtain ⟨g1', O1', hm1', hv1, hs1⟩ := h1.sound g1 O1 v hm1 hv.1
    obtain ⟨g2', O2', hm2', hv2, hs2⟩ := h2.sound g2 O2 v hm2 hv.2
    exact ⟨_, _, VWAA.mem_lprod.mpr ⟨(g1', O1'), hm1', (g2', O2'), hm2', rfl⟩, ⟨hv1, hv2⟩,
      Finset.union_subset_union hs1 hs2⟩
  complete g O v h hv := by
    obtain ⟨⟨g1, O1⟩, hm1, ⟨g2, O2⟩, hm2, heq⟩ := VWAA.mem_lprod.mp h
    injection heq with hg hO
    subst hg hO
    obtain ⟨g1', O1', hm1', hv1, hs1⟩ := h1.complete g1 O1 v hm1 hv.1
    obtain ⟨g2', O2', hm2', hv2, hs2⟩ := h2.complete g2 O2 v hm2 hv.2
    exact ⟨_, _, VWAA.mem_lprod.mpr ⟨(g1', O1'), hm1', (g2', O2'), hm2', rfl⟩, ⟨hv1, hv2⟩,
      Finset.union_subset_union hs1 hs2⟩

/-- A product with a single always-enabled alternative only adds its target. -/
theorem lprod_top (A : List (((α → Prop) → Prop) × Finset Q)) (G : (α → Prop) → Prop) (O : Finset Q)
    (hG : ∀ v, G v) : VWAA.ListSim (VWAA.lprod A [(G, O)]) (A.map fun p => (p.1, p.2 ∪ O)) where
  sound g O' v h hv := by
    obtain ⟨⟨g1, O1⟩, hm1, _, hm2, heq⟩ := VWAA.mem_lprod.mp h
    rw [List.mem_singleton] at hm2
    subst hm2
    injection heq with hg hO
    subst hg hO
    exact ⟨g1, O1 ∪ O, List.mem_map.mpr ⟨(g1, O1), hm1, rfl⟩, hv.1, Finset.Subset.refl _⟩
  complete g O' v h hv := by
    obtain ⟨⟨g1, O1⟩, hm1, heq⟩ := List.mem_map.mp h
    injection heq with hg hO
    subst hg hO
    exact ⟨_, _, VWAA.mem_lprod.mpr ⟨(g1, O1), hm1, (G, O), List.mem_singleton_self _, rfl⟩, ⟨hv, hG v⟩,
      Finset.Subset.refl _⟩

end VWAA.ListSim

namespace VWAA.TargetsIn

theorem lprod {A1 A2 B1 B2 : List (((α → Prop) → Prop) × Finset Q)} (h1 : VWAA.TargetsIn B1 A1)
    (h2 : VWAA.TargetsIn B2 A2) : VWAA.TargetsIn (VWAA.lprod B1 B2) (VWAA.lprod A1 A2) := by
  intro p hp
  obtain ⟨p1, hm1, p2, hm2, rfl⟩ := VWAA.mem_lprod.mp hp
  obtain ⟨q1, hq1, hq1p⟩ := h1 p1 hm1
  obtain ⟨q2, hq2, hq2p⟩ := h2 p2 hm2
  exact ⟨_, VWAA.mem_lprod.mpr ⟨q1, hq1, q2, hq2, rfl⟩, by simp [hq1p, hq2p]⟩

theorem lprod_top (A : List (((α → Prop) → Prop) × Finset Q)) (G : (α → Prop) → Prop) (O : Finset Q) :
    VWAA.TargetsIn (VWAA.lprod A [(G, O)]) (A.map fun p => (p.1, p.2 ∪ O)) := by
  intro p hp
  obtain ⟨p1, hm1, p2, hm2, rfl⟩ := VWAA.mem_lprod.mp hp
  rw [List.mem_singleton] at hm2
  subst hm2
  exact ⟨(p1.1, p1.2 ∪ O), List.mem_map.mpr ⟨p1, hm1, rfl⟩, rfl⟩

end VWAA.TargetsIn

/-! ## Letterwise simulation -/

/-- `B` letterwise simulates `A`: an alternative enabled at a letter on either side is matched on the other by one enabled
there with a target no larger, `[BKŘS12]` §5's local completeness condition. -/
structure VWAA.TransSim (B A : VWAA Q α) : Prop where
  sound : ∀ q g' O' v, (g', O') ∈ B.trans q → g' v → ∃ g O, (g, O) ∈ A.trans q ∧ g v ∧ O ⊆ O'
  complete : ∀ q g O v, (g, O) ∈ A.trans q → g v → ∃ g' O', (g', O') ∈ B.trans q ∧ g' v ∧ O' ⊆ O

/-- Very weakness transfers along any target-shrinking transition change, reusing the old rank. -/
theorem VWAA.veryWeak_of_subset {A : VWAA Q α} {trans' : Q → List (((α → Prop) → Prop) × Finset Q)}
    (hsub : ∀ q g' O', (g', O') ∈ trans' q → ∃ g O, (g, O) ∈ A.trans q ∧ O' ⊆ O) :
    ∀ q g' O', (g', O') ∈ trans' q → ∀ q' ∈ O', q' = q ∨ A.rank q' < A.rank q := by
  intro q g' O' hmem q' hq'
  obtain ⟨g, O, hgO, hOsub⟩ := hsub q g' O' hmem
  exact A.veryWeak q g O hgO q' (hOsub hq')

/-- Per-state `ListSim` is exactly `TransSim`. -/
theorem VWAA.TransSim.of_listSim {A B : VWAA Q α} (h : ∀ q, VWAA.ListSim (B.trans q) (A.trans q)) :
    VWAA.TransSim B A where
  sound q g O v hm hv := (h q).sound g O v hm hv
  complete q g O v hm hv := (h q).complete g O v hm hv

/-! ## Run shrinking -/

section Shrink

variable {X Y : VWAA Q α} {S : Finset Q} {ξ : OmegaWord α} {r : VWAA.Run Q}

private theorem shrinkEx
    (hstep : ∀ q g O v, (g, O) ∈ X.trans q → g v → ∃ g' O', (g', O') ∈ Y.trans q ∧ g' v ∧ O' ⊆ O)
    (hv : r.ValidFrom X S ξ) (i : Nat) (q : Q) (hq : q ∈ r.level i) :
    ∃ p : ((α → Prop) → Prop) × Finset Q, p ∈ Y.trans q ∧ p.1 (ξ i) ∧ p.2 ⊆ r.succ i q := by
  obtain ⟨g, hg, hgv⟩ := hv.step i q hq
  obtain ⟨g', O', hg'mem, hg'v, hsub⟩ := hstep q g (r.succ i q) (ξ i) hg hgv
  exact ⟨(g', O'), hg'mem, hg'v, hsub⟩

/-- The `Y` transition a live state of `r` commits to, junk off `r`'s levels. -/
private noncomputable def shrinkChoice
    (hstep : ∀ q g O v, (g, O) ∈ X.trans q → g v → ∃ g' O', (g', O') ∈ Y.trans q ∧ g' v ∧ O' ⊆ O)
    (hv : r.ValidFrom X S ξ) (i : Nat) (q : Q) : ((α → Prop) → Prop) × Finset Q :=
  if hq : q ∈ r.level i then Classical.choose (shrinkEx hstep hv i q hq) else (fun _ => False, ∅)

private theorem shrinkChoice_spec
    (hstep : ∀ q g O v, (g, O) ∈ X.trans q → g v → ∃ g' O', (g', O') ∈ Y.trans q ∧ g' v ∧ O' ⊆ O)
    (hv : r.ValidFrom X S ξ) (i q) (hq : q ∈ r.level i) :
    shrinkChoice hstep hv i q ∈ Y.trans q ∧ (shrinkChoice hstep hv i q).1 (ξ i) ∧
      (shrinkChoice hstep hv i q).2 ⊆ r.succ i q := by
  unfold shrinkChoice
  rw [dif_pos hq]
  exact Classical.choose_spec (shrinkEx hstep hv i q hq)

private noncomputable def shrinkSucc
    (hstep : ∀ q g O v, (g, O) ∈ X.trans q → g v → ∃ g' O', (g', O') ∈ Y.trans q ∧ g' v ∧ O' ⊆ O)
    (hv : r.ValidFrom X S ξ) (i : Nat) (q : Q) : Finset Q := (shrinkChoice hstep hv i q).2

private theorem shrinkSucc_subset
    (hstep : ∀ q g O v, (g, O) ∈ X.trans q → g v → ∃ g' O', (g', O') ∈ Y.trans q ∧ g' v ∧ O' ⊆ O)
    (hv : r.ValidFrom X S ξ) (i q) : shrinkSucc hstep hv i q ⊆ r.succ i q := by
  by_cases hq : q ∈ r.level i
  · exact (shrinkChoice_spec hstep hv i q hq).2.2
  · show (shrinkChoice hstep hv i q).2 ⊆ r.succ i q
    unfold shrinkChoice
    rw [dif_neg hq]
    exact Finset.empty_subset _

private noncomputable def shrinkLevel
    (hstep : ∀ q g O v, (g, O) ∈ X.trans q → g v → ∃ g' O', (g', O') ∈ Y.trans q ∧ g' v ∧ O' ⊆ O)
    (hv : r.ValidFrom X S ξ) : Nat → Finset Q
  | 0 => S
  | i + 1 => (shrinkLevel hstep hv i).biUnion (shrinkSucc hstep hv i)

private theorem shrinkLevel_subset
    (hstep : ∀ q g O v, (g, O) ∈ X.trans q → g v → ∃ g' O', (g', O') ∈ Y.trans q ∧ g' v ∧ O' ⊆ O)
    (hv : r.ValidFrom X S ξ) : ∀ i, shrinkLevel hstep hv i ⊆ r.level i
  | 0 => by show S ⊆ r.level 0; rw [hv.init]
  | i + 1 => by
      intro x hx
      simp only [shrinkLevel, Finset.mem_biUnion] at hx
      obtain ⟨q, hq, hxq⟩ := hx
      exact hv.succ_sub i q (shrinkLevel_subset hstep hv i hq) (shrinkSucc_subset hstep hv i q hxq)

/-- The run `r` shrinks to along `hstep`, `[HOL4-ltl]`'s `reduced_run` generalised to any letterwise simulation. -/
private noncomputable def shrinkRun
    (hstep : ∀ q g O v, (g, O) ∈ X.trans q → g v → ∃ g' O', (g', O') ∈ Y.trans q ∧ g' v ∧ O' ⊆ O)
    (hv : r.ValidFrom X S ξ) : VWAA.Run Q where
  level := shrinkLevel hstep hv
  succ := shrinkSucc hstep hv

private theorem shrink_validFrom
    (hstep : ∀ q g O v, (g, O) ∈ X.trans q → g v → ∃ g' O', (g', O') ∈ Y.trans q ∧ g' v ∧ O' ⊆ O)
    (hv : r.ValidFrom X S ξ) : (shrinkRun hstep hv).ValidFrom Y S ξ where
  init := rfl
  step i q hq :=
    have hq' : q ∈ r.level i := shrinkLevel_subset hstep hv i hq
    ⟨(shrinkChoice hstep hv i q).1, (shrinkChoice_spec hstep hv i q hq').1,
      (shrinkChoice_spec hstep hv i q hq').2.1⟩
  succ_sub _ _ hq := Finset.subset_biUnion_of_mem _ hq
  no_orphan _ _ hq := Finset.mem_biUnion.mp hq

/-- Every branch of the shrunk run is a branch of `r`. -/
private theorem shrink_branch_of
    (hstep : ∀ q g O v, (g, O) ∈ X.trans q → g v → ∃ g' O', (g', O') ∈ Y.trans q ∧ g' v ∧ O' ⊆ O)
    (hv : r.ValidFrom X S ξ) {b : Nat → Q} (hb : (shrinkRun hstep hv).InfBranch b) : r.InfBranch b :=
  ⟨shrinkLevel_subset hstep hv 0 hb.1, fun i => shrinkSucc_subset hstep hv i (b i) (hb.2 i)⟩

/-- Shrinking an accepting run of `X` along `hstep` gives an accepting run of `Y` from the same level 0. -/
theorem acceptsFrom_of_transSim_step
    (hstep : ∀ q g O v, (g, O) ∈ X.trans q → g v → ∃ g' O', (g', O') ∈ Y.trans q ∧ g' v ∧ O' ⊆ O)
    (hfinal : Y.final = X.final) (h : X.AcceptsFrom S ξ) : Y.AcceptsFrom S ξ := by
  obtain ⟨r, hv, hacc⟩ := h
  refine ⟨shrinkRun hstep hv, shrink_validFrom hstep hv, ?_⟩
  intro b hb
  rw [hfinal]
  exact hacc b (shrink_branch_of hstep hv hb)

end Shrink

/-! ## Acceptance agrees -/

/-- `TransSim` in both directions carries the language across, `[HOL4-ltl]`'s `reduced_run` generalised to an arbitrary
letterwise simulation. -/
theorem VWAA.acceptsFrom_congr {A A' : VWAA Q α} (hsim : VWAA.TransSim A' A) (hfinal : A'.final = A.final)
    (S : Finset Q) (ξ : OmegaWord α) : A'.AcceptsFrom S ξ ↔ A.AcceptsFrom S ξ :=
  ⟨acceptsFrom_of_transSim_step hsim.sound hfinal.symm, acceptsFrom_of_transSim_step hsim.complete hfinal⟩

/-! ## Merging transitions to the same target -/

/-- A transition change keeping, per target, the letters under which some alternative reaches it is a simulation, which
covers merging equal-target alternatives into one disjunctive guard, `[BKŘS12]` §5. -/
theorem VWAA.transSim_of_target_iff {A A' : VWAA Q α}
    (h : ∀ q O v, (∃ g, (g, O) ∈ A.trans q ∧ g v) ↔ (∃ g', (g', O) ∈ A'.trans q ∧ g' v)) :
    VWAA.TransSim A' A where
  sound q g' O' v hmem hv := by
    obtain ⟨g, hgmem, hgv⟩ := (h q O' v).mpr ⟨g', hmem, hv⟩
    exact ⟨g, O', hgmem, hgv, Finset.Subset.refl _⟩
  complete q g O v hmem hv := by
    obtain ⟨g', hg'mem, hg'v⟩ := (h q O v).mp ⟨g, hmem, hv⟩
    exact ⟨g', O, hg'mem, hg'v, Finset.Subset.refl _⟩

/-! ## Splitting away a subsumed target -/

/-- Conjoining `¬ g₁` to `g₂`'s guard is a simulation whenever `(g₁, O₁)` is another alternative at `q₀` with a strictly
smaller target, `[BKŘS12]` §5. -/
theorem VWAA.transSim_split {A A' : VWAA Q α} {q₀ : Q} {g₁ g₂ : (α → Prop) → Prop} {O₁ O₂ : Finset Q}
    (hsub : O₁ ⊂ O₂) (hg₁mem' : (g₁, O₁) ∈ A'.trans q₀) (hg₂mem : (g₂, O₂) ∈ A.trans q₀)
    (hsplitmem : (fun v => g₂ v ∧ ¬ g₁ v, O₂) ∈ A'.trans q₀)
    (hA'sub : ∀ p, p ∈ A'.trans q₀ → p = (fun v => g₂ v ∧ ¬ g₁ v, O₂) ∨ p ∈ A.trans q₀)
    (hAsub : ∀ p, p ∈ A.trans q₀ → p ≠ (g₂, O₂) → p ∈ A'.trans q₀)
    (hrest : ∀ q, q ≠ q₀ → A'.trans q = A.trans q) :
    VWAA.TransSim A' A where
  sound q g O v hmem hv := by
    by_cases hq : q = q₀
    · subst hq
      rcases hA'sub _ hmem with heq | hmem
      · injection heq with heq1 heq2
        subst heq1; subst heq2
        exact ⟨g₂, O, hg₂mem, hv.1, Finset.Subset.refl _⟩
      · exact ⟨g, O, hmem, hv, Finset.Subset.refl _⟩
    · exact ⟨g, O, by rw [← hrest q hq]; exact hmem, hv, Finset.Subset.refl _⟩
  complete q g O v hmem hv := by
    by_cases hq : q = q₀
    · subst hq
      by_cases heq : (g, O) = (g₂, O₂)
      · injection heq with heq1 heq2
        subst heq1; subst heq2
        by_cases hg₁v : g₁ v
        · exact ⟨g₁, O₁, hg₁mem', hg₁v, hsub.subset⟩
        · exact ⟨fun v => g v ∧ ¬ g₁ v, O, hsplitmem, ⟨hv, hg₁v⟩, Finset.Subset.refl _⟩
      · exact ⟨g, O, hAsub _ hmem heq, hv, Finset.Subset.refl _⟩
    · exact ⟨g, O, by rw [hrest q hq]; exact hmem, hv, Finset.Subset.refl _⟩

/-! ## Dropping a dominated transition -/

/-- Dropping an alternative `(g, O)` at `q₀` is a simulation whenever a surviving `(g', O')` is enabled whenever `g` is
and has a target no larger, `[GO01]` §6, `[HOL4-ltl]` `REDUCE_TRANS_CORRECT`. -/
theorem VWAA.transSim_drop {A A' : VWAA Q α} {q₀ : Q} {g g' : (α → Prop) → Prop} {O O' : Finset Q}
    (hdom : ∀ v, g v → g' v) (hOsub : O' ⊆ O)
    (hg'mem : (g', O') ∈ A.trans q₀) (hg'mem' : (g', O') ∈ A'.trans q₀)
    (hA'sub : ∀ p, p ∈ A'.trans q₀ → p ∈ A.trans q₀)
    (hAsub : ∀ p, p ∈ A.trans q₀ → p ≠ (g, O) → p ∈ A'.trans q₀)
    (hrest : ∀ q, q ≠ q₀ → A'.trans q = A.trans q) :
    VWAA.TransSim A' A where
  sound q g₁ O₁ v hmem hv := by
    by_cases hq : q = q₀
    · subst hq; exact ⟨g₁, O₁, hA'sub _ hmem, hv, Finset.Subset.refl _⟩
    · exact ⟨g₁, O₁, by rw [← hrest q hq]; exact hmem, hv, Finset.Subset.refl _⟩
  complete q g₁ O₁ v hmem hv := by
    by_cases hq : q = q₀
    · subst hq
      by_cases heq : (g₁, O₁) = (g, O)
      · injection heq with heq1 heq2
        subst heq1; subst heq2
        exact ⟨g', O', hg'mem', hdom v hv, hOsub⟩
      · exact ⟨g₁, O₁, hAsub _ hmem heq, hv, Finset.Subset.refl _⟩
    · exact ⟨g₁, O₁, by rw [hrest q hq]; exact hmem, hv, Finset.Subset.refl _⟩

/-! ## Restricting to reachable states -/

/-- The states `A` can reach from `S`, ignoring letters, an over-approximation of what any run visits. -/
inductive VWAA.Reachable (A : VWAA Q α) (S : Finset Q) : Q → Prop
  | base : ∀ q ∈ S, VWAA.Reachable A S q
  | step : ∀ p, VWAA.Reachable A S p → ∀ g O, (g, O) ∈ A.trans p → ∀ q ∈ O, VWAA.Reachable A S q

/-- Every live state of a run is reachable, `[HOL4-ltl]`'s `REDUCE_STATE_CORRECT` side condition. -/
theorem VWAA.reachable_of_mem_level {A : VWAA Q α} {S : Finset Q} {ξ : OmegaWord α} {r : VWAA.Run Q}
    (hv : r.ValidFrom A S ξ) : ∀ i q, q ∈ r.level i → VWAA.Reachable A S q := by
  intro i
  induction i with
  | zero => intro q hq; rw [hv.init] at hq; exact .base q hq
  | succ i ih =>
    intro q hq
    obtain ⟨p, hp, hpq⟩ := hv.no_orphan i q hq
    obtain ⟨g, hgmem, _⟩ := hv.step i p hp
    exact .step p (ih p hp) g (r.succ i p) hgmem q hpq

/-- The same for a run of `A'`, when `A'` agrees with `A` on `A`'s reachable states. -/
private theorem reachable_of_mem_level' {A A' : VWAA Q α} {S : Finset Q} {ξ : OmegaWord α} {r : VWAA.Run Q}
    (htrans : ∀ q, VWAA.Reachable A S q → A'.trans q = A.trans q) (hv' : r.ValidFrom A' S ξ) :
    ∀ i q, q ∈ r.level i → VWAA.Reachable A S q := by
  intro i
  induction i with
  | zero => intro q hq; rw [hv'.init] at hq; exact .base q hq
  | succ i ih =>
    intro q hq
    obtain ⟨p, hp, hpq⟩ := hv'.no_orphan i q hq
    obtain ⟨g', hg'mem, _⟩ := hv'.step i p hp
    have hpreach := ih p hp
    rw [htrans p hpreach] at hg'mem
    exact .step p hpreach g' (r.succ i p) hg'mem q hpq

private theorem validFrom_congr_of_reachable {A A' : VWAA Q α} {S : Finset Q} {ξ : OmegaWord α} {r : VWAA.Run Q}
    (htrans : ∀ q, VWAA.Reachable A S q → A'.trans q = A.trans q) (hv : r.ValidFrom A S ξ) :
    r.ValidFrom A' S ξ where
  init := hv.init
  step i q hq := by rw [htrans q (VWAA.reachable_of_mem_level hv i q hq)]; exact hv.step i q hq
  succ_sub := hv.succ_sub
  no_orphan := hv.no_orphan

private theorem validFrom_congr_of_reachable' {A A' : VWAA Q α} {S : Finset Q} {ξ : OmegaWord α} {r : VWAA.Run Q}
    (htrans : ∀ q, VWAA.Reachable A S q → A'.trans q = A.trans q) (hv' : r.ValidFrom A' S ξ) :
    r.ValidFrom A S ξ where
  init := hv'.init
  step i q hq := by
    rw [← htrans q (reachable_of_mem_level' htrans hv' i q hq)]
    exact hv'.step i q hq
  succ_sub := hv'.succ_sub
  no_orphan := hv'.no_orphan

/-- Changing the transitions off `A`'s reachable states preserves the language from `S`, `[GO01]` §6,
`[HOL4-ltl]` `REDUCE_STATE_CORRECT`. -/
theorem VWAA.acceptsFrom_congr_of_reachable {A A' : VWAA Q α} {S : Finset Q}
    (htrans : ∀ q, VWAA.Reachable A S q → A'.trans q = A.trans q) (hfinal : A'.final = A.final)
    (ξ : OmegaWord α) : A.AcceptsFrom S ξ ↔ A'.AcceptsFrom S ξ := by
  constructor
  · rintro ⟨r, hv, hacc⟩
    refine ⟨r, validFrom_congr_of_reachable htrans hv, ?_⟩
    intro b hb; rw [hfinal]; exact hacc b hb
  · rintro ⟨r, hv', hacc⟩
    refine ⟨r, validFrom_congr_of_reachable' htrans hv', ?_⟩
    intro b hb; rw [← hfinal]; exact hacc b hb

/-! ## State relabeling -/

variable {Q' : Type w} [DecidableEq Q']

/-- `B` is `A` relabeled along `e` on the states reachable from `S`, with `d` a left inverse of `e` there, cf. `[HOL4-ltl]`'s
abstraction functions (`concr2AbstrAA`). -/
structure VWAA.RelabelsFrom (A : VWAA Q α) (S : Finset Q) (e : Q → Q') (d : Q' → Q) (B : VWAA Q' α) : Prop where
  left_inv : ∀ q, VWAA.Reachable A S q → d (e q) = q
  trans : ∀ q, VWAA.Reachable A S q → B.trans (e q) = (A.trans q).map (fun (g, O) => (g, O.image e))
  final : ∀ q, VWAA.Reachable A S q → (B.final (e q) ↔ A.final q)

/-- Every state `B` can reach from `S.image e` is `e` of some state `A` reaches from `S`. -/
theorem relabel_reachable_image {A : VWAA Q α} {S : Finset Q} {e : Q → Q'} {d : Q' → Q} {B : VWAA Q' α}
    (hr : VWAA.RelabelsFrom A S e d B) :
    ∀ q', VWAA.Reachable B (S.image e) q' → ∃ q, VWAA.Reachable A S q ∧ e q = q' := by
  intro q' hq'
  induction hq' with
  | base q' hq'mem =>
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'mem
    exact ⟨q, .base q hq, rfl⟩
  | step p' hp' g' O' hgmem q0 hq0mem ih =>
    obtain ⟨p, hpreach, rfl⟩ := ih
    rw [hr.trans p hpreach] at hgmem
    obtain ⟨⟨g, O⟩, hgOmem, heq⟩ := List.mem_map.mp hgmem
    injection heq with heq1 heq2
    subst heq1; subst heq2
    obtain ⟨q, hqO, rfl⟩ := Finset.mem_image.mp hq0mem
    exact ⟨q, .step p hpreach g O hgOmem q hqO, rfl⟩

/-- `RelabelsFrom` is symmetric, relabeling `B` back to `A` along `d` with `e` as left inverse. -/
theorem VWAA.RelabelsFrom.symm {A : VWAA Q α} {S : Finset Q} {e : Q → Q'} {d : Q' → Q} {B : VWAA Q' α}
    (hr : VWAA.RelabelsFrom A S e d B) : VWAA.RelabelsFrom B (S.image e) d e A where
  left_inv q' hq' := by
    obtain ⟨q, hq, rfl⟩ := relabel_reachable_image hr q' hq'
    rw [hr.left_inv q hq]
  trans q' hq' := by
    obtain ⟨q, hq, rfl⟩ := relabel_reachable_image hr q' hq'
    rw [hr.left_inv q hq, hr.trans q hq, List.map_map]
    have heq : ∀ p ∈ A.trans q,
        ((fun (g, O) => (g, O.image d)) ∘ (fun (g, O) => (g, (O : Finset Q).image e))) p = p := by
      rintro ⟨g, O⟩ hmem
      have hOreach : ∀ o ∈ O, VWAA.Reachable A S o := fun o ho => .step q hq g O hmem o ho
      show (g, (O.image e).image d) = (g, O)
      congr 1
      rw [Finset.image_image]
      exact (Finset.image_congr fun o ho => hr.left_inv o (hOreach o ho)).trans Finset.image_id
    rw [List.map_congr_left heq, List.map_id']
  final q' hq' := by
    obtain ⟨q, hq, rfl⟩ := relabel_reachable_image hr q' hq'
    rw [hr.left_inv q hq]
    exact (hr.final q hq).symm

/-- The relabeled run: levels pushed forward along `e`, and each relabeled state taking the successor set of its `d`-image. -/
noncomputable def relabelRun (e : Q → Q') (d : Q' → Q) (r : VWAA.Run Q) : VWAA.Run Q' where
  level i := (r.level i).image e
  succ i q' := (r.succ i (d q')).image e

private theorem relabel_succ_eq {e : Q → Q'} {d : Q' → Q} {r : VWAA.Run Q} {A : VWAA Q α} {S : Finset Q}
    {B : VWAA Q' α} {ξ : OmegaWord α} (hr : VWAA.RelabelsFrom A S e d B) (hv : r.ValidFrom A S ξ)
    (i : Nat) (q : Q) (hq : q ∈ r.level i) :
    (relabelRun e d r).succ i (e q) = (r.succ i q).image e := by
  show (r.succ i (d (e q))).image e = (r.succ i q).image e
  rw [hr.left_inv q (VWAA.reachable_of_mem_level hv i q hq)]

/-- The relabeled run is a run of `B` from `S.image e`. -/
theorem relabel_validFrom {e : Q → Q'} {d : Q' → Q} {r : VWAA.Run Q} {A : VWAA Q α} {S : Finset Q}
    {B : VWAA Q' α} {ξ : OmegaWord α} (hr : VWAA.RelabelsFrom A S e d B) (hv : r.ValidFrom A S ξ) :
    (relabelRun e d r).ValidFrom B (S.image e) ξ where
  init := by show (r.level 0).image e = S.image e; rw [hv.init]
  step i q' hq' := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
    have hreach := VWAA.reachable_of_mem_level hv i q hq
    obtain ⟨g, hgmem, hgv⟩ := hv.step i q hq
    refine ⟨g, ?_, hgv⟩
    rw [relabel_succ_eq hr hv i q hq, hr.trans q hreach]
    exact List.mem_map.mpr ⟨(g, r.succ i q), hgmem, rfl⟩
  succ_sub i q' hq' := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
    rw [relabel_succ_eq hr hv i q hq]
    exact Finset.image_subset_image (hv.succ_sub i q hq)
  no_orphan i q' hq' := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
    obtain ⟨p, hp, hpq⟩ := hv.no_orphan i q hq
    refine ⟨e p, Finset.mem_image_of_mem e hp, ?_⟩
    rw [relabel_succ_eq hr hv i p hp]
    exact Finset.mem_image_of_mem e hpq

/-- A branch of the relabeled run pulls back along `d` to states alive in `r`. -/
private theorem relabel_pullback_mem_level {e : Q → Q'} {d : Q' → Q} {r : VWAA.Run Q} {A : VWAA Q α}
    {S : Finset Q} {B : VWAA Q' α} {ξ : OmegaWord α} (hr : VWAA.RelabelsFrom A S e d B)
    (hv : r.ValidFrom A S ξ) {b' : Nat → Q'} (hb' : (relabelRun e d r).InfBranch b') :
    ∀ i, d (b' i) ∈ r.level i := by
  intro i
  induction i with
  | zero =>
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hb'.1
    rw [← heq, hr.left_inv q (VWAA.reachable_of_mem_level hv 0 q hq)]
    exact hq
  | succ i ih =>
    have hmem : b' (i + 1) ∈ (r.succ i (d (b' i))).image e := hb'.2 i
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hmem
    have hplevel : p ∈ r.level (i + 1) := hv.succ_sub i (d (b' i)) ih hp
    have hpreach : VWAA.Reachable A S p := VWAA.reachable_of_mem_level hv (i + 1) p hplevel
    rw [← heq, hr.left_inv p hpreach]
    exact hplevel

/-- The pullback, `d ∘ b'`, is an infinite branch of `r` itself. -/
private theorem relabel_pullback_infBranch {e : Q → Q'} {d : Q' → Q} {r : VWAA.Run Q} {A : VWAA Q α}
    {S : Finset Q} {B : VWAA Q' α} {ξ : OmegaWord α} (hr : VWAA.RelabelsFrom A S e d B)
    (hv : r.ValidFrom A S ξ) {b' : Nat → Q'} (hb' : (relabelRun e d r).InfBranch b') :
    r.InfBranch (fun i => d (b' i)) := by
  refine ⟨relabel_pullback_mem_level hr hv hb' 0, fun i => ?_⟩
  show d (b' (i + 1)) ∈ r.succ i (d (b' i))
  have hmem : b' (i + 1) ∈ (r.succ i (d (b' i))).image e := hb'.2 i
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hmem
  have hilevel : d (b' i) ∈ r.level i := relabel_pullback_mem_level hr hv hb' i
  have hplevel : p ∈ r.level (i + 1) := hv.succ_sub i (d (b' i)) hilevel hp
  have hpreach : VWAA.Reachable A S p := VWAA.reachable_of_mem_level hv (i + 1) p hplevel
  rw [← heq, hr.left_inv p hpreach]
  exact hp

/-- Relabeling transports acceptance: `A` accepting from `S` gives `B` accepting from `S.image e`. -/
theorem relabel_acceptsFrom_of {A : VWAA Q α} {S : Finset Q} {e : Q → Q'} {d : Q' → Q} {B : VWAA Q' α}
    {ξ : OmegaWord α} (hr : VWAA.RelabelsFrom A S e d B) (h : A.AcceptsFrom S ξ) :
    B.AcceptsFrom (S.image e) ξ := by
  obtain ⟨r, hv, hacc⟩ := h
  refine ⟨relabelRun e d r, relabel_validFrom hr hv, fun b' hb' => ?_⟩
  have hbranch := relabel_pullback_infBranch hr hv hb'
  have hfin := hacc _ hbranch
  have hlevel := mem_level_of_infBranch (relabel_validFrom hr hv) hb'
  refine Set.Finite.subset hfin fun i (hi : B.final (b' i)) => ?_
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp (hlevel i)
  have hreach := VWAA.reachable_of_mem_level hv i q hq
  have hdi : d (b' i) = q := by rw [← heq, hr.left_inv q hreach]
  show A.final (d (b' i))
  rw [hdi, ← hr.final q hreach, heq]
  exact hi

/-- Relabeling preserves the language, `B` accepting from `S.image e` exactly what `A` accepts from `S`, cf. `[HOL4-ltl]`'s
abstraction functions. -/
theorem VWAA.acceptsFrom_relabel {A : VWAA Q α} {S : Finset Q} {e : Q → Q'} {d : Q' → Q} {B : VWAA Q' α}
    (hr : VWAA.RelabelsFrom A S e d B) (ξ : OmegaWord α) :
    B.AcceptsFrom (S.image e) ξ ↔ A.AcceptsFrom S ξ := by
  have hSid : (S.image e).image d = S := by
    rw [Finset.image_image]
    have : S.image (d ∘ e) = S.image id := Finset.image_congr fun q hq => hr.left_inv q (.base q hq)
    rw [this, Finset.image_id]
  constructor
  · intro h
    have := relabel_acceptsFrom_of hr.symm h
    rwa [hSid] at this
  · exact relabel_acceptsFrom_of hr

end LTLLib
