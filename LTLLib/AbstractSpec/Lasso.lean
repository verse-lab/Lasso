module

/-
  Transition-based lasso theory. A valid lasso is a stem of edges into a cycle of edges covering every acceptance mark,
  witnessing non-emptiness of a TGBA. Unlike the state-based `ValidLasso.stem`, `TValidLasso.stemE` can be empty, when
  the initial state is the cycle's own head. `TAcceptingCycle.toTValidLassoOf` bridges a state-level `TAcceptingCycle`
  into an edge-level `TValidLasso`, given a `TEdgeWitness` realizing every step and mark as a concrete edge.

  Defines:
  - `tlassoRun`, `TValidLasso`: the run of a lasso and its validity conditions
  - `TEdgeWitness`: a concrete edge for every `succs`-step and every `edgeMarks`-witnessed mark
  - `stemEdges`, `lapFor`, `TAcceptingCycle.cycleE`: the stem and the cycle lifted to edges, one lap per mark
  - `lassoAt`: the `i`-th state of the sequence a stem and a cycle describe

  Proves:
  - `TValidLasso.accepts_of_validLasso`: a valid lasso with compatible labeling implies the automaton accepts
  - `TAcceptingCycle.toTValidLassoOf`: a `TAcceptingCycle` yields a `TValidLasso` for any `TOASpec` with an edge witness
  - `cycleE_endpoints_mem`: every edge of `cycleE` realizes some cyclic step of the cycle
  - `TValidLasso.run_src_hits_cycle`: every cycle state is the source of arbitrarily late run positions
  - `cycleE_src`: edge `j` of `cycleE` leaves the cycle's state `j` modulo its length
  - `TRegionCycle.toTValidLasso_run_src`: the run of a region cycle passes through exactly its states

  Sections:
  - Lasso run construction
  - Validity conditions for a lasso
  - The run is valid and accepting
  - Edge witnesses
  - The bridge from TAcceptingCycle
-/
public import LTLLib.AbstractSpec.Acceptance
public import LTLLib.AbstractSpec.EmptinessCheck

public section

namespace LTLLib

open Lentil

/-! ## Lasso run construction -/

/-- Infinite edge-run built from a stem and a cycle of edges. -/
noncomputable def tlassoRun {Edge : Type u'} (stemE cycleE : List Edge) (default : Edge) : Nat → Edge :=
  fun i =>
    if h : i < stemE.length then stemE[i]
    else if h2 : cycleE.length > 0 then cycleE[(i - stemE.length) % cycleE.length]'(Nat.mod_lt _ h2)
    else default

theorem tlassoRun_stem {Edge : Type u'} (stemE cycleE : List Edge) (d : Edge)
    (i : Nat) (hi : i < stemE.length) :
    tlassoRun stemE cycleE d i = stemE[i]'hi := by
  simp [tlassoRun, hi]

theorem tlassoRun_cycle {Edge : Type u'} (stemE cycleE : List Edge) (d : Edge)
    (hcycle : cycleE.length ≥ 1) (i : Nat) (hi : ¬ i < stemE.length) :
    tlassoRun stemE cycleE d i =
    cycleE[(i - stemE.length) % cycleE.length]'(Nat.mod_lt _ (by omega)) := by
  simp [tlassoRun, hi, show cycleE.length > 0 by omega]

/-- The run lands on cycle index `j` at position `p` whenever `p`'s offset into the cycle region is `j`. -/
theorem tlassoRun_cycle_at {Edge : Type u'} (stemE cycleE : List Edge) (d : Edge)
    (hcycle : cycleE.length ≥ 1) (p j : Nat) (hp : ¬ p < stemE.length)
    (hmod : (p - stemE.length) % cycleE.length = j) (hj : j < cycleE.length) :
    tlassoRun stemE cycleE d p = cycleE[j]'hj := by
  rw [tlassoRun_cycle stemE cycleE d hcycle p hp]
  simp only [hmod]

/-! ## Validity conditions for a lasso -/

/-- A lasso (stem edges + cycle edges) is valid for a `TOASpec` automaton with `k` acceptance marks. -/
structure TValidLasso {State : Type u} {Edge : Type u'} {α : Type v} {k : Nat}
    (A : TOASpec State Edge α k) (stemE cycleE : List Edge) : Prop where
  cycle_nonempty : cycleE.length ≥ 1
  stem_valid : ∀ e ∈ stemE, A.valid e
  stem_chain : ∀ (i : Nat), (hi : i + 1 < stemE.length) →
    A.dst (stemE[i]'(by omega)) = A.src (stemE[i + 1]'(by omega))
  stem_initial : A.initial (A.src ((stemE ++ cycleE).head
    (List.ne_nil_of_length_pos (by simp only [List.length_append]; omega))))
  overlap : ∀ (h : stemE ≠ []), A.dst (stemE.getLast h) =
    A.src (cycleE.head (List.ne_nil_of_length_pos (by omega)))
  cycle_valid : ∀ e ∈ cycleE, A.valid e
  cycle_chain : ∀ (i : Nat), (hi : i + 1 < cycleE.length) →
    A.dst (cycleE[i]'(by omega)) = A.src (cycleE[i + 1]'(by omega))
  cycle_back : A.dst (cycleE.getLast (List.ne_nil_of_length_pos (by omega))) =
    A.src (cycleE.head (List.ne_nil_of_length_pos (by omega)))
  cycle_covers_marks : ∀ m : Fin k, ∃ (i : Nat) (hi : i < cycleE.length), A.acceptMark m (cycleE[i]'hi)

namespace TValidLasso

variable {State : Type u} {Edge : Type u'} {α : Type v} {k : Nat} {A : TOASpec State Edge α k}
  {stemE cycleE : List Edge} (hv : TValidLasso A stemE cycleE)

/-! ## The run is valid and accepting -/

/-- The constructed run (uses `cycleE.head` as default, which is always valid). -/
@[expose] noncomputable def run : Nat → Edge :=
  tlassoRun stemE cycleE (cycleE.head (List.ne_nil_of_length_pos (by have := hv.cycle_nonempty; omega)))

theorem run_eq_stem (i : Nat) (hi : i < stemE.length) : hv.run i = stemE[i]'hi :=
  tlassoRun_stem stemE cycleE _ i hi

theorem run_eq_cycle (i : Nat) (hi : ¬ i < stemE.length) :
    hv.run i = cycleE[(i - stemE.length) % cycleE.length]'
      (Nat.mod_lt _ (by have := hv.cycle_nonempty; omega)) :=
  tlassoRun_cycle stemE cycleE _ hv.cycle_nonempty i hi

private theorem cycle_trans (j : Nat) :
    A.dst (cycleE[j % cycleE.length]'(Nat.mod_lt _ (by have := hv.cycle_nonempty; omega))) =
    A.src (cycleE[(j + 1) % cycleE.length]'(Nat.mod_lt _ (by have := hv.cycle_nonempty; omega))) := by
  by_cases hwrap : j % cycleE.length + 1 < cycleE.length
  · have hmod_succ : (j + 1) % cycleE.length = j % cycleE.length + 1 := by
      calc (j + 1) % cycleE.length
          = (cycleE.length * (j / cycleE.length) + (j % cycleE.length + 1)) % cycleE.length := by
            congr 1; have := Nat.div_add_mod j cycleE.length; omega
        _ = (j % cycleE.length + 1) % cycleE.length := by rw [Nat.mul_add_mod]
        _ = j % cycleE.length + 1 := Nat.mod_eq_of_lt hwrap
    simp only [hmod_succ]
    exact hv.cycle_chain (j % cycleE.length) hwrap
  · have hclen := hv.cycle_nonempty
    have hjmod : j % cycleE.length = cycleE.length - 1 := by
      have := Nat.mod_lt j (show cycleE.length > 0 by omega); omega
    have hmod_succ : (j + 1) % cycleE.length = 0 := by
      calc (j + 1) % cycleE.length
          = (cycleE.length * (j / cycleE.length) + (j % cycleE.length + 1)) % cycleE.length := by
            congr 1; have := Nat.div_add_mod j cycleE.length; omega
        _ = (j % cycleE.length + 1) % cycleE.length := by rw [Nat.mul_add_mod]
        _ = (cycleE.length - 1 + 1) % cycleE.length := by rw [hjmod]
        _ = cycleE.length % cycleE.length := by congr 1; omega
        _ = 0 := Nat.mod_self cycleE.length
    have hback := hv.cycle_back
    have hcpos : cycleE.length > 0 := by omega
    have h1 : cycleE[j % cycleE.length]'(Nat.mod_lt _ hcpos) = cycleE[cycleE.length - 1]'(by omega) := by
      simp only [hjmod]
    have h2 : cycleE[(j + 1) % cycleE.length]'(Nat.mod_lt _ hcpos) = cycleE[0]'(by omega) := by
      simp only [hmod_succ]
    rw [h1, h2]
    rw [show cycleE[cycleE.length - 1]'(by omega) = cycleE.getLast (List.ne_nil_of_length_pos (by omega))
        from (List.getLast_eq_getElem _).symm]
    rw [show cycleE[0]'(by omega) = cycleE.head (List.ne_nil_of_length_pos (by omega))
        from (List.head_eq_getElem _).symm]
    exact hback

/-- The run has valid transitions at every step. -/
theorem run_trans (n : Nat) : A.dst (hv.run n) = A.src (hv.run (n + 1)) := by
  by_cases h1 : n + 1 < stemE.length
  · rw [hv.run_eq_stem n (by omega), hv.run_eq_stem (n + 1) h1]
    exact hv.stem_chain n (by omega)
  · by_cases h2 : n < stemE.length
    · have hneq : n + 1 = stemE.length := by omega
      rw [hv.run_eq_stem n h2, hv.run_eq_cycle (n + 1) (by omega)]
      have hlast : stemE[n]'h2 = stemE.getLast (List.ne_nil_of_length_pos (by omega)) := by
        rw [List.getLast_eq_getElem]; congr 1; omega
      rw [hlast, hv.overlap (List.ne_nil_of_length_pos (by omega))]
      have hidx : (n + 1 - stemE.length) % cycleE.length = 0 := by
        simp [show n + 1 - stemE.length = 0 by omega]
      congr 1
      simp only [hidx, List.head_eq_getElem]
    · rw [hv.run_eq_cycle n (by omega), hv.run_eq_cycle (n + 1) (by omega)]
      have hoff : n + 1 - stemE.length = (n - stemE.length) + 1 := by omega
      rw [hoff]
      exact cycle_trans hv (n - stemE.length)

theorem run_valid (n : Nat) : A.valid (hv.run n) := by
  by_cases h : n < stemE.length
  · rw [hv.run_eq_stem n h]; exact hv.stem_valid _ (List.getElem_mem h)
  · rw [hv.run_eq_cycle n h]; exact hv.cycle_valid _ (List.getElem_mem _)

theorem run_isRun : A.isRun hv.run := by
  refine ⟨?_, fun n => ⟨hv.run_valid n, hv.run_trans n⟩⟩
  by_cases h : 0 < stemE.length
  · rw [hv.run_eq_stem 0 h]
    have : stemE[0]'h = (stemE ++ cycleE).head
        (List.ne_nil_of_length_pos (by simp only [List.length_append]; omega)) := by
      rw [List.head_eq_getElem, List.getElem_append_left h]
    rw [this]; exact hv.stem_initial
  · have hnil : stemE = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    rw [hv.run_eq_cycle 0 (by simp)]
    have : cycleE[(0 - ([] : List Edge).length) % cycleE.length]'
        (Nat.mod_lt _ (by have := hv.cycle_nonempty; omega)) =
        ([] ++ cycleE).head (List.ne_nil_of_length_pos (by
          have := hv.cycle_nonempty; simp only [List.length_append, List.length_nil]; omega)) := by
      simp [List.head_eq_getElem]
    rw [this]
    exact hv.stem_initial

theorem find_cycle_position_at (j0 : Nat) (hj0 : j0 < cycleE.length) (n : Nat) :
    ∃ t, hv.run (n + t) = cycleE[j0]'hj0 := by
  have hcpos : cycleE.length > 0 := by have := hv.cycle_nonempty; omega
  have hle : n ≤ stemE.length + n * cycleE.length + j0 := by
    have : n ≤ n * cycleE.length := Nat.le_mul_of_pos_right n hcpos
    omega
  refine ⟨stemE.length + n * cycleE.length + j0 - n, ?_⟩
  have hsum : n + (stemE.length + n * cycleE.length + j0 - n) =
      stemE.length + n * cycleE.length + j0 := by omega
  show tlassoRun stemE cycleE _ _ = _
  rw [hsum]
  refine tlassoRun_cycle_at stemE cycleE _ hv.cycle_nonempty _ j0 (by omega) ?_ hj0
  rw [show stemE.length + n * cycleE.length + j0 - stemE.length = n * cycleE.length + j0 from by omega,
    Nat.mul_comm n cycleE.length, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hj0

/-- The lasso run carries every mark infinitely often. -/
theorem run_isAccepting : A.isAcceptingRun hv.run := by
  intro m n
  obtain ⟨i, hi, hmark⟩ := hv.cycle_covers_marks m
  obtain ⟨t, ht⟩ := hv.find_cycle_position_at i hi n
  exact ⟨t, ht ▸ hmark⟩

/-- A valid lasso with compatible labeling implies the automaton accepts. -/
theorem accepts_of_validLasso {ξ : OmegaWord α}
    (hcompat : ∀ n, A.labelCompat (hv.run n) (ξ n)) :
    A.accepts ξ :=
  ⟨hv.run, hv.run_isRun, hcompat, hv.run_isAccepting⟩

end TValidLasso

/-! ## Edge witnesses -/

/-- What the generic bridge needs from a concrete `TOASpec`: a way to realize any `succs`-step as a valid edge,
and any `edgeMarks`-witnessed mark as a valid edge carrying it. -/
structure TEdgeWitness {State : Type u} {Edge : Type u'} {α : Type v} {k : Nat}
    (A : TOASpec State Edge α k) (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) where
  stepEdge : State → State → Edge
  stepEdge_spec : ∀ {s s' : State}, s' ∈ succs s →
    A.valid (stepEdge s s') ∧ A.src (stepEdge s s') = s ∧ A.dst (stepEdge s s') = s'
  markEdge : State → State → Nat → Edge
  -- `s' ∈ succs s` is needed too, since in a product the marks alone do not witness that the edge exists.
  markEdge_spec : ∀ {s s' : State} {m : Nat} (hm : m < k), s' ∈ succs s → m ∈ edgeMarks s s' →
    A.valid (markEdge s s' m) ∧ A.src (markEdge s s' m) = s ∧ A.dst (markEdge s s' m) = s' ∧
    A.acceptMark ⟨m, hm⟩ (markEdge s s' m)

/-! ## The bridge from TAcceptingCycle -/

section Bridge

variable {State : Type u} {Edge : Type u'} {α : Type v} {k : Nat} {A : TOASpec State Edge α k}
  {succs : State → Array State} {edgeMarks : State → State → Std.HashSet Nat}
  {initialStates : List State}

/-- One traversal of `stem`'s consecutive pairs, `stepEdge`-lifted, zero edges if `stem` is a single state. -/
@[expose] def stemEdges (stepEdge : State → State → Edge) : List State → List Edge
  | [] => []
  | [_] => []
  | s :: s' :: rest => stepEdge s s' :: stemEdges stepEdge (s' :: rest)

theorem stemEdges_length (stepEdge : State → State → Edge) (stem : List State) :
    (stemEdges stepEdge stem).length = stem.length - 1 := by
  induction stem with
  | nil => simp [stemEdges]
  | cons s rest ih =>
    cases rest with
    | nil => simp [stemEdges]
    | cons s' rest' =>
      simp only [List.length_cons] at ih ⊢
      simp only [stemEdges, List.length_cons]
      omega

/-- Direct index access into `stemEdges`: position `i` is the step edge between `stem`'s states `i` and `i + 1`. -/
theorem stemEdges_getElem (stepEdge : State → State → Edge) (stem : List State) (i : Nat)
    (hi : i + 1 < stem.length) (hi' : i < (stemEdges stepEdge stem).length) :
    (stemEdges stepEdge stem)[i]'hi' = stepEdge (stem[i]'(by omega)) (stem[i + 1]'hi) := by
  induction stem generalizing i with
  | nil => simp at hi
  | cons s rest ih =>
    cases rest with
    | nil => simp at hi
    | cons s' rest' =>
      cases i with
      | zero => simp [stemEdges]
      | succ j =>
        have hj : j + 1 < (s' :: rest').length := by simpa using hi
        have hj' : j < (stemEdges stepEdge (s' :: rest')).length := by
          simpa [stemEdges] using hi'
        have := ih j hj hj'
        simpa [stemEdges] using this

theorem stemEdges_valid (W : TEdgeWitness A succs edgeMarks) (stem : List State)
    (hchain : ∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs stem[i]) :
    ∀ e ∈ stemEdges W.stepEdge stem, A.valid e := by
  induction stem with
  | nil => simp [stemEdges]
  | cons s rest ih =>
    cases rest with
    | nil => simp [stemEdges]
    | cons s' rest' =>
      have hstep : s' ∈ succs s := by simpa using hchain 0 (by simp)
      have hchain' : ∀ i, (hi : i + 1 < (s' :: rest').length) →
          (s' :: rest')[i + 1] ∈ succs (s' :: rest')[i] := fun i hi => by
        have h := hchain (i + 1) (by simpa using hi); simpa using h
      simp only [stemEdges, List.mem_cons]
      rintro e (rfl | he)
      · exact (W.stepEdge_spec hstep).1
      · exact ih hchain' e he

/-- The first stem edge realizes the state chain's own head, whenever both sides are nonempty. -/
theorem stemEdges_head_src (W : TEdgeWitness A succs edgeMarks) (stem : List State)
    (hchain : ∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs stem[i])
    (hne : stemEdges W.stepEdge stem ≠ []) (hsne : stem ≠ []) :
    A.src ((stemEdges W.stepEdge stem).head hne) = stem.head hsne := by
  cases stem with
  | nil => exact absurd rfl hsne
  | cons s rest =>
    cases rest with
    | nil => exact absurd rfl hne
    | cons s' rest' =>
      have hstep : s' ∈ succs s := by simpa using hchain 0 (by simp)
      have hval : (stemEdges W.stepEdge (s :: s' :: rest')).head hne = W.stepEdge s s' := by
        simp [stemEdges, List.head_eq_getElem]
      rw [hval, (W.stepEdge_spec hstep).2.1]
      simp

/-- The last stem edge realizes the state chain's own last state, whenever both sides are nonempty. -/
theorem stemEdges_last_dst (W : TEdgeWitness A succs edgeMarks) (stem : List State)
    (hchain : ∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs stem[i]) :
    ∀ (hne : stemEdges W.stepEdge stem ≠ []) (hsne : stem ≠ []),
      A.dst ((stemEdges W.stepEdge stem).getLast hne) = stem.getLast hsne := by
  induction stem with
  | nil => intro hne _; exact absurd rfl hne
  | cons s rest ih =>
    cases rest with
    | nil => intro hne _; exact absurd rfl hne
    | cons s' rest' =>
      have hstep : s' ∈ succs s := by simpa using hchain 0 (by simp)
      have hchain' : ∀ i, (hi : i + 1 < (s' :: rest').length) →
          (s' :: rest')[i + 1] ∈ succs (s' :: rest')[i] := fun i hi => by
        have h := hchain (i + 1) (by simpa using hi); simpa using h
      cases rest' with
      | nil =>
        intro hne hsne
        have hval : (stemEdges W.stepEdge (s :: s' :: [])).getLast hne = W.stepEdge s s' := by
          simp [stemEdges]
        rw [hval, (W.stepEdge_spec hstep).2.2]
        simp
      | cons s'' rest'' =>
        intro hne hsne
        have htailne : stemEdges W.stepEdge (s' :: s'' :: rest'') ≠ [] := by simp [stemEdges]
        have hstailne : (s' :: s'' :: rest'' : List State) ≠ [] := by simp
        have hval : (stemEdges W.stepEdge (s :: s' :: s'' :: rest'')).getLast hne =
            (stemEdges W.stepEdge (s' :: s'' :: rest'')).getLast htailne := by
          simp [stemEdges]
        rw [hval, ih hchain' htailne hstailne]
        simp [List.getLast_cons hstailne]

/-- The stem-edge chain condition, at every internal position. -/
theorem stemEdges_chain (W : TEdgeWitness A succs edgeMarks) (stem : List State)
    (hchain : ∀ i, (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs stem[i]) :
    ∀ i, (hi : i + 1 < (stemEdges W.stepEdge stem).length) →
      A.dst ((stemEdges W.stepEdge stem)[i]'(by omega)) =
      A.src ((stemEdges W.stepEdge stem)[i + 1]'(by omega)) := by
  induction stem with
  | nil => intro i hi; simp [stemEdges] at hi
  | cons s rest ih =>
    cases rest with
    | nil => intro i hi; simp [stemEdges] at hi
    | cons s' rest' =>
      have hstep : s' ∈ succs s := by simpa using hchain 0 (by simp)
      have hchain' : ∀ i, (hi : i + 1 < (s' :: rest').length) →
          (s' :: rest')[i + 1] ∈ succs (s' :: rest')[i] := fun i hi => by
        have h := hchain (i + 1) (by simpa using hi); simpa using h
      intro i hi
      cases i with
      | zero =>
        by_cases hrest' : rest' = []
        · subst hrest'; simp [stemEdges] at hi
        · have hrne : (s' :: rest' : List State) ≠ [] := by simp
          have htailne : stemEdges W.stepEdge (s' :: rest') ≠ [] := by
            cases rest' with
            | nil => exact absurd rfl hrest'
            | cons s'' rest'' => simp [stemEdges]
          have e0 : (stemEdges W.stepEdge (s :: s' :: rest'))[0]'(by omega) = W.stepEdge s s' := by
            simp [stemEdges]
          have e1 : (stemEdges W.stepEdge (s :: s' :: rest'))[0 + 1]'(by omega) =
              (stemEdges W.stepEdge (s' :: rest')).head htailne := by
            simp [stemEdges, List.head_eq_getElem]
          rw [e0, e1, (W.stepEdge_spec hstep).2.2]
          exact (stemEdges_head_src W (s' :: rest') hchain' htailne hrne).symm
      | succ j =>
        have hlen_eq : (stemEdges W.stepEdge (s :: s' :: rest')).length =
            (stemEdges W.stepEdge (s' :: rest')).length + 1 := by simp [stemEdges]
        have hj : j + 1 < (stemEdges W.stepEdge (s' :: rest')).length := by
          rw [hlen_eq] at hi; omega
        have hres := ih hchain' j hj
        have e1 : (stemEdges W.stepEdge (s :: s' :: rest'))[j + 1]'(by omega) =
            (stemEdges W.stepEdge (s' :: rest'))[j]'(by omega) := by
          simp [stemEdges]
        have e2 : (stemEdges W.stepEdge (s :: s' :: rest'))[j + 1 + 1]'(by omega) =
            (stemEdges W.stepEdge (s' :: rest'))[j + 1]'(by omega) := by
          simp [stemEdges]
        rw [e1, e2]
        exact hres

private theorem list_set_chain_preserved (l : List Edge) (idx : Nat) (newVal : Edge) (hidx : idx < l.length)
    (hsrc : A.src newVal = A.src (l[idx]'hidx)) (hdst : A.dst newVal = A.dst (l[idx]'hidx))
    (hvalid_new : A.valid newVal) (hvalid : ∀ e ∈ l, A.valid e)
    (hchain : ∀ i, (hi : i + 1 < l.length) → A.dst (l[i]'(by omega)) = A.src (l[i + 1]'(by omega))) :
    (∀ e ∈ l.set idx newVal, A.valid e) ∧
    (∀ i, (hi : i + 1 < (l.set idx newVal).length) →
      A.dst ((l.set idx newVal)[i]'(by omega)) = A.src ((l.set idx newVal)[i + 1]'(by omega))) := by
  constructor
  · intro e he
    rcases List.mem_iff_getElem.mp he with ⟨j, hj, rfl⟩
    rw [List.getElem_set]
    split
    · exact hvalid_new
    · exact hvalid _ (List.getElem_mem _)
  · intro i hi
    have hi' : i + 1 < l.length := by simpa using hi
    by_cases h1 : idx = i
    · have e1 : (l.set idx newVal)[i]'(by omega) = newVal := by
        rw [List.getElem_set]; simp [h1]
      have e2 : (l.set idx newVal)[i + 1]'(by omega) = l[i + 1]'hi' := by
        rw [List.getElem_set]; simp [show idx ≠ i + 1 by omega]
      rw [e1, e2, hdst, getElem_congr_idx h1]
      exact hchain i hi'
    · by_cases h2 : idx = i + 1
      · have e1 : (l.set idx newVal)[i]'(by omega) = l[i]'(by omega) := by
          rw [List.getElem_set]; simp [show idx ≠ i by omega]
        have e2 : (l.set idx newVal)[i + 1]'(by omega) = newVal := by
          rw [List.getElem_set]; simp [h2]
        rw [e1, e2, hsrc, getElem_congr_idx h2]
        exact hchain i hi'
      · have e1 : (l.set idx newVal)[i]'(by omega) = l[i]'(by omega) := by
          rw [List.getElem_set]; simp [h1]
        have e2 : (l.set idx newVal)[i + 1]'(by omega) = l[i + 1]'hi' := by
          rw [List.getElem_set]; simp [h2]
        rw [e1, e2]
        exact hchain i hi'

/-- One full traversal of `cycle`'s states closed by `cycle.head`, `markEdge` at `witnessIdx` and `stepEdge` everywhere
else. -/
def lapFor (W : TEdgeWitness A succs edgeMarks) (cycle : List State) (hne : cycle ≠ [])
    (witnessIdx : Nat) (hidx : witnessIdx < cycle.length) (m : Nat) : List Edge :=
  (stemEdges W.stepEdge (cycle ++ [cycle.head hne])).set witnessIdx
    (W.markEdge (cycle[witnessIdx]'hidx)
      (cycle[(witnessIdx + 1) % cycle.length]'(Nat.mod_lt _ (by omega))) m)

private theorem cycleClosed_chain (ac : TAcceptingCycle initialStates succs edgeMarks k) :
    ∀ i, (hi : i + 1 < (ac.cycle ++ [ac.cycle.head
        (List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega))]).length) →
      (ac.cycle ++ [ac.cycle.head
          (List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega))])[i + 1] ∈
        succs ((ac.cycle ++ [ac.cycle.head
          (List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega))])[i]) :=
  chain_append_singleton ac.cycle
    (ac.cycle.head (List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)))
    ac.cycle_chain (List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)) ac.cycle_back

private theorem lapFor_len (W : TEdgeWitness A succs edgeMarks) (cycle : List State) (hne : cycle ≠ [])
    (witnessIdx : Nat) (hidx : witnessIdx < cycle.length) (m : Nat) :
    (lapFor W cycle hne witnessIdx hidx m).length = cycle.length := by
  simp only [lapFor, List.length_set, stemEdges_length, List.length_append, List.length_cons,
    List.length_nil]
  omega

private theorem cycleClosed_getElem_succ (ac : TAcceptingCycle initialStates succs edgeMarks k)
    (hne : ac.cycle ≠ []) (i : Nat) (hi : i < ac.cycle.length) :
    ac.cycle[(i + 1) % ac.cycle.length]'(Nat.mod_lt _ (by have := ac.cycle_nonempty; omega)) =
    (ac.cycle ++ [ac.cycle.head hne])[i + 1]'(by simp; omega) := by
  by_cases h : i + 1 < ac.cycle.length
  · simp [Nat.mod_eq_of_lt h, h]
  · have heq : i + 1 = ac.cycle.length := by omega
    simp [heq, List.head_eq_getElem]

/-- The cyclic successor step, `cycle_chain` and `cycle_back` read as one statement. -/
theorem TAcceptingCycle.cycle_succ_mem (ac : TAcceptingCycle initialStates succs edgeMarks k)
    (hne : ac.cycle ≠ []) (i : Nat) (hi : i < ac.cycle.length) :
    ac.cycle[(i + 1) % ac.cycle.length]'(Nat.mod_lt _ (by have := ac.cycle_nonempty; omega)) ∈
      succs (ac.cycle[i]'hi) := by
  rw [cycleClosed_getElem_succ ac hne i hi]
  have h := cycleClosed_chain ac i (by simp; omega)
  simpa [List.getElem_append_left hi] using h

/-- Every lap edge is valid and goes from `cycle`'s state at its position to the cyclically next one. -/
theorem lapFor_src_dst (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) (hne : ac.cycle ≠ [])
    (witnessIdx : Nat) (hidx : witnessIdx < ac.cycle.length) (m : Nat) (hm : m < k)
    (hcov : m ∈ edgeMarks (ac.cycle[witnessIdx]'hidx)
      (ac.cycle[(witnessIdx + 1) % ac.cycle.length]'(Nat.mod_lt _ (by have := ac.cycle_nonempty; omega))))
    (i : Nat) (hi : i < ac.cycle.length)
    (hi' : i < (lapFor W ac.cycle hne witnessIdx hidx m).length) :
    A.src ((lapFor W ac.cycle hne witnessIdx hidx m)[i]'hi') = ac.cycle[i]'hi ∧
    A.dst ((lapFor W ac.cycle hne witnessIdx hidx m)[i]'hi') =
      ac.cycle[(i + 1) % ac.cycle.length]'(Nat.mod_lt _ (by have := ac.cycle_nonempty; omega)) ∧
    A.valid ((lapFor W ac.cycle hne witnessIdx hidx m)[i]'hi') := by
  have hstepmem := TAcceptingCycle.cycle_succ_mem ac hne i hi
  have hbaselen : (stemEdges W.stepEdge (ac.cycle ++ [ac.cycle.head hne])).length = ac.cycle.length := by
    rw [stemEdges_length]; simp
  have hi'' : i < (stemEdges W.stepEdge (ac.cycle ++ [ac.cycle.head hne])).length := by
    rw [hbaselen]; exact hi
  have hbaseElem : (stemEdges W.stepEdge (ac.cycle ++ [ac.cycle.head hne]))[i]'hi'' =
      W.stepEdge (ac.cycle[i]'hi)
        (ac.cycle[(i + 1) % ac.cycle.length]'(Nat.mod_lt _ (by have := ac.cycle_nonempty; omega))) := by
    rw [stemEdges_getElem W.stepEdge (ac.cycle ++ [ac.cycle.head hne]) i (by simp; omega) hi'']
    congr 1
    · exact List.getElem_append_left hi
    · exact (cycleClosed_getElem_succ ac hne i hi).symm
  unfold lapFor
  rw [List.getElem_set]
  by_cases h : witnessIdx = i
  · subst h
    rw [if_pos rfl]
    exact ⟨(W.markEdge_spec hm hstepmem hcov).2.1, (W.markEdge_spec hm hstepmem hcov).2.2.1,
      (W.markEdge_spec hm hstepmem hcov).1⟩
  · simp only [if_neg h]
    rw [show (stemEdges W.stepEdge (ac.cycle ++ [ac.cycle.head hne]))[i]'(by omega) =
        (stemEdges W.stepEdge (ac.cycle ++ [ac.cycle.head hne]))[i]'hi'' from rfl, hbaseElem]
    exact ⟨(W.stepEdge_spec hstepmem).2.1, (W.stepEdge_spec hstepmem).2.2, (W.stepEdge_spec hstepmem).1⟩

theorem lapFor_valid (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) (hne : ac.cycle ≠ [])
    (witnessIdx : Nat) (hidx : witnessIdx < ac.cycle.length) (m : Nat) (hm : m < k)
    (hcov : m ∈ edgeMarks (ac.cycle[witnessIdx]'hidx)
      (ac.cycle[(witnessIdx + 1) % ac.cycle.length]'(Nat.mod_lt _ (by have := ac.cycle_nonempty; omega)))) :
    ∀ e ∈ lapFor W ac.cycle hne witnessIdx hidx m, A.valid e := by
  intro e he
  rcases List.mem_iff_getElem.mp he with ⟨i, hi, rfl⟩
  have hlen := lapFor_len W ac.cycle hne witnessIdx hidx m
  have hi1 : i < ac.cycle.length := by omega
  exact (lapFor_src_dst W ac hne witnessIdx hidx m hm hcov i hi1 hi).2.2

theorem lapFor_chain (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) (hne : ac.cycle ≠ [])
    (witnessIdx : Nat) (hidx : witnessIdx < ac.cycle.length) (m : Nat) (hm : m < k)
    (hcov : m ∈ edgeMarks (ac.cycle[witnessIdx]'hidx)
      (ac.cycle[(witnessIdx + 1) % ac.cycle.length]'(Nat.mod_lt _ (by have := ac.cycle_nonempty; omega)))) :
    ∀ i, (hi : i + 1 < (lapFor W ac.cycle hne witnessIdx hidx m).length) →
      A.dst ((lapFor W ac.cycle hne witnessIdx hidx m)[i]'(by omega)) =
      A.src ((lapFor W ac.cycle hne witnessIdx hidx m)[i + 1]'(by omega)) := by
  intro i hi
  have hlen := lapFor_len W ac.cycle hne witnessIdx hidx m
  have hi1 : i < ac.cycle.length := by omega
  have hi2 : i + 1 < ac.cycle.length := by omega
  have heq : (i + 1) % ac.cycle.length = i + 1 := Nat.mod_eq_of_lt hi2
  have hd := (lapFor_src_dst W ac hne witnessIdx hidx m hm hcov i hi1 (by omega)).2.1
  have hs := (lapFor_src_dst W ac hne witnessIdx hidx m hm hcov (i + 1) hi2 (by omega)).1
  rw [hd, hs]
  simp [heq]

theorem lapFor_head (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) (hne : ac.cycle ≠ [])
    (witnessIdx : Nat) (hidx : witnessIdx < ac.cycle.length) (m : Nat) (hm : m < k)
    (hcov : m ∈ edgeMarks (ac.cycle[witnessIdx]'hidx)
      (ac.cycle[(witnessIdx + 1) % ac.cycle.length]'(Nat.mod_lt _ (by have := ac.cycle_nonempty; omega))))
    (hne' : lapFor W ac.cycle hne witnessIdx hidx m ≠ []) :
    A.src ((lapFor W ac.cycle hne witnessIdx hidx m).head hne') = ac.cycle.head hne := by
  have hlen := lapFor_len W ac.cycle hne witnessIdx hidx m
  have h0 : 0 < ac.cycle.length := by have := ac.cycle_nonempty; omega
  have h0' : 0 < (lapFor W ac.cycle hne witnessIdx hidx m).length := by omega
  rw [List.head_eq_getElem hne', (lapFor_src_dst W ac hne witnessIdx hidx m hm hcov 0 h0 h0').1]
  exact (List.head_eq_getElem hne).symm

theorem lapFor_last (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) (hne : ac.cycle ≠ [])
    (witnessIdx : Nat) (hidx : witnessIdx < ac.cycle.length) (m : Nat) (hm : m < k)
    (hcov : m ∈ edgeMarks (ac.cycle[witnessIdx]'hidx)
      (ac.cycle[(witnessIdx + 1) % ac.cycle.length]'(Nat.mod_lt _ (by have := ac.cycle_nonempty; omega))))
    (hne' : lapFor W ac.cycle hne witnessIdx hidx m ≠ []) :
    A.dst ((lapFor W ac.cycle hne witnessIdx hidx m).getLast hne') = ac.cycle.head hne := by
  have hlen := lapFor_len W ac.cycle hne witnessIdx hidx m
  have hL : ac.cycle.length ≥ 1 := by have := ac.cycle_nonempty; omega
  have hidxL : ac.cycle.length - 1 < ac.cycle.length := by omega
  have hidxL' : ac.cycle.length - 1 < (lapFor W ac.cycle hne witnessIdx hidx m).length := by omega
  have hgl : (lapFor W ac.cycle hne witnessIdx hidx m).getLast hne' =
      (lapFor W ac.cycle hne witnessIdx hidx m)[ac.cycle.length - 1]'hidxL' := by
    rw [List.getLast_eq_getElem]; congr 1; omega
  rw [hgl, (lapFor_src_dst W ac hne witnessIdx hidx m hm hcov (ac.cycle.length - 1) hidxL hidxL').2.1]
  have heq : (ac.cycle.length - 1 + 1) % ac.cycle.length = 0 := by
    rw [show ac.cycle.length - 1 + 1 = ac.cycle.length from by omega]; simp
  simp [heq, List.head_eq_getElem hne]

theorem lapFor_mark (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) (hne : ac.cycle ≠ [])
    (witnessIdx : Nat) (hidx : witnessIdx < ac.cycle.length) (m : Nat) (hm : m < k)
    (hcov : m ∈ edgeMarks (ac.cycle[witnessIdx]'hidx)
      (ac.cycle[(witnessIdx + 1) % ac.cycle.length]'(Nat.mod_lt _ (by have := ac.cycle_nonempty; omega)))) :
    ∃ (i : Nat) (hi : i < (lapFor W ac.cycle hne witnessIdx hidx m).length),
      A.acceptMark ⟨m, hm⟩ ((lapFor W ac.cycle hne witnessIdx hidx m)[i]'hi) := by
  have hlen := lapFor_len W ac.cycle hne witnessIdx hidx m
  have hstepmem := TAcceptingCycle.cycle_succ_mem ac hne witnessIdx hidx
  refine ⟨witnessIdx, by omega, ?_⟩
  unfold lapFor
  rw [List.getElem_set, if_pos rfl]
  exact (W.markEdge_spec hm hstepmem hcov).2.2.2

private theorem edgeChain_tail (a : Edge) (l : List Edge)
    (hchain : ∀ i, (hi : i + 1 < (a :: l).length) →
      A.dst ((a :: l)[i]'(by omega)) = A.src ((a :: l)[i + 1]'(by omega))) :
    ∀ i, (hi : i + 1 < l.length) → A.dst (l[i]'(by omega)) = A.src (l[i + 1]'(by omega)) := by
  intro i hi
  have h := hchain (i + 1) (by simpa using hi)
  simpa using h

private theorem edgeChain_cons (a : Edge) (l : List Edge) (hne : l ≠ [])
    (hchain : ∀ i, (hi : i + 1 < l.length) → A.dst (l[i]'(by omega)) = A.src (l[i + 1]'(by omega)))
    (hedge : A.dst a = A.src (l.head hne)) :
    ∀ i, (hi : i + 1 < (a :: l).length) →
      A.dst ((a :: l)[i]'(by omega)) = A.src ((a :: l)[i + 1]'(by omega)) := by
  intro i hi
  cases i with
  | zero => simpa [List.head_eq_getElem] using hedge
  | succ j =>
    have hj : j + 1 < l.length := by simpa using hi
    simpa using hchain j hj

private theorem edgeChain_append (l1 l2 : List Edge)
    (hchain1 : ∀ i, (hi : i + 1 < l1.length) → A.dst (l1[i]'(by omega)) = A.src (l1[i + 1]'(by omega)))
    (hchain2 : ∀ i, (hi : i + 1 < l2.length) → A.dst (l2[i]'(by omega)) = A.src (l2[i + 1]'(by omega)))
    (hne1 : l1 ≠ []) (hne2 : l2 ≠ [])
    (hedge : A.dst (l1.getLast hne1) = A.src (l2.head hne2)) :
    ∀ i, (hi : i + 1 < (l1 ++ l2).length) →
      A.dst ((l1 ++ l2)[i]'(by omega)) = A.src ((l1 ++ l2)[i + 1]'(by omega)) := by
  induction l1 with
  | nil => exact absurd rfl hne1
  | cons a as ih =>
    cases as with
    | nil =>
      simp only [List.getLast_singleton] at hedge
      simpa using edgeChain_cons a l2 hne2 hchain2 hedge
    | cons b bs =>
      have hasne : (b :: bs : List Edge) ≠ [] := by simp
      have hgetlast_eq : (a :: b :: bs).getLast (by simp) = (b :: bs).getLast hasne :=
        List.getLast_cons hasne
      rw [hgetlast_eq] at hedge
      have hchain_as : ∀ i, (hi : i + 1 < (b :: bs).length) →
          A.dst ((b :: bs)[i]'(by omega)) = A.src ((b :: bs)[i + 1]'(by omega)) :=
        edgeChain_tail a (b :: bs) hchain1
      have hrec := ih hchain_as hasne hedge
      have hab : A.dst a = A.src ((b :: bs).head (by simp)) := by
        have h0 := hchain1 0 (by simp)
        simpa using h0
      simpa using edgeChain_cons a ((b :: bs) ++ l2) (by simp) hrec (by simpa using hab)

private theorem flatMap_loop_spec (c : State) (f : Nat → List Edge) (n : Nat) (hn : n ≥ 1)
    (hlen : ∀ m, m < n → (f m).length ≥ 1)
    (hvalid : ∀ m, m < n → ∀ e ∈ f m, A.valid e)
    (hchain : ∀ m, m < n → ∀ i, (hi : i + 1 < (f m).length) →
      A.dst ((f m)[i]'(by omega)) = A.src ((f m)[i + 1]'(by omega)))
    (hhead : ∀ m, (hm : m < n) →
      A.src ((f m).head (List.ne_nil_of_length_pos (by have := hlen m hm; omega))) = c)
    (hlast : ∀ m, (hm : m < n) →
      A.dst ((f m).getLast (List.ne_nil_of_length_pos (by have := hlen m hm; omega))) = c) :
    ((List.range n).flatMap f).length ≥ 1 ∧
    (∀ e ∈ (List.range n).flatMap f, A.valid e) ∧
    (∀ i, (hi : i + 1 < ((List.range n).flatMap f).length) →
      A.dst (((List.range n).flatMap f)[i]'(by omega)) =
      A.src (((List.range n).flatMap f)[i + 1]'(by omega))) ∧
    (∀ (hne' : (List.range n).flatMap f ≠ []), A.src (((List.range n).flatMap f).head hne') = c) ∧
    (∀ (hne' : (List.range n).flatMap f ≠ []), A.dst (((List.range n).flatMap f).getLast hne') = c) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      simp only [List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      exact ⟨hlen 0 (by omega), hvalid 0 (by omega), hchain 0 (by omega),
        fun _ => hhead 0 (by omega), fun _ => hlast 0 (by omega)⟩
    · obtain ⟨hlen', hvalid', hchain', hhead', hlast'⟩ :=
        ih hnpos (fun m hm => hlen m (by omega)) (fun m hm => hvalid m (by omega))
          (fun m hm => hchain m (by omega)) (fun m hm => hhead m (by omega))
          (fun m hm => hlast m (by omega))
      simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      have hne1 : (List.range n).flatMap f ≠ [] := List.ne_nil_of_length_pos (by omega)
      have hne2 : f n ≠ [] := List.ne_nil_of_length_pos (by have := hlen n (by omega); omega)
      have hedge : A.dst (((List.range n).flatMap f).getLast hne1) = A.src ((f n).head hne2) := by
        rw [hlast' hne1, hhead n (by omega)]
      refine ⟨?_, ?_, edgeChain_append _ _ hchain' (hchain n (by omega)) hne1 hne2 hedge, ?_, ?_⟩
      · simp only [List.length_append]; have := hlen n (by omega); omega
      · intro e he
        rcases List.mem_append.mp he with h | h
        · exact hvalid' e h
        · exact hvalid n (by omega) e h
      · intro _; rw [List.head_append_of_ne_nil hne1]; exact hhead' hne1
      · intro _; rw [List.getLast_append_right hne2]; exact hlast n (by omega)

private theorem flatMap_uniform_length (f : Nat → List Edge) (L n : Nat)
    (hflen : ∀ i, i < n → (f i).length = L) :
    ((List.range n).flatMap f).length = n * L := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append, ih (fun i hi => hflen i (by omega)), hflen n (by omega), Nat.succ_mul]

private theorem flatMap_uniform_getElem (f : Nat → List Edge) (L n m j : Nat)
    (hflen : ∀ i, i < n → (f i).length = L) (hm : m < n) (hj : j < L) :
    ∃ hidx : m * L + j < ((List.range n).flatMap f).length,
      ((List.range n).flatMap f)[m * L + j]'hidx = (f m)[j]'(by have := hflen m hm; omega) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hlen_n : ((List.range n).flatMap f).length = n * L :=
      flatMap_uniform_length f L n (fun i hi => hflen i (by omega))
    by_cases hmn : m < n
    · obtain ⟨hidx, heq⟩ := ih (fun i hi => hflen i (by omega)) hmn
      have hmL : m * L + L ≤ n * L := by
        have h1 : (m + 1) * L = m * L + L := by rw [Nat.succ_mul]
        have h2 : (m + 1) * L ≤ n * L := Nat.mul_le_mul (by omega) (Nat.le_refl L)
        omega
      have hidx' : m * L + j < (((List.range n).flatMap f) ++ f n).length := by
        rw [List.length_append]; omega
      exact ⟨hidx', by rw [List.getElem_append_left hidx]; exact heq⟩
    · have hmeq : m = n := by omega
      subst hmeq
      have hidx' : m * L + j < (((List.range m).flatMap f) ++ f m).length := by
        rw [List.length_append, hflen m (by omega)]; omega
      have hge : ((List.range m).flatMap f).length ≤ m * L + j := by omega
      exact ⟨hidx', by rw [List.getElem_append_right hge]; simp [hlen_n]⟩

/-- Lap `m` for `m < k` (a mark-covering lap), nothing otherwise. -/
noncomputable def cycleLapAt (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) (hne : ac.cycle ≠ []) (m : Nat) : List Edge :=
  if h : m < k then
    lapFor W ac.cycle hne (ac.cycle_covers_marks m h).choose
      (ac.cycle_covers_marks m h).choose_spec.choose m
  else []

theorem cycleLapAt_eq (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) (hne : ac.cycle ≠ []) (m : Nat) (hm : m < k) :
    cycleLapAt W ac hne m = lapFor W ac.cycle hne (ac.cycle_covers_marks m hm).choose
      (ac.cycle_covers_marks m hm).choose_spec.choose m := by
  unfold cycleLapAt; rw [dif_pos hm]

theorem cycleLapAt_length (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) (hne : ac.cycle ≠ []) (m : Nat) (hm : m < k) :
    (cycleLapAt W ac hne m).length = ac.cycle.length := by
  rw [cycleLapAt_eq W ac hne m hm]; exact lapFor_len W ac.cycle hne _ _ m

/-- The cycle side of the bridge: `k` laps around `ac.cycle`, lap `m` covering mark `m`, or a single `stepEdge`-only
pass when `k = 0`. -/
@[expose] noncomputable def TAcceptingCycle.cycleE (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) : List Edge :=
  have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)
  if h : k = 0 then stemEdges W.stepEdge (ac.cycle ++ [ac.cycle.head hne])
  else (List.range k).flatMap (cycleLapAt W ac hne)

theorem TAcceptingCycle.cycleE_eq_flatMap (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) (hne : ac.cycle ≠ []) (hk0 : ¬ k = 0) :
    ac.cycleE W = (List.range k).flatMap (cycleLapAt W ac hne) := by
  unfold TAcceptingCycle.cycleE
  rw [dif_neg hk0]

private theorem cycleE_spec (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) :
    (ac.cycleE W).length ≥ 1 ∧ (∀ e ∈ ac.cycleE W, A.valid e) ∧
    (∀ i, (hi : i + 1 < (ac.cycleE W).length) →
      A.dst ((ac.cycleE W)[i]'(by omega)) = A.src ((ac.cycleE W)[i + 1]'(by omega))) ∧
    (∀ (hne' : ac.cycleE W ≠ []), A.src ((ac.cycleE W).head hne') =
      ac.cycle.head (List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega))) ∧
    (∀ (hne' : ac.cycleE W ≠ []), A.dst ((ac.cycleE W).getLast hne') =
      ac.cycle.head (List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega))) := by
  have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)
  by_cases h : k = 0
  · have hcc := cycleClosed_chain ac
    have hcne : ac.cycle ++ [ac.cycle.head hne] ≠ [] := by simp
    have heq : ac.cycleE W = stemEdges W.stepEdge (ac.cycle ++ [ac.cycle.head hne]) := by
      unfold TAcceptingCycle.cycleE; rw [dif_pos h]
    simp only [heq]
    refine ⟨?_, stemEdges_valid W _ hcc, stemEdges_chain W _ hcc, fun _ => ?_, fun _ => ?_⟩
    · rw [stemEdges_length]; simp; have := ac.cycle_nonempty; omega
    · rw [stemEdges_head_src W _ hcc _ hcne]
      simp [List.head_eq_getElem, List.getElem_append_left,
        show 0 < ac.cycle.length from by have := ac.cycle_nonempty; omega]
    · rw [stemEdges_last_dst W _ hcc _ hcne]; simp
  · have heq := ac.cycleE_eq_flatMap W hne h
    simp only [heq]
    have hk1 : k ≥ 1 := by omega
    have hlen : ∀ m, m < k → (cycleLapAt W ac hne m).length ≥ 1 := by
      intro m hm; rw [cycleLapAt_length W ac hne m hm]; have := ac.cycle_nonempty; omega
    have hmwit : ∀ m, (hm : m < k) → A.src ((cycleLapAt W ac hne m).head
        (List.ne_nil_of_length_pos (by have := hlen m hm; omega))) = ac.cycle.head hne ∧
      A.dst ((cycleLapAt W ac hne m).getLast
        (List.ne_nil_of_length_pos (by have := hlen m hm; omega))) = ac.cycle.head hne := by
      intro m hm
      have hlapeq := cycleLapAt_eq W ac hne m hm
      simp only [hlapeq]
      exact ⟨lapFor_head W ac hne _ _ m hm (ac.cycle_covers_marks m hm).choose_spec.choose_spec _,
        lapFor_last W ac hne _ _ m hm (ac.cycle_covers_marks m hm).choose_spec.choose_spec _⟩
    exact flatMap_loop_spec (ac.cycle.head hne) (cycleLapAt W ac hne) k hk1 hlen
      (fun m hm => by
        have hlapeq := cycleLapAt_eq W ac hne m hm
        simp only [hlapeq]
        exact lapFor_valid W ac hne _ _ m hm (ac.cycle_covers_marks m hm).choose_spec.choose_spec)
      (fun m hm => by
        have hlapeq := cycleLapAt_eq W ac hne m hm
        simp only [hlapeq]
        exact lapFor_chain W ac hne _ _ m hm (ac.cycle_covers_marks m hm).choose_spec.choose_spec)
      (fun m hm => (hmwit m hm).1) (fun m hm => (hmwit m hm).2)

private theorem cycleE_covers_marks (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) (m : Fin k) :
    ∃ (i : Nat) (hi : i < (ac.cycleE W).length), A.acceptMark m ((ac.cycleE W)[i]'hi) := by
  have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)
  have hk0 : ¬ k = 0 := by have := m.isLt; omega
  have hmk : m.val < k := m.isLt
  have hflen : ∀ i, i < k → (cycleLapAt W ac hne i).length = ac.cycle.length :=
    fun i hi => cycleLapAt_length W ac hne i hi
  obtain ⟨j, hj, hjmark⟩ :
      ∃ (j : Nat) (hj : j < (cycleLapAt W ac hne m.val).length),
        A.acceptMark m ((cycleLapAt W ac hne m.val)[j]'hj) := by
    have hlapeq := cycleLapAt_eq W ac hne m.val hmk
    simp only [hlapeq]
    exact lapFor_mark W ac hne _ _ m.val hmk (ac.cycle_covers_marks m.val hmk).choose_spec.choose_spec
  have hjlt : j < ac.cycle.length := by rw [← hflen m.val hmk]; exact hj
  obtain ⟨hidx, heq⟩ := flatMap_uniform_getElem (cycleLapAt W ac hne) ac.cycle.length k m.val j hflen hmk hjlt
  have hceq := ac.cycleE_eq_flatMap W hne hk0
  refine ⟨m.val * ac.cycle.length + j, ?_, ?_⟩
  · rw [hceq]; exact hidx
  · simp only [hceq]; rw [heq]; exact hjmark

/-- Every edge of `ac.cycleE` realizes some cyclic step of `ac.cycle`, endpoints included. -/
theorem cycleE_endpoints_mem (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) {e : Edge} (he : e ∈ ac.cycleE W) :
    ∃ (i : Nat) (hi : i < ac.cycle.length), A.src e = ac.cycle[i]'hi ∧
      A.dst e = ac.cycle[(i + 1) % ac.cycle.length]'(Nat.mod_lt _ (by have := ac.cycle_nonempty; omega)) := by
  have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)
  by_cases h : k = 0
  · have heq : ac.cycleE W = stemEdges W.stepEdge (ac.cycle ++ [ac.cycle.head hne]) := by
      unfold TAcceptingCycle.cycleE; rw [dif_pos h]
    rw [heq] at he
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
    have hjlen : (stemEdges W.stepEdge (ac.cycle ++ [ac.cycle.head hne])).length =
        ac.cycle.length := by rw [stemEdges_length]; simp
    have hjlt : j < ac.cycle.length := by rw [hjlen] at hj; exact hj
    have hj' : j + 1 < (ac.cycle ++ [ac.cycle.head hne]).length := by simp; omega
    have hgetElem := stemEdges_getElem W.stepEdge (ac.cycle ++ [ac.cycle.head hne]) j hj' hj
    have h1 : (ac.cycle ++ [ac.cycle.head hne])[j]'(by omega) = ac.cycle[j]'hjlt :=
      List.getElem_append_left hjlt
    have h2 : (ac.cycle ++ [ac.cycle.head hne])[j + 1]'hj' =
        ac.cycle[(j + 1) % ac.cycle.length]'(Nat.mod_lt _ (by have := ac.cycle_nonempty; omega)) :=
      (cycleClosed_getElem_succ ac hne j hjlt).symm
    have hstepmem := TAcceptingCycle.cycle_succ_mem ac hne j hjlt
    refine ⟨j, hjlt, ?_, ?_⟩
    · simp only [hgetElem, h1, h2]; exact (W.stepEdge_spec hstepmem).2.1
    · simp only [hgetElem, h1, h2]; exact (W.stepEdge_spec hstepmem).2.2
  · have heq := ac.cycleE_eq_flatMap W hne h
    rw [heq] at he
    obtain ⟨m, hm, hmem⟩ := List.mem_flatMap.mp he
    have hmk : m < k := List.mem_range.mp hm
    rw [cycleLapAt_eq W ac hne m hmk] at hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hmem
    have hjlt : j < ac.cycle.length := by
      have := lapFor_len W ac.cycle hne (ac.cycle_covers_marks m hmk).choose
        (ac.cycle_covers_marks m hmk).choose_spec.choose m
      omega
    have hspec := lapFor_src_dst W ac hne (ac.cycle_covers_marks m hmk).choose
      (ac.cycle_covers_marks m hmk).choose_spec.choose m hmk
      (ac.cycle_covers_marks m hmk).choose_spec.choose_spec j hjlt hj
    exact ⟨j, hjlt, hspec.1, hspec.2.1⟩

/-- Past the stem, every state the lasso run passes through is one of `ac.cycle`'s. -/
theorem TValidLasso.run_src_mem_cycle {A : TOASpec State Edge α k} {stemE : List Edge}
    (W : TEdgeWitness A succs edgeMarks) (ac : TAcceptingCycle initialStates succs edgeMarks k)
    (hv : TValidLasso A stemE (ac.cycleE W)) (n : Nat) (hn : ¬ n < stemE.length) :
    ∃ (i : Nat) (hi : i < ac.cycle.length), A.src (hv.run n) = ac.cycle[i]'hi := by
  rw [hv.run_eq_cycle n hn]
  obtain ⟨i, hi, hsrc, -⟩ := cycleE_endpoints_mem W ac (List.getElem_mem _)
  exact ⟨i, hi, hsrc⟩

/-- Every state of `ac.cycle` is some `cycleE` edge's source. -/
theorem cycleE_src_hits (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) (i : Nat) (hi : i < ac.cycle.length) :
    ∃ (j : Nat) (hj : j < (ac.cycleE W).length), A.src ((ac.cycleE W)[j]'hj) = ac.cycle[i]'hi := by
  have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)
  by_cases h : k = 0
  · have heq : ac.cycleE W = stemEdges W.stepEdge (ac.cycle ++ [ac.cycle.head hne]) := by
      unfold TAcceptingCycle.cycleE; rw [dif_pos h]
    have hlen : (stemEdges W.stepEdge (ac.cycle ++ [ac.cycle.head hne])).length =
        ac.cycle.length := by rw [stemEdges_length]; simp
    have hi'' : i < (stemEdges W.stepEdge (ac.cycle ++ [ac.cycle.head hne])).length := by omega
    have happ : (ac.cycle ++ [ac.cycle.head hne]).length = ac.cycle.length + 1 := by simp
    have hgetElem :=
      stemEdges_getElem W.stepEdge (ac.cycle ++ [ac.cycle.head hne]) i (by omega) hi''
    have h1 : (ac.cycle ++ [ac.cycle.head hne])[i]'(by omega) = ac.cycle[i]'hi :=
      List.getElem_append_left hi
    have h2 : (ac.cycle ++ [ac.cycle.head hne])[i + 1]'(by omega) =
        ac.cycle[(i + 1) % ac.cycle.length]'(Nat.mod_lt _ (by have := ac.cycle_nonempty; omega)) :=
      (cycleClosed_getElem_succ ac hne i hi).symm
    have hstepmem := TAcceptingCycle.cycle_succ_mem ac hne i hi
    refine ⟨i, by rw [heq]; omega, ?_⟩
    simp only [heq, hgetElem, h1, h2]
    exact (W.stepEdge_spec hstepmem).2.1
  · have hk : 0 < k := Nat.pos_of_ne_zero h
    have hflen : ∀ m, m < k → (cycleLapAt W ac hne m).length = ac.cycle.length :=
      fun m hm => cycleLapAt_length W ac hne m hm
    obtain ⟨hidx, hget⟩ :=
      flatMap_uniform_getElem (cycleLapAt W ac hne) ac.cycle.length k 0 i hflen hk hi
    have hceq := ac.cycleE_eq_flatMap W hne h
    refine ⟨0 * ac.cycle.length + i, by rw [hceq]; exact hidx, ?_⟩
    simp only [hceq]
    rw [hget]
    simp only [cycleLapAt_eq W ac hne 0 hk]
    exact (lapFor_src_dst W ac hne _ _ 0 hk (ac.cycle_covers_marks 0 hk).choose_spec.choose_spec i hi
      (by rw [lapFor_len]; exact hi)).1

/-- Every state of `ac.cycle` is the source of arbitrarily late run positions. -/
theorem TValidLasso.run_src_hits_cycle {A : TOASpec State Edge α k} {stemE : List Edge}
    (W : TEdgeWitness A succs edgeMarks) (ac : TAcceptingCycle initialStates succs edgeMarks k)
    (hv : TValidLasso A stemE (ac.cycleE W)) (i : Nat) (hi : i < ac.cycle.length) (n : Nat) :
    ∃ t, A.src (hv.run (n + t)) = ac.cycle[i]'hi := by
  obtain ⟨j, hj, hsrc⟩ := cycleE_src_hits W ac i hi
  obtain ⟨t, ht⟩ := hv.find_cycle_position_at j hj n
  exact ⟨t, by rw [ht]; exact hsrc⟩

/-! ## Reading a property off the realized edges

Every edge the bridge emits is a `stepEdge` or a `markEdge`, so any property both constructors guarantee
holds of the whole lasso. A witness built over a *restricted* graph only ever emits restricted edges, which
is how a caller reads an `FG` restriction back off the run. -/

theorem stemEdges_forall {stepEdge : State → State → Edge} (P : Edge → Prop)
    (hstep : ∀ s s', s' ∈ succs s → P (stepEdge s s')) :
    ∀ (l : List State), (∀ i, (hi : i + 1 < l.length) → l[i + 1] ∈ succs (l[i])) →
      ∀ e ∈ stemEdges stepEdge l, P e := by
  intro l
  induction l with
  | nil => simp [stemEdges]
  | cons a l ih =>
    cases l with
    | nil => simp [stemEdges]
    | cons b l =>
      intro hchain e he
      rw [stemEdges, List.mem_cons] at he
      rcases he with rfl | he
      · exact hstep a b (by simpa using hchain 0 (by simp))
      · exact ih (fun i hi => hchain (i + 1) (by simpa using hi)) e he

/-- Every edge the bridge emits is a `stepEdge` or a `markEdge` applied to a genuine step of the cycle, so a
property both constructors guarantee there holds of the whole cycle. A witness built over a *restricted*
graph only emits restricted edges, which is how a caller reads an `FG` restriction off the run. -/
theorem cycleE_forall {A : TOASpec State Edge α k} (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) (P : Edge → Prop)
    (hstep : ∀ s s', s' ∈ succs s → P (W.stepEdge s s'))
    (hmark : ∀ s s' m, s' ∈ succs s → m ∈ edgeMarks s s' → P (W.markEdge s s' m)) :
    ∀ e ∈ ac.cycleE W, P e := by
  have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)
  have hclosed := cycleClosed_chain ac
  intro e he
  unfold TAcceptingCycle.cycleE at he
  split at he
  · exact stemEdges_forall P hstep _ hclosed e he
  · obtain ⟨m, -, hem⟩ := List.mem_flatMap.mp he
    unfold cycleLapAt at hem
    split at hem
    · unfold lapFor at hem
      rcases List.mem_or_eq_of_mem_set hem with h | h
      · exact stemEdges_forall P hstep _ hclosed e h
      · rename_i hmlt
        exact h ▸ hmark _ _ m (ac.cycle_succ_mem hne _ _)
          (ac.cycle_covers_marks m hmlt).choose_spec.choose_spec
    · simp at hem

/-- A cycle confined to a subgraph, reached by a stem that need not be — what a static `FG` restriction
asks for. The cycle's edges lie in `succsR` and its marks are `edgeMarksR`'s, because a mark there has to be
realizable by a *restricted* step; see `EdgeLabels.md` §6.3. -/
structure TRegionCycle (initialStates : List State) (succs succsR : State → Array State)
    (edgeMarks edgeMarksR : State → State → Std.HashSet Nat) (numMarks : Nat) where
  stem : List State
  cycle : List State
  stem_nonempty : stem.length ≥ 1
  cycle_nonempty : cycle.length ≥ 1
  stem_head_initial : stem.head (List.ne_nil_of_length_pos (by omega)) ∈ initialStates
  stem_chain : ∀ (i : Nat), (hi : i + 1 < stem.length) → stem[i + 1] ∈ succs (stem[i])
  overlap : stem.getLast (List.ne_nil_of_length_pos (by omega)) =
            cycle.head (List.ne_nil_of_length_pos (by omega))
  cycle_chain : ∀ (i : Nat), (hi : i + 1 < cycle.length) → cycle[i + 1] ∈ succsR (cycle[i])
  cycle_back : cycle.head (List.ne_nil_of_length_pos (by omega)) ∈
    succsR (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
  cycle_covers_marks : ∀ m, m < numMarks → ∃ (i : Nat) (hi : i < cycle.length),
    m ∈ edgeMarksR (cycle[i]) (cycle[(i + 1) % cycle.length]'(Nat.mod_lt _ (by omega)))

/-- The cycle read as an accepting cycle of the *restricted* graph, rooted at its own head. This is what
gives `cycleE` a restricted witness to pick realizations from. -/
@[expose] def TRegionCycle.cycleAc {initialStates : List State} {succs succsR : State → Array State}
    {edgeMarks edgeMarksR : State → State → Std.HashSet Nat} {numMarks : Nat}
    (rc : TRegionCycle initialStates succs succsR edgeMarks edgeMarksR numMarks) :
    TAcceptingCycle rc.cycle succsR edgeMarksR numMarks where
  stem := [rc.cycle.head (List.ne_nil_of_length_pos (by have := rc.cycle_nonempty; omega))]
  cycle := rc.cycle
  stem_nonempty := by simp
  cycle_nonempty := rc.cycle_nonempty
  stem_head_initial := by simp
  stem_chain := by intro i hi; simp at hi
  overlap := by simp
  cycle_chain := rc.cycle_chain
  cycle_back := rc.cycle_back
  cycle_covers_marks := rc.cycle_covers_marks

/-- The full bridge: a `TAcceptingCycle` (over `succs`/`edgeMarks`) yields a `TValidLasso` for any `TOASpec` compatible with it. -/
theorem TAcceptingCycle.toTValidLassoOf {A : TOASpec State Edge α k}
    (W : TEdgeWitness A succs edgeMarks) (hinit : ∀ {s}, s ∈ initialStates → A.initial s)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) :
    TValidLasso A (stemEdges W.stepEdge ac.stem) (ac.cycleE W) := by
  have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)
  obtain ⟨hclen, hcvalid, hcchain, hchead, hclast⟩ := cycleE_spec W ac
  have hschain := ac.stem_chain
  refine
    { cycle_nonempty := hclen
      stem_valid := stemEdges_valid W ac.stem hschain
      stem_chain := stemEdges_chain W ac.stem hschain
      cycle_valid := hcvalid
      cycle_chain := hcchain
      cycle_back := (hclast (List.ne_nil_of_length_pos (by omega))).trans
        (hchead (List.ne_nil_of_length_pos (by omega))).symm
      cycle_covers_marks := cycleE_covers_marks W ac
      stem_initial := ?_
      overlap := ?_ }
  · by_cases hse : stemEdges W.stepEdge ac.stem = []
    · have hcne : ac.cycleE W ≠ [] := List.ne_nil_of_length_pos (by omega)
      have hheq : (stemEdges W.stepEdge ac.stem ++ ac.cycleE W).head
          (List.ne_nil_of_length_pos (by simp only [List.length_append]; omega)) =
          (ac.cycleE W).head hcne := by
        simp only [hse]; simp
      rw [hheq, hchead hcne]
      have hslen1 : ac.stem.length = 1 := by
        have hsl := stemEdges_length W.stepEdge ac.stem
        have hse_len : (stemEdges W.stepEdge ac.stem).length = 0 := by rw [hse]; simp
        have := ac.stem_nonempty
        omega
      have hheadlast : ac.stem.head (List.ne_nil_of_length_pos (by omega)) =
          ac.stem.getLast (List.ne_nil_of_length_pos (by omega)) := by
        rw [List.head_eq_getElem, List.getLast_eq_getElem]; congr 1; omega
      rw [← ac.overlap, ← hheadlast]
      exact hinit ac.stem_head_initial
    · rw [List.head_append_of_ne_nil hse, stemEdges_head_src W ac.stem hschain hse
        (List.ne_nil_of_length_pos (by have := ac.stem_nonempty; omega))]
      exact hinit ac.stem_head_initial
  · intro h
    have hcne : ac.cycleE W ≠ [] := List.ne_nil_of_length_pos (by omega)
    rw [stemEdges_last_dst W ac.stem hschain h (List.ne_nil_of_length_pos (by have := ac.stem_nonempty; omega)),
      hchead hcne, ac.overlap]

/-- The bridge for a region cycle: the stem is realized by `Ws` in the ambient graph, the cycle by `Wc` in
the restricted one. `toTValidLassoOf` is the case where the two coincide. Splitting them is what makes an
edge-indexed `◇□ψ` sound — the cycle's edges must be realized by ψ-steps, and the ambient witness is free to
pick a non-ψ step where a ψ one exists. -/
theorem TRegionCycle.toTValidLasso {A : TOASpec State Edge α k}
    {succsR : State → Array State} {edgeMarksR : State → State → Std.HashSet Nat}
    (Ws : TEdgeWitness A succs edgeMarks) (Wc : TEdgeWitness A succsR edgeMarksR)
    (hinit : ∀ {s}, s ∈ initialStates → A.initial s)
    (rc : TRegionCycle initialStates succs succsR edgeMarks edgeMarksR k) :
    TValidLasso A (stemEdges Ws.stepEdge rc.stem) (rc.cycleAc.cycleE Wc) := by
  have hne : rc.cycleAc.cycle ≠ [] :=
    List.ne_nil_of_length_pos (by have := rc.cycle_nonempty; exact rc.cycleAc.cycle_nonempty)
  obtain ⟨hclen, hcvalid, hcchain, hchead, hclast⟩ := cycleE_spec Wc rc.cycleAc
  have hschain := rc.stem_chain
  refine
    { cycle_nonempty := hclen
      stem_valid := stemEdges_valid Ws rc.stem hschain
      stem_chain := stemEdges_chain Ws rc.stem hschain
      cycle_valid := hcvalid
      cycle_chain := hcchain
      cycle_back := (hclast (List.ne_nil_of_length_pos (by omega))).trans
        (hchead (List.ne_nil_of_length_pos (by omega))).symm
      cycle_covers_marks := cycleE_covers_marks Wc rc.cycleAc
      stem_initial := ?_
      overlap := ?_ }
  · by_cases hse : stemEdges Ws.stepEdge rc.stem = []
    · have hcne : rc.cycleAc.cycleE Wc ≠ [] := List.ne_nil_of_length_pos (by omega)
      have hheq : (stemEdges Ws.stepEdge rc.stem ++ rc.cycleAc.cycleE Wc).head
          (List.ne_nil_of_length_pos (by simp only [List.length_append]; omega)) =
          (rc.cycleAc.cycleE Wc).head hcne := by
        simp only [hse]; simp
      rw [hheq, hchead hcne]
      have hslen1 : rc.stem.length = 1 := by
        have hsl := stemEdges_length Ws.stepEdge rc.stem
        have hse_len : (stemEdges Ws.stepEdge rc.stem).length = 0 := by rw [hse]; simp
        have := rc.stem_nonempty
        omega
      have hheadlast : rc.stem.head (List.ne_nil_of_length_pos (by omega)) =
          rc.stem.getLast (List.ne_nil_of_length_pos (by omega)) := by
        rw [List.head_eq_getElem, List.getLast_eq_getElem]; congr 1; omega
      rw [show (rc.cycleAc.cycle.head hne) = rc.stem.head
          (List.ne_nil_of_length_pos (by omega)) from by
        rw [hheadlast]; exact rc.overlap.symm]
      exact hinit rc.stem_head_initial
    · rw [List.head_append_of_ne_nil hse, stemEdges_head_src Ws rc.stem hschain hse
        (List.ne_nil_of_length_pos (by have := rc.stem_nonempty; omega))]
      exact hinit rc.stem_head_initial
  · intro h
    have hcne : rc.cycleAc.cycleE Wc ≠ [] := List.ne_nil_of_length_pos (by omega)
    rw [stemEdges_last_dst Ws rc.stem hschain h
      (List.ne_nil_of_length_pos (by have := rc.stem_nonempty; omega)), hchead hcne]
    exact rc.overlap

/-! ## The states a lasso run passes through -/

/-- The length of `cycleE` is a multiple of the cycle's: one lap per mark, or one pass when there are none. -/
theorem cycleE_length_dvd (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) :
    ac.cycle.length ∣ (ac.cycleE W).length := by
  have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)
  by_cases hk : k = 0
  · unfold TAcceptingCycle.cycleE
    rw [dif_pos hk, stemEdges_length]
    simp
  · rw [TAcceptingCycle.cycleE_eq_flatMap W ac hne hk,
      flatMap_uniform_length _ _ _ (fun i hi => cycleLapAt_length W ac hne i hi)]
    exact Nat.dvd_mul_left _ _

/-- Edge `j` of `cycleE` leaves the cycle's state `j % ac.cycle.length`: every lap walks the cycle from its head. -/
theorem cycleE_src (W : TEdgeWitness A succs edgeMarks)
    (ac : TAcceptingCycle initialStates succs edgeMarks k) (j : Nat) (hj : j < (ac.cycleE W).length) :
    A.src ((ac.cycleE W)[j]'hj) =
      ac.cycle[j % ac.cycle.length]'(Nat.mod_lt _ (by have := ac.cycle_nonempty; omega)) := by
  have hne : ac.cycle ≠ [] := List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)
  have hL : 0 < ac.cycle.length := by have := ac.cycle_nonempty; omega
  by_cases hk : k = 0
  · have hE : ac.cycleE W = stemEdges W.stepEdge (ac.cycle ++ [ac.cycle.head hne]) := by
      unfold TAcceptingCycle.cycleE; rw [dif_pos hk]
    have hj' : j < (stemEdges W.stepEdge (ac.cycle ++ [ac.cycle.head hne])).length := hE ▸ hj
    have hjL : j < ac.cycle.length := by
      rw [stemEdges_length] at hj'; simpa using hj'
    rw [List.getElem_of_eq hE hj, stemEdges_getElem W.stepEdge _ j (by simp; omega) hj',
      (W.stepEdge_spec (cycleClosed_chain ac j (by simp; omega))).2.1]
    simp [List.getElem_append_left hjL, Nat.mod_eq_of_lt hjL]
  · have hE := TAcceptingCycle.cycleE_eq_flatMap W ac hne hk
    have hflen : ∀ i, i < k → (cycleLapAt W ac hne i).length = ac.cycle.length :=
      fun i hi => cycleLapAt_length W ac hne i hi
    have hlen : (ac.cycleE W).length = k * ac.cycle.length := by
      rw [hE]; exact flatMap_uniform_length _ _ _ hflen
    have hm : j / ac.cycle.length < k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have hr : j % ac.cycle.length < ac.cycle.length := Nat.mod_lt _ hL
    obtain ⟨hidx, heq⟩ := flatMap_uniform_getElem (cycleLapAt W ac hne) ac.cycle.length k
      (j / ac.cycle.length) (j % ac.cycle.length) hflen hm hr
    have hstep : (ac.cycleE W)[j]'hj = (cycleLapAt W ac hne (j / ac.cycle.length))[j % ac.cycle.length]'
        (by rw [hflen _ hm]; exact hr) := by
      rw [← heq, List.getElem_of_eq hE hj]
      congr 1
      exact (Nat.div_add_mod' j ac.cycle.length).symm
    rw [hstep, List.getElem_of_eq (cycleLapAt_eq W ac hne _ hm)]
    have hcov := (ac.cycle_covers_marks (j / ac.cycle.length) hm).choose_spec.choose_spec
    exact (lapFor_src_dst W ac hne _ _ (j / ac.cycle.length) hm hcov _ hr _).1

/-- The `i`-th state of the infinite sequence a stem and a cycle describe: `stem`, whose last state is `cycle`'s
first, then `cycle` repeated forever. -/
@[expose] def lassoAt {State : Type u} (stem cycle : List State) (i : Nat) : Option State :=
  if i + 1 < stem.length then stem[i]? else cycle[(i + 1 - stem.length) % cycle.length]?

theorem lassoAt_map {State : Type u} {State' : Type u'} (f : State → State') (stem cycle : List State)
    (i : Nat) : lassoAt (stem.map f) (cycle.map f) i = (lassoAt stem cycle i).map f := by
  unfold lassoAt
  simp only [List.length_map]
  split <;> simp

/-- The run of a region cycle's lasso passes through exactly its states: `rc.stem`, then `rc.cycle` repeated. -/
theorem TRegionCycle.toTValidLasso_run_src {A : TOASpec State Edge α k}
    {succsR : State → Array State} {edgeMarksR : State → State → Std.HashSet Nat}
    (Ws : TEdgeWitness A succs edgeMarks) (Wc : TEdgeWitness A succsR edgeMarksR)
    (hinit : ∀ {s}, s ∈ initialStates → A.initial s)
    (rc : TRegionCycle initialStates succs succsR edgeMarks edgeMarksR k) (n : Nat) :
    lassoAt rc.stem rc.cycle n = some (A.src ((rc.toTValidLasso Ws Wc hinit).run n)) := by
  have hsl := stemEdges_length Ws.stepEdge rc.stem
  have hs1 := rc.stem_nonempty
  by_cases hn : n + 1 < rc.stem.length
  · have hnE : n < (stemEdges Ws.stepEdge rc.stem).length := by omega
    rw [TValidLasso.run_eq_stem _ n hnE, stemEdges_getElem Ws.stepEdge rc.stem n hn hnE,
      (Ws.stepEdge_spec (rc.stem_chain n hn)).2.1]
    simp [lassoAt, hn]
  · have hnE : ¬ n < (stemEdges Ws.stepEdge rc.stem).length := by omega
    rw [TValidLasso.run_eq_cycle _ n hnE, cycleE_src Wc rc.cycleAc, ← List.getElem?_eq_getElem,
      Nat.mod_mod_of_dvd _ (cycleE_length_dvd Wc rc.cycleAc)]
    have hidx : n + 1 - rc.stem.length = n - (stemEdges Ws.stepEdge rc.stem).length := by omega
    simp only [lassoAt, hn, if_false, hidx]
    rfl

end Bridge

end LTLLib
