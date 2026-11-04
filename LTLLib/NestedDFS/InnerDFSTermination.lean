module

/-
  The executable inner DFS, and its bridge to the fuel-indexed twin.

  `innerDFSCore`/`innerDFSWF` are the structurally-terminating versions, recursing on a `reachCount` measure, and
  `innerDFS_fuel_eq_innerDFSWF` carries the correctness proved in `InnerDFSCorrectness.lean` by induction on fuel
  over to them. The `RFrame` stack and the `pendingSum` measure defined here are what the outer loop of
  `NestedDFSTTermination.lean` recurses on.

  Defines:
  - `RFrame`, `RFrame.push`, `RFrame.consumeOne`: a frame holding a reachable state and its pending successors
  - `pendingSum`: the pending successors summed over a frame stack, the second component of an outer measure
  - `innerDFSCore`, `innerDFSWF`: the executable inner DFS

  Proves:
  - `Reachable.reachCount_insert_lt`, `Reachable.reachCount_le_of_subset`: the measure strictly drops when a fresh
    state is visited, and never rises as the visited set grows
  - `innerDFS_fuel_eq_innerDFSWF`: enough fuel makes the fuel-indexed inner DFS agree with the executable one
  - `innerDFSWF_outerVisited_pres`: the inner DFS leaves `outerVisited` alone

  Sections:
  - HashSet cardinality helpers
  - Finite-reachability hypothesis
  - `reachCount`-based termination-measure helpers
  - Well-founded `innerDFS`
  - Fuel ↔ well-founded bridge, inner half
-/
public import LTLLib.NestedDFS.InnerDFSCorrectness

public section

namespace LTLLib

/-! ## HashSet cardinality helpers -/

section HashSetCard

variable {α : Type u} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]

/-- If every element of `s` is in `t`, `s` is no bigger than `t`. -/
theorem HashSet.size_le_of_subset {s t : Std.HashSet α}
    (h : ∀ x, s.contains x → t.contains x) : s.size ≤ t.size := by
  have heq : (t ∩ s).size = s.size := Std.HashSet.size_inter_eq_size_right h
  have hle : (t ∩ s).size ≤ t.size := Std.HashSet.size_inter_le_size_left
  omega

theorem HashSet.size_pos_of_contains {s : Std.HashSet α} {k : α}
    (h : s.contains k) : 0 < s.size := by
  rcases Nat.eq_zero_or_pos s.size with hz | hp
  · exfalso
    have hempty : s.isEmpty = true := by
      rw [Std.HashSet.isEmpty_eq_size_eq_zero, hz]
      rfl
    have hfalse := Std.HashSet.contains_of_isEmpty (a := k) hempty
    rw [hfalse] at h
    exact absurd h (by decide)
  · exact hp

/-- A strict-subset cardinality bound: if `s ⊆ t` (via `contains`) and some element of `t` is
not in `s`, then `s` is strictly smaller than `t`. -/
theorem HashSet.size_lt_of_ssubset {s t : Std.HashSet α}
    (hsub : ∀ x, s.contains x → t.contains x)
    {k : α} (hk : t.contains k) (hks : ¬ s.contains k) : s.size < t.size := by
  have hd : (t \ s).size + (t ∩ s).size = t.size :=
    Std.HashSet.size_diff_add_size_inter_eq_size_left
  have hi : (t ∩ s).size = s.size := Std.HashSet.size_inter_eq_size_right hsub
  have hmemdiff : (t \ s).contains k := by
    simp [Std.HashSet.contains_diff, hk, hks]
  have hpos : 0 < (t \ s).size := HashSet.size_pos_of_contains hmemdiff
  omega

end HashSetCard

/-! ## Finite-reachability hypothesis -/

section RFrameDef

variable {State : Type u}

/-- One frame of an explicit-stack DFS worklist. -/
structure RFrame (initialStates : List State) (succs : State → Array State) where
  state : State
  hreach : Reachable initialStates succs state
  remaining : List State
  -- `remaining` is a suffix of `state`'s actual successor list.
  hsuffix : remaining <:+ (succs state).toList

/-- Consume the head of a frame's `remaining` list, updating `hsuffix` accordingly. -/
@[expose] def RFrame.consumeOne {initialStates : List State} {succs : State → Array State}
    (frame : RFrame initialStates succs) (succ : State) (tl : List State)
    (heq : frame.remaining = succ :: tl) : RFrame initialStates succs where
  state := frame.state
  hreach := frame.hreach
  remaining := tl
  hsuffix := (List.suffix_cons succ tl).trans (heq ▸ frame.hsuffix)

/-- Push a fresh successor as a new active frame on top. -/
@[expose] def RFrame.push {initialStates : List State} {succs : State → Array State}
    (frame : RFrame initialStates succs) (succ : State) (hmem : succ ∈ succs frame.state) :
    RFrame initialStates succs where
  state := succ
  hreach := .step frame.hreach hmem
  remaining := (succs succ).toList
  hsuffix := List.suffix_refl _

/-- Total pending-successor count across every stack frame. -/
@[expose] def pendingSum {initialStates : List State} {succs : State → Array State}
    (stack : List (RFrame initialStates succs)) : Nat :=
  (stack.map (fun f => f.remaining.length)).sum

@[simp] theorem pendingSum_nil {initialStates : List State} {succs : State → Array State} :
    pendingSum (initialStates := initialStates) (succs := succs) [] = 0 := rfl

@[simp] theorem pendingSum_cons {initialStates : List State} {succs : State → Array State}
    (f : RFrame initialStates succs) (rest : List (RFrame initialStates succs)) :
    pendingSum (f :: rest) = f.remaining.length + pendingSum rest := by
  simp [pendingSum]

end RFrameDef

/-! ## `reachCount`-based termination-measure helpers

`reachCount`-based analogues of `HashSet.size_lt_of_ssubset`/`HashSet.size_le_of_subset` above, for the
measure counting the reachable states outside `iv`. -/

section ReachableCount

variable {State : Type u} [BEq State] [Hashable State]
  {initialStates : List State} {succs : State → Array State}

/-- Inserting a fresh reachable state into `iv` strictly shrinks the count of reachable states outside `iv`. -/
theorem Reachable.reachCount_insert_lt [LawfulBEq State] (fr : FiniteReach initialStates succs)
    {iv : Std.HashSet State} {x : State} (hx_reach : Reachable initialStates succs x)
    (hx_niv : iv.contains x = false) :
    reachCount initialStates succs (fun y => (iv.insert x).contains y = false) <
      reachCount initialStates succs (fun y => iv.contains y = false) :=
  reachCount_lt fr (fun y _ hy => by simp_all [Std.HashSet.contains_insert]) hx_reach (by simp) hx_niv

/-- Growing `iv` (as a `Std.HashSet`, via a `.contains`-subset relation) can't increase the
count of reachable states outside `iv`. -/
theorem Reachable.reachCount_le_of_subset {iv iv' : Std.HashSet State}
    (hsub : ∀ x, iv.contains x → iv'.contains x) :
    reachCount initialStates succs (fun y => iv'.contains y = false) ≤
      reachCount initialStates succs (fun y => iv.contains y = false) :=
  reachCount_le fun y _ hy => Bool.eq_false_iff.mpr fun h => absurd (hsub y h) (by rw [hy]; decide)

end ReachableCount

/-! ## Well-founded `innerDFS` -/

section InnerDFSWellFounded

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-- Well-founded (`reachCount`-measure-terminating) inner-DFS loop over an explicit `RFrame`
stack, looking for a path back to `seed` or into `cyan`. -/
def innerDFSCore [LawfulBEq State] [LawfulHashable State] {initialStates : List State}
    (succs : State → Array State) (fr : FiniteReach initialStates succs)
    (seed : State) (cyan : Std.HashSet State)
    (stack : List (RFrame initialStates succs))
    (pathStack : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    : Option (List State × State) × Std.HashSet State × FNDFSState State :=
  match stack with
  | [] => (none, iv, st)
  | frame :: rest =>
    match hrem : frame.remaining with
    | [] =>
      innerDFSCore succs fr seed cyan rest pathStack.dropLast iv
        { st with innerFinished := st.innerFinished.insert frame.state }
    | succ :: remainingTail =>
      let stack' := frame.consumeOne succ remainingTail hrem :: rest
      if succ == seed || cyan.contains succ then
        (some (pathStack, succ), iv, st)
      else if _hblocked : st.innerFinished.contains succ || iv.contains succ then
        innerDFSCore succs fr seed cyan stack' pathStack iv st
      else
        have hmemrem : succ ∈ frame.remaining := hrem ▸ List.mem_cons_self
        have hmemsuccs : succ ∈ succs frame.state :=
          Array.mem_toList_iff.mp (frame.hsuffix.mem hmemrem)
        innerDFSCore succs fr seed cyan (frame.push succ hmemsuccs :: stack') (pathStack ++ [succ])
          (iv.insert succ) st
termination_by
  (reachCount initialStates succs (fun x => iv.contains x = false),
   pendingSum stack + stack.length)
decreasing_by
  · simp [pendingSum_cons, hrem]
    omega
  · simp [pendingSum_cons, RFrame.consumeOne, hrem]
    omega
  · have hsucc_niv : iv.contains succ = false := by
      rw [Bool.eq_false_iff]
      simp only [Bool.or_eq_true, not_or] at _hblocked
      exact _hblocked.2
    exact Prod.Lex.left _ _ (Reachable.reachCount_insert_lt fr
      (Reachable.step frame.hreach hmemsuccs) hsucc_niv)

/-- Well-founded inner DFS from `current`, short-circuiting on an already-finished or
already-visited start state. -/
@[expose] def innerDFSWF [LawfulHashable State] (succs : State → Array State)
    {initialStates : List State} (fr : FiniteReach initialStates succs) (seed : State)
    (cyan : List State) (current : State) (hcurrent_reach : Reachable initialStates succs current)
    (iv : Std.HashSet State) (st : FNDFSState State)
    : Option (List State × State) × Std.HashSet State × FNDFSState State :=
  if st.innerFinished.contains current then (none, iv, st)
  else if iv.contains current then (none, iv, st)
  else
    innerDFSCore succs fr seed (Std.HashSet.ofList cyan)
      [{ state := current, hreach := hcurrent_reach, remaining := (succs current).toList,
          hsuffix := List.suffix_refl _ }]
      [current] (iv.insert current) st


theorem innerDFSWF_blocked [LawfulHashable State] (succs : State → Array State)
    {initialStates : List State} (fr : FiniteReach initialStates succs) (seed : State)
    (cyan : List State) (current : State) (hcurrent_reach : Reachable initialStates succs current)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hblocked : st.innerFinished.contains current || iv.contains current) :
    innerDFSWF succs fr seed cyan current hcurrent_reach iv st = (none, iv, st) := by
  unfold innerDFSWF
  rcases Bool.or_eq_true_iff.mp hblocked with h | h
  · simp [h]
  · by_cases h1 : st.innerFinished.contains current
    · simp [h1]
    · simp [h1, h]

theorem innerDFSWF_fresh [LawfulHashable State] (succs : State → Array State)
    {initialStates : List State} (fr : FiniteReach initialStates succs) (seed : State)
    (cyan : List State) (current : State) (hcurrent_reach : Reachable initialStates succs current)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hnotfin : st.innerFinished.contains current = false)
    (hnotvisited : iv.contains current = false) :
    innerDFSWF succs fr seed cyan current hcurrent_reach iv st =
      innerDFSCore succs fr seed (Std.HashSet.ofList cyan)
        [{ state := current, hreach := hcurrent_reach, remaining := (succs current).toList,
            hsuffix := List.suffix_refl _ }]
        [current] (iv.insert current) st := by
  unfold innerDFSWF
  simp [hnotfin, hnotvisited]

/-- `innerDFSCore` never touches `outerVisited` (only `innerFinished`). -/
theorem innerDFSCore_outerVisited_pres [LawfulHashable State] {initialStates : List State}
    (succs : State → Array State) (fr : FiniteReach initialStates succs)
    (seed : State) (cyan : Std.HashSet State)
    (stack : List (RFrame initialStates succs)) (pathStack : List State)
    (iv : Std.HashSet State) (st : FNDFSState State) :
    (innerDFSCore succs fr seed cyan stack pathStack iv st).2.2.outerVisited = st.outerVisited := by
  induction stack, pathStack, iv, st using innerDFSCore.induct (succs := succs) (fr := fr)
    (seed := seed) (cyan := cyan)
  all_goals first
    | exact fr
    | rw [innerDFSCore.eq_1]
    | (rw [innerDFSCore.eq_2]; grind)

theorem innerDFSWF_outerVisited_pres [LawfulHashable State] (succs : State → Array State)
    {initialStates : List State} (fr : FiniteReach initialStates succs) (seed : State)
    (cyan : List State) (current : State) (hcurrent_reach : Reachable initialStates succs current)
    (iv : Std.HashSet State) (st : FNDFSState State) :
    (innerDFSWF succs fr seed cyan current hcurrent_reach iv st).2.2.outerVisited =
      st.outerVisited := by
  by_cases hblocked : st.innerFinished.contains current || iv.contains current
  · rw [innerDFSWF_blocked succs fr seed cyan current hcurrent_reach iv st hblocked]
  · have hblocked' : (st.innerFinished.contains current || iv.contains current) = false := by
      rw [Bool.eq_false_iff]; exact hblocked
    have hnotfin : st.innerFinished.contains current = false := by
      simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.1
    have hnotvisited : iv.contains current = false := by
      simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.2
    rw [innerDFSWF_fresh succs fr seed cyan current hcurrent_reach iv st hnotfin hnotvisited]
    exact innerDFSCore_outerVisited_pres succs fr seed (Std.HashSet.ofList cyan) _ _ _ st

end InnerDFSWellFounded

/-! ## Fuel ↔ well-founded bridge, inner half

Bridges the fuel-indexed `innerDFS_fuel` to the well-founded `innerDFSCore`/`innerDFSWF`, for sufficient fuel
the two computing equal results. Every fuel-based correctness theorem of `InnerDFSCorrectness.lean` transports
across this equation. -/

section InnerFuelBridge

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State] [LawfulHashable State]
  {initialStates : List State} (succs : State → Array State) (fr : FiniteReach initialStates succs)
  (seed : State) (cyan : List State)

/-- Sufficient-fuel measure. -/
private noncomputable def innerFuelMeasure (initialStates : List State) (succs : State → Array State)
    (iv : Std.HashSet State) : Nat :=
  reachCount initialStates succs (fun x => iv.contains x = false)

/-- Chains `innerDFS_fuel_fold` calls across an explicit stack of pending frames. -/
@[expose] def innerDFS_fuel_chain [BEq State] [Hashable State] [LawfulBEq State]
    (succs : State → Array State) (seed : State) (cyan : List State) (fuel : Nat)
    (stack : List (State × List State)) (pathStack : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    : InnerResult State :=
  match stack with
  | [] => some (none, iv, st)
  | (current, remaining) :: rest =>
    match innerDFS_fuel_fold succs seed cyan fuel current remaining iv st with
    | none => none
    | some (some (cyc, target), iv', st') => some (some (pathStack ++ cyc.tail, target), iv', st')
    | some (none, iv', st') => innerDFS_fuel_chain succs seed cyan fuel rest pathStack.dropLast iv' st'

/-! One-step unfolding lemmas for `innerDFS_fuel`/`innerDFS_fuel_fold`/`innerDFS_fuel_chain`. -/

omit [LawfulHashable State] in
theorem innerDFS_fuel_fold_nil (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State) :
    innerDFS_fuel_fold succs seed cyan fuel current [] iv st =
      some (none, iv, { st with innerFinished := st.innerFinished.insert current }) := by
  unfold innerDFS_fuel_fold
  rfl

omit [LawfulHashable State] in
theorem innerDFS_fuel_fold_seed (fuel : Nat) (current succ : State) (rest : List State)
    (iv : Std.HashSet State) (st : FNDFSState State) (hse : succ == seed || cyan.contains succ) :
    innerDFS_fuel_fold succs seed cyan fuel current (succ :: rest) iv st =
      some (some ([current], succ), iv, st) := by
  unfold innerDFS_fuel_fold
  simp only [hse, if_true]

omit [LawfulHashable State] in
theorem innerDFS_fuel_fold_cons (fuel : Nat) (current succ : State) (rest : List State)
    (iv : Std.HashSet State) (st : FNDFSState State) (hse : ¬ (succ == seed || cyan.contains succ)) :
    innerDFS_fuel_fold succs seed cyan fuel current (succ :: rest) iv st =
      match innerDFS_fuel succs seed cyan fuel succ iv st with
      | none => none
      | some (some (cyc, target), iv', st') => some (some (current :: cyc, target), iv', st')
      | some (none, iv', st') => innerDFS_fuel_fold succs seed cyan fuel current rest iv' st' := by
  conv => lhs; rw [innerDFS_fuel_fold.eq_def]
  simp only [hse, Bool.false_eq_true, if_false]
  rfl

omit [LawfulHashable State] in
theorem innerDFS_fuel_blocked (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hblocked : st.innerFinished.contains current || iv.contains current) :
    innerDFS_fuel succs seed cyan (fuel + 1) current iv st = some (none, iv, st) := by
  unfold innerDFS_fuel
  rcases Bool.or_eq_true_iff.mp hblocked with h | h
  · simp [h]
  · by_cases h1 : st.innerFinished.contains current
    · simp [h1]
    · simp [h1, h]

omit [LawfulHashable State] in
theorem innerDFS_fuel_fresh (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hnotfin : st.innerFinished.contains current = false)
    (hnotvisited : iv.contains current = false) :
    innerDFS_fuel succs seed cyan (fuel + 1) current iv st =
      innerDFS_fuel_fold succs seed cyan fuel current (succs current).toList (iv.insert current) st := by
  unfold innerDFS_fuel
  simp [hnotfin, hnotvisited]

omit [LawfulHashable State] in
theorem innerDFS_fuel_chain_cons (fuel : Nat) (current : State) (remaining : List State)
    (rest : List (State × List State)) (pathStack : List State)
    (iv : Std.HashSet State) (st : FNDFSState State) :
    innerDFS_fuel_chain succs seed cyan fuel ((current, remaining) :: rest) pathStack iv st =
      match innerDFS_fuel_fold succs seed cyan fuel current remaining iv st with
      | none => none
      | some (some (cyc, target), iv', st') => some (some (pathStack ++ cyc.tail, target), iv', st')
      | some (none, iv', st') =>
          innerDFS_fuel_chain succs seed cyan fuel rest pathStack.dropLast iv' st' := rfl

-- More fuel doesn't change a successful `innerDFS_fuel_fold` result. Needed since
-- `innerDFS_fuel_chain` reuses one uniform fuel value across the whole stack, unlike the
-- original nested-call semantics which decrements fuel by one per descent.
omit [LawfulHashable State] in
private theorem innerDFS_fuel_fold_add_aux (succs : State → Array State) (seed : State)
    (cyan : List State) (extra fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State)
      (result : Option (List State × State)) (iv₁ : Std.HashSet State) (st₁ : FNDFSState State),
      innerDFS_fuel succs seed cyan fuel curr iv₀ st₀ = some (result, iv₁, st₁) →
      innerDFS_fuel succs seed cyan (fuel + extra) curr iv₀ st₀ = some (result, iv₁, st₁))
    (result : Option (List State × State)) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (h : innerDFS_fuel_fold succs seed cyan fuel current remaining iv st =
      some (result, iv', st')) :
    innerDFS_fuel_fold succs seed cyan (fuel + extra) current remaining iv st =
      some (result, iv', st') := by
  induction remaining generalizing iv st result iv' st' with
  | nil =>
    rw [innerDFS_fuel_fold.eq_def] at h ⊢
    exact h
  | cons succ rest ih_rem =>
    by_cases hse : succ == seed || cyan.contains succ
    · rw [innerDFS_fuel_fold_seed succs seed cyan fuel current succ rest iv st hse] at h
      rw [innerDFS_fuel_fold_seed succs seed cyan (fuel + extra) current succ rest iv st hse]
      exact h
    · rw [innerDFS_fuel_fold_cons succs seed cyan fuel current succ rest iv st hse] at h
      rw [innerDFS_fuel_fold_cons succs seed cyan (fuel + extra) current succ rest iv st hse]
      cases hinner : innerDFS_fuel succs seed cyan fuel succ iv st with
      | none => rw [hinner] at h; exact absurd h (by simp)
      | some val =>
        rw [hinner] at h
        rw [ih_inner _ _ _ _ _ _ hinner]
        obtain ⟨cyc, iv_mid, st_mid⟩ := val
        cases cyc with
        | some cyclePath => exact h
        | none => exact ih_rem iv_mid st_mid result iv' st' h

omit [LawfulHashable State] in
/-- Fuel-increase preserves a successful result, for `innerDFS_fuel` itself. -/
theorem innerDFS_fuel_add_preserves (succs : State → Array State) (seed : State)
    (cyan : List State) (extra fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (result : Option (List State × State)) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (h : innerDFS_fuel succs seed cyan fuel current iv st = some (result, iv', st')) :
    innerDFS_fuel succs seed cyan (fuel + extra) current iv st = some (result, iv', st') := by
  induction fuel generalizing current iv st result iv' st' with
  | zero => simp [innerDFS_fuel.eq_def] at h
  | succ n ih =>
    rw [show n + 1 + extra = (n + extra) + 1 by omega]
    by_cases hblocked : st.innerFinished.contains current || iv.contains current
    · rw [innerDFS_fuel_blocked succs seed cyan n current iv st hblocked] at h
      rw [innerDFS_fuel_blocked succs seed cyan (n + extra) current iv st hblocked]
      exact h
    · have hblocked' : (st.innerFinished.contains current || iv.contains current) = false := by
        rw [Bool.eq_false_iff]; exact hblocked
      have hnotfin : st.innerFinished.contains current = false := by
        simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.1
      have hnotvisited : iv.contains current = false := by
        simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.2
      rw [innerDFS_fuel_fresh succs seed cyan n current iv st hnotfin hnotvisited] at h
      rw [innerDFS_fuel_fresh succs seed cyan (n + extra) current iv st hnotfin hnotvisited]
      exact innerDFS_fuel_fold_add_aux succs seed cyan extra n current _ _ st ih result iv' st' h

omit [LawfulHashable State] in
theorem innerDFS_fuel_fold_add_preserves (succs : State → Array State) (seed : State)
    (cyan : List State) (extra fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (result : Option (List State × State)) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (h : innerDFS_fuel_fold succs seed cyan fuel current remaining iv st =
      some (result, iv', st')) :
    innerDFS_fuel_fold succs seed cyan (fuel + extra) current remaining iv st =
      some (result, iv', st') :=
  innerDFS_fuel_fold_add_aux succs seed cyan extra fuel current remaining iv st
    (fun curr iv₀ st₀ res iv₁ st₁ h =>
      innerDFS_fuel_add_preserves succs seed cyan extra fuel curr iv₀ st₀ res iv₁ st₁ h)
    result iv' st' h

omit [LawfulHashable State] in
/-- Sufficient fuel guarantees success. -/
private theorem innerDFS_fuel_fold_exists_aux (succs : State → Array State)
    (seed : State) (cyan : List State) (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hiv : ∀ x, iv.contains x → Reachable initialStates succs x)
    (hcurrent : Reachable initialStates succs current)
    (hremaining : ∀ x ∈ remaining, x ∈ succs current)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State),
      (∀ x, iv₀.contains x → Reachable initialStates succs x) → Reachable initialStates succs curr →
      fuel ≥ innerFuelMeasure initialStates succs iv₀ + 1 →
      ∃ result iv₁ st₁, innerDFS_fuel succs seed cyan fuel curr iv₀ st₀ = some (result, iv₁, st₁) ∧
        (∀ x, iv₁.contains x → Reachable initialStates succs x))
    (hfuel : fuel ≥ innerFuelMeasure initialStates succs iv + 1) :
    ∃ result iv' st', innerDFS_fuel_fold succs seed cyan fuel current remaining iv st =
      some (result, iv', st') ∧ (∀ x, iv'.contains x → Reachable initialStates succs x) := by
  induction remaining generalizing iv st with
  | nil => exact ⟨none, iv, _, innerDFS_fuel_fold_nil succs seed cyan fuel current iv st, hiv⟩
  | cons succ rest ih_rem =>
    by_cases hse : succ == seed || cyan.contains succ
    · exact ⟨some ([current], succ), iv, st,
        innerDFS_fuel_fold_seed succs seed cyan fuel current succ rest iv st hse, hiv⟩
    · rw [innerDFS_fuel_fold_cons succs seed cyan fuel current succ rest iv st hse]
      have hsuccmem : succ ∈ succs current := hremaining succ (List.mem_cons_self ..)
      have hsucc_reach : Reachable initialStates succs succ := Reachable.step hcurrent hsuccmem
      obtain ⟨result1, iv1, st1, heq1, hiv1⟩ := ih_inner succ iv st hiv hsucc_reach hfuel
      rw [heq1]
      cases result1 with
      | some cyclePath => exact ⟨_, _, _, rfl, hiv1⟩
      | none =>
        have hfuel1 : fuel ≥ innerFuelMeasure initialStates succs iv1 + 1 := by
          have hle : innerFuelMeasure initialStates succs iv1 ≤ innerFuelMeasure initialStates succs iv := by
            unfold innerFuelMeasure
            exact Reachable.reachCount_le_of_subset
              ((innerDFS_fuel_mono succs seed cyan fuel succ iv st none iv1 st1 heq1).1)
          omega
        exact ih_rem iv1 st1 hiv1 (fun x hx => hremaining x (List.mem_cons_of_mem _ hx)) hfuel1

private theorem innerDFS_fuel_exists (succs : State → Array State) (fr : FiniteReach initialStates succs)
    (seed : State)
    (cyan : List State) (fuel : Nat) (current : State) (iv : Std.HashSet State) (st : FNDFSState State)
    (hiv : ∀ x, iv.contains x → Reachable initialStates succs x)
    (hcurrent : Reachable initialStates succs current)
    (hfuel : fuel ≥ innerFuelMeasure initialStates succs iv + 1) :
    ∃ result iv' st', innerDFS_fuel succs seed cyan fuel current iv st = some (result, iv', st') ∧
      (∀ x, iv'.contains x → Reachable initialStates succs x) := by
  induction fuel generalizing current iv st with
  | zero => unfold innerFuelMeasure at hfuel; omega
  | succ n ih =>
    by_cases hblocked : st.innerFinished.contains current || iv.contains current
    · exact ⟨none, iv, st, innerDFS_fuel_blocked succs seed cyan n current iv st hblocked, hiv⟩
    · have hblocked' : (st.innerFinished.contains current || iv.contains current) = false := by
        rw [Bool.eq_false_iff]; exact hblocked
      have hnotfin : st.innerFinished.contains current = false := by
        simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.1
      have hnotvisited : iv.contains current = false := by
        simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.2
      rw [innerDFS_fuel_fresh succs seed cyan n current iv st hnotfin hnotvisited]
      have hiv' : ∀ x, (iv.insert current).contains x → Reachable initialStates succs x := by
        intro x hx
        simp only [Std.HashSet.contains_insert, Bool.or_eq_true] at hx
        rcases hx with hx | hx
        · have hxc : current = x := by simpa using hx
          exact hxc ▸ hcurrent
        · exact hiv x hx
      have hmeasure : n ≥ innerFuelMeasure initialStates succs (iv.insert current) + 1 := by
        have hlt : innerFuelMeasure initialStates succs (iv.insert current) < innerFuelMeasure initialStates succs iv := by
          unfold innerFuelMeasure
          exact Reachable.reachCount_insert_lt fr hcurrent hnotvisited
        omega
      exact innerDFS_fuel_fold_exists_aux succs seed cyan n current (succs current).toList
        (iv.insert current) st hiv' hcurrent (fun x hx => Array.mem_toList_iff.mp hx)
        (fun curr iv₀ st₀ hiv₀ hcurr hf => ih curr iv₀ st₀ hiv₀ hcurr hf) hmeasure

/-- The main bridge: `innerDFS_fuel_chain` equals `innerDFSCore` for sufficient fuel. -/
private theorem innerDFS_fuel_chain_eq_innerDFSCore
    (fuel : Nat) (stack : List (RFrame initialStates succs)) (pathStack : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hiv : ∀ x, iv.contains x → Reachable initialStates succs x)
    (hfin : ∀ x, st.innerFinished.contains x → Reachable initialStates succs x)
    (hfuel : fuel ≥ innerFuelMeasure initialStates succs iv + 1) :
    ∃ result iv₁ st₁, innerDFS_fuel_chain succs seed cyan fuel
        (stack.map (fun f => (f.state, f.remaining))) pathStack iv st =
        some (result, iv₁, st₁) ∧
      (∀ x, iv₁.contains x → Reachable initialStates succs x) ∧
      (∀ x, st₁.innerFinished.contains x → Reachable initialStates succs x) ∧
      (result, iv₁, st₁) = innerDFSCore succs fr seed (Std.HashSet.ofList cyan) stack pathStack iv st := by
  obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
  induction stack, pathStack, iv, st using innerDFSCore.induct (succs := succs) (fr := fr)
    (seed := seed) (cyan := Std.HashSet.ofList cyan) with
  | case1 =>
    rename_i pathStack iv st
    refine ⟨none, iv, st, rfl, hiv, hfin, ?_⟩
    unfold innerDFSCore
    rfl
  | case2 =>
    rename_i pathStack iv st frame rest hrem ih1
    have hfin' : ∀ x, (st.innerFinished.insert frame.state).contains x →
        Reachable initialStates succs x := by
      intro x hx
      simp only [Std.HashSet.contains_insert, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · have hxc : frame.state = x := by simpa using hx
        exact hxc ▸ frame.hreach
      · exact hfin x hx
    obtain ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩ := ih1 hiv hfin' hfuel
    refine ⟨result, iv₁, st₁, ?_, hiv1, hfin1, ?_⟩
    · simp only [List.map_cons, hrem]
      rw [innerDFS_fuel_chain_cons, innerDFS_fuel_fold_nil]
      exact heq
    · rw [innerDFSCore.eq_2]
      grind
  | case3 =>
    rename_i pathStack iv st frame rest succ remainingTail hrem hse
    have hseL := hse
    simp only [Std.HashSet.contains_ofList] at hseL
    refine ⟨some (pathStack, succ), iv, st, ?_, hiv, hfin, ?_⟩
    · simp only [List.map_cons, hrem]
      rw [innerDFS_fuel_chain_cons,
        innerDFS_fuel_fold_seed succs seed cyan (fuel' + 1) frame.state succ remainingTail iv st hseL]
      simp
    · rw [innerDFSCore.eq_2]
      grind
  | case4 =>
    rename_i pathStack iv st frame rest succ remainingTail hrem stack' hse hblocked ih1
    have hseL := hse
    simp only [Std.HashSet.contains_ofList] at hseL
    obtain ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩ := ih1 hiv hfin hfuel
    have hmap_eq : List.map (fun f => (f.state, f.remaining)) stack' =
        (frame.state, remainingTail) :: List.map (fun f => (f.state, f.remaining)) rest := by
      simp [stack', RFrame.consumeOne]
    rw [hmap_eq] at heq
    refine ⟨result, iv₁, st₁, ?_, hiv1, hfin1, ?_⟩
    · simp only [List.map_cons, hrem]
      rw [innerDFS_fuel_chain_cons,
        innerDFS_fuel_fold_cons succs seed cyan (fuel' + 1) frame.state succ remainingTail iv st hseL,
        innerDFS_fuel_blocked succs seed cyan fuel' succ iv st hblocked]
      rw [innerDFS_fuel_chain_cons] at heq
      exact heq
    · rw [innerDFSCore.eq_2]
      grind
  | case5 =>
    rename_i pathStack iv st frame rest succ remainingTail hrem stack' hse hblocked hmemrem hmemsuccs ih1
    have hseL := hse
    simp only [Std.HashSet.contains_ofList] at hseL
    have hsucc_reach : Reachable initialStates succs succ := Reachable.step frame.hreach hmemsuccs
    have hnotviv : iv.contains succ = false := by
      rw [Bool.eq_false_iff]
      simp only [Bool.or_eq_true, not_or] at hblocked
      exact hblocked.2
    have hiv' : ∀ x, (iv.insert succ).contains x → Reachable initialStates succs x := by
      intro x hx
      simp only [Std.HashSet.contains_insert, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · have hxc : succ = x := by simpa using hx
        exact hxc ▸ hsucc_reach
      · exact hiv x hx
    have hfuel' : fuel' + 1 ≥ innerFuelMeasure initialStates succs (iv.insert succ) + 1 := by
      have hlt : innerFuelMeasure initialStates succs (iv.insert succ) < innerFuelMeasure initialStates succs iv := by
        unfold innerFuelMeasure
        exact Reachable.reachCount_insert_lt fr hsucc_reach hnotviv
      omega
    obtain ⟨result, iv₁, st₁, heq2, hiv1, hfin1, heqC⟩ := ih1 hiv' hfin hfuel'
    have hnotfin : st.innerFinished.contains succ = false := by
      rw [Bool.eq_false_iff]
      intro hc
      exact hblocked (by simp [hc])
    obtain ⟨result0, iv0, st0, heq0, -⟩ :=
      innerDFS_fuel_exists succs fr seed cyan (fuel' + 1) succ iv st hiv hsucc_reach hfuel
    have hfresh : innerDFS_fuel succs seed cyan (fuel' + 1) succ iv st =
        innerDFS_fuel_fold succs seed cyan fuel' succ (succs succ).toList (iv.insert succ) st :=
      innerDFS_fuel_fresh succs seed cyan fuel' succ iv st hnotfin hnotviv
    have hfold_val : innerDFS_fuel_fold succs seed cyan fuel' succ (succs succ).toList
        (iv.insert succ) st = some (result0, iv0, st0) := by rw [← hfresh, heq0]
    have hfold_val' :
        innerDFS_fuel_fold succs seed cyan (fuel' + 1) succ (succs succ).toList (iv.insert succ) st =
          some (result0, iv0, st0) :=
      innerDFS_fuel_fold_add_preserves succs seed cyan 1 fuel' succ (succs succ).toList
        (iv.insert succ) st result0 iv0 st0 hfold_val
    have hmap_eq : List.map (fun f => (f.state, f.remaining))
        (frame.push succ hmemsuccs :: frame.consumeOne succ remainingTail hrem :: rest) =
        (succ, (succs succ).toList) :: (frame.state, remainingTail) ::
          List.map (fun f => (f.state, f.remaining)) rest := by
      simp [RFrame.push, RFrame.consumeOne]
    rw [hmap_eq] at heq2
    have heq2' : innerDFS_fuel_chain succs seed cyan (fuel' + 1)
        ((succ, (succs succ).toList) :: (frame.state, remainingTail) ::
          List.map (fun f => (f.state, f.remaining)) rest) (pathStack ++ [succ]) (iv.insert succ) st =
        some (result, iv₁, st₁) := heq2
    rw [innerDFS_fuel_chain_cons, hfold_val'] at heq2'
    refine ⟨result, iv₁, st₁, ?_, hiv1, hfin1, ?_⟩
    · simp only [List.map_cons, hrem]
      rw [innerDFS_fuel_chain_cons,
        innerDFS_fuel_fold_cons succs seed cyan (fuel' + 1) frame.state succ remainingTail iv st hseL,
        heq0]
      cases result0 with
      | some val =>
        obtain ⟨cyclePath, target⟩ := val
        have hchain := innerDFS_fuel_cyclePath_chain succs seed cyan (fuel' + 1) succ iv st heq0
        match cyclePath, hchain with
        | [], hchain => simp at hchain
        | c :: cs, hchain =>
          have hhead : c = succ := hchain.2.2.1 (by simp)
          subst hhead
          simp only at heq2' ⊢
          rw [show pathStack ++ (frame.state :: c :: cs).tail = pathStack ++ [c] ++ cs by
            simp [List.append_assoc]]
          exact heq2'
      | none =>
        simp only at heq2' ⊢
        rw [innerDFS_fuel_chain_cons,
          show (pathStack ++ [succ]).dropLast = pathStack by simp] at heq2'
        exact heq2'
    · rw [innerDFSCore.eq_2]
      grind

omit [LawfulHashable State] in
/-- `innerDFS_fuel_fold`'s own "found" result always starts with `current`. -/
private theorem innerDFS_fuel_fold_cyclePath_head (fuel : Nat) (current : State)
    (remaining : List State) (iv : Std.HashSet State) (st : FNDFSState State)
    {cyclePath : List State} {target : State} {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel_fold succs seed cyan fuel current remaining iv st =
      some (some (cyclePath, target), iv', st')) :
    cyclePath.head? = some current := by
  induction remaining generalizing iv st with
  | nil => rw [innerDFS_fuel_fold_nil] at h; simp at h
  | cons succ rest ih_rem =>
    by_cases hse : succ == seed || cyan.contains succ
    · rw [innerDFS_fuel_fold_seed succs seed cyan fuel current succ rest iv st hse] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, -⟩, -, -⟩ := h
      rfl
    · rw [innerDFS_fuel_fold_cons succs seed cyan fuel current succ rest iv st hse] at h
      cases hin : innerDFS_fuel succs seed cyan fuel succ iv st with
      | none => rw [hin] at h; simp at h
      | some val =>
        rw [hin] at h
        obtain ⟨cyc, iv2, st2⟩ := val
        cases cyc with
        | some val2 =>
          obtain ⟨cyclePath2, target2⟩ := val2
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, -⟩, -, -⟩ := h
          rfl
        | none => exact ih_rem iv2 st2 h

omit [LawfulHashable State] in
/-- A singleton-stack `innerDFS_fuel_chain` call is exactly `innerDFS_fuel_fold`. -/
theorem innerDFS_fuel_chain_singleton (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State) :
    innerDFS_fuel_chain succs seed cyan fuel [(current, remaining)] [current] iv st =
      innerDFS_fuel_fold succs seed cyan fuel current remaining iv st := by
  rw [innerDFS_fuel_chain_cons]
  cases h : innerDFS_fuel_fold succs seed cyan fuel current remaining iv st with
  | none => rfl
  | some val =>
    obtain ⟨cyc, iv', st'⟩ := val
    cases cyc with
    | none => rfl
    | some val2 =>
      obtain ⟨cyclePath, target⟩ := val2
      have hhead := innerDFS_fuel_fold_cyclePath_head succs seed cyan fuel current remaining iv st h
      cases cyclePath with
      | nil => cases hhead
      | cons c cs =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        rfl

/-- Top-level bridge: for sufficient fuel, `innerDFS_fuel` equals `innerDFSWF`. -/
private theorem innerDFS_fuel_eq_innerDFSWF
    (fuel : Nat) (current : State) (hcurrent_reach : Reachable initialStates succs current)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hiv : ∀ x, iv.contains x → Reachable initialStates succs x)
    (hfin : ∀ x, st.innerFinished.contains x → Reachable initialStates succs x)
    (hfuel : fuel ≥ innerFuelMeasure initialStates succs iv + 1) :
    ∃ result iv₁ st₁, innerDFS_fuel succs seed cyan fuel current iv st = some (result, iv₁, st₁) ∧
      (∀ x, iv₁.contains x → Reachable initialStates succs x) ∧
      (∀ x, st₁.innerFinished.contains x → Reachable initialStates succs x) ∧
      (result, iv₁, st₁) = innerDFSWF succs fr seed cyan current hcurrent_reach iv st := by
  by_cases hblocked : st.innerFinished.contains current || iv.contains current
  · refine ⟨none, iv, st, ?_, hiv, hfin, ?_⟩
    · obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by unfold innerFuelMeasure at hfuel; omega⟩
      exact innerDFS_fuel_blocked succs seed cyan n current iv st hblocked
    · rw [innerDFSWF_blocked succs fr seed cyan current hcurrent_reach iv st hblocked]
  · have hblocked' : (st.innerFinished.contains current || iv.contains current) = false := by
      rw [Bool.eq_false_iff]; exact hblocked
    have hnotfin : st.innerFinished.contains current = false := by
      simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.1
    have hnotvisited : iv.contains current = false := by
      simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.2
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by unfold innerFuelMeasure at hfuel; omega⟩
    rw [innerDFS_fuel_fresh succs seed cyan n current iv st hnotfin hnotvisited]
    rw [innerDFSWF_fresh succs fr seed cyan current hcurrent_reach iv st hnotfin hnotvisited]
    have hiv' : ∀ x, (iv.insert current).contains x → Reachable initialStates succs x := by
      intro x hx
      simp only [Std.HashSet.contains_insert, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · have hxc : current = x := by simpa using hx
        exact hxc ▸ hcurrent_reach
      · exact hiv x hx
    have hmeasure : n ≥ innerFuelMeasure initialStates succs (iv.insert current) + 1 := by
      have hlt : innerFuelMeasure initialStates succs (iv.insert current) < innerFuelMeasure initialStates succs iv := by
        unfold innerFuelMeasure
        exact Reachable.reachCount_insert_lt fr hcurrent_reach hnotvisited
      omega
    obtain ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩ :=
      innerDFS_fuel_chain_eq_innerDFSCore succs fr seed cyan n
        [{ state := current, hreach := hcurrent_reach, remaining := (succs current).toList,
            hsuffix := List.suffix_refl _ }]
        [current] (iv.insert current) st hiv' hfin hmeasure
    simp only [List.map] at heq
    rw [innerDFS_fuel_chain_singleton] at heq
    exact ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩

end InnerFuelBridge

end LTLLib
