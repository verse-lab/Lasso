module

/-
  Executable nested DFS: well-founded definitions and the fuel bridge.

  `innerDFSCore`/`outerDFSLoopWF`/`nestedDFSWF` are the actual executable
  (structurally-terminating, `reachCount`-measure-based) versions of the
  algorithm. Each is bridged to a fuel-indexed twin (proved correct in
  `NestedDFSCorrectness.lean` by induction on fuel) transferring that
  correctness to the executable version.

  Also packages `nestedDFSWF` as an `EmptinessChecker` instance, and proves
  the reverse direction: an accepting run implies an `AcceptingCycle` exists
  (the "pumping" lemma, `exists_acceptingCycle_of_run`).

  References:
  - Baier & Katoen: "Principles of Model Checking" — Büchi automaton
    non-emptiness via ultimately periodic (lasso-shaped) accepting runs,
    the fact `exists_acceptingCycle_of_run` establishes.
  - Holzmann, Peled & Yannakakis: "On Nested Depth First Search" — the
    accepting-leaf shortcut in `outerDFSLoopWF` (`target` may be any state on `pathStack`, not just `current`).
  - Schwoon & Esparza: "A Note on On-The-Fly Verification Algorithms" — the
    back-edge shortcut in `outerDFSLoopWF` that detects a cycle from
    `pathStack.contains succ` alone, without launching an inner DFS.

  Sections:
  - HashSet cardinality helpers
  - Finite-reachability hypothesis
  - `reachCount`-based termination-measure helpers
  - Well-founded `innerDFS`
  - Fuel ↔ well-founded bridge, inner half
  - Well-founded `outerDFSLoop`
  - Fuel ↔ well-founded bridge, outer half
  - Top-level `nestedDFS`, well-founded
  - Fuel ↔ well-founded bridge, top level
  - `nestedDFSWF` as an `EmptinessChecker` instance
  - Packaging a `FiniteReach` witness from `BA.WellFormed`
  - From an accepting run to an `AcceptingCycle`
-/
public import LTLLib.NestedDFS.NestedDFSCorrectness
public import LTLLib.BA

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

`reachCount`-based analogues of `HashSet.size_lt_of_ssubset`/`HashSet.size_le_of_subset` above,
for the measure counting the reachable states outside `iv`. Kept as a `Nat × Nat` tuple in
every `termination_by` clause below (never a bare `Nat`), so elaboration stays on the erased
`WellFounded.fix` path regardless of `reachCount` being noncomputable. -/

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
      else if hblocked : st.innerFinished.contains succ || iv.contains succ then
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
      simp only [Bool.or_eq_true, not_or] at hblocked
      exact hblocked.2
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

Bridges `innerDFS_fuel` (fuel-indexed) to `innerDFSCore`/`innerDFSWF` (well-founded): for
sufficient fuel, the two compute equal results. Every fuel-based correctness theorem from
`NestedDFSCorrectness.lean` transports across this equation, instead of being reproved
against the well-founded version. -/

section InnerFuelBridge

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State] [LawfulHashable State]
  {initialStates : List State} (succs : State → Array State) (fr : FiniteReach initialStates succs)
  (seed : State) (cyan : List State)

/-- Sufficient-fuel measure. -/
private noncomputable def innerFuelMeasure (succs : State → Array State)
    (fr : FiniteReach initialStates succs)
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

theorem innerDFS_fuel_fold_nil (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State) :
    innerDFS_fuel_fold succs seed cyan fuel current [] iv st =
      some (none, iv, { st with innerFinished := st.innerFinished.insert current }) := by
  unfold innerDFS_fuel_fold
  rfl

theorem innerDFS_fuel_fold_seed (fuel : Nat) (current succ : State) (rest : List State)
    (iv : Std.HashSet State) (st : FNDFSState State) (hse : succ == seed || cyan.contains succ) :
    innerDFS_fuel_fold succs seed cyan fuel current (succ :: rest) iv st =
      some (some ([current], succ), iv, st) := by
  unfold innerDFS_fuel_fold
  simp only [hse, if_true]

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

theorem innerDFS_fuel_fresh (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hnotfin : st.innerFinished.contains current = false)
    (hnotvisited : iv.contains current = false) :
    innerDFS_fuel succs seed cyan (fuel + 1) current iv st =
      innerDFS_fuel_fold succs seed cyan fuel current (succs current).toList (iv.insert current) st := by
  unfold innerDFS_fuel
  simp [hnotfin, hnotvisited]

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

/-- Sufficient fuel guarantees success. -/
private theorem innerDFS_fuel_fold_exists_aux (succs : State → Array State)
    (fr : FiniteReach initialStates succs)
    (seed : State) (cyan : List State) (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hiv : ∀ x, iv.contains x → Reachable initialStates succs x)
    (hcurrent : Reachable initialStates succs current)
    (hremaining : ∀ x ∈ remaining, x ∈ succs current)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State),
      (∀ x, iv₀.contains x → Reachable initialStates succs x) → Reachable initialStates succs curr →
      fuel ≥ innerFuelMeasure succs fr iv₀ + 1 →
      ∃ result iv₁ st₁, innerDFS_fuel succs seed cyan fuel curr iv₀ st₀ = some (result, iv₁, st₁) ∧
        (∀ x, iv₁.contains x → Reachable initialStates succs x))
    (hfuel : fuel ≥ innerFuelMeasure succs fr iv + 1) :
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
        have hfuel1 : fuel ≥ innerFuelMeasure succs fr iv1 + 1 := by
          have hle : innerFuelMeasure succs fr iv1 ≤ innerFuelMeasure succs fr iv := by
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
    (hfuel : fuel ≥ innerFuelMeasure succs fr iv + 1) :
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
      have hmeasure : n ≥ innerFuelMeasure succs fr (iv.insert current) + 1 := by
        have hlt : innerFuelMeasure succs fr (iv.insert current) < innerFuelMeasure succs fr iv := by
          unfold innerFuelMeasure
          exact Reachable.reachCount_insert_lt fr hcurrent hnotvisited
        omega
      exact innerDFS_fuel_fold_exists_aux succs fr seed cyan n current (succs current).toList
        (iv.insert current) st hiv' hcurrent (fun x hx => Array.mem_toList_iff.mp hx)
        (fun curr iv₀ st₀ hiv₀ hcurr hf => ih curr iv₀ st₀ hiv₀ hcurr hf) hmeasure

/-- The main bridge: `innerDFS_fuel_chain` equals `innerDFSCore` for sufficient fuel. -/
private theorem innerDFS_fuel_chain_eq_innerDFSCore
    (fuel : Nat) (stack : List (RFrame initialStates succs)) (pathStack : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hiv : ∀ x, iv.contains x → Reachable initialStates succs x)
    (hfin : ∀ x, st.innerFinished.contains x → Reachable initialStates succs x)
    (hfuel : fuel ≥ innerFuelMeasure succs fr iv + 1) :
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
    have hfuel' : fuel' + 1 ≥ innerFuelMeasure succs fr (iv.insert succ) + 1 := by
      have hlt : innerFuelMeasure succs fr (iv.insert succ) < innerFuelMeasure succs fr iv := by
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
    (hfuel : fuel ≥ innerFuelMeasure succs fr iv + 1) :
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
    have hmeasure : n ≥ innerFuelMeasure succs fr (iv.insert current) + 1 := by
      have hlt : innerFuelMeasure succs fr (iv.insert current) < innerFuelMeasure succs fr iv := by
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

/-! ## Well-founded `outerDFSLoop` -/

section OuterDFSWellFounded

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-- Well-founded `outerDFSLoop`, `RFrame`-based like `innerDFSCore`. Implements the
**Holzmann-Peled-Yannakakis shortcut** (accepting-leaf branch, `target` may be any state on
`pathStack`, not just `current`) and the **Schwoon-Esparza back-edge shortcut**
(`pathStack.contains succ` detects a cycle directly, no inner DFS launched). -/
@[expose] def outerDFSLoopWF [LawfulHashable State] {initialStates : List State}
    (succs : State → Array State) (isAccepting : State → Bool)
    (fr : FiniteReach initialStates succs)
    (stack : List (RFrame initialStates succs))
    (pathStack : List State)
    (st : FNDFSState State)
    : EmptinessResult State × FNDFSState State :=
  match stack with
  | [] => (.empty st.outerVisited.size, st)
  | frame :: rest =>
    match hrem : frame.remaining with
    | [] =>
      if isAccepting frame.state then
        let innerVisited := Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)
        match _hr : innerDFSWF succs fr frame.state pathStack frame.state frame.hreach
            innerVisited st with
        | (some (cyclePath, target), _, st') =>
          -- Holzmann-Peled-Yannakakis shortcut: `target` may be `current` itself or any other
          -- state on `pathStack`; collapses to `current :: cyclePath` when `target = current`.
          let loopTail := (pathStack.dropWhile (fun y => !(y == target))).dropLast
          (.nonEmpty pathStack (frame.state :: cyclePath ++ loopTail), st')
        | (none, _, st') =>
          outerDFSLoopWF succs isAccepting fr rest pathStack.dropLast st'
      else
        outerDFSLoopWF succs isAccepting fr rest pathStack.dropLast st
    | succ :: remainingTail =>
      let stack' := frame.consumeOne succ remainingTail hrem :: rest
      if pathStack.contains succ then
        -- Schwoon-Esparza back-edge shortcut
        if isAccepting frame.state then
          if succ == frame.state then
            (.nonEmpty pathStack [frame.state, frame.state], st)
          else
            let loopTail := (pathStack.dropWhile (fun y => !(y == succ))).dropLast
            (.nonEmpty pathStack (frame.state :: frame.state :: loopTail), st)
        else if isAccepting succ then
          let stem := pathStack.takeWhile (fun y => !(y == succ)) ++ [succ]
          let loop := succ :: pathStack.dropWhile (fun y => !(y == succ))
          (.nonEmpty stem loop, st)
        else
          outerDFSLoopWF succs isAccepting fr stack' pathStack st
      else if _hvis : st.outerVisited.contains succ then
        outerDFSLoopWF succs isAccepting fr stack' pathStack st
      else
        have hmemrem : succ ∈ frame.remaining := hrem ▸ List.mem_cons_self
        have hmemsuccs : succ ∈ succs frame.state :=
          Array.mem_toList_iff.mp (frame.hsuffix.mem hmemrem)
        let st2 := { st with outerVisited := st.outerVisited.insert succ }
        outerDFSLoopWF succs isAccepting fr (frame.push succ hmemsuccs :: stack')
          (pathStack ++ [succ]) st2
termination_by
  (reachCount initialStates succs (fun x => st.outerVisited.contains x = false),
   pendingSum stack + stack.length)
decreasing_by
  · have hst'_eq : st'.outerVisited = st.outerVisited := by
      have hr2 := innerDFSWF_outerVisited_pres succs fr frame.state pathStack frame.state
        frame.hreach innerVisited st
      rw [_hr] at hr2
      exact hr2
    rw [hst'_eq]
    exact Prod.Lex.right _ (by simp [pendingSum_cons, hrem])
  · exact Prod.Lex.right _ (by simp [pendingSum_cons, hrem])
  · exact Prod.Lex.right _ (by simp [pendingSum_cons, RFrame.consumeOne, hrem])
  · exact Prod.Lex.right _ (by simp [pendingSum_cons, RFrame.consumeOne, hrem])
  · have hsucc_niv : st.outerVisited.contains succ = false := by simpa using _hvis
    exact Prod.Lex.left _ _ (Reachable.reachCount_insert_lt fr
      (Reachable.step frame.hreach hmemsuccs) hsucc_niv)

end OuterDFSWellFounded

/-! ## Fuel ↔ well-founded bridge, outer half -/

section OuterFuelBridge

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-! One-step unfolding equations for `outerDFSLoop_fuel` -/

theorem outerDFSLoop_fuel_nil (succs : State → Array State) (isAccepting : State → Bool)
    (fuel : Nat) (pathStack : List State) (st : FNDFSState State) :
    outerDFSLoop_fuel succs isAccepting (fuel + 1) [] pathStack st =
      some (.empty st.outerVisited.size, st) := by
  unfold outerDFSLoop_fuel
  rfl

theorem outerDFSLoop_fuel_backtrack_not_accept (succs : State → Array State)
    (isAccepting : State → Bool) (fuel : Nat) (current : State)
    (rest : List (State × List State)) (pathStack : List State) (st : FNDFSState State)
    (hacc : isAccepting current = false) :
    outerDFSLoop_fuel succs isAccepting (fuel + 1) ((current, []) :: rest) pathStack st =
      outerDFSLoop_fuel succs isAccepting fuel rest pathStack.dropLast st := by
  conv => lhs; rw [outerDFSLoop_fuel.eq_def]
  simp [hacc]

theorem outerDFSLoop_fuel_accept_none (succs : State → Array State) (isAccepting : State → Bool)
    (fuel : Nat) (current : State) (rest : List (State × List State)) (pathStack : List State)
    (st : FNDFSState State) (hacc : isAccepting current = true)
    (hinner : innerDFS_fuel succs current pathStack fuel current
        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st = none) :
    outerDFSLoop_fuel succs isAccepting (fuel + 1) ((current, []) :: rest) pathStack st = none := by
  unfold outerDFSLoop_fuel
  simp [hacc, hinner]

/-- Holzmann-Peled-Yannakakis shortcut: `target` may be `current` itself or any other state
on `pathStack`; the witness formula collapses to `current :: cyclePath` when `target = current`. -/
theorem outerDFSLoop_fuel_accept_found (succs : State → Array State) (isAccepting : State → Bool)
    (fuel : Nat) (current : State) (rest : List (State × List State)) (pathStack : List State)
    (st : FNDFSState State) (hacc : isAccepting current = true)
    (cyclePath : List State) (target : State) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (hinner : innerDFS_fuel succs current pathStack fuel current
        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st =
        some (some (cyclePath, target), iv', st')) :
    outerDFSLoop_fuel succs isAccepting (fuel + 1) ((current, []) :: rest) pathStack st =
      some (.nonEmpty pathStack
        (current :: cyclePath ++ (pathStack.dropWhile (fun y => !(y == target))).dropLast), st') := by
  unfold outerDFSLoop_fuel
  simp [hacc, hinner]

theorem outerDFSLoop_fuel_accept_not_found (succs : State → Array State) (isAccepting : State → Bool)
    (fuel : Nat) (current : State) (rest : List (State × List State)) (pathStack : List State)
    (st : FNDFSState State) (hacc : isAccepting current = true)
    (iv' : Std.HashSet State) (st' : FNDFSState State)
    (hinner : innerDFS_fuel succs current pathStack fuel current
        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st = some (none, iv', st')) :
    outerDFSLoop_fuel succs isAccepting (fuel + 1) ((current, []) :: rest) pathStack st =
      outerDFSLoop_fuel succs isAccepting fuel rest pathStack.dropLast st' := by
  conv => lhs; rw [outerDFSLoop_fuel.eq_def]
  simp [hacc, hinner]

theorem outerDFSLoop_fuel_skip_visited (succs : State → Array State) (isAccepting : State → Bool)
    (fuel : Nat) (current succ : State) (remainingTail : List State)
    (rest : List (State × List State)) (pathStack : List State) (st : FNDFSState State)
    (hnb : succ ∉ pathStack) (hvis : st.outerVisited.contains succ = true) :
    outerDFSLoop_fuel succs isAccepting (fuel + 1) ((current, succ :: remainingTail) :: rest)
        pathStack st =
      outerDFSLoop_fuel succs isAccepting fuel ((current, remainingTail) :: rest) pathStack st := by
  conv => lhs; rw [outerDFSLoop_fuel.eq_def]
  simp [hnb, hvis]

theorem outerDFSLoop_fuel_push (succs : State → Array State) (isAccepting : State → Bool)
    (fuel : Nat) (current succ : State) (remainingTail : List State)
    (rest : List (State × List State)) (pathStack : List State) (st : FNDFSState State)
    (hnb : succ ∉ pathStack) (hvis : st.outerVisited.contains succ = false) :
    outerDFSLoop_fuel succs isAccepting (fuel + 1) ((current, succ :: remainingTail) :: rest)
        pathStack st =
      outerDFSLoop_fuel succs isAccepting fuel
        ((succ, (succs succ).toList) :: (current, remainingTail) :: rest) (pathStack ++ [succ])
        { st with outerVisited := st.outerVisited.insert succ } := by
  conv => lhs; rw [outerDFSLoop_fuel.eq_def]
  simp [hnb, hvis]

/-- Schwoon-Esparza back-edge shortcut, "neither accepting" sub-case: behaves exactly like
`outerDFSLoop_fuel_skip_visited` (recurse with `succ` dropped), just reached via the
back-edge branch instead of the already-visited one. -/
theorem outerDFSLoop_fuel_back_edge_skip (succs : State → Array State) (isAccepting : State → Bool)
    (fuel : Nat) (current succ : State) (remainingTail : List State)
    (rest : List (State × List State)) (pathStack : List State) (st : FNDFSState State)
    (hb : succ ∈ pathStack) (hacc : isAccepting current = false)
    (hsacc : isAccepting succ = false) :
    outerDFSLoop_fuel succs isAccepting (fuel + 1) ((current, succ :: remainingTail) :: rest)
        pathStack st =
      outerDFSLoop_fuel succs isAccepting fuel ((current, remainingTail) :: rest) pathStack st := by
  conv => lhs; rw [outerDFSLoop_fuel.eq_def]
  simp [hb, hacc, hsacc]

/-- Schwoon-Esparza back-edge shortcut, "source accepting" sub-case: an immediate,
fuel-independent `.nonEmpty` result (self-loop or general). -/
theorem outerDFSLoop_fuel_back_edge_current_acc (succs : State → Array State)
    (isAccepting : State → Bool) (fuel : Nat) (current succ : State)
    (remainingTail : List State) (rest : List (State × List State)) (pathStack : List State)
    (st : FNDFSState State) (hb : succ ∈ pathStack) (hacc : isAccepting current = true) :
    outerDFSLoop_fuel succs isAccepting (fuel + 1) ((current, succ :: remainingTail) :: rest)
        pathStack st =
      some (.nonEmpty pathStack
        (if succ == current then [current, current]
          else current :: current :: (pathStack.dropWhile (fun y => !(y == succ))).dropLast), st) := by
  conv => lhs; rw [outerDFSLoop_fuel.eq_def]
  by_cases hsc : succ == current <;> simp [hb, hacc, hsc]

/-- Schwoon-Esparza back-edge shortcut, "target accepting" sub-case: an immediate,
fuel-independent `.nonEmpty` result. -/
theorem outerDFSLoop_fuel_back_edge_succ_acc (succs : State → Array State)
    (isAccepting : State → Bool) (fuel : Nat) (current succ : State)
    (remainingTail : List State) (rest : List (State × List State)) (pathStack : List State)
    (st : FNDFSState State) (hb : succ ∈ pathStack) (hacc : isAccepting current = false)
    (hsacc : isAccepting succ = true) :
    outerDFSLoop_fuel succs isAccepting (fuel + 1) ((current, succ :: remainingTail) :: rest)
        pathStack st =
      some (.nonEmpty (pathStack.takeWhile (fun y => !(y == succ)) ++ [succ])
        (succ :: pathStack.dropWhile (fun y => !(y == succ))), st) := by
  conv => lhs; rw [outerDFSLoop_fuel.eq_def]
  simp [hb, hacc, hsacc]

/-- Fuel-increase preserves a successful `outerDFSLoop_fuel` result. -/
theorem outerDFSLoop_fuel_add_preserves (succs : State → Array State) (isAccepting : State → Bool)
    (extra fuel : Nat)
    (stack : List (State × List State)) (pathStack : List State) (st : FNDFSState State)
    (result : EmptinessResult State) (st' : FNDFSState State)
    (h : outerDFSLoop_fuel succs isAccepting fuel stack pathStack st = some (result, st')) :
    outerDFSLoop_fuel succs isAccepting (fuel + extra) stack pathStack st = some (result, st') := by
  induction fuel generalizing stack pathStack st result st' with
  | zero => simp [outerDFSLoop_fuel.eq_def] at h
  | succ n ih =>
    rw [show n + 1 + extra = (n + extra) + 1 by omega]
    match stack with
    | [] =>
      rw [outerDFSLoop_fuel_nil] at h
      rw [outerDFSLoop_fuel_nil]
      exact h
    | (current, remaining) :: rest =>
      match remaining with
      | [] =>
        by_cases hacc : isAccepting current = true
        · cases hinner : innerDFS_fuel succs current pathStack n current
              (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st with
          | none =>
            rw [outerDFSLoop_fuel_accept_none succs isAccepting n current rest pathStack st hacc
                hinner] at h
            exact absurd h (by simp)
          | some val =>
            obtain ⟨cyc, iv', st''⟩ := val
            cases cyc with
            | some val2 =>
              obtain ⟨cyclePath, target⟩ := val2
              rw [outerDFSLoop_fuel_accept_found succs isAccepting n current rest pathStack st hacc
                  cyclePath target iv' st'' hinner] at h
              rw [outerDFSLoop_fuel_accept_found succs isAccepting (n + extra) current rest pathStack
                  st hacc cyclePath target iv' st''
                  (innerDFS_fuel_add_preserves succs current pathStack extra n current
                    (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st (some (cyclePath, target))
                    iv' st'' hinner)]
              exact h
            | none =>
              rw [outerDFSLoop_fuel_accept_not_found succs isAccepting n current rest pathStack st
                  hacc iv' st'' hinner] at h
              rw [outerDFSLoop_fuel_accept_not_found succs isAccepting (n + extra) current rest
                  pathStack st hacc iv' st''
                  (innerDFS_fuel_add_preserves succs current pathStack extra n current
                    (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st none iv' st''
                    hinner)]
              exact ih rest pathStack.dropLast st'' result st' h
        · simp only [Bool.not_eq_true] at hacc
          rw [outerDFSLoop_fuel_backtrack_not_accept succs isAccepting n current rest pathStack st
              hacc] at h
          rw [outerDFSLoop_fuel_backtrack_not_accept succs isAccepting (n + extra) current rest
              pathStack st hacc]
          exact ih rest pathStack.dropLast st result st' h
      | succ :: remainingTail =>
        by_cases hb : succ ∈ pathStack
        · by_cases hacc : isAccepting current = true
          · rw [outerDFSLoop_fuel_back_edge_current_acc succs isAccepting n current succ
                remainingTail rest pathStack st hb hacc] at h
            rw [outerDFSLoop_fuel_back_edge_current_acc succs isAccepting (n + extra) current succ
                remainingTail rest pathStack st hb hacc]
            exact h
          · simp only [Bool.not_eq_true] at hacc
            by_cases hsacc : isAccepting succ = true
            · rw [outerDFSLoop_fuel_back_edge_succ_acc succs isAccepting n current succ
                  remainingTail rest pathStack st hb hacc hsacc] at h
              rw [outerDFSLoop_fuel_back_edge_succ_acc succs isAccepting (n + extra) current succ
                  remainingTail rest pathStack st hb hacc hsacc]
              exact h
            · simp only [Bool.not_eq_true] at hsacc
              rw [outerDFSLoop_fuel_back_edge_skip succs isAccepting n current succ remainingTail
                  rest pathStack st hb hacc hsacc] at h
              rw [outerDFSLoop_fuel_back_edge_skip succs isAccepting (n + extra) current succ
                  remainingTail rest pathStack st hb hacc hsacc]
              exact ih ((current, remainingTail) :: rest) pathStack st result st' h
        · by_cases hvis : st.outerVisited.contains succ = true
          · rw [outerDFSLoop_fuel_skip_visited succs isAccepting n current succ remainingTail rest
                pathStack st hb hvis] at h
            rw [outerDFSLoop_fuel_skip_visited succs isAccepting (n + extra) current succ
                remainingTail rest pathStack st hb hvis]
            exact ih ((current, remainingTail) :: rest) pathStack st result st' h
          · simp only [Bool.not_eq_true] at hvis
            rw [outerDFSLoop_fuel_push succs isAccepting n current succ remainingTail rest pathStack
                st hb hvis] at h
            rw [outerDFSLoop_fuel_push succs isAccepting (n + extra) current succ remainingTail rest
                pathStack st hb hvis]
            exact ih ((succ, (succs succ).toList) :: (current, remainingTail) :: rest)
              (pathStack ++ [succ]) { st with outerVisited := st.outerVisited.insert succ }
              result st' h

variable {initialStates : List State} [LawfulHashable State] (succs : State → Array State)
  (fr : FiniteReach initialStates succs) (isAccepting : State → Bool)

/-- Top-level bridge: for a suitable `stack`/`pathStack`/`st`, there is a fuel value for which
`outerDFSLoop_fuel` succeeds and agrees exactly with `outerDFSLoopWF`. -/
theorem outerDFSLoop_fuel_eq_outerDFSLoopWF
    (stack : List (RFrame initialStates succs)) (pathStack : List State) (st : FNDFSState State)
    (hfin : ∀ x, st.innerFinished.contains x → Reachable initialStates succs x) :
    ∃ fuel result st', outerDFSLoop_fuel succs isAccepting fuel
        (stack.map (fun f => (f.state, f.remaining))) pathStack st =
        some (result, st') ∧
      (∀ x, st'.innerFinished.contains x → Reachable initialStates succs x) ∧
      (result, st') = outerDFSLoopWF succs isAccepting fr stack pathStack st := by
  induction stack, pathStack, st using outerDFSLoopWF.induct (succs := succs)
      (isAccepting := isAccepting) (fr := fr) with
  | case1 =>
    rename_i pathStack st
    refine ⟨1, .empty st.outerVisited.size, st,
      outerDFSLoop_fuel_nil succs isAccepting 0 pathStack st, hfin, ?_⟩
    unfold outerDFSLoopWF
    rfl
  | case2 =>
    rename_i pathStack st frame rest hrem hacc innerVisited cyclePath target fst st' hr
    have hiv : ∀ x, innerVisited.contains x → Reachable initialStates succs x := by
      simp [innerVisited, Std.HashSet.contains_emptyWithCapacity]
    obtain ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩ :=
      innerDFS_fuel_eq_innerDFSWF succs fr frame.state pathStack
        (innerFuelMeasure succs fr innerVisited + 1) frame.state frame.hreach innerVisited st
        hiv hfin (by omega)
    rw [hr] at heqC
    simp only [Prod.mk.injEq] at heqC
    obtain ⟨rfl, rfl, rfl⟩ := heqC
    refine ⟨innerFuelMeasure succs fr innerVisited + 1 + 1,
      .nonEmpty pathStack
        (frame.state :: cyclePath ++ (pathStack.dropWhile (fun y => !(y == target))).dropLast), st₁,
      ?_, hfin1, ?_⟩
    · simp only [List.map_cons, hrem]
      exact outerDFSLoop_fuel_accept_found succs isAccepting
        (innerFuelMeasure succs fr innerVisited + 1) frame.state (List.map (fun f => (f.state, f.remaining)) rest) pathStack st hacc
        cyclePath target iv₁ st₁ heq
    · rw [outerDFSLoopWF.eq_2]
      grind
  | case3 =>
    rename_i pathStack st frame rest hrem hacc innerVisited fst st' hr ih1
    have hiv : ∀ x, innerVisited.contains x → Reachable initialStates succs x := by
      simp [innerVisited, Std.HashSet.contains_emptyWithCapacity]
    obtain ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩ :=
      innerDFS_fuel_eq_innerDFSWF succs fr frame.state pathStack
        (innerFuelMeasure succs fr innerVisited + 1) frame.state frame.hreach innerVisited st
        hiv hfin (by omega)
    rw [hr] at heqC
    simp only [Prod.mk.injEq] at heqC
    obtain ⟨rfl, rfl, rfl⟩ := heqC
    obtain ⟨fuel2, result2, st2, heq2, hfin2, heqC2⟩ := ih1 hfin1
    let m := max (innerFuelMeasure succs fr innerVisited + 1) fuel2
    have heqm : innerDFS_fuel succs frame.state pathStack m frame.state innerVisited st =
        some (none, iv₁, st₁) := by
      rw [show m = (innerFuelMeasure succs fr innerVisited + 1) +
          (m - (innerFuelMeasure succs fr innerVisited + 1)) by
        simp only [m]; omega]
      exact innerDFS_fuel_add_preserves succs frame.state pathStack _
        (innerFuelMeasure succs fr innerVisited + 1) frame.state innerVisited st none iv₁ st₁ heq
    have heq2m : outerDFSLoop_fuel succs isAccepting m
        (List.map (fun f => (f.state, f.remaining)) rest) pathStack.dropLast st₁ =
        some (result2, st2) := by
      rw [show m = fuel2 + (m - fuel2) by
        simp only [m]; omega]
      exact outerDFSLoop_fuel_add_preserves succs isAccepting _ fuel2
        (List.map (fun f => (f.state, f.remaining)) rest) pathStack.dropLast st₁ result2 st2 heq2
    refine ⟨m + 1, result2, st2, ?_, hfin2, ?_⟩
    · simp only [List.map_cons, hrem]
      exact (outerDFSLoop_fuel_accept_not_found succs isAccepting m frame.state (List.map (fun f => (f.state, f.remaining)) rest) pathStack st
        hacc iv₁ st₁ heqm).trans heq2m
    · rw [outerDFSLoopWF.eq_2]
      grind
  | case4 =>
    rename_i pathStack st frame rest hrem hacc ih1
    have hacc' : isAccepting frame.state = false := by
      simp only [Bool.not_eq_true] at hacc; exact hacc
    obtain ⟨fuel2, result2, st2, heq2, hfin2, heqC2⟩ := ih1 hfin
    refine ⟨fuel2 + 1, result2, st2, ?_, hfin2, ?_⟩
    · simp only [List.map_cons, hrem]
      exact outerDFSLoop_fuel_backtrack_not_accept succs isAccepting fuel2 frame.state (List.map (fun f => (f.state, f.remaining)) rest)
        pathStack st hacc' ▸ heq2
    · rw [outerDFSLoopWF.eq_2]
      grind
  | case5 =>
    rename_i pathStack st frame rest succ remainingTail hrem hb hacc hsc
    refine ⟨1, .nonEmpty pathStack [frame.state, frame.state], st, ?_, hfin, ?_⟩
    · simp only [List.map_cons, hrem]
      rw [outerDFSLoop_fuel_back_edge_current_acc succs isAccepting 0 frame.state succ
        remainingTail (List.map (fun f => (f.state, f.remaining)) rest) pathStack st (by simpa using hb) hacc]
      simp [hsc]
    · rw [outerDFSLoopWF.eq_2]
      grind
  | case6 =>
    rename_i pathStack st frame rest succ remainingTail hrem hb hacc hsc
    refine ⟨1, .nonEmpty pathStack
      (frame.state :: frame.state :: (pathStack.dropWhile (fun y => !(y == succ))).dropLast), st,
      ?_, hfin, ?_⟩
    · simp only [List.map_cons, hrem]
      rw [outerDFSLoop_fuel_back_edge_current_acc succs isAccepting 0 frame.state succ
        remainingTail (List.map (fun f => (f.state, f.remaining)) rest) pathStack st (by simpa using hb) hacc]
      simp [hsc]
    · rw [outerDFSLoopWF.eq_2]
      grind
  | case7 =>
    rename_i pathStack st frame rest succ remainingTail hrem hb hacc hsacc
    have hacc' : isAccepting frame.state = false := by simpa using hacc
    refine ⟨1, .nonEmpty (pathStack.takeWhile (fun y => !(y == succ)) ++ [succ])
      (succ :: pathStack.dropWhile (fun y => !(y == succ))), st, ?_, hfin, ?_⟩
    · simp only [List.map_cons, hrem]
      exact outerDFSLoop_fuel_back_edge_succ_acc succs isAccepting 0 frame.state succ remainingTail
        (List.map (fun f => (f.state, f.remaining)) rest) pathStack st (by simpa using hb) hacc' hsacc
    · rw [outerDFSLoopWF.eq_2]
      grind
  | case8 =>
    rename_i pathStack st frame rest succ remainingTail hrem stack' hb hacc hsacc ih1
    have hb' : succ ∈ pathStack := by simpa using hb
    have hacc' : isAccepting frame.state = false := by simpa using hacc
    have hsacc' : isAccepting succ = false := by simpa using hsacc
    obtain ⟨fuel2, result2, st2, heq2, hfin2, heqC2⟩ := ih1 hfin
    have hmap_eq : List.map (fun f => (f.state, f.remaining)) stack' =
        (frame.state, remainingTail) :: List.map (fun f => (f.state, f.remaining)) rest := by
      simp [stack', RFrame.consumeOne]
    rw [hmap_eq] at heq2
    refine ⟨fuel2 + 1, result2, st2, ?_, hfin2, ?_⟩
    · simp only [List.map_cons, hrem]
      exact outerDFSLoop_fuel_back_edge_skip succs isAccepting fuel2 frame.state succ remainingTail
        (List.map (fun f => (f.state, f.remaining)) rest) pathStack st hb' hacc' hsacc' ▸ heq2
    · rw [outerDFSLoopWF.eq_2]
      grind
  | case9 =>
    rename_i pathStack st frame rest succ remainingTail hrem stack' hnb h ih1
    have hnb' : succ ∉ pathStack := by simpa using hnb
    obtain ⟨fuel2, result2, st2, heq2, hfin2, heqC2⟩ := ih1 hfin
    have hmap_eq : List.map (fun f => (f.state, f.remaining)) stack' =
        (frame.state, remainingTail) :: List.map (fun f => (f.state, f.remaining)) rest := by
      simp [stack', RFrame.consumeOne]
    rw [hmap_eq] at heq2
    refine ⟨fuel2 + 1, result2, st2, ?_, hfin2, ?_⟩
    · simp only [List.map_cons, hrem]
      exact outerDFSLoop_fuel_skip_visited succs isAccepting fuel2 frame.state succ remainingTail
        (List.map (fun f => (f.state, f.remaining)) rest) pathStack st hnb' h ▸ heq2
    · rw [outerDFSLoopWF.eq_2]
      grind
  | case10 =>
    rename_i pathStack st frame rest succ remainingTail hrem stack' hnb hnotvis hmemrem hmemsuccs
      st2 ih1
    have hnb' : succ ∉ pathStack := by simpa using hnb
    have hnotvis' : st.outerVisited.contains succ = false := by
      simp only [Bool.not_eq_true] at hnotvis; exact hnotvis
    have hfin2' : ∀ x, st2.innerFinished.contains x → Reachable initialStates succs x := by
      simp only [st2]; exact hfin
    obtain ⟨fuel2, result2, st2', heq2, hfin2, heqC2⟩ := ih1 hfin2'
    have hmap_eq : List.map (fun f => (f.state, f.remaining)) (frame.push succ hmemsuccs :: stack') =
        (succ, (succs succ).toList) :: (frame.state, remainingTail) ::
          List.map (fun f => (f.state, f.remaining)) rest := by
      simp [stack', RFrame.push, RFrame.consumeOne]
    rw [hmap_eq] at heq2
    refine ⟨fuel2 + 1, result2, st2', ?_, hfin2, ?_⟩
    · simp only [List.map_cons, hrem]
      exact outerDFSLoop_fuel_push succs isAccepting fuel2 frame.state succ remainingTail (List.map (fun f => (f.state, f.remaining)) rest)
        pathStack st hnb' hnotvis' ▸ heq2
    · rw [outerDFSLoopWF.eq_2]
      grind

end OuterFuelBridge

/-! ## Top-level `nestedDFS`, well-founded -/

section TopLevelWF

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-- Well-founded top-level nested DFS emptiness check. -/
@[expose] def nestedDFSWF [LawfulHashable State] (succs : State → Array State) (initialStates : List State)
    (fr : FiniteReach initialStates succs) (isAccepting : State → Bool) : EmptinessResult State :=
  let st : FNDFSState State := {
    outerVisited := Std.HashSet.emptyWithCapacity 1024
    innerFinished := Std.HashSet.emptyWithCapacity 1024
  }
  nestedDFSWF.go succs initialStates fr isAccepting initialStates (List.suffix_refl _) st
where
  go [LawfulHashable State] (succs : State → Array State) (initialStates : List State)
      (fr : FiniteReach initialStates succs) (isAccepting : State → Bool)
      (remaining : List State) (hsub : remaining <:+ initialStates) (st : FNDFSState State) :
      EmptinessResult State :=
    match remaining with
    | [] => .empty st.outerVisited.size
    | init :: rest =>
      if st.outerVisited.contains init then
        go succs initialStates fr isAccepting rest ((List.suffix_cons init rest).trans hsub) st
      else
        let st := { st with outerVisited := st.outerVisited.insert init }
        have hinit_reach : Reachable initialStates succs init :=
          .base (hsub.mem List.mem_cons_self)
        let succsList := (succs init).toList
        match outerDFSLoopWF succs isAccepting fr
            [{ state := init, hreach := hinit_reach, remaining := succsList,
                hsuffix := List.suffix_refl _ }]
            [init] st with
        | (.nonEmpty stem loop, _) => .nonEmpty stem loop
        | (.empty _, st') =>
          go succs initialStates fr isAccepting rest ((List.suffix_cons init rest).trans hsub) st'

end TopLevelWF

/-! ## Fuel ↔ well-founded bridge, top level -/

section TopLevelFuelBridge

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

theorem nestedDFS_fuel_go_nil (succs : State → Array State) (isAccepting : State → Bool)
    (st : FNDFSState State) (fuel : Nat) :
    nestedDFS_fuel.go succs isAccepting [] st (fuel + 1) = some (.empty st.outerVisited.size) := by
  unfold nestedDFS_fuel.go
  rfl

theorem nestedDFS_fuel_go_skip (succs : State → Array State) (isAccepting : State → Bool)
    (init : State) (rest : List State) (st : FNDFSState State) (fuel : Nat)
    (hvis : st.outerVisited.contains init = true) :
    nestedDFS_fuel.go succs isAccepting (init :: rest) st (fuel + 1) =
      nestedDFS_fuel.go succs isAccepting rest st fuel := by
  conv => lhs; rw [nestedDFS_fuel.go.eq_def]
  simp [hvis]

theorem nestedDFS_fuel_go_none (succs : State → Array State) (isAccepting : State → Bool)
    (init : State) (rest : List State) (st : FNDFSState State) (fuel : Nat)
    (hvis : st.outerVisited.contains init = false)
    (houter : outerDFSLoop_fuel succs isAccepting fuel
        [(init, (succs init).toList)] [init] { st with outerVisited := st.outerVisited.insert init } =
      none) :
    nestedDFS_fuel.go succs isAccepting (init :: rest) st (fuel + 1) = none := by
  unfold nestedDFS_fuel.go
  simp [hvis, houter]

theorem nestedDFS_fuel_go_nonEmpty (succs : State → Array State) (isAccepting : State → Bool)
    (init : State) (rest : List State) (st : FNDFSState State) (fuel : Nat)
    (hvis : st.outerVisited.contains init = false)
    (stem loop : List State) (st'' : FNDFSState State)
    (houter : outerDFSLoop_fuel succs isAccepting fuel
        [(init, (succs init).toList)] [init] { st with outerVisited := st.outerVisited.insert init } =
      some (.nonEmpty stem loop, st'')) :
    nestedDFS_fuel.go succs isAccepting (init :: rest) st (fuel + 1) = some (.nonEmpty stem loop) := by
  unfold nestedDFS_fuel.go
  simp [hvis, houter]

theorem nestedDFS_fuel_go_continue (succs : State → Array State) (isAccepting : State → Bool)
    (init : State) (rest : List State) (st : FNDFSState State) (fuel : Nat)
    (hvis : st.outerVisited.contains init = false)
    (m : Nat) (st' : FNDFSState State)
    (houter : outerDFSLoop_fuel succs isAccepting fuel
        [(init, (succs init).toList)] [init] { st with outerVisited := st.outerVisited.insert init } =
      some (.empty m, st')) :
    nestedDFS_fuel.go succs isAccepting (init :: rest) st (fuel + 1) =
      nestedDFS_fuel.go succs isAccepting rest st' fuel := by
  conv => lhs; rw [nestedDFS_fuel.go.eq_def]
  simp [hvis, houter]

/-- Fuel-increase preserves a successful `nestedDFS_fuel.go` result. -/
theorem nestedDFS_fuel_go_add_preserves (succs : State → Array State) (isAccepting : State → Bool)
    (extra fuel : Nat) (remaining : List State) (st : FNDFSState State)
    (result : EmptinessResult State)
    (h : nestedDFS_fuel.go succs isAccepting remaining st fuel = some result) :
    nestedDFS_fuel.go succs isAccepting remaining st (fuel + extra) = some result := by
  induction fuel generalizing remaining st result with
  | zero => simp [nestedDFS_fuel.go.eq_def] at h
  | succ n ih =>
    rw [show n + 1 + extra = (n + extra) + 1 by omega]
    match remaining with
    | [] =>
      rw [nestedDFS_fuel_go_nil] at h
      rw [nestedDFS_fuel_go_nil]
      exact h
    | init :: rest =>
      by_cases hvis : st.outerVisited.contains init = true
      · rw [nestedDFS_fuel_go_skip succs isAccepting init rest st n hvis] at h
        rw [nestedDFS_fuel_go_skip succs isAccepting init rest st (n + extra) hvis]
        exact ih rest st result h
      · simp only [Bool.not_eq_true] at hvis
        cases houter : outerDFSLoop_fuel succs isAccepting n
            [(init, (succs init).toList)] [init]
            { st with outerVisited := st.outerVisited.insert init } with
        | none =>
          rw [nestedDFS_fuel_go_none succs isAccepting init rest st n hvis houter] at h
          exact absurd h (by simp)
        | some val =>
          obtain ⟨res, st'⟩ := val
          cases res with
          | nonEmpty stem loop =>
            rw [nestedDFS_fuel_go_nonEmpty succs isAccepting init rest st n hvis stem loop st'
                houter] at h
            rw [nestedDFS_fuel_go_nonEmpty succs isAccepting init rest st (n + extra) hvis stem loop
                st'
                (outerDFSLoop_fuel_add_preserves succs isAccepting extra n
                  [(init, (succs init).toList)] [init]
                  { st with outerVisited := st.outerVisited.insert init }
                  (.nonEmpty stem loop) st' houter)]
            exact h
          | empty m =>
            rw [nestedDFS_fuel_go_continue succs isAccepting init rest st n hvis m st' houter] at h
            rw [nestedDFS_fuel_go_continue succs isAccepting init rest st (n + extra) hvis m st'
                (outerDFSLoop_fuel_add_preserves succs isAccepting extra n
                  [(init, (succs init).toList)] [init]
                  { st with outerVisited := st.outerVisited.insert init }
                  (.empty m) st' houter)]
            exact ih rest st' result h

variable {initialStates : List State} [LawfulHashable State] (succs : State → Array State)
  (fr : FiniteReach initialStates succs) (isAccepting : State → Bool)

/-- Top-level bridge: for a suitable `remaining`/`st`, there is a fuel value for which
`nestedDFS_fuel.go` succeeds and agrees exactly with `nestedDFSWF.go`. -/
theorem nestedDFS_fuel_go_eq_nestedDFSWF_go
    (remaining : List State) (hsub : remaining <:+ initialStates) (st : FNDFSState State)
    (hfin : ∀ x, st.innerFinished.contains x → Reachable initialStates succs x) :
    ∃ fuel result, nestedDFS_fuel.go succs isAccepting remaining st fuel = some result ∧
      result = nestedDFSWF.go succs initialStates fr isAccepting remaining hsub st := by
  induction remaining generalizing st with
  | nil =>
    refine ⟨1, .empty st.outerVisited.size, nestedDFS_fuel_go_nil succs isAccepting st 0, ?_⟩
    unfold nestedDFSWF.go
    rfl
  | cons init rest ih =>
    have hinit_reach : Reachable initialStates succs init := .base (hsub.mem List.mem_cons_self)
    have hsub_rest : rest <:+ initialStates := (List.suffix_cons init rest).trans hsub
    by_cases hvis : st.outerVisited.contains init = true
    · obtain ⟨fuel2, result2, heq2, heqC2⟩ := ih hsub_rest st hfin
      refine ⟨fuel2 + 1, result2, ?_, ?_⟩
      · rw [nestedDFS_fuel_go_skip succs isAccepting init rest st fuel2 hvis]
        exact heq2
      · unfold nestedDFSWF.go
        simp only [hvis]
        exact heqC2
    · simp only [Bool.not_eq_true] at hvis
      let st2 := { st with outerVisited := st.outerVisited.insert init }
      have hfin2 : ∀ x, st2.innerFinished.contains x → Reachable initialStates succs x := hfin
      obtain ⟨fuelI, resultI, stI, heqI, hfinI, heqCI⟩ :=
        outerDFSLoop_fuel_eq_outerDFSLoopWF succs fr isAccepting
          [{ state := init, hreach := hinit_reach, remaining := (succs init).toList,
              hsuffix := List.suffix_refl _ }]
          [init] st2 hfin2
      simp only [List.map] at heqI
      cases resultI with
      | nonEmpty stem loop =>
        refine ⟨fuelI + 1, .nonEmpty stem loop, ?_, ?_⟩
        · exact nestedDFS_fuel_go_nonEmpty succs isAccepting init rest st fuelI hvis stem loop stI
            heqI
        · unfold nestedDFSWF.go
          have heqCI' : (EmptinessResult.nonEmpty stem loop, stI) =
              outerDFSLoopWF succs isAccepting fr
                [{ state := init, hreach := hinit_reach, remaining := (succs init).toList,
                    hsuffix := List.suffix_refl _ }]
                [init] { st with outerVisited := st.outerVisited.insert init } := by
            simpa only [st2] using heqCI
          rw [if_neg (by simp [hvis])]
          show EmptinessResult.nonEmpty stem loop =
              match outerDFSLoopWF succs isAccepting fr
                  [{ state := init, hreach := hinit_reach, remaining := (succs init).toList,
                      hsuffix := List.suffix_refl _ }]
                  [init] { st with outerVisited := st.outerVisited.insert init } with
              | (EmptinessResult.nonEmpty stem loop, _) => EmptinessResult.nonEmpty stem loop
              | (EmptinessResult.empty _, st') =>
                nestedDFSWF.go succs initialStates fr isAccepting rest hsub_rest st'
          rw [← heqCI']
      | empty m =>
        obtain ⟨fuelR, resultR, heqR, heqCR⟩ := ih hsub_rest stI hfinI
        have heqI' : outerDFSLoop_fuel succs isAccepting (max fuelI fuelR)
            [(init, (succs init).toList)] [init] st2 = some (.empty m, stI) := by
          rw [show max fuelI fuelR = fuelI + (max fuelI fuelR - fuelI) by omega]
          exact outerDFSLoop_fuel_add_preserves succs isAccepting _ fuelI
            [(init, (succs init).toList)] [init] st2 (.empty m) stI heqI
        have heqR' : nestedDFS_fuel.go succs isAccepting rest stI (max fuelI fuelR) =
            some resultR := by
          rw [show max fuelI fuelR = fuelR + (max fuelI fuelR - fuelR) by omega]
          exact nestedDFS_fuel_go_add_preserves succs isAccepting _ fuelR rest stI resultR heqR
        refine ⟨max fuelI fuelR + 1, resultR, ?_, ?_⟩
        · rw [nestedDFS_fuel_go_continue succs isAccepting init rest st (max fuelI fuelR) hvis m stI
              heqI']
          exact heqR'
        · unfold nestedDFSWF.go
          simp only [hvis, st2] at heqCI ⊢
          rw [← heqCI]
          exact heqCR

/-- Top-level bridge: there is a fuel value for which `nestedDFS_fuel` succeeds and agrees
exactly with `nestedDFSWF`. -/
theorem nestedDFS_fuel_eq_nestedDFSWF :
    ∃ fuel, nestedDFS_fuel initialStates succs isAccepting fuel =
      some (nestedDFSWF succs initialStates fr isAccepting) := by
  unfold nestedDFS_fuel nestedDFSWF
  obtain ⟨fuel, result, heq, heqC⟩ :=
    nestedDFS_fuel_go_eq_nestedDFSWF_go succs fr isAccepting initialStates (List.suffix_refl _)
      { outerVisited := Std.HashSet.emptyWithCapacity 1024
        innerFinished := Std.HashSet.emptyWithCapacity 1024 }
      (fun x hx => absurd hx (by simp [Std.HashSet.contains_emptyWithCapacity]))
  exact ⟨fuel, heqC ▸ heq⟩

/-- `nestedDFSWF`'s `.empty` case implies no accepting cycle exists. -/
theorem nestedDFSWF_empty_no_cycle
    (n : Nat) (h : nestedDFSWF succs initialStates fr isAccepting = .empty n) :
    ¬∃ _ac : AcceptingCycle initialStates succs isAccepting, True := by
  obtain ⟨fuel, heq⟩ := nestedDFS_fuel_eq_nestedDFSWF succs fr isAccepting
  rw [h] at heq
  exact nestedDFS_fuel_empty_no_cycle heq

/-- `nestedDFSWF`'s `.nonEmpty` case yields a genuine accepting-cycle witness. -/
theorem nestedDFSWF_nonEmpty_valid
    (stem loop : List State)
    (h : nestedDFSWF succs initialStates fr isAccepting = .nonEmpty stem loop) :
    ∃ ac : AcceptingCycle initialStates succs isAccepting,
      ac.stem = stem ∧ ac.cycle = loop.tail := by
  obtain ⟨fuel, heq⟩ := nestedDFS_fuel_eq_nestedDFSWF succs fr isAccepting
  rw [h] at heq
  exact nestedDFS_fuel_nonEmpty_valid heq

end TopLevelFuelBridge

/-! ## `nestedDFSWF` as an `EmptinessChecker` instance -/

section EmptinessCheckerInterface

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-- `nestedDFSWF` packaged as an `EmptinessChecker` instance. -/
@[expose] def nestedDFSChecker [LawfulHashable State] : EmptinessChecker State where
  check := nestedDFSWF
  nonEmpty_valid := fun {succs initialStates fr isAccepting stem loop} h =>
    nestedDFSWF_nonEmpty_valid succs fr isAccepting stem loop h
  empty_no_cycle := fun {succs initialStates fr isAccepting n} h =>
    nestedDFSWF_empty_no_cycle succs fr isAccepting n h

end EmptinessCheckerInterface

/-! ## Packaging a `FiniteReach` witness from `BA.WellFormed` -/

section BAFiniteReach

variable {α : Type u} [BEq α] [Hashable α]

/-- A well-formed `BA`'s own state set is a `FiniteReach` witness for its `getSuccessors` function. -/
theorem BA.finiteReach (ba : BA α) (hwf : ba.WellFormed) :
    FiniteReach ba.initialStates.toList ba.getSuccessors := by
  refine ⟨ba.states.toList, fun s hs => Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr ?_)⟩
  induction hs with
  | base hi =>
    exact hwf.initial_mem _ (Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hi))
  | step _ hmem ih => exact hwf.succ_mem _ _ ih hmem

end BAFiniteReach

/-! ## From an accepting run to an `AcceptingCycle` -/

section PumpingLemma

variable {State : Type u}

/-- An increasing sequence of indices at which `σ` is accepting, built by repeatedly
re-invoking `hacc` past the previous index. -/
private noncomputable def accIdxSeq (σ : Nat → State) (isAccepting : State → Bool)
    (hacc : ∀ N, ∃ n ≥ N, isAccepting (σ n) = true) : Nat → Nat
  | 0 => (hacc 0).choose
  | k + 1 => (hacc (accIdxSeq σ isAccepting hacc k + 1)).choose

private theorem accIdxSeq_succ_spec (σ : Nat → State) (isAccepting : State → Bool)
    (hacc : ∀ N, ∃ n ≥ N, isAccepting (σ n) = true) (k : Nat) :
    accIdxSeq σ isAccepting hacc k + 1 ≤ accIdxSeq σ isAccepting hacc (k + 1) ∧
      isAccepting (σ (accIdxSeq σ isAccepting hacc (k + 1))) = true := by
  show (accIdxSeq σ isAccepting hacc k + 1 ≤ (hacc (accIdxSeq σ isAccepting hacc k + 1)).choose) ∧
      isAccepting (σ (hacc (accIdxSeq σ isAccepting hacc k + 1)).choose) = true
  exact (hacc (accIdxSeq σ isAccepting hacc k + 1)).choose_spec

private theorem accIdxSeq_mono (σ : Nat → State) (isAccepting : State → Bool)
    (hacc : ∀ N, ∃ n ≥ N, isAccepting (σ n) = true) (k : Nat) :
    accIdxSeq σ isAccepting hacc k < accIdxSeq σ isAccepting hacc (k + 1) :=
  Nat.lt_of_succ_le (accIdxSeq_succ_spec σ isAccepting hacc k).1

private theorem accIdxSeq_accepting (σ : Nat → State) (isAccepting : State → Bool)
    (hacc : ∀ N, ∃ n ≥ N, isAccepting (σ n) = true) (k : Nat) :
    isAccepting (σ (accIdxSeq σ isAccepting hacc k)) = true := by
  cases k with
  | zero => exact (hacc 0).choose_spec.2
  | succ k => exact (accIdxSeq_succ_spec σ isAccepting hacc k).2

private theorem accIdxSeq_lt_of_lt (σ : Nat → State) (isAccepting : State → Bool)
    (hacc : ∀ N, ∃ n ≥ N, isAccepting (σ n) = true) :
    ∀ {i j : Nat}, i < j → accIdxSeq σ isAccepting hacc i < accIdxSeq σ isAccepting hacc j := by
  intro i j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro h
    by_cases heq : i = j
    · rw [heq]; exact accIdxSeq_mono σ isAccepting hacc j
    · exact Nat.lt_trans (ih (by omega)) (accIdxSeq_mono σ isAccepting hacc j)

/-- The reverse direction of `nestedDFSWF_empty_no_cycle`/`nestedDFS_fuel_empty_no_cycle`:
an accepting run yields an `AcceptingCycle` witness. -/
theorem exists_acceptingCycle_of_run
    {succs : State → Array State} {isAccepting : State → Bool}
    {initialStates : List State} (fr : FiniteReach initialStates succs)
    {σ : Nat → State} (hinit : σ 0 ∈ initialStates)
    (htrans : ∀ n, σ (n + 1) ∈ succs (σ n))
    (hacc : ∀ N, ∃ n ≥ N, isAccepting (σ n) = true) :
    ∃ _ac : AcceptingCycle initialStates succs isAccepting, True := by
  obtain ⟨i, j, hij, heq⟩ :=
    fr.exists_lt_sample_eq (Reachable.of_run hinit htrans) (accIdxSeq σ isAccepting hacc)
  have hpq : accIdxSeq σ isAccepting hacc i < accIdxSeq σ isAccepting hacc j :=
    accIdxSeq_lt_of_lt σ isAccepting hacc hij
  let p := accIdxSeq σ isAccepting hacc i
  let q := accIdxSeq σ isAccepting hacc j
  have hstem_get : ∀ i, (hi : i < p + 1) →
      ((List.range (p + 1)).map σ)[i]'(by simpa using hi) = σ i := by
    intro i hi; simp
  have hcycle_get : ∀ i, (hi : i < q - p) →
      ((List.range (q - p)).map (fun k => σ (p + k)))[i]'(by simpa using hi) = σ (p + i) := by
    intro i hi; simp
  refine ⟨{
    stem := (List.range (p + 1)).map σ
    cycle := (List.range (q - p)).map (fun k => σ (p + k))
    stem_nonempty := by simp
    cycle_nonempty := by simp; omega
    stem_head_initial := by
      rw [List.head_eq_getElem, hstem_get 0 (by omega)]
      exact hinit
    stem_chain := by
      intro i hi
      simp only [List.length_map, List.length_range] at hi
      rw [hstem_get i (by omega), hstem_get (i + 1) (by omega)]
      exact htrans i
    overlap := by
      rw [List.getLast_eq_getElem, List.head_eq_getElem]
      simp only [List.length_map, List.length_range, Nat.add_sub_cancel]
      rw [hstem_get p (by omega), hcycle_get 0 (by omega)]
      rfl
    cycle_chain := by
      intro i hi
      simp only [List.length_map, List.length_range] at hi
      rw [hcycle_get i (by omega), hcycle_get (i + 1) (by omega)]
      simpa [Nat.add_assoc] using htrans (p + i)
    cycle_back := by
      rw [List.head_eq_getElem, List.getLast_eq_getElem]
      simp only [List.length_map, List.length_range]
      rw [hcycle_get 0 (by omega), hcycle_get (q - p - 1) (by omega)]
      have ht := htrans (p + (q - p - 1))
      have heq2 : p + (q - p - 1) + 1 = q := by omega
      rw [heq2] at ht
      rwa [← heq] at ht
    cycle_head_accepting := by
      rw [List.head_eq_getElem, hcycle_get 0 (by omega)]
      exact accIdxSeq_accepting σ isAccepting hacc i
  }, trivial⟩

end PumpingLemma

end LTLLib
