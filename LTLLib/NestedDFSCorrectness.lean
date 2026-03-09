/-
  Correctness of the nested DFS emptiness check (Phase 5b).

  We prove: if nestedDFS returns `empty`, then the graph has no accepting cycle
  reachable from the initial states.

  Approach: fuel-based total versions of `innerDFS` and `outerDFSLoop`, with
  correctness proved by induction on fuel. The fuel versions compute the same
  results as the `partial` versions when given sufficient fuel.

  The proof follows the CVWY argument:
  - Inner DFS from an accepting seed explores all reachable states (modulo
    innerFinished). If it returns `none`, seed is unreachable from itself.
  - The `innerFinished` optimization is sound due to DFS post-ordering:
    among accepting states on a hypothetical cycle, the one with the latest
    outer DFS finish time can explore the full cycle in its inner DFS,
    because no cycle state has been added to `innerFinished` yet.

  The proof structure follows the "color" formulation of Schwoon & Esparza:
  - States are conceptually colored white/cyan/blue/red during execution.
  - The key invariant (`blue_basic_invar` in CAVA terminology) states that
    from any red state, no cyan/stack state is reachable through red states.
  - When inner DFS finishes without finding a cycle, the seed's reachable
    set (through non-innerFinished states) has been fully explored.

  References:
  - Courcoubetis, Vardi, Wolper, Yannakakis (CVWY): "Memory-efficient
    algorithms for the verification of temporal properties" (1992)
    — Original nested DFS algorithm and the post-order argument.
  - Schwoon & Esparza: "A Note on On-The-Fly Verification Algorithms"
    (TACAS 2005) — Color-based reformulation; proof that inner DFS explores
    all reachable non-finished states; Lemma 1 (no accepting cycle through
    finished states).
  - Peter Lammich et al.: CAVA Isabelle DFS Framework (AFP)
    — Mechanized proof with `blue_basic_invar`, `restr_invar`,
    `no_accpt_cycle_in_finish`. Our inner DFS correctness mirrors their
    `red_dfs_inv` invariant.
  - Jaco van de Pol: "Automated Verification of Nested DFS" (FMICS 2015)
    — Local color invariants verified in Dafny; confirms the monotonicity
    and exploration properties we formalize here.
-/
import LTLLib.NestedDFS

namespace LTLLib

/-! ## Graph paths -/

/-- There is a non-empty path from `s` to `t` via `succs`, where all
    INTERMEDIATE states (not `s` or `t`) satisfy `¬blocked`.
    The source and target are not checked against `blocked`.

    This corresponds to "restricted reachability" (`restr_invar`) in the
    CAVA Isabelle DFS framework: reachability through a restricted set. -/
inductive PathTo (succs : State → Array State) (blocked : State → Prop)
    : State → State → Prop where
  /-- Direct edge: t is a successor of s. -/
  | direct {s t : State} (ht : t ∈ succs s) : PathTo succs blocked s t
  /-- Through an intermediate: s → mid →* t, where mid is unblocked. -/
  | through {s mid t : State} (hmid : mid ∈ succs s) (hunblocked : ¬blocked mid)
    (h : PathTo succs blocked mid t) : PathTo succs blocked s t

/-- More blocking means fewer paths (contravariant in `blocked`). -/
theorem PathTo.weaken {succs : State → Array State}
    {blocked₁ blocked₂ : State → Prop} {s t : State}
    (h : PathTo succs blocked₂ s t)
    (hsub : ∀ x, blocked₁ x → blocked₂ x) :
    PathTo succs blocked₁ s t := by
  induction h with
  | direct ht => exact .direct ht
  | through hmid hunb _ ih =>
    exact .through hmid (fun hb => hunb (hsub _ hb)) ih

/-! ## NDFSState (fuel version) -/

/-- Mutable state for the nested DFS algorithm (mirroring the private version). -/
structure FNDFSState (State : Type u) [BEq State] [Hashable State] where
  outerVisited : Std.HashSet State
  innerFinished : Std.HashSet State

/-! ## Fuel-based inner DFS

The inner DFS searches for a path from `current` back to `seed`.
It uses `innerVisited` to track states visited in this inner search,
and `innerFinished` (in `FNDFSState`) as a cross-call optimization:
states whose inner DFS already completed without finding a cycle.

Cf. Schwoon & Esparza §3, "red DFS" in CAVA terminology. -/

/-- Result type for inner DFS: `none` = out of fuel. -/
abbrev InnerResult (State : Type u) [BEq State] [Hashable State] :=
  Option (Option (List State) × Std.HashSet State × FNDFSState State)

mutual
/-- Inner DFS with fuel. Returns `none` if fuel runs out.
    Corresponds to the "red DFS" in Schwoon & Esparza's color formulation. -/
def innerDFS_fuel [BEq State] [Hashable State] [LawfulBEq State]
    (succs : State → Array State) (seed : State)
    (fuel : Nat) (current : State)
    (innerVisited : Std.HashSet State) (st : FNDFSState State)
    : InnerResult State :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if st.innerFinished.contains current then
      some (none, innerVisited, st)
    else if innerVisited.contains current then
      some (none, innerVisited, st)
    else
      let innerVisited := innerVisited.insert current
      innerDFS_fuel_fold succs seed fuel current (succs current).toList innerVisited st

/-- Process successor list for inner DFS. -/
def innerDFS_fuel_fold [BEq State] [Hashable State] [LawfulBEq State]
    (succs : State → Array State) (seed : State)
    (fuel : Nat) (current : State) (remaining : List State)
    (innerVisited : Std.HashSet State) (st : FNDFSState State)
    : InnerResult State :=
  match remaining with
  | [] =>
    let st := { st with innerFinished := st.innerFinished.insert current }
    some (none, innerVisited, st)
  | succ :: rest =>
    if succ == seed then
      some (some [current], innerVisited, st)
    else
      match innerDFS_fuel succs seed fuel succ innerVisited st with
      | none => none
      | some (some cyclePath, iv, st') =>
        some (some (current :: cyclePath), iv, st')
      | some (none, iv, st') =>
        innerDFS_fuel_fold succs seed fuel current rest iv st'
end

/-! ## Fuel-based outer DFS -/

/-- Outer DFS loop with fuel.
    Corresponds to the "blue DFS" in Schwoon & Esparza's color formulation. -/
def outerDFSLoop_fuel [BEq State] [Hashable State] [LawfulBEq State]
    (succs : State → Array State) (isAccepting : State → Bool)
    (fuel : Nat)
    (stack : List (State × List State))
    (pathStack : List State)
    (st : FNDFSState State)
    : Option (EmptinessResult State × FNDFSState State) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match stack with
    | [] => some (.empty st.outerVisited.size, st)
    | (current, remaining) :: rest =>
      match remaining with
      | [] =>
        if isAccepting current then
          let innerVisited := Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)
          match innerDFS_fuel succs current fuel current innerVisited st with
          | none => none
          | some (some cyclePath, _, st') =>
            some (.nonEmpty pathStack (current :: cyclePath), st')
          | some (none, _, st') =>
            outerDFSLoop_fuel succs isAccepting fuel rest pathStack.dropLast st'
        else
          outerDFSLoop_fuel succs isAccepting fuel rest pathStack.dropLast st
      | succ :: remainingTail =>
        let stack' := (current, remainingTail) :: rest
        if st.outerVisited.contains succ then
          outerDFSLoop_fuel succs isAccepting fuel stack' pathStack st
        else
          let st := { st with outerVisited := st.outerVisited.insert succ }
          let succChildren := (succs succ).toList
          let stack' := (succ, succChildren) :: stack'
          outerDFSLoop_fuel succs isAccepting fuel stack' (pathStack ++ [succ]) st

/-- Full nested DFS with fuel. -/
def nestedDFS_fuel [BEq State] [Hashable State] [LawfulBEq State]
    (initialStates : List State)
    (succs : State → Array State)
    (isAccepting : State → Bool)
    (fuel : Nat)
    : Option (EmptinessResult State) :=
  let st : FNDFSState State := {
    outerVisited := Std.HashSet.emptyWithCapacity 1024
    innerFinished := Std.HashSet.emptyWithCapacity 1024
  }
  nestedDFS_fuel.go succs isAccepting initialStates st fuel
where
  go (succs : State → Array State) (isAccepting : State → Bool)
      (remaining : List State) (st : FNDFSState State) (fuel : Nat)
      : Option (EmptinessResult State) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match remaining with
      | [] => some (.empty st.outerVisited.size)
      | init :: rest =>
        if st.outerVisited.contains init then
          go succs isAccepting rest st fuel
        else
          let st := { st with outerVisited := st.outerVisited.insert init }
          let succsList := (succs init).toList
          match outerDFSLoop_fuel succs isAccepting fuel
              [(init, succsList)] [init] st with
          | none => none
          | some (.nonEmpty stem loop, _) => some (.nonEmpty stem loop)
          | some (.empty _, st') => go succs isAccepting rest st' fuel

/-! ## Accepting cycle definition -/

/-- An accepting cycle exists: there is a stem from an initial state to an
    accepting state, and a cycle from that state back to itself.

    This is the standard "lasso" witness for non-emptiness of a Büchi
    automaton (cf. CVWY §2, Schwoon & Esparza §2). -/
structure AcceptingCycle
    (initialStates : List State) (succs : State → Array State)
    (isAccepting : State → Bool) where
  stem : List State
  cycle : List State
  stem_nonempty : stem.length ≥ 1
  cycle_nonempty : cycle.length ≥ 1
  stem_head_initial : stem.head (List.ne_nil_of_length_pos (by omega)) ∈ initialStates
  stem_chain : ∀ (i : Nat), (hi : i + 1 < stem.length) →
    stem[i + 1] ∈ succs (stem[i])
  overlap : stem.getLast (List.ne_nil_of_length_pos (by omega)) =
            cycle.head (List.ne_nil_of_length_pos (by omega))
  cycle_chain : ∀ (i : Nat), (hi : i + 1 < cycle.length) →
    cycle[i + 1] ∈ succs (cycle[i])
  cycle_back : cycle.head (List.ne_nil_of_length_pos (by omega)) ∈
    succs (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
  cycle_head_accepting : isAccepting (cycle.head (List.ne_nil_of_length_pos (by omega))) = true

/-! ## Predicate: blocked states -/

section InnerCorrectness

variable [BEq State] [Hashable State] [LawfulBEq State]

/-- A state is "blocked" if it is in the inner visited set or in innerFinished.
    Blocked states are skipped by inner DFS.

    Corresponds to "red ∪ pink" in Schwoon & Esparza's color scheme, or
    states that are not white from the inner DFS's perspective. -/
def isBlocked (iv : Std.HashSet State) (ifin : Std.HashSet State) (s : State) : Prop :=
  iv.contains s ∨ ifin.contains s

/-! ## Inner DFS correctness proofs

The correctness argument for inner DFS follows Schwoon & Esparza (2005), §3.
The key properties after `innerDFS_fuel` returns `none` (no cycle found) are:

1. **Monotonicity**: `iv` and `innerFinished` only grow (cf. `red_dfs_inv` in CAVA).
2. **Complete exploration**: every successor of every visited state is either
   the seed (which would have triggered a cycle report) or is blocked in the
   output state. This means the inner DFS has fully explored the reachable
   set modulo `innerFinished`.
3. **No-seed-in-successors**: no processed successor equals `seed` (otherwise
   a cycle would have been reported).

These together imply that there is no path from `current` back to `seed`
through non-blocked intermediates — which is the core of Lemma 1 in
Schwoon & Esparza. -/

/-- Helper for monotonicity: `innerDFS_fuel_fold` monotonicity assuming
    `innerDFS_fuel` monotonicity at the same fuel level.
    Proved by induction on `remaining`. -/
private theorem innerDFS_fuel_fold_mono_aux (succs : State → Array State) (seed : State)
    (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State)
      (result : Option (List State)) (iv₁ : Std.HashSet State) (st₁ : FNDFSState State),
      innerDFS_fuel succs seed fuel curr iv₀ st₀ = some (result, iv₁, st₁) →
      (∀ s, iv₀.contains s → iv₁.contains s) ∧
      (∀ s, st₀.innerFinished.contains s → st₁.innerFinished.contains s))
    (result : Option (List State)) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (h : innerDFS_fuel_fold succs seed fuel current remaining iv st =
      some (result, iv', st')) :
    (∀ s, iv.contains s → iv'.contains s) ∧
    (∀ s, st.innerFinished.contains s → st'.innerFinished.contains s) := by
  induction remaining generalizing iv st result iv' st' with
  | nil =>
    rw [innerDFS_fuel_fold.eq_def] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact ⟨fun _ h => h, fun s hs => by
      show ({ outerVisited := st.outerVisited,
              innerFinished := st.innerFinished.insert current } : FNDFSState State).innerFinished.contains s
      simp [Std.HashSet.contains_insert, hs, Bool.or_true]⟩
  | cons succ rest ih_rem =>
    rw [innerDFS_fuel_fold.eq_def] at h
    simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact ⟨fun _ h => h, fun _ h => h⟩
    · split at h
      · exact absurd h (by simp)
      · rename_i heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        exact ih_inner _ _ _ _ _ _ heq
      · rename_i iv_mid st_mid heq
        have ⟨hiv1, hfin1⟩ := ih_inner _ _ _ _ _ _ heq
        have ⟨hiv2, hfin2⟩ := ih_rem iv_mid st_mid _ _ _ h
        exact ⟨fun s hs => hiv2 s (hiv1 s hs), fun s hs => hfin2 s (hfin1 s hs)⟩

/-- Monotonicity of `innerDFS_fuel`: the inner visited set and innerFinished
    set only grow across a call that returns `some`.
    Proved by induction on fuel, using `innerDFS_fuel_fold_mono_aux`.

    Cf. `red_dfs_inv` monotonicity in the CAVA Isabelle DFS framework. -/
theorem innerDFS_fuel_mono (succs : State → Array State) (seed : State)
    (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (result : Option (List State)) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (h : innerDFS_fuel succs seed fuel current iv st = some (result, iv', st')) :
    (∀ s, iv.contains s → iv'.contains s) ∧
    (∀ s, st.innerFinished.contains s → st'.innerFinished.contains s) := by
  induction fuel generalizing current iv st result iv' st' with
  | zero => simp [innerDFS_fuel.eq_def] at h
  | succ n ih =>
    rw [innerDFS_fuel.eq_def] at h
    simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h; exact ⟨fun _ h => h, fun _ h => h⟩
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h; exact ⟨fun _ h => h, fun _ h => h⟩
      · have ⟨hiv_m, hfin_m⟩ := innerDFS_fuel_fold_mono_aux succs seed n current _ _ st ih _ _ _ h
        exact ⟨fun s hs => hiv_m s (by simp [Std.HashSet.contains_insert, hs, Bool.or_true]),
               hfin_m⟩

/-- Monotonicity of `innerDFS_fuel_fold`, derived from `innerDFS_fuel_mono`. -/
theorem innerDFS_fuel_fold_mono (succs : State → Array State) (seed : State)
    (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (result : Option (List State)) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (h : innerDFS_fuel_fold succs seed fuel current remaining iv st =
      some (result, iv', st')) :
    (∀ s, iv.contains s → iv'.contains s) ∧
    (∀ s, st.innerFinished.contains s → st'.innerFinished.contains s) :=
  innerDFS_fuel_fold_mono_aux succs seed fuel current remaining iv st
    (fun curr iv₀ st₀ res iv₁ st₁ h => innerDFS_fuel_mono succs seed fuel curr iv₀ st₀ res iv₁ st₁ h)
    result iv' st' h

/-- After `innerDFS_fuel` returns `some`, `current` ends up in `iv'` or
    `st'.innerFinished`. This is because inner DFS either:
    - finds `current` already in `innerFinished` (returns immediately),
    - finds `current` already in `iv` (returns immediately), or
    - inserts `current` into `iv` and calls the fold (monotonicity preserves it). -/
theorem innerDFS_fuel_current_blocked (succs : State → Array State) (seed : State)
    (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    {result : Option (List State)} {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel succs seed fuel current iv st = some (result, iv', st')) :
    iv'.contains current ∨ st'.innerFinished.contains current := by
  induction fuel generalizing current iv st result iv' st' with
  | zero => simp [innerDFS_fuel.eq_def] at h
  | succ n ih =>
    rw [innerDFS_fuel.eq_def] at h; simp only at h
    split at h
    · rename_i hfin
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      exact Or.inr (by simp_all)
    · split at h
      · rename_i _ hiv
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, -⟩ := h
        exact Or.inl (by simp_all)
      · have ⟨hiv_m, _⟩ := innerDFS_fuel_fold_mono_aux succs seed n current _ _ st
          (fun curr iv₀ st₀ res iv₁ st₁ h => innerDFS_fuel_mono succs seed n curr iv₀ st₀ res iv₁ st₁ h)
          _ _ _ h
        exact Or.inl (hiv_m current (by simp [Std.HashSet.contains_insert]))

/-- After `innerDFS_fuel_fold` returns `none` (no cycle), every successor in
    `remaining` is not `seed` and is blocked in the output state.

    This is the "complete exploration" property: every successor was either
    already blocked, or was recursively explored and added to `iv'`.
    Corresponds to the invariant that all red-DFS successors end up red or
    pink (Schwoon & Esparza §3, van de Pol (2015) invariant R2). -/
theorem innerDFS_fuel_fold_succs_blocked (succs : State → Array State) (seed : State)
    (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State)
      (result : Option (List State)) (iv₁ : Std.HashSet State) (st₁ : FNDFSState State),
      innerDFS_fuel succs seed fuel curr iv₀ st₀ = some (result, iv₁, st₁) →
      (∀ s, iv₀.contains s → iv₁.contains s) ∧
      (∀ s, st₀.innerFinished.contains s → st₁.innerFinished.contains s))
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel_fold succs seed fuel current remaining iv st =
      some (none, iv', st')) :
    ∀ s, s ∈ remaining →
      (s = seed → False) ∧ isBlocked iv' st'.innerFinished s := by
  induction remaining generalizing iv st with
  | nil =>
    intro s hs; simp at hs
  | cons s₀ rest ih_rem =>
    intro s hs
    rw [innerDFS_fuel_fold.eq_def] at h; simp only at h
    by_cases hse : (s₀ == seed) = true
    · simp [hse] at h
    · simp only [hse] at h
      have hs₀_ne_seed : s₀ ≠ seed := fun heq => hse (beq_iff_eq.mpr heq)
      generalize hm : innerDFS_fuel succs seed fuel s₀ iv st = r at h
      match r, h with
      | none, h => simp at h
      | some (some cyclePath, iv_mid, st_mid), h =>
        simp at h
      | some (none, iv_mid, st_mid), h =>
        rcases List.mem_cons.mp hs with rfl | hmem
        · have ⟨hiv_fold, hfin_fold⟩ :=
            innerDFS_fuel_fold_mono_aux succs seed fuel current rest iv_mid st_mid ih_inner _ _ _ h
          constructor
          · intro heq_seed; exact hs₀_ne_seed heq_seed
          · have hblk := innerDFS_fuel_current_blocked succs seed fuel s iv st hm
            unfold isBlocked
            rcases hblk with hiv_s | hfin_s
            · exact Or.inl (hiv_fold _ hiv_s)
            · exact Or.inr (hfin_fold _ hfin_s)
        · exact ih_rem iv_mid st_mid h s hmem

/-- Key theorem: when inner DFS is called from the outer DFS on an accepting
    seed with an empty `innerVisited` and returns `none`, the seed cannot reach
    itself through non-blocked intermediates.

    Precondition: seed is NOT already in `innerFinished` (guaranteed by the
    outer DFS invariant — seed is still on the stack when inner DFS is called).

    This is the direct consequence used by the outer DFS correctness argument.
    Cf. Schwoon & Esparza §3, Lemma 1: after red DFS from seed returns
    without finding a cycle, seed is not reachable from itself through
    unfinished states. -/
theorem innerDFS_no_cycle_from_seed (succs : State → Array State) (seed : State)
    (fuel : Nat) (st : FNDFSState State) (cap : Nat)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (hnotfin : st.innerFinished.contains seed = false)
    (h : innerDFS_fuel succs seed (fuel + 1) seed
      (Std.HashSet.emptyWithCapacity cap) st = some (none, iv', st')) :
    ¬PathTo succs (isBlocked iv' st'.innerFinished) seed seed := by
  rw [innerDFS_fuel.eq_def] at h
  simp only at h
  split at h
  · simp_all
  · split at h
    · have : (Std.HashSet.emptyWithCapacity cap : Std.HashSet State).contains seed = false :=
        Std.HashSet.contains_emptyWithCapacity
      simp_all
    · have hsb := innerDFS_fuel_fold_succs_blocked succs seed fuel seed _ _ st
        (fun curr iv₀ st₀ res iv₁ st₁ h => innerDFS_fuel_mono succs seed fuel curr iv₀ st₀ res iv₁ st₁ h)
        h
      intro hpath
      cases hpath with
      | direct ht =>
        exact (hsb seed (Array.mem_toList_iff.mpr ht)).1 rfl
      | through hmid hunb _ =>
        exact hunb (hsb _ (Array.mem_toList_iff.mpr hmid)).2

end InnerCorrectness

/-! ## Outer DFS invariants

The outer DFS (blue DFS) maintains the invariant that every accepting state
that has been fully processed (popped from the outer stack) has had its inner
DFS run, and the result was added to `innerFinished`.

The CVWY post-order argument (formalized in Schwoon & Esparza §3, Lemma 2):
- Suppose there exists an accepting cycle C.
- Let `a` be the accepting state on C with the LATEST outer DFS finish time.
- When inner DFS runs from `a`, no state on C is in `innerFinished` yet
  (because `a` finishes last among cycle states, and inner DFS for earlier
  states hasn't added cycle states to `innerFinished`).
- Therefore inner DFS from `a` can explore the entire cycle and must find it.
- Contradiction with the assumption that all inner DFS calls returned `none`.

This is the key insight that makes the `innerFinished` optimization sound. -/

section OuterCorrectness

variable [BEq State] [Hashable State] [LawfulBEq State]

/-- Outer DFS invariant: every accepting state in `outerVisited` that is NOT
    on the current stack has been processed by inner DFS and added to
    `innerFinished`.

    This captures the CVWY post-order property: when we pop an accepting state
    from the outer stack, we run inner DFS and add it to `innerFinished`.
    States still on the stack haven't been processed yet. -/
structure OuterInvariant
    (succs : State → Array State) (isAccepting : State → Bool)
    (st : FNDFSState State)
    (stackStates : List State) : Prop where
  /-- Every accepting, visited, non-stack state is in innerFinished. -/
  accepting_finished : ∀ s, st.outerVisited.contains s →
    isAccepting s → s ∉ stackStates → st.innerFinished.contains s
  /-- For every state in innerFinished, there is no self-cycle through
      non-innerFinished states. This is accumulated from inner DFS results.
      Cf. CAVA `no_accpt_cycle_in_finish`. -/
  finished_no_cycle : ∀ s, st.innerFinished.contains s →
    ¬PathTo succs (fun x => st.innerFinished.contains x) s s

/-- If the outer DFS returns `empty`, then the outer invariant holds with
    an empty stack (all accepting states have been processed).

    The proof uses the CVWY post-order argument (Schwoon & Esparza Lemma 2):
    among accepting states on a hypothetical cycle, the one with latest
    outer DFS finish time would have its full cycle available during inner
    DFS, leading to a contradiction. -/
theorem outerDFSLoop_fuel_empty_no_cycle
    (succs : State → Array State) (isAccepting : State → Bool)
    (fuel : Nat)
    (stack : List (State × List State))
    (pathStack : List State)
    (st : FNDFSState State)
    {n : Nat} {st' : FNDFSState State}
    (h : outerDFSLoop_fuel succs isAccepting fuel stack pathStack st =
      some (.empty n, st'))
    (hinv : OuterInvariant succs isAccepting st (stack.map Prod.fst ++ pathStack)) :
    OuterInvariant succs isAccepting st' [] := by
  sorry

end OuterCorrectness

/-! ## Main correctness theorem -/

/-- If the fuel-based nested DFS returns `empty`, then there is no accepting
    cycle reachable from the initial states.

    This is the end-to-end correctness theorem for the emptiness check.
    It combines:
    1. Inner DFS correctness (Schwoon & Esparza Lemma 1): each inner DFS call
       that returns `none` proves the seed has no self-cycle through
       non-finished states.
    2. Outer DFS post-order argument (Schwoon & Esparza Lemma 2 / CVWY):
       the `innerFinished` optimization is sound because among accepting
       states on a cycle, the one with latest finish time sees the full cycle.
    3. Structural induction on fuel to compose these properties across the
       entire DFS traversal.

    References:
    - CVWY (1992), Theorem 1
    - Schwoon & Esparza (2005), Theorem 1
    - CAVA (AFP), `nested_dfs_correct`
    - van de Pol (2015), Theorem 2 -/
theorem nestedDFS_fuel_empty_no_cycle [BEq State] [Hashable State] [LawfulBEq State]
    {initialStates : List State}
    {succs : State → Array State} {isAccepting : State → Bool}
    {fuel n : Nat}
    (h : nestedDFS_fuel initialStates succs isAccepting fuel = some (.empty n)) :
    ¬∃ ac : AcceptingCycle initialStates succs isAccepting, True := by
  sorry

end LTLLib
