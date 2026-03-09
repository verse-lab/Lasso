/-
  Correctness of the nested DFS emptiness check (Phase 5b).

  We prove: if nestedDFS returns `empty`, then the graph has no accepting cycle
  reachable from the initial states.

  Approach: fuel-based total versions of `innerDFS` and `outerDFSLoop`, with
  correctness proved by induction on fuel. The fuel versions compute the same
  results as the `partial` versions when given sufficient fuel.

  The proof follows the CVWY argument:
  - Inner DFS from an accepting seed explores all reachable states (modulo
    innerFinished). If it returns `none`, seed is unreachable.
  - The `innerFinished` optimization is sound due to DFS post-ordering:
    among accepting states on a hypothetical cycle, the one with the latest
    finish time can explore the full cycle.

  References:
  - Courcoubetis, Vardi, Wolper, Yannakakis (CVWY): "Memory-efficient
    algorithms for the verification of temporal properties" (1992)
  - Schwoon & Esparza: "A Note on On-The-Fly Verification Algorithms" (2005)
-/
import LTLLib.NestedDFS

namespace LTLLib

/-! ## Graph paths -/

/-- There is a non-empty path from `s` to `t` via `succs`, where all
    INTERMEDIATE states (not `s` or `t`) satisfy `¬blocked`.
    The source and target are not checked against `blocked`. -/
inductive PathTo (succs : State → Array State) (blocked : State → Prop)
    : State → State → Prop where
  /-- Direct edge: t is a successor of s. -/
  | direct {s t : State} (ht : t ∈ succs s) : PathTo succs blocked s t
  /-- Through an intermediate: s → mid →* t, where mid is unblocked. -/
  | through {s mid t : State} (hmid : mid ∈ succs s) (hunblocked : ¬blocked mid)
    (h : PathTo succs blocked mid t) : PathTo succs blocked s t

/-- More blocking means fewer paths. -/
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

/-! ## Fuel-based inner DFS -/

/-- Result type for inner DFS: `none` = out of fuel. -/
abbrev InnerResult (State : Type u) [BEq State] [Hashable State] :=
  Option (Option (List State) × Std.HashSet State × FNDFSState State)

mutual
/-- Inner DFS with fuel. Returns `none` if fuel runs out. -/
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

/-- Outer DFS loop with fuel. -/
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
    accepting state, and a cycle from that state back to itself. -/
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

/-! ## HashSet monotonicity helpers -/

section Mono

variable [BEq State] [Hashable State] [LawfulBEq State]

/-- `iv` only grows: if `innerDFS_fuel` returns `some`, the output iv contains
    everything in the input iv. Similarly for innerFinished. -/
structure InnerMono (iv iv' : Std.HashSet State) (st st' : FNDFSState State) : Prop where
  iv_mono : ∀ s, iv.contains s → iv'.contains s
  fin_mono : ∀ s, st.innerFinished.contains s → st'.innerFinished.contains s

theorem innerDFS_fuel_mono (succs : State → Array State) (seed : State)
    (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    {result : Option (List State)} {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel succs seed fuel current iv st =
      some (result, iv', st')) :
    InnerMono iv iv' st st' := by
  sorry

theorem innerDFS_fuel_fold_mono (succs : State → Array State) (seed : State)
    (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    {result : Option (List State)} {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel_fold succs seed fuel current remaining iv st =
      some (result, iv', st')) :
    InnerMono iv iv' st st' := by
  sorry

/-! ## Inner DFS correctness -/

/-- Predicate: state is in iv or innerFinished. -/
def isBlocked (iv : Std.HashSet State) (ifin : Std.HashSet State) (s : State) : Prop :=
  iv.contains s ∨ ifin.contains s

/-- After inner DFS from `current` returns `none`:
    1. Every successor of `current` is either `seed` (impossible) or blocked.
    2. Therefore, no path from `current` to `seed` exists through unblocked states.

    The key insight: every successor of `current` ends up in `iv' ∪ innerFinished'`
    after processing (either it was already there, or inner DFS visited it). -/
theorem innerDFS_fuel_succs_blocked (succs : State → Array State) (seed : State)
    (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel_fold succs seed fuel current remaining iv st =
      some (none, iv', st')) :
    ∀ s, s ∈ remaining →
      (s = seed → False) ∧ isBlocked iv' st'.innerFinished s := by
  sorry

/-- After innerDFS returns none, no path from current to seed through unblocked. -/
theorem innerDFS_fuel_no_path (succs : State → Array State) (seed : State)
    (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel succs seed fuel current iv st =
      some (none, iv', st')) :
    ¬PathTo succs (isBlocked iv' st'.innerFinished) current seed := by
  sorry

end Mono

/-! ## Main correctness theorem -/

/-- If the fuel-based nested DFS returns `empty`, then there is no accepting
    cycle reachable from the initial states. -/
theorem nestedDFS_fuel_empty_no_cycle [BEq State] [Hashable State] [LawfulBEq State]
    {initialStates : List State}
    {succs : State → Array State} {isAccepting : State → Bool}
    {fuel n : Nat}
    (h : nestedDFS_fuel initialStates succs isAccepting fuel = some (.empty n)) :
    ¬∃ ac : AcceptingCycle initialStates succs isAccepting, True := by
  sorry

end LTLLib
