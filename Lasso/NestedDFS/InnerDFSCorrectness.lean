module

/-
  The inner DFS of the nested-DFS emptiness check, fuel-indexed, with its correctness.

  Both nested searches share this half, because the inner DFS never reads acceptance. It only asks whether a seed
  is reachable from itself through states that are not yet `innerFinished`, so the edge-aware outer loop of
  `NestedDFST.lean` reuses it unchanged. Correctness is proved by induction on fuel, and
  `InnerDFSTermination.lean` carries it over to the executable version.

  Defines:
  - `FNDFSState`: the visited and `innerFinished` bookkeeping the search carries
  - `innerDFS_fuel`, `innerDFS_fuel_fold`: the fuel-indexed inner DFS, and its fold over a successor list
  - `isBlocked`: a state visited in the current inner call or already `innerFinished`, "red ∪ pink" in the colour scheme
  - `ReachChain`: an explicit chain of `succs` steps, the form a reported cycle path is handed back in

  Proves:
  - `innerDFS_fuel_mono`: the visited and finished sets only grow
  - `innerDFS_fuel_new_succs_blocked`: on `none`, every successor of a visited state is blocked in the result
  - `innerDFS_no_cycle_from_seed`: on `none`, no path leads back to the seed through unblocked intermediates
  - `innerDFS_new_finished_closed`: the states added to `innerFinished` are closed under `succs`
  - `innerDFS_no_cycle_from_seed_finished`: those two combined, no self-cycle through never-finished intermediates
  - `innerDFS_fuel_cyclePath_chain`: a reported cycle path really is a `succs` chain
  - the `PathTo` closure lemmas the above are assembled from

  References:
  - Courcoubetis, Vardi, Wolper, Yannakakis (CVWY): "Memory-efficient algorithms for the verification of temporal
    properties" (1992) — the original nested DFS algorithm and the post-order argument.
  - Schwoon & Esparza: "A Note on On-The-Fly Verification Algorithms" (TACAS 2005) — the colour-based
    reformulation, white/cyan/blue/red, the proof that inner DFS explores all reachable non-finished states, and
    Lemma 1, no accepting cycle through finished states.
  - Holzmann, Peled, Yannakakis: "On Nested Depth First Search" (SPIN 1996) — the inner-DFS shortcut of stopping
    at any state on the outer DFS's current stack, not just the inner DFS's own seed.
  - Peter Lammich et al.: CAVA Isabelle DFS Framework (AFP) — the `red_dfs_inv` invariant this mirrors.
  - Jaco van de Pol: "Automated Verification of Nested DFS" (FMICS 2015) — the local colour invariants, verified
    in Dafny, that the monotonicity and exploration properties here correspond to.

  Sections:
  - Closure lemmas (includes a second upgrade for when `s ∈ F` is unavoidable)
  - NDFSState (fuel version)
  - Fuel-based inner DFS
  - Predicate: blocked states
  - Inner DFS correctness proofs
-/
public import Lasso.AbstractSpec.GraphPaths
public import Lasso.AbstractSpec.Reachability

public section

namespace Lasso

/-! ## Closure lemmas

Upgrade a restricted no-cycle fact (no path through never-blocked intermediates) into an unrestricted
one (no path at all), given that the blocking set is closed under `succs`, the key step in the
CVWY/Schwoon-Esparza argument that doesn't reduce to plain monotonicity/weakening. -/

/-- If `F` is closed under `succs` and `s ∈ F`, any unrestricted path from `s` stays inside `F`, in particular
its endpoint is in `F`. -/
theorem PathTo.mem_of_closed {State} {succs : State → Array State} {F : State → Prop}
    (hclosed : ∀ s, F s → ∀ t, t ∈ succs s → F t) :
    ∀ {s t : State}, PathTo succs (fun _ => False) s t → F s → F t := by
  intro s t h
  induction h with
  | direct ht => exact fun hFs => hclosed _ hFs _ ht
  | through hmid _ _ ih => exact fun hFs => ih (hclosed _ hFs _ hmid)

/-- An unrestricted path between two states outside a closed set `F` avoids `F` entirely, so it is also a
path restricted to avoid `F`. -/
theorem PathTo.of_unrestricted_avoiding_closed {State} {succs : State → Array State}
    {F : State → Prop} (hclosed : ∀ s, F s → ∀ t, t ∈ succs s → F t)
    {s t : State} (hnotF_t : ¬F t)
    (h : PathTo succs (fun _ => False) s t) (hnotF_s : ¬F s) :
    PathTo succs (fun x => F x) s t := by
  revert hnotF_s hnotF_t
  induction h with
  | direct ht => intro _ _; exact .direct ht
  | @through _ mid _ hmid _ hrest ih =>
    intro hnotF_t hnotF_s
    by_cases hFmid : F mid
    · exact absurd (PathTo.mem_of_closed hclosed hrest hFmid) hnotF_t
    · exact .through hmid hFmid (ih hnotF_t hFmid)

/-- No self-cycle through a closed set's complement, with the set closed and the state outside it, gives no
self-cycle at all. -/
theorem PathTo.no_self_loop_of_closed {State} {succs : State → Array State}
    {F : State → Prop} (hclosed : ∀ s, F s → ∀ t, t ∈ succs s → F t)
    {s : State} (hnotF_s : ¬F s)
    (hno_restricted : ¬PathTo succs (fun x => F x) s s) :
    ¬PathTo succs (fun _ => False) s s :=
  fun h => hno_restricted (PathTo.of_unrestricted_avoiding_closed hclosed hnotF_s h hnotF_s)

/-! ### A second closure upgrade, for when `s ∈ F` is unavoidable

`PathTo.no_self_loop_of_closed` needs `s ∉ F`, but for `F := innerFinished` right after `s`'s own successful
inner-DFS call `s` is always in `F`. It is enough instead that nothing in `F` has an edge back to `s`, a
weaker fact that inner DFS gives for a different reason, its own `succ == seed` check. -/

/-- If nothing in the closed set `F` has an edge to `t`, reaching `t` from an `F`-member is impossible. -/
theorem PathTo.false_of_mem_closed_reaches {State} {succs : State → Array State}
    {F : State → Prop} (hclosed : ∀ s, F s → ∀ t ∈ succs s, F t)
    {t : State} (hno_edge : ∀ x, F x → t ∉ succs x) :
    ∀ {mid : State}, PathTo succs (fun _ => False) mid t → F mid → False := by
  intro mid h
  induction h with
  | @direct mid t ht => exact fun hFmid => hno_edge mid hFmid ht
  | @through mid mid2 t hmid2 _ hrest ih =>
    exact fun hFmid => ih hno_edge (hclosed mid hFmid mid2 hmid2)

/-- With nothing in the closed set `F` having an edge to `t`, every unrestricted path to `t` is `F`-avoiding,
since dipping into `F` traps it there and `t` is then unreachable. -/
theorem PathTo.avoids_closed_of_no_incoming {State} {succs : State → Array State}
    {F : State → Prop} (hclosed : ∀ s, F s → ∀ t ∈ succs s, F t)
    {t : State} (hno_edge : ∀ x, F x → t ∉ succs x) :
    ∀ {s : State}, PathTo succs (fun _ => False) s t → PathTo succs (fun x => F x) s t := by
  intro s h
  induction h with
  | direct ht => exact .direct ht
  | @through s mid t hmid _ hrest ih =>
    by_cases hFmid : F mid
    · exact (PathTo.false_of_mem_closed_reaches hclosed hno_edge hrest hFmid).elim
    · exact .through hmid hFmid (ih hno_edge)

/-- The same with `s` allowed inside the closed set `F`, nothing in `F` having an edge back to `s`. -/
theorem PathTo.no_self_loop_of_closed_no_incoming {State} {succs : State → Array State}
    {F : State → Prop} (hclosed : ∀ s, F s → ∀ t ∈ succs s, F t)
    {s : State} (hno_edge : ∀ x, F x → s ∉ succs x)
    (hno_restricted : ¬PathTo succs (fun x => F x) s s) :
    ¬PathTo succs (fun _ => False) s s :=
  fun h => hno_restricted (PathTo.avoids_closed_of_no_incoming hclosed hno_edge h)

/-- The same for an arbitrary target `t` rather than a self-loop. -/
theorem PathTo.no_reach_of_closed_no_incoming {State} {succs : State → Array State}
    {F : State → Prop} (hclosed : ∀ s, F s → ∀ t ∈ succs s, F t)
    {s t : State} (hno_edge : ∀ x, F x → t ∉ succs x)
    (hno_restricted : ¬PathTo succs (fun x => F x) s t) :
    ¬PathTo succs (fun _ => False) s t :=
  fun h => hno_restricted (PathTo.avoids_closed_of_no_incoming hclosed hno_edge h)

/-- If `F`'s successors stay in `F ∪ S` and nothing reachable from an `F`-member `x` escapes into `S`, then
everything reachable from `x` stays in `F`. -/
theorem PathTo.closed_of_no_escape {State} {succs : State → Array State} {F S : State → Prop}
    (hCL : ∀ x, F x → ∀ y ∈ succs x, F y ∨ S y) :
    ∀ {x v}, PathTo succs (fun _ => False) x v →
      F x → (∀ w, PathTo succs (fun _ => False) x w → ¬S w) → F v := by
  intro x v h
  induction h with
  | @direct x0 v ht =>
    intro hFx hNRx
    rcases hCL x0 hFx _ ht with hF | hS
    · exact hF
    · exact absurd hS (hNRx _ (.direct ht))
  | @through x0 mid v hmid _ hrest ih =>
    intro hFx hNRx
    rcases hCL x0 hFx mid hmid with hF | hS
    · have hNRmid : ∀ w, PathTo succs (fun _ => False) mid w → ¬S w :=
        fun w hw => hNRx w (PathTo.trans (PathTo.direct hmid) hw)
      exact ih hF hNRmid
    · exact absurd hS (hNRx _ (.direct hmid))

/-- If `x` occurs in `l`, dropping elements until the first occurrence of `x`
    leaves a list whose head is `x`. -/
theorem dropWhile_ne_head?_eq_some {State : Type u} [BEq State] [LawfulBEq State]
    (l : List State) (x : State) (hx : x ∈ l) :
    (l.dropWhile (fun y => !(y == x))).head? = some x := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    by_cases hax : a == x
    · have ha : a = x := LawfulBEq.eq_of_beq hax
      simp [ha]
    · have hxt : x ∈ t := by
        rcases List.mem_cons.mp hx with rfl | hx
        · simp at hax
        · exact hx
      have hax' : (fun y => !(y == x)) a = true := by simp [hax]
      simp only [List.dropWhile_cons, hax', ite_true]
      exact ih hxt

/-- A length-1 list's head and last element coincide. -/
theorem head_eq_getLast_of_length_eq_one {α : Type u} (l : List α) (hl : l.length = 1)
    (hne : l ≠ []) : l.head hne = l.getLast hne := by
  cases l with
  | nil => simp at hl
  | cons a t =>
    have ht : t = [] := by simpa using hl
    subst ht
    rfl

/-- `ReachChain succs l` holds when every element of `l` can reach the previous
    element (later elements reach earlier ones). On the outer-DFS stack (top at the
    head), this is the tree-path fact that makes reaching an ancestor via inner DFS
    force a self-cycle. -/
@[expose] def ReachChain {State} (succs : State → Array State) : List State → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => PathTo succs (fun _ => False) b a ∧ ReachChain succs (b :: rest)

/-- Every element in the tail of a `ReachChain` can reach the head. -/
theorem ReachChain.reaches_head {State} {succs : State → Array State} :
    ∀ (hd : State) (tl : List State), ReachChain succs (hd :: tl) →
    ∀ a ∈ tl, PathTo succs (fun _ => False) a hd := by
  intro hd tl h
  induction tl generalizing hd with
  | nil => intro a ha; simp at ha
  | cons b rest ih =>
    intro a ha
    obtain ⟨hba, hrest⟩ := h
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hba
    · exact PathTo.trans (ih b hrest a ha') hba

/-- Dropping the head of a `ReachChain` leaves a `ReachChain`. -/
theorem ReachChain.tail {State} {succs : State → Array State} (hd : State) (tl : List State)
    (h : ReachChain succs (hd :: tl)) : ReachChain succs tl := by
  cases tl with
  | nil => trivial
  | cons b rest => exact h.2

/-! ## NDFSState (fuel version) -/

/-- Mutable state threaded through the nested DFS algorithm. -/
structure FNDFSState (State : Type u) [BEq State] [Hashable State] where
  outerVisited : Std.HashSet State
  innerFinished : Std.HashSet State

/-! ## Fuel-based inner DFS

The inner DFS searches for a path from `current` back to `seed`, or, with the Holzmann-Peled-Yannakakis
shortcut, back to any state on the outer DFS's current stack. `innerVisited` tracks the states this search
has visited, and `innerFinished` those whose own inner DFS already completed without finding a cycle. -/

/-- Result type for inner DFS: `none` = out of fuel. On success, `some (path, target)` records
    both the path found and which state in `{seed} ∪ cyan` was actually hit. -/
abbrev InnerResult (State : Type u) [BEq State] [Hashable State] :=
  Option (Option (List State × State) × Std.HashSet State × FNDFSState State)

mutual
/-- Inner DFS with fuel. Returns `none` if fuel runs out.
    Corresponds to the "red DFS" in Schwoon & Esparza's color formulation. -/
@[expose] def innerDFS_fuel {State} [BEq State] [Hashable State] [LawfulBEq State]
    (succs : State → Array State) (seed : State) (cyan : List State)
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
      innerDFS_fuel_fold succs seed cyan fuel current (succs current).toList innerVisited st

/-- Process successor list for inner DFS. -/
@[expose] def innerDFS_fuel_fold {State} [BEq State] [Hashable State] [LawfulBEq State]
    (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State) (remaining : List State)
    (innerVisited : Std.HashSet State) (st : FNDFSState State)
    : InnerResult State :=
  match remaining with
  | [] =>
    let st := { st with innerFinished := st.innerFinished.insert current }
    some (none, innerVisited, st)
  | succ :: rest =>
    if succ == seed || cyan.contains succ then
      some (some ([current], succ), innerVisited, st)
    else
      match innerDFS_fuel succs seed cyan fuel succ innerVisited st with
      | none => none
      | some (some (cyclePath, target), iv, st') =>
        some (some (current :: cyclePath, target), iv, st')
      | some (none, iv, st') =>
        innerDFS_fuel_fold succs seed cyan fuel current rest iv st'
end

/-! ## Predicate: blocked states -/

section InnerCorrectness

variable {State} [BEq State] [Hashable State] [LawfulBEq State]

/-- `s` is blocked if visited in the current inner DFS call, or already `innerFinished`.
    Corresponds to "red ∪ pink" in Schwoon & Esparza's color scheme. -/
@[expose] def isBlocked (iv : Std.HashSet State) (ifin : Std.HashSet State) (s : State) : Prop :=
  iv.contains s ∨ ifin.contains s

/-! ## Inner DFS correctness proofs

The argument follows Schwoon & Esparza (2005) §3. After `innerDFS_fuel` returns `none`, no cycle found, three
properties hold: `iv` and `innerFinished` only grow, every successor of every visited state is either the seed,
which would have triggered a cycle report, or blocked in the output state, and no processed successor equals the
seed. Together they give no path from `current` back to `seed` through unblocked intermediates, which is the core
of Lemma 1 there. -/

private theorem innerDFS_fuel_fold_mono_aux (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State)
      (result : Option (List State × State)) (iv₁ : Std.HashSet State) (st₁ : FNDFSState State),
      innerDFS_fuel succs seed cyan fuel curr iv₀ st₀ = some (result, iv₁, st₁) →
      (∀ s, iv₀.contains s → iv₁.contains s) ∧
      (∀ s, st₀.innerFinished.contains s → st₁.innerFinished.contains s))
    (result : Option (List State × State)) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (h : innerDFS_fuel_fold succs seed cyan fuel current remaining iv st =
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

/-- Monotonicity of `innerDFS_fuel`: the inner visited set and `innerFinished`
    set only grow across a call that returns `some`. -/
theorem innerDFS_fuel_mono (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (result : Option (List State × State)) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (h : innerDFS_fuel succs seed cyan fuel current iv st = some (result, iv', st')) :
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
      · have ⟨hiv_m, hfin_m⟩ := innerDFS_fuel_fold_mono_aux succs seed cyan n current _ _ st ih _ _ _ h
        exact ⟨fun s hs => hiv_m s (by simp [Std.HashSet.contains_insert, hs, Bool.or_true]),
               hfin_m⟩

/-- Monotonicity of `innerDFS_fuel_fold`, derived from `innerDFS_fuel_mono`. -/
theorem innerDFS_fuel_fold_mono (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (result : Option (List State × State)) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (h : innerDFS_fuel_fold succs seed cyan fuel current remaining iv st =
      some (result, iv', st')) :
    (∀ s, iv.contains s → iv'.contains s) ∧
    (∀ s, st.innerFinished.contains s → st'.innerFinished.contains s) :=
  innerDFS_fuel_fold_mono_aux succs seed cyan fuel current remaining iv st
    (fun curr iv₀ st₀ res iv₁ st₁ h => innerDFS_fuel_mono succs seed cyan fuel curr iv₀ st₀ res iv₁ st₁ h)
    result iv' st' h

/-- After `innerDFS_fuel` returns `some`, `current` ends up in `iv'` or
    `st'.innerFinished`. This is because inner DFS either:
    - finds `current` already in `innerFinished` (returns immediately),
    - finds `current` already in `iv` (returns immediately), or
    - inserts `current` into `iv` and calls the fold (monotonicity preserves it). -/
theorem innerDFS_fuel_current_blocked (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    {result : Option (List State × State)} {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel succs seed cyan fuel current iv st = some (result, iv', st')) :
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
      · have ⟨hiv_m, _⟩ := innerDFS_fuel_fold_mono_aux succs seed cyan n current _ _ st
          (fun curr iv₀ st₀ res iv₁ st₁ h => innerDFS_fuel_mono succs seed cyan n curr iv₀ st₀ res iv₁ st₁ h)
          _ _ _ h
        exact Or.inl (hiv_m current (by simp [Std.HashSet.contains_insert]))

/-- After `innerDFS_fuel_fold` returns `none`, every successor in `remaining` is neither `seed` nor on `cyan`
(Holzmann-Peled-Yannakakis) and is blocked in the output state, invariant R2 of van de Pol (2015). -/
theorem innerDFS_fuel_fold_succs_blocked (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State)
      (result : Option (List State × State)) (iv₁ : Std.HashSet State) (st₁ : FNDFSState State),
      innerDFS_fuel succs seed cyan fuel curr iv₀ st₀ = some (result, iv₁, st₁) →
      (∀ s, iv₀.contains s → iv₁.contains s) ∧
      (∀ s, st₀.innerFinished.contains s → st₁.innerFinished.contains s))
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel_fold succs seed cyan fuel current remaining iv st =
      some (none, iv', st')) :
    ∀ s, s ∈ remaining →
      (s = seed → False) ∧ (s ∈ cyan → False) ∧ isBlocked iv' st'.innerFinished s := by
  induction remaining generalizing iv st with
  | nil =>
    intro s hs; simp at hs
  | cons s₀ rest ih_rem =>
    intro s hs
    rw [innerDFS_fuel_fold.eq_def] at h; simp only at h
    split at h
    · simp at h
    · rename_i hse
      have hs₀_ne_seed : s₀ ≠ seed := by intro heq; subst heq; simp_all
      have hs₀_notin_cyan : s₀ ∉ cyan := by intro hmem; simp_all
      generalize hm : innerDFS_fuel succs seed cyan fuel s₀ iv st = r at h
      match r, h with
      | none, h => simp at h
      | some (some _, iv_mid, st_mid), h =>
        simp at h
      | some (none, iv_mid, st_mid), h =>
        rcases List.mem_cons.mp hs with rfl | hmem
        · have ⟨hiv_fold, hfin_fold⟩ :=
            innerDFS_fuel_fold_mono_aux succs seed cyan fuel current rest iv_mid st_mid ih_inner _ _ _ h
          refine ⟨fun heq_seed => hs₀_ne_seed heq_seed, fun hmem_cyan => hs₀_notin_cyan hmem_cyan, ?_⟩
          have hblk := innerDFS_fuel_current_blocked succs seed cyan fuel s iv st hm
          unfold isBlocked
          rcases hblk with hiv_s | hfin_s
          · exact Or.inl (hiv_fold _ hiv_s)
          · exact Or.inr (hfin_fold _ hfin_s)
        · exact ih_rem iv_mid st_mid h s hmem

/-- Called on a seed not yet in `innerFinished` and returning `none`, inner DFS leaves the seed unable to
reach itself through unblocked intermediates, Lemma 1 of Schwoon & Esparza. -/
theorem innerDFS_no_cycle_from_seed (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (st : FNDFSState State) (cap : Nat)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (hnotfin : st.innerFinished.contains seed = false)
    (h : innerDFS_fuel succs seed cyan (fuel + 1) seed
      (Std.HashSet.emptyWithCapacity cap) st = some (none, iv', st')) :
    ∀ t, (t = seed ∨ t ∈ cyan) →
      ¬PathTo succs (isBlocked iv' st'.innerFinished) seed t := by
  rw [innerDFS_fuel.eq_def] at h
  simp only at h
  split at h
  · simp_all
  · split at h
    · have : (Std.HashSet.emptyWithCapacity cap : Std.HashSet State).contains seed = false :=
        Std.HashSet.contains_emptyWithCapacity
      simp_all
    · have hsb := innerDFS_fuel_fold_succs_blocked succs seed cyan fuel seed _ _ st
        (fun curr iv₀ st₀ res iv₁ st₁ h => innerDFS_fuel_mono succs seed cyan fuel curr iv₀ st₀ res iv₁ st₁ h)
        h
      intro t ht hpath
      cases hpath with
      | direct hedge =>
        have hblk := hsb t (Array.mem_toList_iff.mpr hedge)
        rcases ht with rfl | htcyan
        · exact hblk.1 rfl
        · exact hblk.2.1 htcyan
      | through hmid hunb _ =>
        exact hunb (hsb _ (Array.mem_toList_iff.mpr hmid)).2.2

/-- After fold returns none, all states in iv' that are NOT in iv are in st'.innerFinished. -/
private theorem fold_iv_subset_finished_aux (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State)
      (iv₁ : Std.HashSet State) (st₁ : FNDFSState State),
      innerDFS_fuel succs seed cyan fuel curr iv₀ st₀ = some (none, iv₁, st₁) →
      ∀ s, iv₁.contains s → ¬iv₀.contains s → st₁.innerFinished.contains s)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel_fold succs seed cyan fuel current remaining iv st =
      some (none, iv', st')) :
    ∀ s, iv'.contains s → ¬iv.contains s → st'.innerFinished.contains s := by
  induction remaining generalizing iv st with
  | nil =>
    rw [innerDFS_fuel_fold.eq_def] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    intro s hs hns; exact absurd hs hns
  | cons s₀ rest ih_rem =>
    intro s hs hns
    rw [innerDFS_fuel_fold.eq_def] at h; simp only at h
    split at h
    · simp at h
    · generalize hm : innerDFS_fuel succs seed cyan fuel s₀ iv st = r at h
      match r, h with
      | none, h => simp at h
      | some (some _, _, _), h => simp at h
      | some (none, iv_mid, st_mid), h =>
        by_cases hm_s : iv_mid.contains s
        · have := ih_inner s₀ iv st iv_mid st_mid hm s hm_s hns
          have ⟨_, hfin_mono⟩ := innerDFS_fuel_fold_mono succs seed cyan fuel current rest iv_mid st_mid none iv' st' h
          exact hfin_mono s this
        · exact ih_rem iv_mid st_mid h s hs hm_s

/-- After fold returns none, current is in st'.innerFinished. -/
theorem innerDFS_fuel_fold_adds_current (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel_fold succs seed cyan fuel current remaining iv st =
      some (none, iv', st')) :
    st'.innerFinished.contains current := by
  induction remaining generalizing iv st with
  | nil =>
    rw [innerDFS_fuel_fold.eq_def] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    show ({ outerVisited := st.outerVisited,
            innerFinished := st.innerFinished.insert current } : FNDFSState State).innerFinished.contains current
    simp [Std.HashSet.contains_insert]
  | cons s₀ rest ih_rem =>
    rw [innerDFS_fuel_fold.eq_def] at h; simp only at h
    split at h
    · simp at h
    · generalize hm : innerDFS_fuel succs seed cyan fuel s₀ iv st = r at h
      match r, h with
      | none, h => simp at h
      | some (some _, _, _), h => simp at h
      | some (none, iv_mid, st_mid), h =>
        exact ih_rem iv_mid st_mid h

/-- After innerDFS_fuel returns none with fresh current, all new iv states
    are in st'.innerFinished. -/
theorem innerDFS_fuel_iv_subset_finished (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel succs seed cyan fuel current iv st = some (none, iv', st')) :
    ∀ s, iv'.contains s → ¬iv.contains s → st'.innerFinished.contains s := by
  induction fuel generalizing current iv st iv' st' with
  | zero => simp [innerDFS_fuel.eq_def] at h
  | succ n ih =>
    rw [innerDFS_fuel.eq_def] at h; simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      intro s hs hns; exact absurd hs hns
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        intro s hs hns; exact absurd hs hns
      · intro s hs hns
        by_cases hcur : (iv.insert current).contains s
        · simp [Std.HashSet.contains_insert] at hcur
          rcases hcur with rfl | hiv_s
          · exact innerDFS_fuel_fold_adds_current succs seed cyan n current _ _ st h
          · exact absurd hiv_s hns
        · exact fold_iv_subset_finished_aux succs seed cyan n current _ _ st ih h s hs hcur

/-- After innerDFS from seed with empty iv returns none, seed has no self-cycle
    through st'.innerFinished. This strengthens `innerDFS_no_cycle_from_seed`. -/
theorem innerDFS_no_cycle_from_seed_finished (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (st : FNDFSState State) (cap : Nat)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (hnotfin : st.innerFinished.contains seed = false)
    (h : innerDFS_fuel succs seed cyan (fuel + 1) seed
      (Std.HashSet.emptyWithCapacity cap) st = some (none, iv', st')) :
    ∀ t, (t = seed ∨ t ∈ cyan) →
      ¬PathTo succs (fun x => st'.innerFinished.contains x) seed t := by
  have hno := innerDFS_no_cycle_from_seed succs seed cyan fuel st cap hnotfin h
  have hiv_sub := innerDFS_fuel_iv_subset_finished succs seed cyan (fuel + 1) seed
    (Std.HashSet.emptyWithCapacity cap) st h
  intro t ht hpath
  apply hno t ht
  exact hpath.weaken fun x (hblk : isBlocked iv' st'.innerFinished x) => by
    rcases hblk with hiv | hfin
    · exact hiv_sub x hiv (by simp [Std.HashSet.contains_emptyWithCapacity])
    · exact hfin

/-- After `innerDFS_fuel_fold` returns `none`, every state newly visited during
    the fold (added to `iv` since the call started) has all its successors blocked in the output state. -/
private theorem fold_new_succs_blocked_aux (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State)
      (iv₁ : Std.HashSet State) (st₁ : FNDFSState State),
      innerDFS_fuel succs seed cyan fuel curr iv₀ st₀ = some (none, iv₁, st₁) →
      ∀ s, iv₁.contains s → ¬iv₀.contains s →
        ∀ t ∈ succs s, isBlocked iv₁ st₁.innerFinished t)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel_fold succs seed cyan fuel current remaining iv st =
      some (none, iv', st')) :
    ∀ s, iv'.contains s → ¬iv.contains s →
      ∀ t ∈ succs s, isBlocked iv' st'.innerFinished t := by
  induction remaining generalizing iv st with
  | nil =>
    rw [innerDFS_fuel_fold.eq_def] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    intro s hs hns; exact absurd hs hns
  | cons s₀ rest ih_rem =>
    intro s hs hns t ht
    rw [innerDFS_fuel_fold.eq_def] at h; simp only at h
    split at h
    · simp at h
    · generalize hm : innerDFS_fuel succs seed cyan fuel s₀ iv st = r at h
      match r, h with
      | none, h => simp at h
      | some (some _, _, _), h => simp at h
      | some (none, iv_mid, st_mid), h =>
        by_cases hm_s : iv_mid.contains s
        · have hblk := ih_inner s₀ iv st iv_mid st_mid hm s hm_s hns t ht
          have ⟨hiv_mono, hfin_mono⟩ :=
            innerDFS_fuel_fold_mono succs seed cyan fuel current rest iv_mid st_mid none iv' st' h
          unfold isBlocked at hblk ⊢
          rcases hblk with hiv | hfin
          · exact Or.inl (hiv_mono _ hiv)
          · exact Or.inr (hfin_mono _ hfin)
        · exact ih_rem iv_mid st_mid h s hs hm_s t ht

/-- After `innerDFS_fuel` returns `none`, every state newly visited during the
    call (added to `iv`) has all its successors blocked by the end. -/
theorem innerDFS_fuel_new_succs_blocked (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel succs seed cyan fuel current iv st = some (none, iv', st')) :
    ∀ s, iv'.contains s → ¬iv.contains s →
      ∀ t ∈ succs s, isBlocked iv' st'.innerFinished t := by
  induction fuel generalizing current iv st iv' st' with
  | zero => simp [innerDFS_fuel.eq_def] at h
  | succ n ih =>
    rw [innerDFS_fuel.eq_def] at h; simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      intro s hs hns; exact absurd hs hns
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        intro s hs hns; exact absurd hs hns
      · intro s hs hns t ht
        by_cases hcur : (iv.insert current).contains s
        · simp [Std.HashSet.contains_insert] at hcur
          rcases hcur with rfl | hiv_s
          · have hblk := innerDFS_fuel_fold_succs_blocked succs seed cyan n current
              (succs current).toList (iv.insert current) st
              (fun curr iv₀ st₀ res iv₁ st₁ h' =>
                innerDFS_fuel_mono succs seed cyan n curr iv₀ st₀ res iv₁ st₁ h')
              h
            exact (hblk t (Array.mem_toList_iff.mpr ht)).2.2
          · exact absurd hiv_s hns
        · exact fold_new_succs_blocked_aux succs seed cyan n current _ (iv.insert current) st
            ih h s hs hcur t ht

/-- Converse of `fold_iv_subset_finished_aux`: everything newly `innerFinished` during the
    fold was already in `iv`, the fold only ever inserts its own `current`, which is
    always already in `iv` by the time it does so. -/
private theorem fold_new_finished_subset_iv_aux (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State) (remaining : List State)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State)
      (iv₁ : Std.HashSet State) (st₁ : FNDFSState State),
      innerDFS_fuel succs seed cyan fuel curr iv₀ st₀ = some (none, iv₁, st₁) →
      ∀ s, st₁.innerFinished.contains s → ¬st₀.innerFinished.contains s → iv₁.contains s) :
    ∀ (iv : Std.HashSet State) (st : FNDFSState State), iv.contains current →
    ∀ {iv' : Std.HashSet State} {st' : FNDFSState State},
      innerDFS_fuel_fold succs seed cyan fuel current remaining iv st = some (none, iv', st') →
      ∀ s, st'.innerFinished.contains s → ¬st.innerFinished.contains s → iv'.contains s := by
  induction remaining with
  | nil =>
    intro iv st hcur iv' st' h
    rw [innerDFS_fuel_fold.eq_def] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    intro s hs hns
    simp [Std.HashSet.contains_insert] at hs
    rcases hs with rfl | hs2
    · exact hcur
    · exact absurd hs2 hns
  | cons s₀ rest ih_rem =>
    intro iv st hcur iv' st' h
    rw [innerDFS_fuel_fold.eq_def] at h; simp only at h
    split at h
    · simp at h
    · generalize hm : innerDFS_fuel succs seed cyan fuel s₀ iv st = r at h
      match r, h with
      | none, h => simp at h
      | some (some _, _, _), h => simp at h
      | some (none, iv_mid, st_mid), h =>
        intro s hs hns
        by_cases hfin_mid : st_mid.innerFinished.contains s
        · by_cases hfin_old : st.innerFinished.contains s
          · exact absurd hfin_old hns
          · have hs_iv_mid := ih_inner s₀ iv st iv_mid st_mid hm s hfin_mid hfin_old
            have ⟨hiv_mono, _⟩ :=
              innerDFS_fuel_fold_mono succs seed cyan fuel current rest iv_mid st_mid none iv' st' h
            exact hiv_mono s hs_iv_mid
        · have hcur_mid : iv_mid.contains current :=
            (innerDFS_fuel_mono succs seed cyan fuel s₀ iv st none iv_mid st_mid hm).1 current hcur
          exact ih_rem iv_mid st_mid hcur_mid h s hs hfin_mid

/-- Every state newly finished during an `innerDFS_fuel` call was already in
    `iv` (hence, by monotonicity, is in the final `iv'` too). Converse of
    `innerDFS_fuel_iv_subset_finished`. -/
theorem innerDFS_fuel_new_finished_subset_iv (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel succs seed cyan fuel current iv st = some (none, iv', st')) :
    ∀ s, st'.innerFinished.contains s → ¬st.innerFinished.contains s → iv'.contains s := by
  induction fuel generalizing current iv st iv' st' with
  | zero => simp [innerDFS_fuel.eq_def] at h
  | succ n ih =>
    rw [innerDFS_fuel.eq_def] at h; simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      intro s hs hns; exact absurd hs hns
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        intro s hs hns; exact absurd hs hns
      · exact fold_new_finished_subset_iv_aux succs seed cyan n current _ ih
          (iv.insert current) st (by simp [Std.HashSet.contains_insert]) h

/-- Specialize `innerDFS_fuel_new_succs_blocked` to the actual outer-DFS call
    site (`seed = current`, `iv = ∅`) and combine with the old `innerFinished`
    already being closed to conclude the new `innerFinished` is closed too. -/
theorem innerDFS_new_finished_closed (succs : State → Array State) (current : State) (cyan : List State)
    (fuel : Nat) (st : FNDFSState State) (cap : Nat)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel succs current cyan (fuel + 1) current
      (Std.HashSet.emptyWithCapacity cap) st = some (none, iv', st'))
    (hold_closed : ∀ s, st.innerFinished.contains s →
      ∀ t ∈ succs s, st.innerFinished.contains t) :
    ∀ s, st'.innerFinished.contains s → ∀ t ∈ succs s, st'.innerFinished.contains t := by
  have ⟨_, hfin_mono⟩ := innerDFS_fuel_mono succs current cyan (fuel + 1) current
    (Std.HashSet.emptyWithCapacity cap) st none iv' st' h
  have hnew := innerDFS_fuel_new_succs_blocked succs current cyan (fuel + 1) current
    (Std.HashSet.emptyWithCapacity cap) st h
  have hiv_sub := innerDFS_fuel_iv_subset_finished succs current cyan (fuel + 1) current
    (Std.HashSet.emptyWithCapacity cap) st h
  have hnew_fin_iv := innerDFS_fuel_new_finished_subset_iv succs current cyan (fuel + 1) current
    (Std.HashSet.emptyWithCapacity cap) st h
  intro s hs t ht
  by_cases hold : st.innerFinished.contains s
  · exact hfin_mono t (hold_closed s hold t ht)
  · have hs_iv' : iv'.contains s := hnew_fin_iv s hs hold
    have hs_notin_empty : ¬(Std.HashSet.emptyWithCapacity (α := State) cap).contains s := by
      simp [Std.HashSet.contains_emptyWithCapacity]
    have hblk := hnew s hs_iv' hs_notin_empty t ht
    rcases hblk with hiv_t | hfin_t
    · exact hiv_sub t hiv_t (by simp [Std.HashSet.contains_emptyWithCapacity])
    · exact hfin_t

/-- Inner DFS never touches `outerVisited`, only `innerFinished` is ever updated. -/
private theorem innerDFS_fuel_fold_outerVisited_eq_aux (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State)
      (result : Option (List State × State)) (iv₁ : Std.HashSet State) (st₁ : FNDFSState State),
      innerDFS_fuel succs seed cyan fuel curr iv₀ st₀ = some (result, iv₁, st₁) →
      st₁.outerVisited = st₀.outerVisited)
    (result : Option (List State × State)) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (h : innerDFS_fuel_fold succs seed cyan fuel current remaining iv st =
      some (result, iv', st')) :
    st'.outerVisited = st.outerVisited := by
  induction remaining generalizing iv st result iv' st' with
  | nil =>
    rw [innerDFS_fuel_fold.eq_def] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    rfl
  | cons succ rest ih_rem =>
    rw [innerDFS_fuel_fold.eq_def] at h
    simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      rfl
    · split at h
      · exact absurd h (by simp)
      · rename_i heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        exact ih_inner _ _ _ _ _ _ heq
      · rename_i iv_mid st_mid heq
        rw [ih_rem iv_mid st_mid _ _ _ h, ih_inner _ _ _ _ _ _ heq]

theorem innerDFS_fuel_outerVisited_eq (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (result : Option (List State × State)) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (h : innerDFS_fuel succs seed cyan fuel current iv st = some (result, iv', st')) :
    st'.outerVisited = st.outerVisited := by
  induction fuel generalizing current iv st result iv' st' with
  | zero => simp [innerDFS_fuel.eq_def] at h
  | succ n ih =>
    rw [innerDFS_fuel.eq_def] at h
    simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      rfl
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        rfl
      · exact innerDFS_fuel_fold_outerVisited_eq_aux succs seed cyan n current _ _ st ih _ _ _ h

/-- After `innerDFS_fuel_fold` returns `none`, no state newly visited during the fold has `seed`, or any `cyan`
state (Holzmann-Peled-Yannakakis), as a successor. If it did, the fold's own widened check
`if succ == seed || cyan.contains succ then FOUND` would have fired the moment it was reached,
and the whole call would have returned `some (...)`, not `none`. -/
private theorem fold_new_no_edge_to_seed_aux (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State)
      (iv₁ : Std.HashSet State) (st₁ : FNDFSState State),
      innerDFS_fuel succs seed cyan fuel curr iv₀ st₀ = some (none, iv₁, st₁) →
      ∀ s, iv₁.contains s → ¬iv₀.contains s →
        ∀ t, (t = seed ∨ t ∈ cyan) → t ∉ succs s)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel_fold succs seed cyan fuel current remaining iv st =
      some (none, iv', st')) :
    ∀ s, iv'.contains s → ¬iv.contains s → ∀ t, (t = seed ∨ t ∈ cyan) → t ∉ succs s := by
  induction remaining generalizing iv st with
  | nil =>
    rw [innerDFS_fuel_fold.eq_def] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    intro s hs hns; exact absurd hs hns
  | cons succ' rest ih_rem =>
    intro s hs hns
    rw [innerDFS_fuel_fold.eq_def] at h; simp only at h
    split at h
    · simp at h
    · generalize hm : innerDFS_fuel succs seed cyan fuel succ' iv st = r at h
      match r, h with
      | none, h => simp at h
      | some (some _, _, _), h => simp at h
      | some (none, iv_mid, st_mid), h =>
        by_cases hm_s : iv_mid.contains s
        · exact ih_inner succ' iv st iv_mid st_mid hm s hm_s hns
        · exact ih_rem iv_mid st_mid h s hs hm_s

/-- After `innerDFS_fuel` returns `none`, no state newly visited during the
    call has `seed`, or any `cyan` state, as a successor. -/
theorem innerDFS_fuel_new_no_edge_to_seed (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel succs seed cyan fuel current iv st = some (none, iv', st')) :
    ∀ s, iv'.contains s → ¬iv.contains s → ∀ t, (t = seed ∨ t ∈ cyan) → t ∉ succs s := by
  induction fuel generalizing current iv st iv' st' with
  | zero => simp [innerDFS_fuel.eq_def] at h
  | succ n ih =>
    rw [innerDFS_fuel.eq_def] at h; simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      intro s hs hns; exact absurd hs hns
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        intro s hs hns; exact absurd hs hns
      · intro s hs hns
        by_cases hcur : (iv.insert current).contains s
        · simp [Std.HashSet.contains_insert] at hcur
          rcases hcur with rfl | hiv_s
          · have hblk := innerDFS_fuel_fold_succs_blocked succs seed cyan n current
              (succs current).toList (iv.insert current) st
              (fun curr iv₀ st₀ res iv₁ st₁ h' =>
                innerDFS_fuel_mono succs seed cyan n curr iv₀ st₀ res iv₁ st₁ h')
              h
            intro t ht hmem
            have hblk_t := hblk t (Array.mem_toList_iff.mpr hmem)
            rcases ht with rfl | htcyan
            · exact hblk_t.1 rfl
            · exact hblk_t.2.1 htcyan
          · exact absurd hiv_s hns
        · exact fold_new_no_edge_to_seed_aux succs seed cyan n current _ (iv.insert current) st
            ih h s hs hcur

/-- After `innerDFS_fuel_fold` returns `none`, every state newly visited
    during the fold is reachable from the fold's own `current` (which stays
    fixed across the whole fold, only `remaining` shrinks). -/
private theorem fold_new_reachable_aux (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State)
      (iv₁ : Std.HashSet State) (st₁ : FNDFSState State),
      innerDFS_fuel succs seed cyan fuel curr iv₀ st₀ = some (none, iv₁, st₁) →
      ∀ s, iv₁.contains s → ¬iv₀.contains s → s = curr ∨ PathTo succs (fun _ => False) curr s) :
    ∀ (remaining : List State), (∀ x ∈ remaining, x ∈ succs current) →
    ∀ (iv : Std.HashSet State) (st : FNDFSState State) {iv' : Std.HashSet State}
      {st' : FNDFSState State},
      innerDFS_fuel_fold succs seed cyan fuel current remaining iv st = some (none, iv', st') →
      ∀ s, iv'.contains s → ¬iv.contains s → PathTo succs (fun _ => False) current s := by
  intro remaining
  induction remaining with
  | nil =>
    intro _ iv st iv' st' h s hs hns
    rw [innerDFS_fuel_fold.eq_def] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact absurd hs hns
  | cons succ' rest ih_rem =>
    intro hsub iv st iv' st' h s hs hns
    rw [innerDFS_fuel_fold.eq_def] at h; simp only at h
    split at h
    · simp at h
    · generalize hm : innerDFS_fuel succs seed cyan fuel succ' iv st = r at h
      match r, h with
      | none, h => simp at h
      | some (some _, _, _), h => simp at h
      | some (none, iv_mid, st_mid), h =>
        have hsucc'_edge : succ' ∈ succs current := hsub succ' (List.mem_cons_self ..)
        by_cases hm_s : iv_mid.contains s
        · rcases ih_inner succ' iv st iv_mid st_mid hm s hm_s hns with rfl | hp
          · exact PathTo.direct hsucc'_edge
          · exact PathTo.trans (PathTo.direct hsucc'_edge) hp
        · exact ih_rem (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) iv_mid st_mid h s hs hm_s

/-- After `innerDFS_fuel` returns `none`, every state newly visited during the
    call is reachable from `current`. -/
theorem innerDFS_fuel_new_reachable (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel succs seed cyan fuel current iv st = some (none, iv', st')) :
    ∀ s, iv'.contains s → ¬iv.contains s →
      s = current ∨ PathTo succs (fun _ => False) current s := by
  induction fuel generalizing current iv st iv' st' with
  | zero => simp [innerDFS_fuel.eq_def] at h
  | succ n ih =>
    rw [innerDFS_fuel.eq_def] at h; simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      intro s hs hns; exact absurd hs hns
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        intro s hs hns; exact absurd hs hns
      · intro s hs hns
        by_cases hcur : (iv.insert current).contains s
        · simp [Std.HashSet.contains_insert] at hcur
          rcases hcur with rfl | hiv_s
          · exact Or.inl rfl
          · exact absurd hiv_s hns
        · exact Or.inr (fold_new_reachable_aux succs seed cyan n current ih
            (succs current).toList (fun x hx => Array.mem_toList_iff.mp hx)
            (iv.insert current) st h s hs hcur)

/-- If `innerDFS_fuel_fold` finds a cycle back to `seed`, or (Holzmann-Peled-
    Yannakakis) back to some other `cyan` state, the returned `cyclePath` is a
    genuine `succs`-chain starting at `current` and ending with an edge into
    the state actually hit. -/
theorem fold_cyclePath_chain_aux (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State)
      (cyclePath : List State) (target : State) (iv₁ : Std.HashSet State) (st₁ : FNDFSState State),
      innerDFS_fuel succs seed cyan fuel curr iv₀ st₀ = some (some (cyclePath, target), iv₁, st₁) →
      (target = seed ∨ target ∈ cyan) ∧
      cyclePath.length ≥ 1 ∧
      (∀ (hne : cyclePath ≠ []), cyclePath.head hne = curr) ∧
      (∀ i, (hi : i + 1 < cyclePath.length) → cyclePath[i+1] ∈ succs cyclePath[i]) ∧
      (∀ (hne : cyclePath ≠ []), target ∈ succs (cyclePath.getLast hne)))
    (remaining : List State) (hremaining : ∀ x ∈ remaining, x ∈ succs current)
    (iv : Std.HashSet State) (st : FNDFSState State)
    {cyclePath : List State} {target : State} {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel_fold succs seed cyan fuel current remaining iv st =
      some (some (cyclePath, target), iv', st')) :
    (target = seed ∨ target ∈ cyan) ∧
    cyclePath.length ≥ 1 ∧
    (∀ (hne : cyclePath ≠ []), cyclePath.head hne = current) ∧
    (∀ i, (hi : i + 1 < cyclePath.length) → cyclePath[i+1] ∈ succs cyclePath[i]) ∧
    (∀ (hne : cyclePath ≠ []), target ∈ succs (cyclePath.getLast hne)) := by
  induction remaining generalizing iv st with
  | nil =>
    rw [innerDFS_fuel_fold.eq_def] at h
    simp at h
  | cons succ rest ih_rem =>
    rw [innerDFS_fuel_fold.eq_def] at h
    simp only at h
    have hsucc_edge : succ ∈ succs current := hremaining succ (List.mem_cons_self ..)
    split at h
    · -- succ == seed || cyan.contains succ: cyclePath = [current], target = succ
      rename_i hse
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨heq, heqt⟩, -, -⟩ := h
      subst heq
      subst heqt
      have htarget : succ = seed ∨ succ ∈ cyan := by simpa using hse
      refine ⟨htarget, by simp, fun _ => rfl, fun i hi => by simp at hi, fun _ => ?_⟩
      rw [List.getLast_singleton]
      exact hsucc_edge
    · rcases hres : innerDFS_fuel succs seed cyan fuel succ iv st with _ | ⟨cp, iv_mid, st_mid⟩
      · rw [hres] at h; simp at h
      · rcases cp with _ | ⟨cyclePath0, target0⟩
        · rw [hres] at h
          exact ih_rem (fun x hx => hremaining x (List.mem_cons_of_mem _ hx)) iv_mid st_mid h
        · rw [hres] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨heq2, heqt2⟩, -, -⟩ := h
          obtain ⟨htarget0, hlen0, hhead0, hchain0, hback0⟩ :=
            ih_inner succ iv st cyclePath0 target0 iv_mid st_mid hres
          have hne0 : cyclePath0 ≠ [] := by
            intro hcontra; rw [hcontra] at hlen0; simp at hlen0
          subst heq2
          subst heqt2
          refine ⟨htarget0, by simp, fun _ => rfl, ?_, ?_⟩
          · exact chain_cons current cyclePath0 hne0 hchain0 (hhead0 hne0 ▸ hsucc_edge)
          · intro _
            rw [List.getLast_cons hne0]
            exact hback0 hne0

/-- If `innerDFS_fuel` finds a cycle back to `seed`, or (Holzmann-Peled-
    Yannakakis) back to some other `cyan` state, the returned `cyclePath` is a
    genuine `succs`-chain starting at `current` and ending with an edge into
    the state actually hit (`target`). See `fold_cyclePath_chain_aux` for the
    core argument. -/
theorem innerDFS_fuel_cyclePath_chain (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    {cyclePath : List State} {target : State} {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel succs seed cyan fuel current iv st = some (some (cyclePath, target), iv', st')) :
    (target = seed ∨ target ∈ cyan) ∧
    cyclePath.length ≥ 1 ∧
    (∀ (hne : cyclePath ≠ []), cyclePath.head hne = current) ∧
    (∀ i, (hi : i + 1 < cyclePath.length) → cyclePath[i+1] ∈ succs cyclePath[i]) ∧
    (∀ (hne : cyclePath ≠ []), target ∈ succs (cyclePath.getLast hne)) := by
  induction fuel generalizing current iv st cyclePath target iv' st' with
  | zero => simp [innerDFS_fuel.eq_def] at h
  | succ n ih =>
    rw [innerDFS_fuel.eq_def] at h
    simp only at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · exact fold_cyclePath_chain_aux succs seed cyan n current ih (succs current).toList
          (fun x hx => Array.mem_toList_iff.mp hx) _ st h

end InnerCorrectness

end Lasso
