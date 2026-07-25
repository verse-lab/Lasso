/-
  Phase 2 (partial): fuel-sufficiency for the nested DFS emptiness check.

  `innerDFS`/`outerDFSLoop` (`NestedDFS.lean`) are marked `partial`. CAVA proves
  termination of the analogous generic DFS framework (`Param_DFS.thy`) from a
  single locale assumption: the set of states reachable from the roots is
  finite (`fb_graph`; finite branching is free there too, since `E x` is
  required finite per-state). The well-founded measure used is

    `param_dfs_variant ≡ inv_image
       (finite_psupset reachable <*lex*> finite_psubset <*lex*> less_than)
       (λs. (dom (discovered s), pending s, length (stack s)))`

  i.e. a *lexicographic* order: (1) the discovered-state set, growing inside
  the fixed finite `reachable` univ: (2) the pending-successor multiset at
  the top stack frame, shrinking; (3) stack length, as a final tie-break.

  We port the finiteness hypothesis as `FiniteReach` below (a finite `univ`
  closed under `succs`, containing `initialStates` — this is exactly what
  `constructGBA`'s or a degeneralized `BA`'s state set gives for free, since
  those are `Std.HashMap`/`Std.HashSet`-backed by construction).

  This file proves the *inner* DFS half of fuel-sufficiency. A key structural
  fact makes this half easy, and is worth recording: `innerDFS_fuel`'s fuel
  argument is *not* a depleting total-work counter. Every sibling call inside
  `innerDFS_fuel_fold` (one per successor of `current`) receives the *same*
  fuel value, not a further-decremented share of it — Lean's `fuel : Nat`
  argument is a plain value, not a resource that is threaded/returned, so
  each sibling call — and each *continuation* after a sub-call resolves —
  gets to reuse the full numeral its caller had. Consequently fuel here plays
  the role of a *maximum recursion depth* cap, reusable across branches, not
  a total-step budget: `univ.size + 1` uniformly suffices for any
  `innerDFS_fuel` call, regardless of how many successors `current` (or any
  state reachable from it) has.

  This reuse phenomenon does *not* carry over to `outerDFSLoop_fuel`: its own
  recursion is a single non-branching chain (no fold over siblings), so fuel
  there really is consumed once per actual step of the whole outer traversal.
  A fuel-sufficiency proof was attempted here and abandoned: combining the
  "launch inner DFS" and "continue the outer traversal" sub-obligations via
  `max` of two independently-obtained existential thresholds hit a genuine
  circularity (the second threshold depends on the post-inner-DFS state,
  which isn't known until a fuel value — the very thing being chosen — is
  fixed). Re-checking CAVA at that point showed it doesn't hit this at all:
  Isabelle's `RECT`/WF-recursion package uses `wf param_dfs_variant` *directly*
  to justify the recursive definition, with no separate fuel parameter ever
  threaded through the code, so there is nothing to "combine" across nested
  calls in the first place. The fuel-based encoding (right tool for Phase
  5b/5c's *correctness*-modulo-termination proofs) is the wrong tool for
  termination itself — using it forces reconstructing, by hand, exactly the
  bookkeeping `termination_by`/`decreasing_by` already provides natively.
  Current plan (not yet done): convert `innerDFS`/`outerDFSLoop`
  (`NestedDFS.lean`) directly to well-founded recursion via `termination_by`,
  using the same `(A, B) := (univ.size - visited.size, pendingSum + stack
  length)` measure, matching `param_dfs_variant` structurally — see
  `NestedDFSPlan.md` for the up-to-date plan.
-/
import LTLLib.NestedDFSCorrectness

namespace LTLLib

section HashSetCard

variable {α : Type u} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]

/-- If every element of `s` is in `t`, `s` is no bigger than `t`. Std's
`HashSet` doesn't expose a `Subset`-implies-`size≤` lemma directly, so we
derive it from the `inter`/`diff` size identities it does provide. -/
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

/-- A strict-subset cardinality bound: if `s ⊆ t` (via `contains`) and some
element of `t` is not in `s`, then `s` is strictly smaller than `t`. -/
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

/-! ## Finite-reachability hypothesis

Lean analogue of CAVA's `fb_graph` locale assumption. Any concrete automaton
built by `constructGBA`/`GBA.degeneralize` satisfies this with `univ :=`
its own (finite, `Std.HashMap`-backed) state set.

No `initialStates` field here — that's only relevant at `nestedDFS`'s own
level (as a separate hypothesis `∀ i ∈ initialStates, univ.contains i`),
not at `innerDFS`/`outerDFSLoop`'s. -/
structure FiniteReach {State : Type u} [BEq State] [Hashable State]
    (succs : State → Array State) where
  univ : Std.HashSet State
  closed : ∀ s, univ.contains s → ∀ t ∈ succs s, univ.contains t

section InnerFuelSufficiency

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]
  (succs : State → Array State) (seed : State) (univ : Std.HashSet State)

/-- Sufficient-fuel measure: how many more univ-members could still be
freshly visited from here. Decreases by exactly 1 each time a fresh state is
inserted into `iv` (or `st.innerFinished`, which is always a superset of the
call's own `iv` by the time it's inserted — see `innerDFS_fuel`'s body). -/
private def innerFuelMeasure (iv : Std.HashSet State) : Nat := univ.size - iv.size

/-- Fold half, proved by induction on `remaining`, taking `innerDFS_fuel`
sufficiency at the *same* fuel level as a hypothesis (`ih_inner`) — the same
fuel/fold double-induction template used throughout `NestedDFSCorrectness.lean`.

The conclusion bundles the closure invariant (`iv₁`/`st₁.innerFinished ⊆
univ`) alongside "returns `some`", since later sibling calls in the fold
need it to keep applying `ih_inner`. -/
private theorem innerDFS_fuel_fold_sufficient_aux
    (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State),
      univ.contains curr → (∀ x, iv₀.contains x → univ.contains x) →
      (∀ x, st₀.innerFinished.contains x → univ.contains x) →
      fuel ≥ innerFuelMeasure univ iv₀ + 1 →
      ∃ result iv₁ st₁, innerDFS_fuel succs seed fuel curr iv₀ st₀ = some (result, iv₁, st₁) ∧
        (∀ x, iv₁.contains x → univ.contains x) ∧
        (∀ x, st₁.innerFinished.contains x → univ.contains x))
    (hcurrent : univ.contains current)
    (hrem : ∀ x ∈ remaining, univ.contains x)
    (hiv : ∀ x, iv.contains x → univ.contains x)
    (hfin : ∀ x, st.innerFinished.contains x → univ.contains x)
    (hfuel : fuel ≥ innerFuelMeasure univ iv + 1) :
    ∃ result iv₁ st₁, innerDFS_fuel_fold succs seed fuel current remaining iv st =
        some (result, iv₁, st₁) ∧
      (∀ x, iv₁.contains x → univ.contains x) ∧
      (∀ x, st₁.innerFinished.contains x → univ.contains x) := by
  induction remaining generalizing iv st with
  | nil =>
    rw [innerDFS_fuel_fold.eq_def]
    refine ⟨none, iv, _, rfl, hiv, fun x hx => ?_⟩
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true] at hx
    rcases hx with hx | hx
    · have hxc : current = x := by simpa using hx
      exact hxc ▸ hcurrent
    · exact hfin x hx
  | cons succ rest ih_rem =>
    rw [innerDFS_fuel_fold.eq_def]
    simp only []
    split
    · exact ⟨some [current], iv, st, rfl, hiv, hfin⟩
    · rename_i hne
      have hsucc : univ.contains succ := hrem succ (List.mem_cons_self ..)
      obtain ⟨result, iv₁, st₁, heq1, hiv1, hfin1⟩ :=
        ih_inner succ iv st hsucc hiv hfin hfuel
      rw [heq1]
      rcases result with _ | cyclePath
      · have hrem' : ∀ x ∈ rest, univ.contains x :=
          fun x hx => hrem x (List.mem_cons_of_mem _ hx)
        have hmono := innerDFS_fuel_mono succs seed fuel succ iv st _ _ _ heq1
        have hsize : iv.size ≤ iv₁.size := HashSet.size_le_of_subset hmono.1
        have hfuel' : fuel ≥ innerFuelMeasure univ iv₁ + 1 := by
          unfold innerFuelMeasure at *
          omega
        exact ih_rem iv₁ st₁ hrem' hiv1 hfin1 hfuel'
      · exact ⟨_, iv₁, st₁, rfl, hiv1, hfin1⟩

/-- Inner DFS never runs out of fuel once `fuel ≥ innerFuelMeasure univ iv
+ 1`, given `current`/`iv`/`st.innerFinished` all stay within a `succs`-closed
finite `univ`. Proved by induction on `fuel`, mirroring
`innerDFS_fuel_mono`'s own structure: the recursive case hands the previous
fuel level's instance of this very theorem to
`innerDFS_fuel_fold_sufficient_aux` as `ih_inner`. -/
theorem innerDFS_fuel_sufficient
    (fuel : Nat) (current : State) (iv : Std.HashSet State) (st : FNDFSState State)
    (hcurrent : univ.contains current)
    (hiv : ∀ x, iv.contains x → univ.contains x)
    (hfin : ∀ x, st.innerFinished.contains x → univ.contains x)
    (hclosed : ∀ s, univ.contains s → ∀ t ∈ succs s, univ.contains t)
    (hfuel : fuel ≥ innerFuelMeasure univ iv + 1) :
    ∃ result iv₁ st₁, innerDFS_fuel succs seed fuel current iv st = some (result, iv₁, st₁) ∧
      (∀ x, iv₁.contains x → univ.contains x) ∧
      (∀ x, st₁.innerFinished.contains x → univ.contains x) := by
  induction fuel generalizing current iv st with
  | zero => unfold innerFuelMeasure at hfuel; omega
  | succ n ih =>
    rw [innerDFS_fuel.eq_def]
    split
    · exact absurd (by assumption) (by omega)
    · rename_i fuel' heq0
      have hfe : fuel' = n := by omega
      rw [hfe]
      split
      · exact ⟨none, iv, st, rfl, hiv, hfin⟩
      · split
        · exact ⟨none, iv, st, rfl, hiv, hfin⟩
        · rename_i hnotfin hnotiv
          have hnotmem : ¬ iv.contains current := by simpa using hnotiv
          have hiv' : ∀ x, (iv.insert current).contains x → univ.contains x := by
            intro x hx
            simp only [Std.HashSet.contains_insert, Bool.or_eq_true] at hx
            rcases hx with hx | hx
            · have hxc : current = x := by simpa using hx
              exact hxc ▸ hcurrent
            · exact hiv x hx
          have hrem : ∀ x ∈ (succs current).toList, univ.contains x := by
            intro x hx
            exact hclosed current hcurrent x (by simpa using hx)
          have hfuel' : n ≥ innerFuelMeasure univ (iv.insert current) + 1 := by
            have hsize : (iv.insert current).size = iv.size + 1 := by
              rw [Std.HashSet.size_insert]
              simp [Std.HashSet.mem_iff_contains, hnotmem]
            unfold innerFuelMeasure at *
            have hivlt : iv.size < univ.size :=
              HashSet.size_lt_of_ssubset hiv hcurrent hnotmem
            omega
          exact innerDFS_fuel_fold_sufficient_aux succs seed univ n current
            (succs current).toList (iv.insert current) st
            (fun curr iv₀ st₀ hc hi hf hfl => ih curr iv₀ st₀ hc hi hf hfl)
            hcurrent hrem hiv' hfin hfuel'

end InnerFuelSufficiency

/-! ## Well-founded `innerDFS` (Phase 2, `innerDFS` half — first genuinely
terminating conversion, 2026-07-25)

Direct well-founded-recursion port, matching CAVA's own architecture: this
converts `innerDFS` to a genuinely terminating function *on its own*,
independent of `outerDFSLoop` — see `ProofPlan.md`'s corrected Phase 2
write-up: CAVA's blue/red DFS are two *independently*-terminating functions,
not one mutually recursive definition, and there's no need to combine a
"how much fuel does the inner call need" bound with an "outer" one.

**Key design choice, found empirically while implementing this (not fully
anticipated by the original plan draft)**: the measure is
`(fr.univ \ iv).size` (`HashSet` set-difference size), *not*
`univ.size - iv.size` (`Nat` subtraction, `InnerFuelSufficiency`'s own
`innerFuelMeasure`). The `\`-based measure is well-defined and usable
regardless of whether `iv` has elements outside `univ` — no `iv ⊆ univ`
invariant ever needs to be *maintained* across the recursion for the measure
itself to make sense. This sidesteps most of what the original plan called
"the hard part."

A *much lighter* Subtype-bundled fact is still genuinely needed, though —
this part of the earlier plan's diagnosis was correct in spirit, just
overstated in scope: within the fold over `current`'s successors, the
"continue with `rest` after having just explored a fresh successor" call
needs to know that exploring that successor didn't *increase* the measure
(weak monotonicity), and that fact can only be obtained from the recursive
call's own return value — no external theorem about a not-yet-defined
function can supply it externally. Hence `innerDFSCore`'s return type. -/

section InnerDFSWellFounded

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-- `sdiff`-based analogue of `HashSet.size_lt_of_ssubset`: inserting a
fresh (not-yet-in-`iv`, but `univ`-member) state into `iv` strictly shrinks
`univ \ iv`. Reuses `HashSet.size_lt_of_ssubset` directly — no fresh
extensionality argument needed (`Std.HashSet` doesn't expose one; this is
exactly why the measure is phrased via `\` and `size_lt_of_ssubset`'s
subset-of-`contains` hypothesis, rather than via reconstructing set
equalities). -/
theorem HashSet.sdiff_insert_lt {univ iv : Std.HashSet State} {x : State}
    (hx_univ : univ.contains x) (hx_niv : iv.contains x = false) :
    (univ \ (iv.insert x)).size < (univ \ iv).size := by
  apply HashSet.size_lt_of_ssubset (s := univ \ (iv.insert x)) (t := univ \ iv) (k := x)
  · intro y hy
    simp only [Std.HashSet.contains_diff, Bool.and_eq_true, Bool.not_eq_true'] at hy ⊢
    obtain ⟨hyu, hyni⟩ := hy
    refine ⟨hyu, ?_⟩
    simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff] at hyni
    exact hyni.2
  · simp [Std.HashSet.contains_diff, hx_univ, hx_niv]
  · simp [Std.HashSet.contains_diff, Std.HashSet.contains_insert]

/-- The well-founded engine. Explores `remaining` (a suffix of `current`'s
own successor list, tracked via `hremaining`), assuming `current` itself is
*already* known-fresh and inserted into `iv` by the caller — this is what
lets `innerDFS` below stay a thin, non-recursive wrapper: the "already
finished"/"already visited" check for `current` happens once, at the top,
not once per fold level.

The returned Subtype bundles exactly the one fact the "continue with `rest`
after a fresh successor's exploration" call needs: `(fr.univ \ ·).size`
(evaluated at the returned `iv`) is no bigger than it was at this call's own
`iv` argument — plain non-strict monotonicity of the measure, nothing about
`iv ⊆ univ` or any other closure property.

`succs`/`fr`/`seed` are written as explicit parameters *on this def itself*
(rather than left to `variable`-section auto-binding) so their argument
position at every recursive call site is unambiguous — `variable`-based
auto-inclusion orders parameters by first syntactic use, which (since
`succs`/`fr` are first mentioned inside `hcurrent`/`hremaining`'s *types*,
and `seed` only appears in the *body*) does not put them where a
straightforwardly-written recursive call would expect them. -/
def innerDFSCore (succs : State → Array State) (fr : FiniteReach succs) (seed : State)
    (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hcurrent : fr.univ.contains current)
    (hremaining : ∀ x ∈ remaining, x ∈ succs current)
    : {p : Option (List State) × Std.HashSet State × FNDFSState State //
        (fr.univ \ p.2.1).size ≤ (fr.univ \ iv).size} :=
  match remaining with
  | [] =>
    ⟨(none, iv, { st with innerFinished := st.innerFinished.insert current }), Nat.le_refl _⟩
  | succ :: rest =>
    if succ == seed then
      ⟨(some [current], iv, st), Nat.le_refl _⟩
    else if hblocked : st.innerFinished.contains succ || iv.contains succ then
      innerDFSCore succs fr seed current rest iv st hcurrent
        (fun x hx => hremaining x (List.mem_cons_of_mem _ hx))
    else
      have hsucc_mem : succ ∈ succs current := hremaining succ (List.mem_cons_self ..)
      have hsucc_univ : fr.univ.contains succ := fr.closed current hcurrent succ hsucc_mem
      have hsucc_niv : iv.contains succ = false := by
        rw [Bool.eq_false_iff]
        simp only [Bool.or_eq_true, not_or] at hblocked
        exact hblocked.2
      let iv' := iv.insert succ
      let r := innerDFSCore succs fr seed succ (succs succ).toList iv' st
        hsucc_univ (fun x hx => Array.mem_toList_iff.mp hx)
      have hlt : (fr.univ \ iv').size ≤ (fr.univ \ iv).size :=
        Nat.le_of_lt (HashSet.sdiff_insert_lt hsucc_univ hsucc_niv)
      match hr : r.1 with
      | (some cyclePath, iv'', st'') =>
        ⟨(some (current :: cyclePath), iv'', st''), by
          have hr2 := r.2; simp only [hr] at hr2
          exact Nat.le_trans hr2 hlt⟩
      | (none, iv'', st'') =>
        let r2 := innerDFSCore succs fr seed current rest iv'' st'' hcurrent
          (fun x hx => hremaining x (List.mem_cons_of_mem _ hx))
        ⟨r2.1, by
          have hr2 := r.2; simp only [hr] at hr2
          exact Nat.le_trans r2.2 (Nat.le_trans hr2 hlt)⟩
termination_by ((fr.univ \ iv).size, remaining.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.left _ _ (HashSet.sdiff_insert_lt hsucc_univ hsucc_niv)
  · have hr2 := r.2; simp only [hr] at hr2
    rcases Nat.lt_or_ge (fr.univ \ iv'').size (fr.univ \ iv).size with h' | h'
    · exact Prod.Lex.left _ _ h'
    · have heq : (fr.univ \ iv'').size = (fr.univ \ iv).size := by omega
      rw [heq]
      exact Prod.Lex.right _ (by simp)

/-- Thin, non-recursive entry point matching the *public* shape of the
original `partial def innerDFS` (`NestedDFS.lean`): the "already
finished"/"already visited" checks for the top-level `current` happen here,
once; `innerDFSCore` handles everything below that, assuming freshness.
Trivially total (a single non-recursive call to the already-total
`innerDFSCore`), so no termination proof of its own is needed. -/
def innerDFSWF (succs : State → Array State) (fr : FiniteReach succs) (seed : State)
    (current : State) (hcurrent : fr.univ.contains current)
    (iv : Std.HashSet State) (st : FNDFSState State)
    : Option (List State) × Std.HashSet State × FNDFSState State :=
  if st.innerFinished.contains current then (none, iv, st)
  else if iv.contains current then (none, iv, st)
  else
    (innerDFSCore succs fr seed current (succs current).toList (iv.insert current) st
      hcurrent (fun _ hx => Array.mem_toList_iff.mp hx)).1

end InnerDFSWellFounded

end LTLLib
