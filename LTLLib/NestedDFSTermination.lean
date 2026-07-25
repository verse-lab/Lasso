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

-- (The old `InnerFuelSufficiency` section — `innerDFS_fuel_sufficient`,
-- `innerDFS_fuel_fold_sufficient_aux`, keyed on bare `univ`/`hclosed` params
-- — has been superseded by the strengthened `InnerFuelBridge` section below
-- `InnerDFSWellFounded`, which proves the same "returns `some`" fact *and*
-- that the result equals `innerDFSWF`'s, in one pass, using `FiniteReach`
-- directly to match `innerDFSCore`'s own signature.)

/-- Total pending-successor count across every stack frame — the Lean
analogue of CAVA's `pending s` (`Param_DFS.thy`'s `param_dfs_variant`). No
typeclass assumptions needed (generic over `State`), so this lives outside
any `variable`-scoped section entirely rather than needing `omit ... in` on
every lemma. Moved ahead of `InnerDFSWellFounded` (2026-07-25, later still)
because the restructured `innerDFSCore` now needs it for its own termination
measure too — see that section's docstring. -/
def pendingSum {State : Type u} (stack : List (State × List State)) : Nat :=
  (stack.map (fun p => p.2.length)).sum

@[simp] theorem pendingSum_nil {State : Type u} :
    pendingSum ([] : List (State × List State)) = 0 := rfl

@[simp] theorem pendingSum_cons {State : Type u}
    (p : State × List State) (rest : List (State × List State)) :
    pendingSum (p :: rest) = p.2.length + pendingSum rest := rfl

/-! ## Well-founded `innerDFS` (Phase 2, `innerDFS` half)

**Rebuilt 2026-07-25, later still, to align with CAVA's actual architecture.**
The first attempt (kept in git history) converted `innerDFS` directly,
preserving its *original* shape: a fold over `current`'s successors, with a
genuine nested nested Lean recursive call to "descend into a fresh
successor's subtree" before continuing the fold on the remaining siblings.
That forced the "continue the fold" call's termination proof to depend on a
fact about the *previous* (nested) call's actual return value — unrecoverable
without bundling that fact into the return type as a `Subtype`, which in turn
made the function impossible to unfold/rewrite externally later (`.eq_def`
on a `Subtype`-returning well-founded definition whose bundled property is
itself stated in terms of the return value's own projections hits an
unavoidable "motive is not type correct" error — confirmed exhaustively
across every rewrite-family tactic).

Re-reading CAVA's actual sources (`Param_DFS.thy`, `DFS_Find_Path.thy`)
resolved this: CAVA's red (inner) DFS is *not* a separate hand-written
recursive function at all. `Nested_DFS.thy` defines `red_dfs` as literally
`find_path1_restr_spec`, an abstract `SPEC`; its concrete implementation
(`find_path1_restr`, `DFS_Find_Path.thy`) is built from the refinement
framework's generic `FOREACHc` combinator — an explicit-worklist iteration
whose *termination* is a single generic fact ("the iteration set shrinks by
one element per step"), entirely independent of whatever the loop body
computes. Concretely: **both CAVA's blue and red DFS reduce to the same
generic `param_DFS`/`it_dfs` engine** (`Param_DFS.thy`) — one flat
explicit-stack `WHILE` loop over a single state record, never nested
recursive-descent-with-fold. There is no CAVA analogue of "prove a fact
about a sibling call's return value to justify continuing a fold", because
there are no nested calls in the first place — only single-step transitions
on an explicit stack, exactly like `outerDFSLoopWF` below (which *was*
already built this way from `NestedDFS.lean`'s original design, which is
*why* its own conversion needed no `Subtype` at all).

`innerDFSCore` is rebuilt here the same way: an explicit stack of
`(state, remaining successors)` frames plus a `pathStack` (mirroring
`outerDFSLoopWF`'s own `pathStack` bookkeeping, used to reconstruct the
witness path on success), structurally identical in shape to
`outerDFSLoopWF` and reusing the exact same measure/`decreasing_by` idioms
(already proven to work there, 0 sorry). No `Subtype`-bundled return type is
needed any more: every recursive call's termination is justified purely from
*local, syntactic* facts about that call's own arguments (either `iv`
strictly shrinks `fr.univ \ iv`, or `pendingSum stack + stack.length`
strictly decreases), never from a fact about a previous call's result. -/

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

/-- The well-founded engine, now an **explicit-stack single flat loop**,
structurally identical to `outerDFSLoopWF` below: `stack` holds
`(state, remaining successors)` frames (deepest/active frame at the head),
`pathStack` mirrors `outerDFSLoopWF`'s own bookkeeping (`++ [x]` on push,
`.dropLast` on pop) and — since it always holds exactly the states of the
frames currently on `stack`, from outermost to innermost — doubles as the
witness path the moment a successor equal to `seed` is found: at that point
`pathStack` already ends in the active frame's own state, so no separate
"unwind and prepend" step (the old fold-based version's `current ::
cyclePath` wrapping) is needed at all.

`succs`/`fr`/`seed` stay explicit parameters on the def itself (not
`variable`-bound) for the same reason as before: unambiguous argument
position at every recursive call site.

**No proof-carrying arguments** (revised again, same day, after the first
plain-return version still proved fragile to `rw`/`induction ... using
.induct`-based external reasoning about calls with dependent `hstack_states
: ∀ p ∈ stack, …`/`hstack_remaining` hypotheses in their argument list —
`rw [innerDFSCore.eq_def]` intermittently failed to fire depending on how
those proof terms were phrased at the call site, and `exact`-based defeq
never bridges well-founded recursive calls at all, so *any* dependent
argument threading here becomes a recurring tax on every future lemma).
The membership facts (`current`/`succ ∈ fr.univ`) are only ever needed
*locally*, to justify the `decreasing_by` measure — they were never needed
for the function's own *value* computation. So instead of threading them as
hypotheses, they're re-checked with a plain runtime `if fr.univ.contains …`
and a defensive fallback (treat as blocked) on failure — a standard "junk
value on out-of-domain input" pattern. For any call reachable from
`innerDFSWF` (whose own `current` is `fr.univ`-closed under `succs` via
`fr.closed`), the fallback branch is dead code; it exists purely so the
*type* of `innerDFSCore` carries no proof obligations at all, making every
later equation/induction-based proof about it an ordinary (non-dependent)
one. -/
def innerDFSCore [LawfulBEq State] (succs : State → Array State) (fr : FiniteReach succs)
    (seed : State)
    (stack : List (State × List State))
    (pathStack : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    : Option (List State) × Std.HashSet State × FNDFSState State :=
  match stack with
  | [] => (none, iv, st)
  | (current, remaining) :: rest =>
    match remaining with
    | [] =>
      innerDFSCore succs fr seed rest pathStack.dropLast iv
        { st with innerFinished := st.innerFinished.insert current }
    | succ :: remainingTail =>
      let stack' := (current, remainingTail) :: rest
      if succ == seed then
        (some pathStack, iv, st)
      else if hblocked : st.innerFinished.contains succ || iv.contains succ then
        innerDFSCore succs fr seed stack' pathStack iv st
      else if hsucc_univ : fr.univ.contains succ then
        have hsucc_niv : iv.contains succ = false := by
          rw [Bool.eq_false_iff]
          simp only [Bool.or_eq_true, not_or] at hblocked
          exact hblocked.2
        let iv' := iv.insert succ
        let succChildren := (succs succ).toList
        let stack2 := (succ, succChildren) :: stack'
        innerDFSCore succs fr seed stack2 (pathStack ++ [succ]) iv' st
      else
        innerDFSCore succs fr seed stack' pathStack iv st
termination_by ((fr.univ \ iv).size, pendingSum stack + stack.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.left _ _ (HashSet.sdiff_insert_lt hsucc_univ hsucc_niv)
  · exact Prod.Lex.right _ (by simp)

/-- Thin, non-recursive entry point matching the *public* shape of the
original `partial def innerDFS` (`NestedDFS.lean`): the "already
finished"/"already visited" checks for the top-level `current` happen here,
once; `innerDFSCore` handles everything below that, assuming freshness, seeded
with the singleton stack `[(current, succs current)]` and `pathStack :=
[current]` — mirroring `nestedDFS`'s own top-level `pathStack := [init]`
initialization for the outer loop. Trivially total (a single non-recursive
call to the already-total `innerDFSCore`), so no termination proof of its own
is needed. -/
def innerDFSWF (succs : State → Array State) (fr : FiniteReach succs) (seed : State)
    (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    : Option (List State) × Std.HashSet State × FNDFSState State :=
  if st.innerFinished.contains current then (none, iv, st)
  else if iv.contains current then (none, iv, st)
  else
    innerDFSCore succs fr seed [(current, (succs current).toList)] [current]
      (iv.insert current) st

/-- `innerDFSWF`'s "already blocked" case, as a reusable equation — needed by
the fuel bridge (`InnerFuelBridge`, below `OuterDFSWellFounded`) to align
`innerDFS_fuel`'s uniform "always call the top-level function" style with
`innerDFSCore`'s own explicit `hblocked` branch. -/
theorem innerDFSWF_blocked (succs : State → Array State) (fr : FiniteReach succs) (seed : State)
    (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hblocked : st.innerFinished.contains current || iv.contains current) :
    innerDFSWF succs fr seed current iv st = (none, iv, st) := by
  unfold innerDFSWF
  rcases Bool.or_eq_true_iff.mp hblocked with h | h
  · simp [h]
  · by_cases h1 : st.innerFinished.contains current
    · simp [h1]
    · simp [h1, h]

/-- `innerDFSWF`'s "fresh" case, as a reusable equation. -/
theorem innerDFSWF_fresh (succs : State → Array State) (fr : FiniteReach succs) (seed : State)
    (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hnotfin : st.innerFinished.contains current = false)
    (hnotvisited : iv.contains current = false) :
    innerDFSWF succs fr seed current iv st =
      innerDFSCore succs fr seed [(current, (succs current).toList)] [current]
        (iv.insert current) st := by
  unfold innerDFSWF
  simp [hnotfin, hnotvisited]

/-- `innerDFSCore` never touches `outerVisited` (only `innerFinished`) —
needed by `outerDFSLoop`'s well-founded conversion below, whose measure is
defined purely from `outerVisited`/the outer stack. Unlike the old
fold-based `innerDFSCore` (where the auto-derived `.induct` failed to
generate for a `Subtype`-returning definition), this is now a completely
ordinary well-founded recursive function, so `innerDFSCore.induct` generates
normally and this is a plain structural induction — no bundling into the
return type needed. -/
theorem innerDFSCore_outerVisited_pres (succs : State → Array State) (fr : FiniteReach succs)
    (seed : State)
    (stack : List (State × List State)) (pathStack : List State)
    (iv : Std.HashSet State) (st : FNDFSState State) :
    (innerDFSCore succs fr seed stack pathStack iv st).2.2.outerVisited = st.outerVisited := by
  induction stack, pathStack, iv, st using innerDFSCore.induct (succs := succs) (fr := fr) (seed := seed)
  all_goals (unfold innerDFSCore; dsimp only; try simp_all; try (rename_i ih; simpa using ih))

end InnerDFSWellFounded

/-! ## Fuel ↔ well-founded bridge, inner half (Phase 2, 2026-07-25)

Mirrors CAVA's own `it_dfsT_eq_it_dfs`/`WHILET_eq_WHILE_tproof`: rather than
re-proving `NestedDFSCorrectness.lean`'s ~2000 sorry-free lines of `innerDFS_fuel`
correctness against the new well-founded `innerDFSCore`/`innerDFSWF`, prove a
single equation showing the two agree (for sufficient fuel), then transport
every existing fuel-based theorem across it for free.

Strengthens the old `innerDFS_fuel_sufficient`/`innerDFS_fuel_fold_sufficient_aux`
(same double-induction template, same fuel/fold shape) to conclude the
fuel-indexed and well-founded results are *equal*, not just that the
fuel-indexed one "succeeds" — the old conclusion is a trivial corollary of
the new one, so nothing is lost by only keeping this version. -/

section InnerFuelBridge

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]
  (succs : State → Array State) (fr : FiniteReach succs) (seed : State)

/-- Sufficient-fuel measure — same role as `innerDFSCore`'s own well-founded
measure (`(fr.univ \ iv).size`), phrased via `Nat` subtraction because this
section's proofs need to match `innerDFS_fuel`'s pre-existing `iv ⊆ univ`
hypotheses; the two measures agree whenever `iv ⊆ univ`, which is this
section's standing assumption throughout. -/
private def innerFuelMeasure (succs : State → Array State) (fr : FiniteReach succs)
    (iv : Std.HashSet State) : Nat := fr.univ.size - iv.size

-- TODO (2026-07-25, later still): the fold-level bridge needs a full
-- redesign now that `innerDFSCore` is stack-based instead of fold-based —
-- see `ProofPlan.md`'s Phase 2 write-up for the design (generalize over an
-- arbitrary stack tail, induct on `innerDFSCore.induct` directly rather than
-- on `remaining`, relating `innerDFS_fuel_fold`'s recursive-descent order to
-- the explicit stack's push/pop order one frame at a time). Not yet
-- rewritten; `innerDFS_fuel_eq_innerDFSWF` below is `sorry` pending this.

/-- Top-level bridge: for sufficient fuel, `innerDFS_fuel` equals
`innerDFSWF`. -/
theorem innerDFS_fuel_eq_innerDFSWF
    (fuel : Nat) (current : State) (iv : Std.HashSet State) (st : FNDFSState State)
    (hcurrent : fr.univ.contains current)
    (hiv : ∀ x, iv.contains x → fr.univ.contains x)
    (hfin : ∀ x, st.innerFinished.contains x → fr.univ.contains x)
    (hfuel : fuel ≥ innerFuelMeasure succs fr iv + 1) :
    ∃ result iv₁ st₁, innerDFS_fuel succs seed fuel current iv st = some (result, iv₁, st₁) ∧
      (∀ x, iv₁.contains x → fr.univ.contains x) ∧
      (∀ x, st₁.innerFinished.contains x → fr.univ.contains x) ∧
      (result, iv₁, st₁) = innerDFSWF succs fr seed current iv st := by
  sorry

end InnerFuelBridge

/-! ## Well-founded `outerDFSLoop` (Phase 2, `outerDFSLoop` half, 2026-07-25)

The second, independent conversion — CAVA's own blue DFS, matching
`param_dfs_variant`'s `(discovered, pending, stack-length)` triple about as
directly as `outerDFSLoop`'s explicit-stack representation allows: primary
component `(fr.univ \ st.outerVisited).size` (`discovered` growth, same
`sdiff`-based measure and reasoning as `innerDFSCore`'s own `iv`), secondary
`pendingSum stack + stack.length` (CAVA's `pending`+stack-length tie-break,
combined into one `Nat` since both only ever need to *weakly* decrease
together as one unit here — see the "skip already-visited successor" branch
below, which decreases `pendingSum` by exactly 1 while leaving `stack.length`
untouched).

Confirms the corrected Phase 2 plan's step-2 prediction: **no Subtype-bundled
return type is needed here**, unlike `innerDFSCore`. `outerDFSLoop` has no
fold over siblings (a single self-call per branch, never two in sequence
within one equation), and the one place it calls into the *other* well-
founded function (`innerDFSCore`, at the accepting-leaf branch) only needs
the `outerVisited`-preservation fact already bundled into *that* function's
own return type (see `innerDFSCore`'s docstring) — no new induction
principle, no circularity. This is the Lean-native mirror of CAVA gluing
blue/red DFS via ordinary composition rather than a joint measure. -/

section OuterDFSWellFounded

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-- Well-founded `outerDFSLoop`. Takes `fr : FiniteReach succs` plus two
threaded closure hypotheses (mirroring `NestedDFSCorrectness.lean`'s
`OuterReachClosed.stack_remaining_subset`-style bookkeeping, needed here
purely for termination rather than full correctness): every stack state is
a `fr.univ` member, and every frame's `remaining` list only contains genuine
successors of that frame's own state. Both are re-derived structurally at
each call site (never needing a fact about a *previous* call's result — the
key structural difference from `innerDFSCore`), so — as anticipated — no
Subtype-bundled return type is needed. -/
def outerDFSLoopWF (succs : State → Array State) (isAccepting : State → Bool)
    (fr : FiniteReach succs)
    (stack : List (State × List State))
    (pathStack : List State)
    (st : FNDFSState State)
    (hstack_states : ∀ p ∈ stack, fr.univ.contains p.1)
    (hstack_remaining : ∀ p ∈ stack, ∀ x ∈ p.2, x ∈ succs p.1)
    : EmptinessResult State × FNDFSState State :=
  match stack with
  | [] => (.empty st.outerVisited.size, st)
  | (current, remaining) :: rest =>
    have hcurrent_univ : fr.univ.contains current :=
      hstack_states (current, remaining) (List.mem_cons_self ..)
    have hcurrent_remaining : ∀ x ∈ remaining, x ∈ succs current :=
      hstack_remaining (current, remaining) (List.mem_cons_self ..)
    have hrest_states : ∀ p ∈ rest, fr.univ.contains p.1 :=
      fun p hp => hstack_states p (List.mem_cons_of_mem _ hp)
    have hrest_remaining : ∀ p ∈ rest, ∀ x ∈ p.2, x ∈ succs p.1 :=
      fun p hp => hstack_remaining p (List.mem_cons_of_mem _ hp)
    match remaining with
    | [] =>
      if hacc : isAccepting current then
        let innerVisited := Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)
        match hr : innerDFSCore succs fr current [(current, (succs current).toList)] [current]
            innerVisited st with
        | (some cyclePath, _, st') =>
          (.nonEmpty pathStack cyclePath, st')
        | (none, _, st') =>
          have hst'_eq : st'.outerVisited = st.outerVisited := by
            have hr2 := innerDFSCore_outerVisited_pres succs fr current
              [(current, (succs current).toList)] [current] innerVisited st
            rw [hr] at hr2
            exact hr2
          outerDFSLoopWF succs isAccepting fr rest pathStack.dropLast st'
            hrest_states hrest_remaining
      else
        outerDFSLoopWF succs isAccepting fr rest pathStack.dropLast st
          hrest_states hrest_remaining
    | succ :: remainingTail =>
      have hsucc_mem : succ ∈ succs current :=
        hcurrent_remaining succ (List.mem_cons_self ..)
      have hremainingTail : ∀ x ∈ remainingTail, x ∈ succs current :=
        fun x hx => hcurrent_remaining x (List.mem_cons_of_mem _ hx)
      let stack' := (current, remainingTail) :: rest
      have hstack'_states : ∀ p ∈ stack', fr.univ.contains p.1 := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact hcurrent_univ
        · exact hrest_states p hp'
      have hstack'_remaining : ∀ p ∈ stack', ∀ x ∈ p.2, x ∈ succs p.1 := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact hremainingTail
        · exact hrest_remaining p hp'
      if hvis : st.outerVisited.contains succ then
        outerDFSLoopWF succs isAccepting fr stack' pathStack st
          hstack'_states hstack'_remaining
      else
        have hsucc_univ : fr.univ.contains succ := fr.closed current hcurrent_univ succ hsucc_mem
        have hsucc_niv : st.outerVisited.contains succ = false := by
          simpa using hvis
        let st2 := { st with outerVisited := st.outerVisited.insert succ }
        let succChildren := (succs succ).toList
        let stack2 := (succ, succChildren) :: stack'
        have hstack2_states : ∀ p ∈ stack2, fr.univ.contains p.1 := by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact hsucc_univ
          · exact hstack'_states p hp'
        have hstack2_remaining : ∀ p ∈ stack2, ∀ x ∈ p.2, x ∈ succs p.1 := by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact fun x hx => Array.mem_toList_iff.mp hx
          · exact hstack'_remaining p hp'
        outerDFSLoopWF succs isAccepting fr stack2 (pathStack ++ [succ]) st2
          hstack2_states hstack2_remaining
termination_by ((fr.univ \ st.outerVisited).size, pendingSum stack + stack.length)
decreasing_by
  · rw [hst'_eq]
    exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.left _ _ (HashSet.sdiff_insert_lt hsucc_univ hsucc_niv)

end OuterDFSWellFounded

end LTLLib
