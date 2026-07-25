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

/-- Chains `innerDFS_fuel_fold` calls across an explicit stack of pending
frames — the fuel-side companion to `innerDFSCore`'s own `stack` argument.
`innerDFS_fuel`/`innerDFS_fuel_fold` encode "descend into a fresh successor"
via a genuine *nested Lean call* (their own call stack *is* the frame
stack); this makes that implicit stack explicit, so it can be related to
`innerDFSCore`'s. Plain structural recursion on `stack` — no termination
proof needed at all (unlike `innerDFSCore`, this never needs to *push* a
longer stack; "descending" is still handled entirely by the nested
`innerDFS_fuel`/`innerDFS_fuel_fold` call inside `hd`'s own fold, exactly as
before — only "this frame finished, move to the next one" is new here).

`pathStack` bookkeeping mirrors `innerDFSCore`'s exactly, and is needed for
the same reason: `innerDFS_fuel_fold current remaining iv st`'s own "found"
result is always of the form `some (current :: suffix)` (built by its own
pre-existing `current :: cyclePath` wrapping around nested calls) —
*relative* to `current`'s own frame, not the full witness path. Replacing
the leading `current` with the full `pathStack` (which — by the same
invariant `innerDFSCore` maintains — already ends in `current`) recovers
the absolute path: `pathStack ++ suffix`. Verified algebraically for both
the "descend into a fresh successor" and "backtrack to the parent frame"
transitions before implementing (see `ProofPlan.md`'s Phase 2 write-up) —
this is *not* simply "propagate the cycle unchanged", which is wrong by
exactly one `current ::`/`succ ::` layer at every frame boundary. -/
def innerDFS_fuel_chain [BEq State] [Hashable State] [LawfulBEq State]
    (succs : State → Array State) (seed : State) (fuel : Nat)
    (stack : List (State × List State)) (pathStack : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    : InnerResult State :=
  match stack with
  | [] => some (none, iv, st)
  | (current, remaining) :: rest =>
    match innerDFS_fuel_fold succs seed fuel current remaining iv st with
    | none => none
    | some (some cyc, iv', st') => some (some (pathStack ++ cyc.tail), iv', st')
    | some (none, iv', st') => innerDFS_fuel_chain succs seed fuel rest pathStack.dropLast iv' st'

/-- One-step unfolding lemmas for `innerDFS_fuel`/`innerDFS_fuel_fold`/
`innerDFS_fuel_chain` — all ordinary structural/fuel recursion (no
proof-carrying arguments), so these go through by plain `rfl`/`unfold` +
`simp`, unlike the old fold-shaped `innerDFSCore`'s equation lemmas. Kept as
small reusable rewrite facts rather than inlining `unfold`/`simp [name]` at
every call site in the main bridge proof below, both for readability and to
avoid simp's "possibly looping" concern on self-referential equations (each
of these exposes exactly *one* layer, never simp-normalizing recursively). -/
theorem innerDFS_fuel_fold_nil (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State) :
    innerDFS_fuel_fold succs seed fuel current [] iv st =
      some (none, iv, { st with innerFinished := st.innerFinished.insert current }) := by
  unfold innerDFS_fuel_fold
  rfl

theorem innerDFS_fuel_fold_seed (fuel : Nat) (current succ : State) (rest : List State)
    (iv : Std.HashSet State) (st : FNDFSState State) (hse : succ == seed) :
    innerDFS_fuel_fold succs seed fuel current (succ :: rest) iv st =
      some (some [current], iv, st) := by
  unfold innerDFS_fuel_fold
  simp only [hse, if_true]

theorem innerDFS_fuel_fold_cons (fuel : Nat) (current succ : State) (rest : List State)
    (iv : Std.HashSet State) (st : FNDFSState State) (hse : ¬ succ == seed) :
    innerDFS_fuel_fold succs seed fuel current (succ :: rest) iv st =
      match innerDFS_fuel succs seed fuel succ iv st with
      | none => none
      | some (some cyc, iv', st') => some (some (current :: cyc), iv', st')
      | some (none, iv', st') => innerDFS_fuel_fold succs seed fuel current rest iv' st' := by
  conv => lhs; rw [innerDFS_fuel_fold.eq_def]
  simp only [hse, Bool.false_eq_true, if_false]
  rfl

theorem innerDFS_fuel_blocked (fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hblocked : st.innerFinished.contains current || iv.contains current) :
    innerDFS_fuel succs seed (fuel + 1) current iv st = some (none, iv, st) := by
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
    innerDFS_fuel succs seed (fuel + 1) current iv st =
      innerDFS_fuel_fold succs seed fuel current (succs current).toList (iv.insert current) st := by
  unfold innerDFS_fuel
  simp [hnotfin, hnotvisited]

theorem innerDFS_fuel_chain_cons (fuel : Nat) (current : State) (remaining : List State)
    (rest : List (State × List State)) (pathStack : List State)
    (iv : Std.HashSet State) (st : FNDFSState State) :
    innerDFS_fuel_chain succs seed fuel ((current, remaining) :: rest) pathStack iv st =
      match innerDFS_fuel_fold succs seed fuel current remaining iv st with
      | none => none
      | some (some cyc, iv', st') => some (some (pathStack ++ cyc.tail), iv', st')
      | some (none, iv', st') =>
          innerDFS_fuel_chain succs seed fuel rest pathStack.dropLast iv' st' := rfl

/-- Fuel-increase preserves a successful result: more fuel than strictly
needed can't change what `innerDFS_fuel_fold` computes. Needed because
`innerDFS_fuel_chain` reuses one *uniform* fuel value across every stack
frame — matching how the bridge theorem's own induction keeps `fuel` fixed
throughout — whereas the *original* nested-call semantics genuinely
decrements fuel by one on every "descend into a fresh successor" (via
`innerDFS_fuel_fresh`). This lemma is what reconciles the two: the uniform
(more generous) fuel `innerDFS_fuel_chain` hands to a pushed frame's fold
call computes the *same* result as the slightly smaller amount the
original nested call would actually have used, provided the smaller amount
was already enough. Proved by the same fuel/fold mutual-induction template
used throughout this file (cf. `innerDFS_fuel_mono` in
`NestedDFSCorrectness.lean`). -/
private theorem innerDFS_fuel_fold_add_aux (succs : State → Array State) (seed : State)
    (extra fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State)
      (result : Option (List State)) (iv₁ : Std.HashSet State) (st₁ : FNDFSState State),
      innerDFS_fuel succs seed fuel curr iv₀ st₀ = some (result, iv₁, st₁) →
      innerDFS_fuel succs seed (fuel + extra) curr iv₀ st₀ = some (result, iv₁, st₁))
    (result : Option (List State)) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (h : innerDFS_fuel_fold succs seed fuel current remaining iv st =
      some (result, iv', st')) :
    innerDFS_fuel_fold succs seed (fuel + extra) current remaining iv st =
      some (result, iv', st') := by
  induction remaining generalizing iv st result iv' st' with
  | nil =>
    rw [innerDFS_fuel_fold.eq_def] at h ⊢
    exact h
  | cons succ rest ih_rem =>
    by_cases hse : succ == seed
    · rw [innerDFS_fuel_fold_seed succs seed fuel current succ rest iv st hse] at h
      rw [innerDFS_fuel_fold_seed succs seed (fuel + extra) current succ rest iv st hse]
      exact h
    · rw [innerDFS_fuel_fold_cons succs seed fuel current succ rest iv st hse] at h
      rw [innerDFS_fuel_fold_cons succs seed (fuel + extra) current succ rest iv st hse]
      cases hinner : innerDFS_fuel succs seed fuel succ iv st with
      | none => rw [hinner] at h; exact absurd h (by simp)
      | some val =>
        rw [hinner] at h
        rw [ih_inner _ _ _ _ _ _ hinner]
        obtain ⟨cyc, iv_mid, st_mid⟩ := val
        cases cyc with
        | some cyclePath => exact h
        | none => exact ih_rem iv_mid st_mid result iv' st' h

/-- Fuel-increase preserves a successful result, for `innerDFS_fuel` itself.
Proved by induction on `fuel`, using `innerDFS_fuel_fold_add_aux` for the
mutual recursion — the same shape as `innerDFS_fuel_mono`'s own proof. -/
theorem innerDFS_fuel_add_preserves (succs : State → Array State) (seed : State)
    (extra fuel : Nat) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (result : Option (List State)) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (h : innerDFS_fuel succs seed fuel current iv st = some (result, iv', st')) :
    innerDFS_fuel succs seed (fuel + extra) current iv st = some (result, iv', st') := by
  induction fuel generalizing current iv st result iv' st' with
  | zero => simp [innerDFS_fuel.eq_def] at h
  | succ n ih =>
    rw [show n + 1 + extra = (n + extra) + 1 by omega]
    by_cases hblocked : st.innerFinished.contains current || iv.contains current
    · rw [innerDFS_fuel_blocked succs seed n current iv st hblocked] at h
      rw [innerDFS_fuel_blocked succs seed (n + extra) current iv st hblocked]
      exact h
    · have hblocked' : (st.innerFinished.contains current || iv.contains current) = false := by
        rw [Bool.eq_false_iff]; exact hblocked
      have hnotfin : st.innerFinished.contains current = false := by
        simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.1
      have hnotvisited : iv.contains current = false := by
        simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.2
      rw [innerDFS_fuel_fresh succs seed n current iv st hnotfin hnotvisited] at h
      rw [innerDFS_fuel_fresh succs seed (n + extra) current iv st hnotfin hnotvisited]
      exact innerDFS_fuel_fold_add_aux succs seed extra n current _ _ st ih result iv' st' h

theorem innerDFS_fuel_fold_add_preserves (succs : State → Array State) (seed : State)
    (extra fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (result : Option (List State)) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (h : innerDFS_fuel_fold succs seed fuel current remaining iv st =
      some (result, iv', st')) :
    innerDFS_fuel_fold succs seed (fuel + extra) current remaining iv st =
      some (result, iv', st') :=
  innerDFS_fuel_fold_add_aux succs seed extra fuel current remaining iv st
    (fun curr iv₀ st₀ res iv₁ st₁ h =>
      innerDFS_fuel_add_preserves succs seed extra fuel curr iv₀ st₀ res iv₁ st₁ h)
    result iv' st' h

/-- Sufficient fuel guarantees success — the existence counterpart to
`innerDFS_fuel_add_preserves`'s "more fuel can't hurt". Needed for the
"fresh push" case of the main bridge below: relating a *uniform* fuel value
(what `innerDFS_fuel_chain` uses) to the *naturally decremented* fuel a
nested `innerDFS_fuel` call would actually use (via `innerDFS_fuel_fresh`)
requires knowing the decremented amount is *already* enough on its own —
this is exactly that fact. Mirrors the deleted `innerDFS_fuel_sufficient`
from the file's very first (fold-based) design, resurrected here in the
mutual-aux style used throughout this section. Proved by ordinary induction
on `fuel` (not strong induction on the measure): each recursive descent
both decrements `fuel` by exactly one *and* strictly shrinks
`innerFuelMeasure` by exactly one (since the descended-into state is
freshly inserted), so they stay in lockstep and structural induction on
`fuel` suffices. -/
private theorem innerDFS_fuel_fold_exists_aux (succs : State → Array State) (fr : FiniteReach succs)
    (seed : State) (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hiv : ∀ x, iv.contains x → fr.univ.contains x)
    (hcurrent : fr.univ.contains current)
    (hremaining : ∀ x ∈ remaining, x ∈ succs current)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State),
      (∀ x, iv₀.contains x → fr.univ.contains x) → fr.univ.contains curr →
      fuel ≥ innerFuelMeasure succs fr iv₀ + 1 →
      ∃ result iv₁ st₁, innerDFS_fuel succs seed fuel curr iv₀ st₀ = some (result, iv₁, st₁) ∧
        (∀ x, iv₁.contains x → fr.univ.contains x))
    (hfuel : fuel ≥ innerFuelMeasure succs fr iv + 1) :
    ∃ result iv' st', innerDFS_fuel_fold succs seed fuel current remaining iv st =
      some (result, iv', st') ∧ (∀ x, iv'.contains x → fr.univ.contains x) := by
  induction remaining generalizing iv st with
  | nil => exact ⟨none, iv, _, innerDFS_fuel_fold_nil succs seed fuel current iv st, hiv⟩
  | cons succ rest ih_rem =>
    by_cases hse : succ == seed
    · exact ⟨some [current], iv, st,
        innerDFS_fuel_fold_seed succs seed fuel current succ rest iv st hse, hiv⟩
    · rw [innerDFS_fuel_fold_cons succs seed fuel current succ rest iv st hse]
      have hsuccmem : succ ∈ succs current := hremaining succ (List.mem_cons_self ..)
      have hsucc_univ : fr.univ.contains succ := fr.closed current hcurrent succ hsuccmem
      obtain ⟨result1, iv1, st1, heq1, hiv1⟩ := ih_inner succ iv st hiv hsucc_univ hfuel
      rw [heq1]
      cases result1 with
      | some cyclePath => exact ⟨_, _, _, rfl, hiv1⟩
      | none =>
        have hfuel1 : fuel ≥ innerFuelMeasure succs fr iv1 + 1 := by
          have hle : iv.size ≤ iv1.size :=
            HashSet.size_le_of_subset ((innerDFS_fuel_mono succs seed fuel succ iv st none iv1 st1
              heq1).1)
          unfold innerFuelMeasure at *
          omega
        exact ih_rem iv1 st1 hiv1 (fun x hx => hremaining x (List.mem_cons_of_mem _ hx)) hfuel1

theorem innerDFS_fuel_exists (succs : State → Array State) (fr : FiniteReach succs) (seed : State)
    (fuel : Nat) (current : State) (iv : Std.HashSet State) (st : FNDFSState State)
    (hiv : ∀ x, iv.contains x → fr.univ.contains x)
    (hcurrent : fr.univ.contains current)
    (hfuel : fuel ≥ innerFuelMeasure succs fr iv + 1) :
    ∃ result iv' st', innerDFS_fuel succs seed fuel current iv st = some (result, iv', st') ∧
      (∀ x, iv'.contains x → fr.univ.contains x) := by
  induction fuel generalizing current iv st with
  | zero => unfold innerFuelMeasure at hfuel; omega
  | succ n ih =>
    by_cases hblocked : st.innerFinished.contains current || iv.contains current
    · exact ⟨none, iv, st, innerDFS_fuel_blocked succs seed n current iv st hblocked, hiv⟩
    · have hblocked' : (st.innerFinished.contains current || iv.contains current) = false := by
        rw [Bool.eq_false_iff]; exact hblocked
      have hnotfin : st.innerFinished.contains current = false := by
        simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.1
      have hnotvisited : iv.contains current = false := by
        simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.2
      rw [innerDFS_fuel_fresh succs seed n current iv st hnotfin hnotvisited]
      have hiv' : ∀ x, (iv.insert current).contains x → fr.univ.contains x := by
        intro x hx
        simp only [Std.HashSet.contains_insert, Bool.or_eq_true] at hx
        rcases hx with hx | hx
        · have hxc : current = x := by simpa using hx
          exact hxc ▸ hcurrent
        · exact hiv x hx
      have hmeasure : n ≥ innerFuelMeasure succs fr (iv.insert current) + 1 := by
        have hlt : iv.size < (iv.insert current).size :=
          HashSet.size_lt_of_ssubset
            (fun x hx => by simp [Std.HashSet.contains_insert, hx, Bool.or_true])
            (Std.HashSet.contains_insert_self ..) (by simpa using hnotvisited)
        have hle : (iv.insert current).size ≤ fr.univ.size := HashSet.size_le_of_subset hiv'
        unfold innerFuelMeasure at hfuel ⊢
        omega
      exact innerDFS_fuel_fold_exists_aux succs fr seed n current (succs current).toList
        (iv.insert current) st hiv' hcurrent (fun x hx => Array.mem_toList_iff.mp hx)
        (fun curr iv₀ st₀ hiv₀ hcurr hf => ih curr iv₀ st₀ hiv₀ hcurr hf) hmeasure

/-- The main bridge: `innerDFS_fuel_chain` (nested-call semantics, made
explicit-stack) equals `innerDFSCore` (well-founded, explicit-stack), for
sufficient fuel. Driven by `innerDFSCore.induct` — each case unfolds the
*matching* `innerDFS_fuel_fold`/`innerDFS_fuel`/`innerDFS_fuel_chain` step
(all ordinary structural/fuel recursion, no proof-carrying arguments, so
`simp`/`rw` on their equations is reliable, unlike the old fold-shaped
`innerDFSCore`). -/
theorem innerDFS_fuel_chain_eq_innerDFSCore
    (fuel : Nat) (stack : List (State × List State)) (pathStack : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hiv : ∀ x, iv.contains x → fr.univ.contains x)
    (hfin : ∀ x, st.innerFinished.contains x → fr.univ.contains x)
    (hstack_states : ∀ p ∈ stack, fr.univ.contains p.1)
    (hstack_remaining : ∀ p ∈ stack, ∀ x ∈ p.2, x ∈ succs p.1)
    (hfuel : fuel ≥ innerFuelMeasure succs fr iv + 1) :
    ∃ result iv₁ st₁, innerDFS_fuel_chain succs seed fuel stack pathStack iv st =
        some (result, iv₁, st₁) ∧
      (∀ x, iv₁.contains x → fr.univ.contains x) ∧
      (∀ x, st₁.innerFinished.contains x → fr.univ.contains x) ∧
      (result, iv₁, st₁) = innerDFSCore succs fr seed stack pathStack iv st := by
  obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
  induction stack, pathStack, iv, st using innerDFSCore.induct (succs := succs) (fr := fr)
    (seed := seed) with
  | case1 =>
    rename_i pathStack iv st
    refine ⟨none, iv, st, rfl, hiv, hfin, ?_⟩
    unfold innerDFSCore
    rfl
  | case2 =>
    rename_i pathStack iv st current rest ih1
    have hcurrent_univ : fr.univ.contains current :=
      hstack_states (current, []) (List.mem_cons_self ..)
    have hfin' : ∀ x, (st.innerFinished.insert current).contains x → fr.univ.contains x := by
      intro x hx
      simp only [Std.HashSet.contains_insert, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · have hxc : current = x := by simpa using hx
        exact hxc ▸ hcurrent_univ
      · exact hfin x hx
    have hrest_states : ∀ p ∈ rest, fr.univ.contains p.1 :=
      fun p hp => hstack_states p (List.mem_cons_of_mem _ hp)
    have hrest_remaining : ∀ p ∈ rest, ∀ x ∈ p.2, x ∈ succs p.1 :=
      fun p hp => hstack_remaining p (List.mem_cons_of_mem _ hp)
    obtain ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩ :=
      ih1 hiv hfin' hrest_states hrest_remaining hfuel
    refine ⟨result, iv₁, st₁, ?_, hiv1, hfin1, ?_⟩
    · rw [innerDFS_fuel_chain_cons, innerDFS_fuel_fold_nil]
      exact heq
    · unfold innerDFSCore
      exact heqC
  | case3 =>
    rename_i pathStack iv st current rest succ remainingTail hse
    refine ⟨some pathStack, iv, st, ?_, hiv, hfin, ?_⟩
    · rw [innerDFS_fuel_chain_cons,
        innerDFS_fuel_fold_seed succs seed (fuel' + 1) current succ remainingTail iv st hse]
      simp
    · unfold innerDFSCore
      simp [hse]
  | case4 =>
    rename_i pathStack iv st current rest succ remainingTail stack' hse hblocked ih1
    have hstack'_states : ∀ p ∈ (current, remainingTail) :: rest, fr.univ.contains p.1 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact hstack_states (current, succ :: remainingTail) (List.mem_cons_self ..)
      · exact hstack_states p (List.mem_cons_of_mem _ hp')
    have hstack'_remaining :
        ∀ p ∈ (current, remainingTail) :: rest, ∀ x ∈ p.2, x ∈ succs p.1 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · intro x hx
        exact hstack_remaining (current, succ :: remainingTail) (List.mem_cons_self ..) x
          (List.mem_cons_of_mem _ hx)
      · exact hstack_remaining p (List.mem_cons_of_mem _ hp')
    obtain ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩ :=
      ih1 hiv hfin hstack'_states hstack'_remaining hfuel
    refine ⟨result, iv₁, st₁, ?_, hiv1, hfin1, ?_⟩
    · rw [innerDFS_fuel_chain_cons,
        innerDFS_fuel_fold_cons succs seed (fuel' + 1) current succ remainingTail iv st hse,
        innerDFS_fuel_blocked succs seed fuel' succ iv st hblocked]
      exact heq
    · unfold innerDFSCore
      simp only [hse, Bool.false_eq_true, if_false, hblocked, dif_pos]
      exact heqC
  | case5 =>
    rename_i pathStack iv st current rest succ remainingTail stack' hse hblocked hsucc_univ
      hsucc_niv iv' succChildren stack2 ih1
    have hcurrent_univ : fr.univ.contains current :=
      hstack_states (current, succ :: remainingTail) (List.mem_cons_self ..)
    have hcurrent_remaining : ∀ x ∈ succ :: remainingTail, x ∈ succs current :=
      hstack_remaining (current, succ :: remainingTail) (List.mem_cons_self ..)
    have hrest_states : ∀ p ∈ rest, fr.univ.contains p.1 :=
      fun p hp => hstack_states p (List.mem_cons_of_mem _ hp)
    have hrest_remaining : ∀ p ∈ rest, ∀ x ∈ p.2, x ∈ succs p.1 :=
      fun p hp => hstack_remaining p (List.mem_cons_of_mem _ hp)
    have hiv' : ∀ x, iv'.contains x → fr.univ.contains x := by
      intro x hx
      simp only [iv', Std.HashSet.contains_insert, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · have hxc : succ = x := by simpa using hx
        exact hxc ▸ hsucc_univ
      · exact hiv x hx
    have hstack2_states : ∀ p ∈ stack2, fr.univ.contains p.1 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact hsucc_univ
      · rcases List.mem_cons.mp hp' with rfl | hp''
        · exact hcurrent_univ
        · exact hrest_states p hp''
    have hstack2_remaining : ∀ p ∈ stack2, ∀ x ∈ p.2, x ∈ succs p.1 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact fun x hx => Array.mem_toList_iff.mp hx
      · rcases List.mem_cons.mp hp' with rfl | hp''
        · exact fun x hx => hcurrent_remaining x (List.mem_cons_of_mem _ hx)
        · exact hrest_remaining p hp''
    have hfuel' : fuel' + 1 ≥ innerFuelMeasure succs fr iv' + 1 := by
      have hle : iv.size ≤ iv'.size := HashSet.size_le_of_subset (fun x hx => by
        simp only [iv', Std.HashSet.contains_insert, hx, Bool.or_true])
      unfold innerFuelMeasure at hfuel ⊢
      omega
    obtain ⟨result, iv₁, st₁, heq2, hiv1, hfin1, heqC⟩ :=
      ih1 hiv' hfin hstack2_states hstack2_remaining hfuel'
    have hnotfin : st.innerFinished.contains succ = false := by
      rw [Bool.eq_false_iff]
      intro hc
      exact hblocked (by simp [hc])
    obtain ⟨result0, iv0, st0, heq0, -⟩ :=
      innerDFS_fuel_exists succs fr seed (fuel' + 1) succ iv st hiv hsucc_univ hfuel
    have hfresh : innerDFS_fuel succs seed (fuel' + 1) succ iv st =
        innerDFS_fuel_fold succs seed fuel' succ (succs succ).toList (iv.insert succ) st :=
      innerDFS_fuel_fresh succs seed fuel' succ iv st hnotfin hsucc_niv
    have hfold_val : innerDFS_fuel_fold succs seed fuel' succ (succs succ).toList (iv.insert succ) st
        = some (result0, iv0, st0) := by rw [← hfresh, heq0]
    have hfold_val' :
        innerDFS_fuel_fold succs seed (fuel' + 1) succ (succs succ).toList (iv.insert succ) st =
          some (result0, iv0, st0) :=
      innerDFS_fuel_fold_add_preserves succs seed 1 fuel' succ (succs succ).toList
        (iv.insert succ) st result0 iv0 st0 hfold_val
    have heq2' : innerDFS_fuel_chain succs seed (fuel' + 1) stack2 (pathStack ++ [succ]) iv' st =
        some (result, iv₁, st₁) := heq2
    rw [innerDFS_fuel_chain_cons, hfold_val'] at heq2'
    refine ⟨result, iv₁, st₁, ?_, hiv1, hfin1, ?_⟩
    · rw [innerDFS_fuel_chain_cons,
        innerDFS_fuel_fold_cons succs seed (fuel' + 1) current succ remainingTail iv st hse, heq0]
      cases result0 with
      | some cyclePath =>
        have hchain := innerDFS_fuel_cyclePath_chain succs seed (fuel' + 1) succ iv st heq0
        match cyclePath, hchain with
        | [], hchain => simp at hchain
        | c :: cs, hchain =>
          have hhead : c = succ := hchain.2.1 (by simp)
          subst hhead
          simp only at heq2' ⊢
          rw [show pathStack ++ (current :: c :: cs).tail = pathStack ++ [c] ++ cs by
            simp [List.append_assoc]]
          exact heq2'
      | none =>
        simp only at heq2' ⊢
        rw [innerDFS_fuel_chain_cons,
          show (pathStack ++ [succ]).dropLast = pathStack by simp] at heq2'
        exact heq2'
    · unfold innerDFSCore
      simp only [hse, Bool.false_eq_true, if_false, hblocked, hsucc_univ, dif_pos]
      exact heqC
  | case6 =>
    rename_i pathStack iv st current rest succ remainingTail stack' hse hblocked hnot_univ ih1
    exfalso
    apply hnot_univ
    have hcurrent_univ : fr.univ.contains current :=
      hstack_states (current, succ :: remainingTail) (List.mem_cons_self ..)
    have hsuccmem : succ ∈ succs current :=
      hstack_remaining (current, succ :: remainingTail) (List.mem_cons_self ..) succ
        (List.mem_cons_self ..)
    exact fr.closed current hcurrent_univ succ hsuccmem

/-- `innerDFS_fuel_fold`'s own "found" result always starts with `current` —
the same invariant `innerDFS_fuel_cyclePath_chain` establishes for plain
`innerDFS_fuel`, needed here in the `_fold`-level form to relate a
singleton-stack `innerDFS_fuel_chain` call to `innerDFS_fuel_fold` exactly
(no `pathStack`-prefix mismatch, since a singleton stack's `pathStack` is
just `[current]` itself). -/
private theorem innerDFS_fuel_fold_cyclePath_head (fuel : Nat) (current : State)
    (remaining : List State) (iv : Std.HashSet State) (st : FNDFSState State)
    {cyclePath : List State} {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel_fold succs seed fuel current remaining iv st =
      some (some cyclePath, iv', st')) :
    cyclePath.head? = some current := by
  induction remaining generalizing iv st with
  | nil => rw [innerDFS_fuel_fold_nil] at h; simp at h
  | cons succ rest ih_rem =>
    by_cases hse : succ == seed
    · rw [innerDFS_fuel_fold_seed succs seed fuel current succ rest iv st hse] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      rfl
    · rw [innerDFS_fuel_fold_cons succs seed fuel current succ rest iv st hse] at h
      cases hin : innerDFS_fuel succs seed fuel succ iv st with
      | none => rw [hin] at h; simp at h
      | some val =>
        rw [hin] at h
        obtain ⟨cyc, iv2, st2⟩ := val
        cases cyc with
        | some cyclePath2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -, -⟩ := h
          rfl
        | none => exact ih_rem iv2 st2 h

/-- A singleton-stack `innerDFS_fuel_chain` call is exactly
`innerDFS_fuel_fold` — no `pathStack`-rewrapping discrepancy, since
`[current]`'s only element already *is* `current`. This is what lets the
top-level bridge below reuse `innerDFS_fuel_chain_eq_innerDFSCore` (proved
against the general stack shape) at `innerDFSWF`'s own entry point, which
calls `innerDFSCore` with the singleton stack `[(current, succs current)]`. -/
theorem innerDFS_fuel_chain_singleton (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State) :
    innerDFS_fuel_chain succs seed fuel [(current, remaining)] [current] iv st =
      innerDFS_fuel_fold succs seed fuel current remaining iv st := by
  rw [innerDFS_fuel_chain_cons]
  cases h : innerDFS_fuel_fold succs seed fuel current remaining iv st with
  | none => rfl
  | some val =>
    obtain ⟨cyc, iv', st'⟩ := val
    cases cyc with
    | none => rfl
    | some cyclePath =>
      have hhead := innerDFS_fuel_fold_cyclePath_head succs seed fuel current remaining iv st h
      cases cyclePath with
      | nil => cases hhead
      | cons c cs =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        rfl

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
  by_cases hblocked : st.innerFinished.contains current || iv.contains current
  · refine ⟨none, iv, st, ?_, hiv, hfin, ?_⟩
    · obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by unfold innerFuelMeasure at hfuel; omega⟩
      exact innerDFS_fuel_blocked succs seed n current iv st hblocked
    · rw [innerDFSWF_blocked succs fr seed current iv st hblocked]
  · have hblocked' : (st.innerFinished.contains current || iv.contains current) = false := by
      rw [Bool.eq_false_iff]; exact hblocked
    have hnotfin : st.innerFinished.contains current = false := by
      simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.1
    have hnotvisited : iv.contains current = false := by
      simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.2
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by unfold innerFuelMeasure at hfuel; omega⟩
    rw [innerDFS_fuel_fresh succs seed n current iv st hnotfin hnotvisited]
    rw [innerDFSWF_fresh succs fr seed current iv st hnotfin hnotvisited]
    have hiv' : ∀ x, (iv.insert current).contains x → fr.univ.contains x := by
      intro x hx
      simp only [Std.HashSet.contains_insert, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · have hxc : current = x := by simpa using hx
        exact hxc ▸ hcurrent
      · exact hiv x hx
    have hstack1_states : ∀ p ∈ [(current, (succs current).toList)], fr.univ.contains p.1 :=
      fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hcurrent
    have hstack1_remaining :
        ∀ p ∈ [(current, (succs current).toList)], ∀ x ∈ p.2, x ∈ succs p.1 :=
      fun p hp x hx => by rw [List.mem_singleton] at hp; subst hp; exact Array.mem_toList_iff.mp hx
    have hmeasure : n ≥ innerFuelMeasure succs fr (iv.insert current) + 1 := by
      have hlt : iv.size < (iv.insert current).size :=
        HashSet.size_lt_of_ssubset
          (fun x hx => by simp [Std.HashSet.contains_insert, hx, Bool.or_true])
          (Std.HashSet.contains_insert_self ..) (by simpa using hnotvisited)
      have hle : (iv.insert current).size ≤ fr.univ.size := HashSet.size_le_of_subset hiv'
      unfold innerFuelMeasure at hfuel ⊢
      omega
    obtain ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩ :=
      innerDFS_fuel_chain_eq_innerDFSCore succs fr seed n [(current, (succs current).toList)]
        [current] (iv.insert current) st hiv' hfin hstack1_states hstack1_remaining hmeasure
    rw [innerDFS_fuel_chain_singleton] at heq
    exact ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩

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
