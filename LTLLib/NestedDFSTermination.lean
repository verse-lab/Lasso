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
import LTLLib.BA

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

`FiniteReach` itself now lives in `EmptinessCheck.lean` alongside
`EmptinessResult`/`AcceptingCycle`/`EmptinessChecker` — it's the
algorithm-agnostic reachability precondition (Lean analogue of CAVA's
`fb_graph` locale assumption), not specific to nested DFS. Imported
transitively via `NestedDFSCorrectness.lean`/`NestedDFS.lean`. -/

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
    (seed : State) (cyan : Std.HashSet State)
    (stack : List (State × List State))
    (pathStack : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    : Option (List State × State) × Std.HashSet State × FNDFSState State :=
  match stack with
  | [] => (none, iv, st)
  | (current, remaining) :: rest =>
    match remaining with
    | [] =>
      innerDFSCore succs fr seed cyan rest pathStack.dropLast iv
        { st with innerFinished := st.innerFinished.insert current }
    | succ :: remainingTail =>
      let stack' := (current, remainingTail) :: rest
      if succ == seed || cyan.contains succ then
        (some (pathStack, succ), iv, st)
      else if hblocked : st.innerFinished.contains succ || iv.contains succ then
        innerDFSCore succs fr seed cyan stack' pathStack iv st
      else if hsucc_univ : fr.univ.contains succ then
        have hsucc_niv : iv.contains succ = false := by
          rw [Bool.eq_false_iff]
          simp only [Bool.or_eq_true, not_or] at hblocked
          exact hblocked.2
        let iv' := iv.insert succ
        let succChildren := (succs succ).toList
        let stack2 := (succ, succChildren) :: stack'
        innerDFSCore succs fr seed cyan stack2 (pathStack ++ [succ]) iv' st
      else
        innerDFSCore succs fr seed cyan stack' pathStack iv st
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
    (cyan : List State)
    (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    : Option (List State × State) × Std.HashSet State × FNDFSState State :=
  if st.innerFinished.contains current then (none, iv, st)
  else if iv.contains current then (none, iv, st)
  else
    innerDFSCore succs fr seed (Std.HashSet.ofList cyan) [(current, (succs current).toList)] [current]
      (iv.insert current) st

/-- `innerDFSWF`'s "already blocked" case, as a reusable equation — needed by
the fuel bridge (`InnerFuelBridge`, below `OuterDFSWellFounded`) to align
`innerDFS_fuel`'s uniform "always call the top-level function" style with
`innerDFSCore`'s own explicit `hblocked` branch. -/
theorem innerDFSWF_blocked (succs : State → Array State) (fr : FiniteReach succs) (seed : State)
    (cyan : List State) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hblocked : st.innerFinished.contains current || iv.contains current) :
    innerDFSWF succs fr seed cyan current iv st = (none, iv, st) := by
  unfold innerDFSWF
  rcases Bool.or_eq_true_iff.mp hblocked with h | h
  · simp [h]
  · by_cases h1 : st.innerFinished.contains current
    · simp [h1]
    · simp [h1, h]

/-- `innerDFSWF`'s "fresh" case, as a reusable equation. -/
theorem innerDFSWF_fresh (succs : State → Array State) (fr : FiniteReach succs) (seed : State)
    (cyan : List State) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hnotfin : st.innerFinished.contains current = false)
    (hnotvisited : iv.contains current = false) :
    innerDFSWF succs fr seed cyan current iv st =
      innerDFSCore succs fr seed (Std.HashSet.ofList cyan) [(current, (succs current).toList)] [current]
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
    (seed : State) (cyan : Std.HashSet State)
    (stack : List (State × List State)) (pathStack : List State)
    (iv : Std.HashSet State) (st : FNDFSState State) :
    (innerDFSCore succs fr seed cyan stack pathStack iv st).2.2.outerVisited = st.outerVisited := by
  induction stack, pathStack, iv, st using innerDFSCore.induct (succs := succs) (fr := fr)
    (seed := seed) (cyan := cyan)
  all_goals (unfold innerDFSCore; dsimp only; try simp_all; try (rename_i ih; simpa using ih))

/-- Thin wrapper around `innerDFSCore_outerVisited_pres` for `innerDFSWF`
itself — needed by `outerDFSLoopWF`'s own `decreasing_by`, which calls
`innerDFSWF` (not `innerDFSCore` directly; see that function's docstring for
why) at its accepting-leaf branch. -/
theorem innerDFSWF_outerVisited_pres (succs : State → Array State) (fr : FiniteReach succs)
    (seed : State) (cyan : List State) (current : State)
    (iv : Std.HashSet State) (st : FNDFSState State) :
    (innerDFSWF succs fr seed cyan current iv st).2.2.outerVisited = st.outerVisited := by
  by_cases hblocked : st.innerFinished.contains current || iv.contains current
  · rw [innerDFSWF_blocked succs fr seed cyan current iv st hblocked]
  · have hblocked' : (st.innerFinished.contains current || iv.contains current) = false := by
      rw [Bool.eq_false_iff]; exact hblocked
    have hnotfin : st.innerFinished.contains current = false := by
      simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.1
    have hnotvisited : iv.contains current = false := by
      simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.2
    rw [innerDFSWF_fresh succs fr seed cyan current iv st hnotfin hnotvisited]
    exact innerDFSCore_outerVisited_pres succs fr seed (Std.HashSet.ofList cyan) _ _ _ st

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
  (succs : State → Array State) (fr : FiniteReach succs) (seed : State) (cyan : List State)

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

/-- Fuel-increase preserves a successful result, for `innerDFS_fuel` itself.
Proved by induction on `fuel`, using `innerDFS_fuel_fold_add_aux` for the
mutual recursion — the same shape as `innerDFS_fuel_mono`'s own proof. -/
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
    (seed : State) (cyan : List State) (fuel : Nat) (current : State) (remaining : List State)
    (iv : Std.HashSet State) (st : FNDFSState State)
    (hiv : ∀ x, iv.contains x → fr.univ.contains x)
    (hcurrent : fr.univ.contains current)
    (hremaining : ∀ x ∈ remaining, x ∈ succs current)
    (ih_inner : ∀ (curr : State) (iv₀ : Std.HashSet State) (st₀ : FNDFSState State),
      (∀ x, iv₀.contains x → fr.univ.contains x) → fr.univ.contains curr →
      fuel ≥ innerFuelMeasure succs fr iv₀ + 1 →
      ∃ result iv₁ st₁, innerDFS_fuel succs seed cyan fuel curr iv₀ st₀ = some (result, iv₁, st₁) ∧
        (∀ x, iv₁.contains x → fr.univ.contains x))
    (hfuel : fuel ≥ innerFuelMeasure succs fr iv + 1) :
    ∃ result iv' st', innerDFS_fuel_fold succs seed cyan fuel current remaining iv st =
      some (result, iv', st') ∧ (∀ x, iv'.contains x → fr.univ.contains x) := by
  induction remaining generalizing iv st with
  | nil => exact ⟨none, iv, _, innerDFS_fuel_fold_nil succs seed cyan fuel current iv st, hiv⟩
  | cons succ rest ih_rem =>
    by_cases hse : succ == seed || cyan.contains succ
    · exact ⟨some ([current], succ), iv, st,
        innerDFS_fuel_fold_seed succs seed cyan fuel current succ rest iv st hse, hiv⟩
    · rw [innerDFS_fuel_fold_cons succs seed cyan fuel current succ rest iv st hse]
      have hsuccmem : succ ∈ succs current := hremaining succ (List.mem_cons_self ..)
      have hsucc_univ : fr.univ.contains succ := fr.closed current hcurrent succ hsuccmem
      obtain ⟨result1, iv1, st1, heq1, hiv1⟩ := ih_inner succ iv st hiv hsucc_univ hfuel
      rw [heq1]
      cases result1 with
      | some cyclePath => exact ⟨_, _, _, rfl, hiv1⟩
      | none =>
        have hfuel1 : fuel ≥ innerFuelMeasure succs fr iv1 + 1 := by
          have hle : iv.size ≤ iv1.size :=
            HashSet.size_le_of_subset ((innerDFS_fuel_mono succs seed cyan fuel succ iv st none iv1 st1
              heq1).1)
          unfold innerFuelMeasure at *
          omega
        exact ih_rem iv1 st1 hiv1 (fun x hx => hremaining x (List.mem_cons_of_mem _ hx)) hfuel1

theorem innerDFS_fuel_exists (succs : State → Array State) (fr : FiniteReach succs) (seed : State)
    (cyan : List State) (fuel : Nat) (current : State) (iv : Std.HashSet State) (st : FNDFSState State)
    (hiv : ∀ x, iv.contains x → fr.univ.contains x)
    (hcurrent : fr.univ.contains current)
    (hfuel : fuel ≥ innerFuelMeasure succs fr iv + 1) :
    ∃ result iv' st', innerDFS_fuel succs seed cyan fuel current iv st = some (result, iv', st') ∧
      (∀ x, iv'.contains x → fr.univ.contains x) := by
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
      exact innerDFS_fuel_fold_exists_aux succs fr seed cyan n current (succs current).toList
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
    ∃ result iv₁ st₁, innerDFS_fuel_chain succs seed cyan fuel stack pathStack iv st =
        some (result, iv₁, st₁) ∧
      (∀ x, iv₁.contains x → fr.univ.contains x) ∧
      (∀ x, st₁.innerFinished.contains x → fr.univ.contains x) ∧
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
    have hseL := hse
    simp only [Std.HashSet.contains_ofList] at hseL
    refine ⟨some (pathStack, succ), iv, st, ?_, hiv, hfin, ?_⟩
    · rw [innerDFS_fuel_chain_cons,
        innerDFS_fuel_fold_seed succs seed cyan (fuel' + 1) current succ remainingTail iv st hseL]
      simp
    · unfold innerDFSCore
      simp only [hse, if_true]
  | case4 =>
    rename_i pathStack iv st current rest succ remainingTail stack' hse hblocked ih1
    have hseL := hse
    simp only [Std.HashSet.contains_ofList] at hseL
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
        innerDFS_fuel_fold_cons succs seed cyan (fuel' + 1) current succ remainingTail iv st hseL,
        innerDFS_fuel_blocked succs seed cyan fuel' succ iv st hblocked]
      exact heq
    · unfold innerDFSCore
      simp only [hse, Bool.false_eq_true, if_false, hblocked, dif_pos]
      exact heqC
  | case5 =>
    rename_i pathStack iv st current rest succ remainingTail stack' hse hblocked hsucc_univ
      hsucc_niv iv' succChildren stack2 ih1
    have hseL := hse
    simp only [Std.HashSet.contains_ofList] at hseL
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
      innerDFS_fuel_exists succs fr seed cyan (fuel' + 1) succ iv st hiv hsucc_univ hfuel
    have hfresh : innerDFS_fuel succs seed cyan (fuel' + 1) succ iv st =
        innerDFS_fuel_fold succs seed cyan fuel' succ (succs succ).toList (iv.insert succ) st :=
      innerDFS_fuel_fresh succs seed cyan fuel' succ iv st hnotfin hsucc_niv
    have hfold_val : innerDFS_fuel_fold succs seed cyan fuel' succ (succs succ).toList (iv.insert succ) st
        = some (result0, iv0, st0) := by rw [← hfresh, heq0]
    have hfold_val' :
        innerDFS_fuel_fold succs seed cyan (fuel' + 1) succ (succs succ).toList (iv.insert succ) st =
          some (result0, iv0, st0) :=
      innerDFS_fuel_fold_add_preserves succs seed cyan 1 fuel' succ (succs succ).toList
        (iv.insert succ) st result0 iv0 st0 hfold_val
    have heq2' : innerDFS_fuel_chain succs seed cyan (fuel' + 1) stack2 (pathStack ++ [succ]) iv' st =
        some (result, iv₁, st₁) := heq2
    rw [innerDFS_fuel_chain_cons, hfold_val'] at heq2'
    refine ⟨result, iv₁, st₁, ?_, hiv1, hfin1, ?_⟩
    · rw [innerDFS_fuel_chain_cons,
        innerDFS_fuel_fold_cons succs seed cyan (fuel' + 1) current succ remainingTail iv st hseL, heq0]
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

/-- A singleton-stack `innerDFS_fuel_chain` call is exactly
`innerDFS_fuel_fold` — no `pathStack`-rewrapping discrepancy, since
`[current]`'s only element already *is* `current`. This is what lets the
top-level bridge below reuse `innerDFS_fuel_chain_eq_innerDFSCore` (proved
against the general stack shape) at `innerDFSWF`'s own entry point, which
calls `innerDFSCore` with the singleton stack `[(current, succs current)]`. -/
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

/-- Top-level bridge: for sufficient fuel, `innerDFS_fuel` equals
`innerDFSWF`. -/
theorem innerDFS_fuel_eq_innerDFSWF
    (fuel : Nat) (current : State) (iv : Std.HashSet State) (st : FNDFSState State)
    (hcurrent : fr.univ.contains current)
    (hiv : ∀ x, iv.contains x → fr.univ.contains x)
    (hfin : ∀ x, st.innerFinished.contains x → fr.univ.contains x)
    (hfuel : fuel ≥ innerFuelMeasure succs fr iv + 1) :
    ∃ result iv₁ st₁, innerDFS_fuel succs seed cyan fuel current iv st = some (result, iv₁, st₁) ∧
      (∀ x, iv₁.contains x → fr.univ.contains x) ∧
      (∀ x, st₁.innerFinished.contains x → fr.univ.contains x) ∧
      (result, iv₁, st₁) = innerDFSWF succs fr seed cyan current iv st := by
  by_cases hblocked : st.innerFinished.contains current || iv.contains current
  · refine ⟨none, iv, st, ?_, hiv, hfin, ?_⟩
    · obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by unfold innerFuelMeasure at hfuel; omega⟩
      exact innerDFS_fuel_blocked succs seed cyan n current iv st hblocked
    · rw [innerDFSWF_blocked succs fr seed cyan current iv st hblocked]
  · have hblocked' : (st.innerFinished.contains current || iv.contains current) = false := by
      rw [Bool.eq_false_iff]; exact hblocked
    have hnotfin : st.innerFinished.contains current = false := by
      simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.1
    have hnotvisited : iv.contains current = false := by
      simp only [Bool.or_eq_false_iff] at hblocked'; exact hblocked'.2
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by unfold innerFuelMeasure at hfuel; omega⟩
    rw [innerDFS_fuel_fresh succs seed cyan n current iv st hnotfin hnotvisited]
    rw [innerDFSWF_fresh succs fr seed cyan current iv st hnotfin hnotvisited]
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
      innerDFS_fuel_chain_eq_innerDFSCore succs fr seed cyan n [(current, (succs current).toList)]
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

/-- Well-founded `outerDFSLoop`. Mirrors `innerDFSCore`'s own redesign: **no
proof-carrying arguments**. Re-checking CAVA's `Param_DFS.thy` confirms this
is the right shape, not just a Lean-side workaround — CAVA's `step` itself
(`('v,'es) state_scheme ⇒ ('v,'es) state_scheme nres`) carries no invariant
in its type either. `DFS_invar` is proved as a wholly external SPEC-level
fact; `param_dfs_variant_step` takes `DFS_invar G param s` only as a *side
hypothesis* when proving the variant decreases, never as part of `step`'s
signature. So here too, `fr.univ` membership is checked at runtime via
`dite` (mirroring `innerDFSCore`'s `hsucc_univ` check) with a defensive
"treat as already-visited" fallback branch — dead code under `fr.closed`,
exactly like `innerDFSCore`'s analogous fallback. The two closure
hypotheses that used to be threaded through the signature
(`hstack_states`/`hstack_remaining`) now live only in the bridge theorem
below, exactly as `DFS_invar` lives only in CAVA's separate correctness
lemmas about `step`, never in `step`'s own definition. -/
def outerDFSLoopWF (succs : State → Array State) (isAccepting : State → Bool)
    (fr : FiniteReach succs)
    (stack : List (State × List State))
    (pathStack : List State)
    (st : FNDFSState State)
    : EmptinessResult State × FNDFSState State :=
  match stack with
  | [] => (.empty st.outerVisited.size, st)
  | (current, remaining) :: rest =>
    match remaining with
    | [] =>
      if isAccepting current then
        let innerVisited := Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)
        match _hr : innerDFSWF succs fr current pathStack current innerVisited st with
        | (some (cyclePath, target), _, st') =>
          -- Holzmann-Peled-Yannakakis shortcut (mirroring `outerDFSLoop_fuel`
          -- exactly, `NestedDFSCorrectness.lean`): `target` may be `current`
          -- itself or any other state on `pathStack`; collapses to the
          -- pre-HPY `current :: cyclePath` formula when `target = current`.
          let loopTail := (pathStack.dropWhile (fun y => !(y == target))).dropLast
          (.nonEmpty pathStack (current :: cyclePath ++ loopTail), st')
        | (none, _, st') =>
          outerDFSLoopWF succs isAccepting fr rest pathStack.dropLast st'
      else
        outerDFSLoopWF succs isAccepting fr rest pathStack.dropLast st
    | succ :: remainingTail =>
      let stack' := (current, remainingTail) :: rest
      if pathStack.contains succ then
        -- Schwoon-Esparza back-edge shortcut, mirroring `outerDFSLoop_fuel`
        -- exactly (`NestedDFSCorrectness.lean`).
        if isAccepting current then
          if succ == current then
            (.nonEmpty pathStack [current, current], st)
          else
            let loopTail := (pathStack.dropWhile (fun y => !(y == succ))).dropLast
            (.nonEmpty pathStack (current :: current :: loopTail), st)
        else if isAccepting succ then
          let stem := pathStack.takeWhile (fun y => !(y == succ)) ++ [succ]
          let loop := succ :: pathStack.dropWhile (fun y => !(y == succ))
          (.nonEmpty stem loop, st)
        else
          outerDFSLoopWF succs isAccepting fr stack' pathStack st
      else if _hvis : st.outerVisited.contains succ then
        outerDFSLoopWF succs isAccepting fr stack' pathStack st
      else if _hsucc_univ : fr.univ.contains succ then
        let st2 := { st with outerVisited := st.outerVisited.insert succ }
        let succChildren := (succs succ).toList
        let stack2 := (succ, succChildren) :: stack'
        outerDFSLoopWF succs isAccepting fr stack2 (pathStack ++ [succ]) st2
      else
        outerDFSLoopWF succs isAccepting fr stack' pathStack st
termination_by ((fr.univ \ st.outerVisited).size, pendingSum stack + stack.length)
decreasing_by
  · have hst'_eq : st'.outerVisited = st.outerVisited := by
      have hr2 := innerDFSWF_outerVisited_pres succs fr current pathStack current innerVisited st
      rw [_hr] at hr2
      exact hr2
    rw [hst'_eq]
    exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · have hsucc_niv : st.outerVisited.contains succ = false := by simpa using _hvis
    exact Prod.Lex.left _ _ (HashSet.sdiff_insert_lt _hsucc_univ hsucc_niv)
  · exact Prod.Lex.right _ (by simp)

end OuterDFSWellFounded

/-! ## Fuel ↔ well-founded bridge, outer half (Phase 2, 2026-07-25, continued)

Mirrors `InnerFuelBridge`, but simpler: `outerDFSLoop_fuel`/`outerDFSLoopWF` are
*already* the same explicit-stack shape (unlike inner's original fold-vs-stack
mismatch), so no `_chain`-style reindexing function is needed — a direct
induction via `outerDFSLoopWF.induct` suffices.

The one genuine new subtlety: `outerDFSLoop_fuel` spends exactly one fuel unit
per *loop iteration* (every recursive call pattern-matches `fuel = _ + 1` and
passes the decremented value on), unlike `innerDFS_fuel`/`innerDFS_fuel_fold`
which only spent fuel on a *descend*. So there is no single closed-form
Nat measure playing the role `innerFuelMeasure` did — the number of
iterations isn't bounded by `(fr.univ \ outerVisited).size` alone (backtrack/
skip transitions leave it unchanged while still costing fuel). Re-checking
CAVA (`Param_DFS.thy`) confirms this is expected, not a gap: CAVA's own
`it_dfsT_eq_it_dfs` never computes a numeral fuel bound either — it transports
`WHILET` to `WHILE` via `WHILET_eq_WHILE_tproof`, an abstract well-founded
argument keyed on `param_dfs_variant`'s lex order directly, with no explicit
step-count formula anywhere. We do the same: `outerDFSLoop_fuel_eq_outerDFSLoopWF`
below proves *existence* of a sufficient fuel by induction on `outerDFSLoopWF`'s
own recursion (i.e. on the same lex measure), never a formula in `fuel`. This
matches how the existing fuel-based correctness theorems in
`NestedDFSCorrectness.lean` are already stated (e.g. `nestedDFS_fuel_empty_no_cycle`
takes an arbitrary implicit `fuel` and only assumes *success*, never a lower
bound) — so existence-of-*some*-sufficient-fuel is exactly what's needed to
transport them across the bridge, nothing stronger.

Every branch of `outerDFSLoopWF.induct` has exactly one nested computation to
solve for fuel, EXCEPT the "accepting, cycle not found" branch, which has two
independent ones sharing the same fuel slot (the `innerDFS_fuel` call and the
"continue with `rest`" recursive call) — that one needs an explicit max, hence
needs its own fuel-monotonicity fact for `outerDFSLoop_fuel` itself
(`outerDFSLoop_fuel_add_preserves`, proved first, mirroring
`innerDFS_fuel_add_preserves`) to reconcile the two to a shared value. -/

section OuterFuelBridge

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-! One-step unfolding equations for `outerDFSLoop_fuel`, mirroring the
`innerDFS_fuel_blocked`/`innerDFS_fuel_fresh`/etc. family — a clean `rw`-based
alternative to raw `split`, avoiding any dependence on well-founded-recursion
equation-lemma machinery (`outerDFSLoop_fuel` is ordinary structural recursion
on `fuel`, so these are all provable by `unfold`/`simp`/`rfl`, exactly as
reliably as the inner ones were). -/

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

/-- Holzmann-Peled-Yannakakis shortcut: `target` may be `current` itself or
    any other state on `pathStack`; the witness formula collapses to the
    pre-HPY `current :: cyclePath` when `target = current` (see
    `NestedDFSCorrectness.lean`'s `outerDFSLoop_fuel` for the same formula). -/
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

/-- Schwoon-Esparza back-edge shortcut, "neither accepting" sub-case: behaves
    exactly like `outerDFSLoop_fuel_skip_visited` (recurse with `succ`
    dropped), just reached via the back-edge branch instead of the
    already-visited one. -/
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

/-- Schwoon-Esparza back-edge shortcut, "source accepting" sub-case: an
    immediate, fuel-independent `.nonEmpty` result (self-loop or general). -/
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

/-- Schwoon-Esparza back-edge shortcut, "target accepting" sub-case: an
    immediate, fuel-independent `.nonEmpty` result. -/
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

/-- Fuel-increase preserves a successful `outerDFSLoop_fuel` result. Proved by
induction on `fuel`, mirroring `innerDFS_fuel_add_preserves`; needs
`innerDFS_fuel_add_preserves` itself at the "accepting" branch, since that
branch's nested `innerDFS_fuel` call also receives the same bumped fuel. -/
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

variable (succs : State → Array State) (fr : FiniteReach succs) (isAccepting : State → Bool)

/-- Top-level bridge: for a suitable `stack`/`pathStack`/`st`, there is a fuel
value for which `outerDFSLoop_fuel` succeeds and agrees exactly with
`outerDFSLoopWF`. Proved by induction on `outerDFSLoopWF`'s own recursion
(rather than on `fuel`, or via a closed-form fuel formula — see this
section's docstring for why). -/
theorem outerDFSLoop_fuel_eq_outerDFSLoopWF
    (stack : List (State × List State)) (pathStack : List State) (st : FNDFSState State)
    (hfin : ∀ x, st.innerFinished.contains x → fr.univ.contains x)
    (hstack_states : ∀ p ∈ stack, fr.univ.contains p.1)
    (hstack_remaining : ∀ p ∈ stack, ∀ x ∈ p.2, x ∈ succs p.1) :
    ∃ fuel result st', outerDFSLoop_fuel succs isAccepting fuel stack pathStack st =
        some (result, st') ∧
      (∀ x, st'.innerFinished.contains x → fr.univ.contains x) ∧
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
    rename_i pathStack st current rest hacc innerVisited cyclePath target iv' st' hr
    have hcurrent : fr.univ.contains current := hstack_states (current, []) (List.mem_cons_self ..)
    have hiv : ∀ x, innerVisited.contains x → fr.univ.contains x := by
      simp [innerVisited, Std.HashSet.contains_emptyWithCapacity]
    obtain ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩ :=
      innerDFS_fuel_eq_innerDFSWF succs fr current pathStack
        (innerFuelMeasure succs fr innerVisited + 1) current innerVisited st
        hcurrent hiv hfin (by omega)
    rw [hr] at heqC
    simp only [Prod.mk.injEq] at heqC
    obtain ⟨rfl, rfl, rfl⟩ := heqC
    refine ⟨innerFuelMeasure succs fr innerVisited + 1 + 1,
      .nonEmpty pathStack
        (current :: cyclePath ++ (pathStack.dropWhile (fun y => !(y == target))).dropLast), st₁,
      ?_, hfin1, ?_⟩
    · exact outerDFSLoop_fuel_accept_found succs isAccepting
        (innerFuelMeasure succs fr innerVisited + 1) current rest pathStack st hacc
        cyclePath target iv₁ st₁ heq
    · unfold outerDFSLoopWF
      simp only [hacc, if_true, innerVisited] at hr ⊢
      rw [hr]
  | case3 =>
    rename_i pathStack st current rest hacc innerVisited iv' st' hr ih1
    have hcurrent : fr.univ.contains current := hstack_states (current, []) (List.mem_cons_self ..)
    have hiv : ∀ x, innerVisited.contains x → fr.univ.contains x := by
      simp [innerVisited, Std.HashSet.contains_emptyWithCapacity]
    have hstack_states_rest : ∀ p ∈ rest, fr.univ.contains p.1 :=
      fun p hp => hstack_states p (List.mem_cons_of_mem _ hp)
    have hstack_remaining_rest : ∀ p ∈ rest, ∀ x ∈ p.2, x ∈ succs p.1 :=
      fun p hp => hstack_remaining p (List.mem_cons_of_mem _ hp)
    obtain ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩ :=
      innerDFS_fuel_eq_innerDFSWF succs fr current pathStack
        (innerFuelMeasure succs fr innerVisited + 1) current innerVisited st
        hcurrent hiv hfin (by omega)
    rw [hr] at heqC
    simp only [Prod.mk.injEq] at heqC
    obtain ⟨rfl, rfl, rfl⟩ := heqC
    obtain ⟨fuel2, result2, st2, heq2, hfin2, heqC2⟩ :=
      ih1 hfin1 hstack_states_rest hstack_remaining_rest
    let m := max (innerFuelMeasure succs fr innerVisited + 1) fuel2
    have heqm : innerDFS_fuel succs current pathStack m current innerVisited st =
        some (none, iv₁, st₁) := by
      rw [show m = (innerFuelMeasure succs fr innerVisited + 1) +
          (m - (innerFuelMeasure succs fr innerVisited + 1)) by
        simp only [m]; omega]
      exact innerDFS_fuel_add_preserves succs current pathStack _
        (innerFuelMeasure succs fr innerVisited + 1) current innerVisited st none iv₁ st₁ heq
    have heq2m : outerDFSLoop_fuel succs isAccepting m rest pathStack.dropLast st₁ =
        some (result2, st2) := by
      rw [show m = fuel2 + (m - fuel2) by
        simp only [m]; omega]
      exact outerDFSLoop_fuel_add_preserves succs isAccepting _ fuel2 rest pathStack.dropLast st₁
        result2 st2 heq2
    refine ⟨m + 1, result2, st2,
      ?_, hfin2, ?_⟩
    · exact (outerDFSLoop_fuel_accept_not_found succs isAccepting m current rest pathStack st hacc
        iv₁ st₁ heqm).trans heq2m
    · unfold outerDFSLoopWF
      simp only [hacc, if_true, innerVisited] at hr ⊢
      rw [hr]
      exact heqC2
  | case4 =>
    rename_i pathStack st current rest hacc ih1
    have hacc' : isAccepting current = false := by
      simp only [Bool.not_eq_true] at hacc; exact hacc
    have hstack_states_rest : ∀ p ∈ rest, fr.univ.contains p.1 :=
      fun p hp => hstack_states p (List.mem_cons_of_mem _ hp)
    have hstack_remaining_rest : ∀ p ∈ rest, ∀ x ∈ p.2, x ∈ succs p.1 :=
      fun p hp => hstack_remaining p (List.mem_cons_of_mem _ hp)
    obtain ⟨fuel2, result2, st2, heq2, hfin2, heqC2⟩ :=
      ih1 hfin hstack_states_rest hstack_remaining_rest
    refine ⟨fuel2 + 1, result2, st2, ?_, hfin2, ?_⟩
    · exact outerDFSLoop_fuel_backtrack_not_accept succs isAccepting fuel2 current rest pathStack
        st hacc' ▸ heq2
    · unfold outerDFSLoopWF
      simp only [hacc]
      exact heqC2
  | case5 =>
    rename_i _inst pathStack st current rest succ remainingTail hb hacc hsc
    refine ⟨1, .nonEmpty pathStack [current, current], st, ?_, hfin, ?_⟩
    · rw [outerDFSLoop_fuel_back_edge_current_acc succs isAccepting 0 current succ remainingTail
        rest pathStack st (by simpa using hb) hacc]
      simp [hsc]
    · unfold outerDFSLoopWF
      simp only [hb, hacc, hsc, if_true]
  | case6 =>
    rename_i _inst pathStack st current rest succ remainingTail hb hacc hsc
    refine ⟨1, .nonEmpty pathStack
      (current :: current :: (pathStack.dropWhile (fun y => !(y == succ))).dropLast), st,
      ?_, hfin, ?_⟩
    · rw [outerDFSLoop_fuel_back_edge_current_acc succs isAccepting 0 current succ remainingTail
        rest pathStack st (by simpa using hb) hacc]
      simp [hsc]
    · unfold outerDFSLoopWF
      simp only [hb, hacc, hsc, if_true]
      rfl
  | case7 =>
    rename_i _inst pathStack st current rest succ remainingTail hb hacc hsacc
    have hacc' : isAccepting current = false := by simpa using hacc
    refine ⟨1, .nonEmpty (pathStack.takeWhile (fun y => !(y == succ)) ++ [succ])
      (succ :: pathStack.dropWhile (fun y => !(y == succ))), st, ?_, hfin, ?_⟩
    · exact outerDFSLoop_fuel_back_edge_succ_acc succs isAccepting 0 current succ remainingTail
        rest pathStack st (by simpa using hb) hacc' hsacc
    · unfold outerDFSLoopWF
      simp only [hb, hacc, hsacc, if_true]
      rfl
  | case8 =>
    rename_i pathStack st current rest succ remainingTail stack' hb hacc hsacc ih1
    have hb' : succ ∈ pathStack := by simpa using hb
    have hacc' : isAccepting current = false := by simpa using hacc
    have hsacc' : isAccepting succ = false := by simpa using hsacc
    have hstack'_states : ∀ p ∈ stack', fr.univ.contains p.1 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact hstack_states (current, succ :: remainingTail) (List.mem_cons_self ..)
      · exact hstack_states p (List.mem_cons_of_mem _ hp')
    have hstack'_remaining : ∀ p ∈ stack', ∀ x ∈ p.2, x ∈ succs p.1 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact fun x hx => hstack_remaining (current, succ :: remainingTail)
          (List.mem_cons_self ..) x (List.mem_cons_of_mem _ hx)
      · exact hstack_remaining p (List.mem_cons_of_mem _ hp')
    obtain ⟨fuel2, result2, st2, heq2, hfin2, heqC2⟩ :=
      ih1 hfin hstack'_states hstack'_remaining
    refine ⟨fuel2 + 1, result2, st2, ?_, hfin2, ?_⟩
    · exact outerDFSLoop_fuel_back_edge_skip succs isAccepting fuel2 current succ remainingTail
        rest pathStack st hb' hacc' hsacc' ▸ heq2
    · unfold outerDFSLoopWF
      simp only [hb, hacc, hsacc]
      exact heqC2
  | case9 =>
    rename_i pathStack st current rest succ remainingTail stack' hnb h ih1
    have hnb' : succ ∉ pathStack := by simpa using hnb
    have hstack'_states : ∀ p ∈ stack', fr.univ.contains p.1 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact hstack_states (current, succ :: remainingTail) (List.mem_cons_self ..)
      · exact hstack_states p (List.mem_cons_of_mem _ hp')
    have hstack'_remaining : ∀ p ∈ stack', ∀ x ∈ p.2, x ∈ succs p.1 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact fun x hx => hstack_remaining (current, succ :: remainingTail)
          (List.mem_cons_self ..) x (List.mem_cons_of_mem _ hx)
      · exact hstack_remaining p (List.mem_cons_of_mem _ hp')
    obtain ⟨fuel2, result2, st2, heq2, hfin2, heqC2⟩ :=
      ih1 hfin hstack'_states hstack'_remaining
    refine ⟨fuel2 + 1, result2, st2, ?_, hfin2, ?_⟩
    · exact outerDFSLoop_fuel_skip_visited succs isAccepting fuel2 current succ remainingTail rest
        pathStack st hnb' h ▸ heq2
    · unfold outerDFSLoopWF
      simp only [hnb, h]
      exact heqC2
  | case10 =>
    rename_i pathStack st current rest succ remainingTail stack' hnb hnotvis hunivsucc st2
      succChildren stack2 ih1
    have hnb' : succ ∉ pathStack := by simpa using hnb
    have hnotvis' : st.outerVisited.contains succ = false := by
      simp only [Bool.not_eq_true] at hnotvis; exact hnotvis
    have hfin2' : ∀ x, st2.innerFinished.contains x → fr.univ.contains x := by
      simp only [st2]; exact hfin
    have hstack2_states : ∀ p ∈ stack2, fr.univ.contains p.1 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact hunivsucc
      · rcases List.mem_cons.mp hp' with rfl | hp''
        · exact hstack_states (current, succ :: remainingTail) (List.mem_cons_self ..)
        · exact hstack_states p (List.mem_cons_of_mem _ hp'')
    have hstack2_remaining : ∀ p ∈ stack2, ∀ x ∈ p.2, x ∈ succs p.1 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact fun x hx => Array.mem_toList_iff.mp hx
      · rcases List.mem_cons.mp hp' with rfl | hp''
        · exact fun x hx => hstack_remaining (current, succ :: remainingTail)
            (List.mem_cons_self ..) x (List.mem_cons_of_mem _ hx)
        · exact hstack_remaining p (List.mem_cons_of_mem _ hp'')
    obtain ⟨fuel2, result2, st2', heq2, hfin2, heqC2⟩ :=
      ih1 hfin2' hstack2_states hstack2_remaining
    refine ⟨fuel2 + 1, result2, st2', ?_, hfin2, ?_⟩
    · exact outerDFSLoop_fuel_push succs isAccepting fuel2 current succ remainingTail rest
        pathStack st hnb' hnotvis' ▸ heq2
    · unfold outerDFSLoopWF
      simp only [hnb, hnotvis, hunivsucc]
      exact heqC2
  | case11 =>
    rename_i pathStack st current rest succ remainingTail stack' hnb hnotvis hnotuniv ih1
    exfalso
    apply hnotuniv
    have hcurrent : fr.univ.contains current :=
      hstack_states (current, succ :: remainingTail) (List.mem_cons_self ..)
    have hsuccmem : succ ∈ succs current :=
      hstack_remaining (current, succ :: remainingTail) (List.mem_cons_self ..) succ
        (List.mem_cons_self ..)
    exact fr.closed current hcurrent succ hsuccmem

end OuterFuelBridge

/-! ## Top-level `nestedDFS`, well-founded (Phase 2, wiring, 2026-07-25 continued)

CAVA's actual top-level assembly (`Nested_DFS.thy`): `nested_dfs G accpt ≡ do
{ s ← it_dfs G accpt; RETURN (lasso s) }` — a *single* call into the generic
`it_dfs` engine, which handles the entire `V0` (multi-root) traversal
internally via `get_new_root`/`do_new_root`, folded into `step` itself and
covered by the *same* well-founded `param_dfs_variant` measure used for
ordinary successor discovery (picking a new root is just another kind of
"discover a new state" transition, per `step`'s own `is_empty_stack s then
get_new_root ...` branch).

Our own `nestedDFS_fuel`/`nestedDFS_fuel.go` (`NestedDFSCorrectness.lean`,
Phase 5, ✅ done, ~2000 sorry-free lines) does *not* mirror this exactly: it
factors multi-root handling as a second, outer structural loop over
`initialStates`, calling `outerDFSLoop_fuel` once per unvisited root, rather
than folding root-selection into one generic engine. That's a consequence of
not having ported CAVA's generic, reusable `param_DFS` locale (a
substantially larger undertaking, well out of scope here) — not a deviation
from the *algorithm* CAVA describes (CVWY nested DFS over multiple initial
states), which is identical either way; CAVA's single-engine shape is a
framework-engineering artifact of `param_DFS` being shared across many
different DFS-based algorithms, not a property of nested DFS itself.
Rebuilding `nestedDFS_fuel`/`outerDFSLoop_fuel` to match CAVA's single-loop
code shape would mean reopening and re-proving all of Phase 5's already-
complete, already-verified correctness proof for a purely organizational
gain — so `nestedDFSWF` below instead mirrors `nestedDFS_fuel`'s *existing*
two-loop shape exactly, keeping faithful to the algorithm without touching
already-finished work.

`nestedDFSWF.go`'s own recursion is *plain* structural recursion on
`remaining : List State` (`init :: rest → rest`, strictly smaller) — no
fuel, no well-founded measure, no `termination_by` needed at all; only the
*single* call it makes into `outerDFSLoopWF` per root needs the well-founded
machinery, already built above. -/

section TopLevelWF

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-- Well-founded top-level nested DFS emptiness check. Mirrors
`nestedDFS_fuel`'s exact shape (see this section's docstring for why),
using `outerDFSLoopWF` in place of `outerDFSLoop_fuel`. -/
def nestedDFSWF (succs : State → Array State) (fr : FiniteReach succs)
    (isAccepting : State → Bool) (initialStates : List State) : EmptinessResult State :=
  let st : FNDFSState State := {
    outerVisited := Std.HashSet.emptyWithCapacity 1024
    innerFinished := Std.HashSet.emptyWithCapacity 1024
  }
  nestedDFSWF.go succs fr isAccepting initialStates st
where
  go (succs : State → Array State) (fr : FiniteReach succs) (isAccepting : State → Bool)
      (remaining : List State) (st : FNDFSState State) : EmptinessResult State :=
    match remaining with
    | [] => .empty st.outerVisited.size
    | init :: rest =>
      if st.outerVisited.contains init then go succs fr isAccepting rest st
      else
        let st := { st with outerVisited := st.outerVisited.insert init }
        let succsList := (succs init).toList
        match outerDFSLoopWF succs isAccepting fr [(init, succsList)] [init] st with
        | (.nonEmpty stem loop, _) => .nonEmpty stem loop
        | (.empty _, st') => go succs fr isAccepting rest st'

end TopLevelWF

/-! ## Fuel ↔ well-founded bridge, top level (Phase 2, wiring, continued)

Mirrors `OuterFuelBridge` one level up: `nestedDFS_fuel.go`'s own recursion
spends exactly one fuel unit per *iteration* over `initialStates`, same
"per-iteration, not per-descend" shape as `outerDFSLoop_fuel`, so the same
recipe applies verbatim — one-step unfolding equations, a fuel-monotonicity
lemma, then an existence-style bridge by induction (here on `remaining`
directly, matching `nestedDFSWF.go`'s own *plain* structural recursion,
rather than on `fuel` or on a `.induct` principle — there is no well-founded
recursion on the top-level loop at all, so this is the simplest bridge in
the file). -/

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

/-- Fuel-increase preserves a successful `nestedDFS_fuel.go` result. Mirrors
`outerDFSLoop_fuel_add_preserves`; needs it directly at the "fresh root"
branch, since that branch's nested `outerDFSLoop_fuel` call also receives
the same bumped fuel. -/
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

variable (succs : State → Array State) (fr : FiniteReach succs) (isAccepting : State → Bool)

/-- Top-level bridge: for a suitable `remaining`/`st`, there is a fuel value
for which `nestedDFS_fuel.go` succeeds and agrees exactly with
`nestedDFSWF.go`. Proved by induction on `remaining` directly — matching
`nestedDFSWF.go`'s own plain structural recursion — rather than on `fuel` or
via a `.induct` principle. -/
theorem nestedDFS_fuel_go_eq_nestedDFSWF_go
    (remaining : List State) (st : FNDFSState State)
    (hfin : ∀ x, st.innerFinished.contains x → fr.univ.contains x)
    (hremaining : ∀ x ∈ remaining, fr.univ.contains x) :
    ∃ fuel result, nestedDFS_fuel.go succs isAccepting remaining st fuel = some result ∧
      result = nestedDFSWF.go succs fr isAccepting remaining st := by
  induction remaining generalizing st with
  | nil =>
    refine ⟨1, .empty st.outerVisited.size, nestedDFS_fuel_go_nil succs isAccepting st 0, ?_⟩
    unfold nestedDFSWF.go
    rfl
  | cons init rest ih =>
    have hinit : fr.univ.contains init := hremaining init (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, fr.univ.contains x :=
      fun x hx => hremaining x (List.mem_cons_of_mem _ hx)
    by_cases hvis : st.outerVisited.contains init = true
    · obtain ⟨fuel2, result2, heq2, heqC2⟩ := ih st hfin hrest
      refine ⟨fuel2 + 1, result2, ?_, ?_⟩
      · rw [nestedDFS_fuel_go_skip succs isAccepting init rest st fuel2 hvis]
        exact heq2
      · unfold nestedDFSWF.go
        simp only [hvis]
        exact heqC2
    · simp only [Bool.not_eq_true] at hvis
      let st2 := { st with outerVisited := st.outerVisited.insert init }
      have hfin2 : ∀ x, st2.innerFinished.contains x → fr.univ.contains x := hfin
      have hstack_states : ∀ p ∈ [(init, (succs init).toList)], fr.univ.contains p.1 :=
        fun p hp => by rw [List.mem_singleton] at hp; subst hp; exact hinit
      have hstack_remaining :
          ∀ p ∈ [(init, (succs init).toList)], ∀ x ∈ p.2, x ∈ succs p.1 :=
        fun p hp x hx => by
          rw [List.mem_singleton] at hp; subst hp; exact Array.mem_toList_iff.mp hx
      obtain ⟨fuelI, resultI, stI, heqI, hfinI, heqCI⟩ :=
        outerDFSLoop_fuel_eq_outerDFSLoopWF succs fr isAccepting [(init, (succs init).toList)]
          [init] st2 hfin2 hstack_states hstack_remaining
      cases resultI with
      | nonEmpty stem loop =>
        refine ⟨fuelI + 1, .nonEmpty stem loop, ?_, ?_⟩
        · exact nestedDFS_fuel_go_nonEmpty succs isAccepting init rest st fuelI hvis stem loop stI
            heqI
        · unfold nestedDFSWF.go
          have heqCI' : (EmptinessResult.nonEmpty stem loop, stI) =
              outerDFSLoopWF succs isAccepting fr [(init, (succs init).toList)] [init]
                { st with outerVisited := st.outerVisited.insert init } := by
            simpa only [st2] using heqCI
          rw [if_neg (by simp [hvis])]
          show EmptinessResult.nonEmpty stem loop =
              match outerDFSLoopWF succs isAccepting fr [(init, (succs init).toList)] [init]
                  { st with outerVisited := st.outerVisited.insert init } with
              | (EmptinessResult.nonEmpty stem loop, _) => EmptinessResult.nonEmpty stem loop
              | (EmptinessResult.empty _, st') => nestedDFSWF.go succs fr isAccepting rest st'
          rw [← heqCI']
      | empty m =>
        obtain ⟨fuelR, resultR, heqR, heqCR⟩ := ih stI hfinI hrest
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

/-- Top-level bridge: for well-founded-reachable `initialStates`, there is a
fuel value for which `nestedDFS_fuel` succeeds and agrees exactly with
`nestedDFSWF`. -/
theorem nestedDFS_fuel_eq_nestedDFSWF
    (initialStates : List State)
    (hinitial : ∀ x ∈ initialStates, fr.univ.contains x) :
    ∃ fuel, nestedDFS_fuel initialStates succs isAccepting fuel =
      some (nestedDFSWF succs fr isAccepting initialStates) := by
  unfold nestedDFS_fuel nestedDFSWF
  obtain ⟨fuel, result, heq, heqC⟩ :=
    nestedDFS_fuel_go_eq_nestedDFSWF_go succs fr isAccepting initialStates
      { outerVisited := Std.HashSet.emptyWithCapacity 1024
        innerFinished := Std.HashSet.emptyWithCapacity 1024 }
      (fun x hx => absurd hx (by simp [Std.HashSet.contains_emptyWithCapacity])) hinitial
  exact ⟨fuel, heqC ▸ heq⟩

/-- `nestedDFSWF`'s `.empty` case implies no accepting cycle exists — the
well-founded mirror of `nestedDFS_fuel_empty_no_cycle`, obtained for free by
transporting across `nestedDFS_fuel_eq_nestedDFSWF`. -/
theorem nestedDFSWF_empty_no_cycle
    (initialStates : List State) (n : Nat)
    (hinitial : ∀ x ∈ initialStates, fr.univ.contains x)
    (h : nestedDFSWF succs fr isAccepting initialStates = .empty n) :
    ¬∃ _ac : AcceptingCycle initialStates succs isAccepting, True := by
  obtain ⟨fuel, heq⟩ := nestedDFS_fuel_eq_nestedDFSWF succs fr isAccepting initialStates hinitial
  rw [h] at heq
  exact nestedDFS_fuel_empty_no_cycle heq

/-- `nestedDFSWF`'s `.nonEmpty` case yields a genuine accepting-cycle witness
— the well-founded mirror of `nestedDFS_fuel_nonEmpty_valid`. -/
theorem nestedDFSWF_nonEmpty_valid
    (initialStates : List State) (stem loop : List State)
    (hinitial : ∀ x ∈ initialStates, fr.univ.contains x)
    (h : nestedDFSWF succs fr isAccepting initialStates = .nonEmpty stem loop) :
    ∃ ac : AcceptingCycle initialStates succs isAccepting,
      ac.stem = stem ∧ ac.cycle = loop.tail := by
  obtain ⟨fuel, heq⟩ := nestedDFS_fuel_eq_nestedDFSWF succs fr isAccepting initialStates hinitial
  rw [h] at heq
  exact nestedDFS_fuel_nonEmpty_valid heq

end TopLevelFuelBridge

section EmptinessCheckerInterface

/-! ## `nestedDFSWF` as an `EmptinessChecker` instance

`EmptinessChecker` itself (the algorithm-agnostic `find_ce_spec`-style
contract) now lives in `EmptinessCheck.lean`, alongside
`EmptinessResult`/`AcceptingCycle`/`FiniteReach` — imported transitively via
`NestedDFSCorrectness.lean`/`NestedDFS.lean`. What belongs here, in the
nested-DFS-specific file, is just this one concrete instance of it. -/

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-- `nestedDFSWF` packaged as an `EmptinessChecker` instance — the (so far)
only refinement of the contract in `EmptinessCheck.lean`. Corresponds to
CAVA's `find_ce_impl` being proven to refine `find_ce_spec`. -/
def nestedDFSChecker : EmptinessChecker State where
  check := nestedDFSWF
  nonEmpty_valid := fun {succs fr isAccepting initialStates stem loop} hinit h =>
    nestedDFSWF_nonEmpty_valid succs fr isAccepting initialStates stem loop hinit h
  empty_no_cycle := fun {succs fr isAccepting initialStates n} hinit h =>
    nestedDFSWF_empty_no_cycle succs fr isAccepting initialStates n hinit h

end EmptinessCheckerInterface

section BAFiniteReach

/-! ## Packaging a `FiniteReach` witness from `BA.WellFormed`

Matches CAVA's own two-layer split noted above under "Should the old
`partial def innerDFS`/... be deleted?": `nested_dfs_code`'s precondition is
an explicit `ASSERT (fb_graph G)` threaded through as an argument-level
assumption, never internally re-derived (`Nested_DFS.thy`) — exactly the
role `FiniteReach succs` plays for `nestedDFSWF`. Here, `BA.WellFormed`
(`BA.lean`) supplies exactly the closure fact `FiniteReach.closed` needs,
with `univ := ba.states`; nothing about *why* `ba` is well-formed is needed
at this layer, only the two `WellFormed` fields themselves (which, for a
`BA` produced by `GBA.degeneralize` from a well-formed `GBA`, come from
`degeneralize_wellFormed`; for `constructGBA`'s own `GBA`, from
`constructGBA_wellFormed`). -/

variable {α : Type u} [BEq α] [Hashable α]

/-- A well-formed `BA`'s own state set is a `FiniteReach` witness for its
`getSuccessors` function. -/
def BA.finiteReach (ba : BA α) (hwf : ba.WellFormed) : FiniteReach ba.getSuccessors where
  univ := ba.states
  closed s hs t ht := hwf.succ_mem s t hs ht

/-- A well-formed `BA`'s initial states all lie in its own `finiteReach`
witness's universe — the `hinitial` hypothesis every `nestedDFSWF` call
needs. -/
theorem BA.initialStates_subset_finiteReach (ba : BA α) (hwf : ba.WellFormed) :
    ∀ x ∈ ba.initialStates.toList, (ba.finiteReach hwf).univ.contains x :=
  fun x hx => hwf.initial_mem x (Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hx))

end BAFiniteReach

section PumpingLemma

/-! ## From an accepting run to an `AcceptingCycle`

The reverse direction `nestedDFSWF_empty_no_cycle`/`nestedDFSWF_nonEmpty_valid`
don't give: those connect `nestedDFSWF`'s *output* to a graph-cycle witness,
but say nothing about whether "no accepting cycle" actually implies "no
accepting infinite run" of the underlying automaton. CAVA needs exactly this
too — not inside `blue_dfs_correct` itself (which, like our
`nestedDFSWF_empty_no_cycle`, is stated purely at the graph-cycle level), but
one layer out, when assembling a genuinely usable decision procedure:
`CAVA_Impl.thy`'s `ndfs_find_ce` (which has to satisfy the *run*-level
`find_ce_spec` contract) explicitly invokes `gb_graph.accepted_lasso`
(`CAVA_Automata/Lasso.thy`):
```isabelle
lemma accepted_lasso:
  assumes "finite (E⇧* `` V0)" and A: "is_acc_run r"
  shows "∃L. is_lasso L"
```
proved via CAVA's abstract `limit`/`ipath` machinery (a state visited
infinitely often exists by pigeonhole on the finite reachable set; any two
`limit`-points are connected by a path since the run passes through both
infinitely often).

This port takes a more concrete route, avoiding CAVA's `limit`/`ipath`
abstractions entirely: since we only ever need this for a *single*
acceptance set (`AcceptingCycle`/`OASpec _ _ 1`, never the general `igb_graph`
case), the argument reduces to finding *one* accepting state that repeats —
a finite pigeonhole on an explicit prefix of length `univ.size + 1`, not an
argument about the infinite limit set. Concretely: sample the run at
`univ.size + 1` increasing accepting-visit indices; since all these visited
states lie in the finite `univ`, two of them must coincide (pigeonhole);
the run segment between those two repeated indices is *exactly* the cycle,
by construction (each step is a genuine `succs`-edge, since it comes from
`σ`'s own transition hypothesis). -/

variable {State : Type u}

/-- An increasing sequence of indices at which `σ` is accepting, built by
repeatedly re-invoking `hacc` past the previous index. Classical/noncomputable
(existence witnesses only, never executed). -/
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

/-- Pigeonhole: among `univ.size + 1` states all drawn from `univ`, two
coincide. Proved by threading an accumulator `HashSet` through the sampled
prefix and using `HashSet.size_le_of_subset` for the base case where no
duplicate was ever found. -/
private theorem exists_dup_of_size_lt [BEq State] [Hashable State] [LawfulBEq State]
    [LawfulHashable State] (univ : Std.HashSet State) (f : Nat → State)
    (hmem : ∀ k, univ.contains (f k) = true) :
    ∃ i j, i < j ∧ j ≤ univ.size ∧ f i = f j := by
  suffices h : ∀ k, (∃ i j, i < j ∧ j ≤ k ∧ f i = f j) ∨
      ∃ acc : Std.HashSet State, acc.size = k + 1 ∧
        (∀ x, acc.contains x → univ.contains x) ∧
        (∀ x, acc.contains x → ∃ i ≤ k, f i = x) by
    rcases h univ.size with h1 | ⟨acc, hsize, hsub, _⟩
    · exact h1
    · exact absurd (HashSet.size_le_of_subset hsub) (by omega)
  intro k
  induction k with
  | zero =>
    right
    refine ⟨Std.HashSet.emptyWithCapacity 1 |>.insert (f 0),
      by simp [Std.HashSet.size_insert, Std.HashSet.size_emptyWithCapacity], ?_, ?_⟩
    · intro x hx
      simp only [Std.HashSet.contains_insert, Std.HashSet.contains_emptyWithCapacity,
        Bool.or_false] at hx
      exact (LawfulBEq.eq_of_beq hx) ▸ hmem 0
    · intro x hx
      simp only [Std.HashSet.contains_insert, Std.HashSet.contains_emptyWithCapacity,
        Bool.or_false] at hx
      exact ⟨0, Nat.le_refl 0, LawfulBEq.eq_of_beq hx⟩
  | succ k ih =>
    rcases ih with ⟨i, j, hij, hjk, heq⟩ | ⟨acc, hsize, hsub, hall⟩
    · exact Or.inl ⟨i, j, hij, by omega, heq⟩
    · by_cases hdup : acc.contains (f (k + 1)) = true
      · obtain ⟨i', hi'k, hi'⟩ := hall (f (k + 1)) hdup
        exact Or.inl ⟨i', k + 1, by omega, by omega, hi'⟩
      · right
        refine ⟨acc.insert (f (k + 1)), ?_, ?_, ?_⟩
        · rw [Std.HashSet.size_insert,
            if_neg (by rw [Std.HashSet.mem_iff_contains]; exact hdup)]
          omega
        · intro x hx
          simp only [Std.HashSet.contains_insert] at hx
          rcases (Bool.or_eq_true _ _).mp hx with h | h
          · exact (LawfulBEq.eq_of_beq h) ▸ hmem (k + 1)
          · exact hsub x h
        · intro x hx
          simp only [Std.HashSet.contains_insert] at hx
          rcases (Bool.or_eq_true _ _).mp hx with h | h
          · exact ⟨k + 1, Nat.le_refl _, LawfulBEq.eq_of_beq h⟩
          · obtain ⟨i, hik, hi⟩ := hall x h
            exact ⟨i, by omega, hi⟩

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

/-- The reverse direction of `nestedDFSWF_empty_no_cycle`/
`nestedDFS_fuel_empty_no_cycle`: an accepting run yields an `AcceptingCycle`
witness. Direct analogue of CAVA's `gb_graph.accepted_lasso`
(`CAVA_Automata/Lasso.thy`), specialized to a single acceptance set and
proved via the finite pigeonhole above rather than the general `limit`/
`ipath` machinery. -/
theorem exists_acceptingCycle_of_run [BEq State] [Hashable State] [LawfulBEq State]
    [LawfulHashable State]
    {succs : State → Array State} {isAccepting : State → Bool}
    {initialStates : List State} (fr : FiniteReach succs)
    (hinitial : ∀ x ∈ initialStates, fr.univ.contains x)
    {σ : Nat → State} (hinit : σ 0 ∈ initialStates)
    (htrans : ∀ n, σ (n + 1) ∈ succs (σ n))
    (hacc : ∀ N, ∃ n ≥ N, isAccepting (σ n) = true) :
    ∃ _ac : AcceptingCycle initialStates succs isAccepting, True := by
  have hmem : ∀ n, fr.univ.contains (σ n) = true := by
    intro n
    induction n with
    | zero => exact hinitial _ hinit
    | succ n ih => exact fr.closed _ ih _ (htrans n)
  obtain ⟨i, j, hij, _, heq⟩ := exists_dup_of_size_lt fr.univ
    (fun k => σ (accIdxSeq σ isAccepting hacc k)) (fun k => hmem _)
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
      simpa using htrans (p + i)
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
