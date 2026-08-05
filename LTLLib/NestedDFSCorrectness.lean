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

/-! ### Closure lemmas (Lean port of CAVA's `closed_restrict_aux`/`rel_restrict_tranclI`)

    These let us upgrade a *restricted* no-cycle fact (no path through
    never-blocked intermediates) into an *unrestricted* one (no path at all),
    given that the blocking set is closed under `succs`. This is the key step
    in the CVWY/Schwoon-Esparza argument that doesn't reduce to a simple
    monotonicity/weakening fact. -/

/-- If `F` is closed under `succs` and `s ∈ F`, any unrestricted path from `s`
    stays entirely inside `F` — in particular its endpoint is in `F`. -/
theorem PathTo.mem_of_closed {succs : State → Array State} {F : State → Prop}
    (hclosed : ∀ s, F s → ∀ t, t ∈ succs s → F t) :
    ∀ {s t : State}, PathTo succs (fun _ => False) s t → F s → F t := by
  intro s t h
  induction h with
  | direct ht => exact fun hFs => hclosed _ hFs _ ht
  | through hmid _ _ ih => exact fun hFs => ih (hclosed _ hFs _ hmid)

/-- An unrestricted path from a state outside a closed set `F` to another state
    outside `F` must avoid `F` entirely, i.e. is also a path restricted to
    avoid `F`. This is the bridge lemma: combined with `s = t` and a
    restricted no-cycle fact, it yields the unrestricted no-cycle fact. -/
theorem PathTo.of_unrestricted_avoiding_closed {succs : State → Array State}
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

/-- No self-cycle through a closed set's complement, plus the set being closed
    and the state itself not being in the set, implies no self-cycle at all. -/
theorem PathTo.no_self_loop_of_closed {succs : State → Array State}
    {F : State → Prop} (hclosed : ∀ s, F s → ∀ t, t ∈ succs s → F t)
    {s : State} (hnotF_s : ¬F s)
    (hno_restricted : ¬PathTo succs (fun x => F x) s s) :
    ¬PathTo succs (fun _ => False) s s :=
  fun h => hno_restricted (PathTo.of_unrestricted_avoiding_closed hclosed hnotF_s h hnotF_s)

/-! ### A second closure upgrade, for when `s ∈ F` is unavoidable

    `PathTo.no_self_loop_of_closed` needs `s ∉ F`, but for `F := innerFinished`
    right after `s`'s own successful inner-DFS call, `s` is *always* in `F`
    (that's the whole point of the call). The fix: instead of "`s ∉ F`",
    it's enough that *nothing in `F` has an edge back to `s`* — a weaker,
    differently-shaped fact, but one inner DFS gives us for a different
    reason (its own `succ == seed` check). -/

/-- If nothing in the closed set `F` has an edge to `t`, then `F` can't be
    re-entered from a member and still reach `t` — reaching `t` from an
    `F`-member is impossible outright. -/
theorem PathTo.false_of_mem_closed_reaches {succs : State → Array State}
    {F : State → Prop} (hclosed : ∀ s, F s → ∀ t ∈ succs s, F t)
    {t : State} (hno_edge : ∀ x, F x → t ∉ succs x) :
    ∀ {mid : State}, PathTo succs (fun _ => False) mid t → F mid → False := by
  intro mid h
  induction h with
  | @direct mid t ht => exact fun hFmid => hno_edge mid hFmid ht
  | @through mid mid2 t hmid2 _ hrest ih =>
    exact fun hFmid => ih hno_edge (hclosed mid hFmid mid2 hmid2)

/-- An unrestricted path to `t`, given nothing in the closed set `F` has an
    edge to `t`, is automatically `F`-avoiding: it can never dip into `F`,
    since doing so would trap it there (closedness) and it could never reach
    `t` again (`hno_edge`). -/
theorem PathTo.avoids_closed_of_no_incoming {succs : State → Array State}
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

/-- The upgrade actually needed in Phase D.1: `s` need not be outside the
    closed set `F` — it's enough that nothing in `F` has an edge back to `s`. -/
theorem PathTo.no_self_loop_of_closed_no_incoming {succs : State → Array State}
    {F : State → Prop} (hclosed : ∀ s, F s → ∀ t ∈ succs s, F t)
    {s : State} (hno_edge : ∀ x, F x → s ∉ succs x)
    (hno_restricted : ¬PathTo succs (fun x => F x) s s) :
    ¬PathTo succs (fun _ => False) s s :=
  fun h => hno_restricted (PathTo.avoids_closed_of_no_incoming hclosed hno_edge h)

/-- Generalizes `no_self_loop_of_closed_no_incoming` from a fixed self-loop
    target to an arbitrary target `t`. Needed for the Holzmann-Peled-
    Yannakakis inner-DFS shortcut: the widened stop condition gives a "no
    reach to any cyan/stack state" fact directly (CAVA's `restr_invar`, which
    is stated for the whole stack at once), rather than only a self-loop
    fact that then needs a separate `ReachChain`-based composition to reach
    the rest of the stack. -/
theorem PathTo.no_reach_of_closed_no_incoming {succs : State → Array State}
    {F : State → Prop} (hclosed : ∀ s, F s → ∀ t ∈ succs s, F t)
    {s t : State} (hno_edge : ∀ x, F x → t ∉ succs x)
    (hno_restricted : ¬PathTo succs (fun x => F x) s t) :
    ¬PathTo succs (fun _ => False) s t :=
  fun h => hno_restricted (PathTo.avoids_closed_of_no_incoming hclosed hno_edge h)

/-- Unrestricted `PathTo` is transitive. Used to compose "s can reach t" facts,
    e.g. an ancestor's tree-path down to a descendant, with a descendant's
    discovered back-edge, into a single self-loop witness. -/
theorem PathTo.trans {succs : State → Array State} {s t u : State}
    (h1 : PathTo succs (fun _ => False) s t) :
    PathTo succs (fun _ => False) t u → PathTo succs (fun _ => False) s u := by
  induction h1 with
  | direct ht => intro h2; exact .through ht (fun h => h) h2
  | through hmid _ _ ih => intro h2; exact .through hmid (fun h => h) (ih h2)

/-- Lean port of CAVA's `closed_restrict_aux`: if `F`'s successors stay in
    `F ∪ S`, and nothing reachable from `x` (inclusive) escapes into `S`,
    then everything reachable from `x` (an `F`-member) stays in `F`. This
    handles "extend visitedness along an arbitrary witnessed path" in one
    shot, rather than needing bespoke induction at each use site. -/
theorem PathTo.closed_of_no_escape {succs : State → Array State} {F S : State → Prop}
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

/-- An index-based chain condition (as used by `AcceptingCycle.stem_chain`/
    `cycle_chain`) gives a `PathTo` witness from the list's head to its last
    element — or an equality, if the list is a singleton. -/
theorem chain_reaches {succs : State → Array State} (l : List State)
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    ∀ (hne : l ≠ []), l.head hne = l.getLast hne ∨
      PathTo succs (fun _ => False) (l.head hne) (l.getLast hne) := by
  induction l with
  | nil => intro hne; exact absurd rfl hne
  | cons a t ih =>
    intro _
    cases t with
    | nil => left; rfl
    | cons b t' =>
      right
      have hab : b ∈ succs a := by
        have h0 := hchain 0 (by simp)
        simpa using h0
      have hchain_tail : ∀ i, (hi : i + 1 < (b :: t').length) →
          (b :: t')[i+1] ∈ succs (b :: t')[i] := by
        intro i hi
        have h1 := hchain (i + 1) (by simpa using hi)
        simpa using h1
      have hhead : (a :: b :: t').head (by simp) = a := rfl
      have hgetlast : (a :: b :: t').getLast (by simp) = (b :: t').getLast (by simp) :=
        List.getLast_cons (by simp)
      rw [hhead, hgetlast]
      rcases ih hchain_tail (by simp) with heq | hp
      · exact heq ▸ PathTo.direct hab
      · exact PathTo.trans (PathTo.direct hab) hp

/-- Dropping the last element of a `succs`-chain list leaves a `succs`-chain. -/
theorem chain_dropLast {succs : State → Array State} (l : List State)
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    ∀ i, (hi : i + 1 < l.dropLast.length) → l.dropLast[i+1] ∈ succs l.dropLast[i] := by
  intro i hi
  have hi' : i + 1 < l.length := by
    have hlen := List.length_dropLast (xs := l)
    omega
  have e1 : l.dropLast[i] = l[i]'(by omega) := List.getElem_dropLast (by omega)
  have e2 : l.dropLast[i+1] = l[i+1]'hi' := List.getElem_dropLast (by omega)
  rw [e1, e2]
  exact hchain i hi'

/-- Appending a genuine successor of a chain's last element to a `succs`-chain
    keeps it a `succs`-chain. -/
theorem chain_append_singleton {succs : State → Array State} (l : List State) (x : State)
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i])
    (hne : l ≠ []) (hedge : x ∈ succs (l.getLast hne)) :
    ∀ i, (hi : i + 1 < (l ++ [x]).length) → (l ++ [x])[i+1] ∈ succs (l ++ [x])[i] := by
  have hlen : (l ++ [x]).length = l.length + 1 := by simp
  intro i hi
  by_cases hlt : i + 1 < l.length
  · have e1 : (l ++ [x])[i] = l[i]'(by omega) := List.getElem_append_left (by omega)
    have e2 : (l ++ [x])[i+1] = l[i+1]'(by omega) := List.getElem_append_left (by omega)
    rw [e1, e2]
    exact hchain i (by omega)
  · have hi1 : i + 1 = l.length := by omega
    have e1 : (l ++ [x])[i] = l[i]'(by omega) := List.getElem_append_left (by omega)
    have e2 : (l ++ [x])[i+1] = x := by simp [hi1]
    rw [e1, e2]
    have hlast : l[i]'(by omega) = l.getLast hne := by
      rw [List.getLast_eq_getElem]
      congr 1
      omega
    rw [hlast]
    exact hedge

/-- Prepending a state with an edge into a chain-list's head keeps it a
    `succs`-chain. -/
theorem chain_cons {succs : State → Array State} (a : State) (l : List State)
    (hne : l ≠ [])
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i])
    (hedge : l.head hne ∈ succs a) :
    ∀ i, (hi : i + 1 < (a :: l).length) → (a :: l)[i+1] ∈ succs (a :: l)[i] := by
  intro i hi
  cases i with
  | zero => simpa [List.head_eq_getElem] using hedge
  | succ k =>
    have hk : k + 1 < l.length := by simpa using hi
    simpa using hchain k hk

/-- Dropping the head of a `succs`-chain list leaves a `succs`-chain (index
    version, sibling of `ReachChain.tail`). -/
private theorem chain_tail {succs : State → Array State} (a : State) (l : List State)
    (hchain : ∀ i, (hi : i + 1 < (a :: l).length) → (a :: l)[i+1] ∈ succs (a :: l)[i]) :
    ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i] := by
  intro i hi
  have h := hchain (i + 1) (by simpa using hi)
  simpa using h

/-- Concatenating two `succs`-chains with a boundary edge from the first's
    last element to the second's head gives a `succs`-chain over the
    concatenation. Needed for the Holzmann-Peled-Yannakakis inner-DFS
    shortcut's witness construction: splicing the path `innerDFS` found with
    a stack tree-path segment (cf. `chain_append_singleton`, the special case
    where the second list is a singleton). Proved by induction on `l1`
    (rather than raw index arithmetic) to avoid rewriting inside a
    `getElem`/`head`/`getLast` proof-argument position — the same class of
    Lean dependent-rewrite trap documented elsewhere in this file's history. -/
theorem chain_append {succs : State → Array State} (l1 l2 : List State)
    (hchain1 : ∀ i, (hi : i + 1 < l1.length) → l1[i+1] ∈ succs l1[i])
    (hchain2 : ∀ i, (hi : i + 1 < l2.length) → l2[i+1] ∈ succs l2[i])
    (hne1 : l1 ≠ []) (hne2 : l2 ≠ [])
    (hedge : l2.head hne2 ∈ succs (l1.getLast hne1)) :
    ∀ i, (hi : i + 1 < (l1 ++ l2).length) → (l1 ++ l2)[i+1] ∈ succs (l1 ++ l2)[i] := by
  induction l1 with
  | nil => exact absurd rfl hne1
  | cons a as ih =>
    cases as with
    | nil =>
      simp only [List.getLast_singleton] at hedge
      simpa using chain_cons a l2 hne2 hchain2 hedge
    | cons b bs =>
      have hasne : (b :: bs : List State) ≠ [] := by simp
      have hgetlast_eq : (a :: b :: bs).getLast (by simp) = (b :: bs).getLast hasne :=
        List.getLast_cons hasne
      rw [hgetlast_eq] at hedge
      have hchain_as : ∀ i, (hi : i + 1 < (b :: bs).length) →
          (b :: bs)[i+1] ∈ succs (b :: bs)[i] := chain_tail a (b :: bs) hchain1
      have hrec := ih hchain_as hasne hedge
      have hab : b ∈ succs a := by simpa using hchain1 0 (by simp)
      simpa using chain_cons a ((b :: bs) ++ l2) (by simp) hrec (by simpa using hab)

/-- A `take n` prefix of a `succs`-chain list is itself a `succs`-chain.
    Needed for the Schwoon-Esparza back-edge shortcut: slicing `pathStack` at
    the back-edge target's index keeps the prefix a valid chain (cf. CAVA's
    `takeWhileNot v` in `se_back_edge_lasso_inv`, `Nested_DFS.thy:494` — we use
    an explicit index instead of a predicate to stay clear of a Lean
    dependent-rewrite trap under `takeWhile`'s recursive unfolding). -/
theorem chain_take {succs : State → Array State} (l : List State) (n : Nat)
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    ∀ i, (hi : i + 1 < (l.take n).length) → (l.take n)[i+1] ∈ succs (l.take n)[i] := by
  intro i hi
  have hi' : i + 1 < l.length := by
    have hlen : (l.take n).length ≤ l.length := by simp only [List.length_take]; omega
    omega
  have e1 : (l.take n)[i] = l[i]'(by omega) := List.getElem_take
  have e2 : (l.take n)[i+1] = l[i+1]'hi' := List.getElem_take
  rw [e1, e2]
  exact hchain i hi'

/-- A `drop n` suffix of a `succs`-chain list is itself a `succs`-chain.
    Needed for the Schwoon-Esparza back-edge shortcut: slicing `pathStack` at
    the back-edge target's index keeps the suffix a valid chain (cf. CAVA's
    `dropWhileNot v` in `se_back_edge_lasso_inv`, `Nested_DFS.thy:495`). -/
theorem chain_drop {succs : State → Array State} (l : List State) (n : Nat)
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    ∀ i, (hi : i + 1 < (l.drop n).length) → (l.drop n)[i+1] ∈ succs (l.drop n)[i] := by
  intro i hi
  have hbound : n + i + 1 < l.length := by
    have hlen : (l.drop n).length = l.length - n := by simp
    omega
  have e1 : (l.drop n)[i] = l[n+i]'(by omega) := List.getElem_drop
  have e2 : (l.drop n)[i+1] = l[n+i+1]'hbound := List.getElem_drop
  rw [e1, e2]
  exact hchain (n + i) hbound

/-- The left part of an append-split `succs`-chain is itself a `succs`-chain.
    Takes the split as an explicit hypothesis (rather than requiring the
    caller to cast an existing chain fact along an equation) to sidestep a
    Lean dependent-rewrite trap: `subst`-ing the split *before* inducting
    avoids ever rewriting inside the chain fact's own `∀`-quantified type. -/
theorem chain_append_left {succs : State → Array State} (l a b : List State)
    (heq : l = a ++ b)
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    ∀ i, (hi : i + 1 < a.length) → a[i+1] ∈ succs a[i] := by
  subst heq
  induction a with
  | nil => simp
  | cons x xs ih =>
    intro i hi
    cases i with
    | zero =>
      have hxs0 : 0 < xs.length := by simpa using hi
      have h := hchain 0 (by simp only [List.length_cons, List.length_append]; omega)
      have e : (xs ++ b)[0]'(by simp; omega) = xs[0]'hxs0 := List.getElem_append_left hxs0
      simpa [e] using h
    | succ k =>
      have hk : k + 1 < xs.length := by simpa using hi
      exact ih (chain_tail x (xs ++ b) hchain) k hk

/-- The right part of an append-split `succs`-chain is itself a `succs`-chain.
    Same rationale for the explicit `heq` parameter as `chain_append_left`. -/
theorem chain_append_right {succs : State → Array State} (l a b : List State)
    (heq : l = a ++ b)
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    ∀ i, (hi : i + 1 < b.length) → b[i+1] ∈ succs b[i] := by
  subst heq
  induction a with
  | nil => simpa using hchain
  | cons x xs ih => exact ih (chain_tail x (xs ++ b) hchain)

/-- The edge closing off a chain-list's last step: if `l ≠ []` and
    `l.dropLast ≠ []`, the chain property at the second-to-last index gives
    exactly `l.getLast ∈ succs (l.dropLast.getLast)`. Needed for the
    Schwoon-Esparza back-edge shortcut's "source accepting" case: closes the
    cycle `current :: (loop-tail)` back to `current`. -/
theorem chain_getLast_edge {succs : State → Array State} (l : List State)
    (hne : l ≠ []) (hne' : l.dropLast ≠ [])
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    l.getLast hne ∈ succs (l.dropLast.getLast hne') := by
  have hlen : l.dropLast.length ≥ 1 := List.length_pos_iff.mpr hne'
  have hlen2 : l.length ≥ 2 := by
    have := List.length_dropLast (xs := l)
    omega
  have hdlen : l.dropLast.length = l.length - 1 := List.length_dropLast (xs := l)
  have e1 : l.dropLast.getLast hne' = l[l.length - 2]'(by omega) := by
    rw [List.getLast_eq_getElem, List.getElem_dropLast]
    congr 1
    omega
  have e2 : l.getLast hne = l[l.length - 1]'(by omega) := List.getLast_eq_getElem ..
  rw [e1, e2]
  have hstep := hchain (l.length - 2) (by omega)
  simpa [show l.length - 2 + 1 = l.length - 1 from by omega] using hstep

/-- The edge across an append boundary: if `l = a ++ b` with both `a` and `b`
    nonempty, the chain property at the boundary index gives exactly
    `b.head ∈ succs (a.getLast)`. Needed for the Schwoon-Esparza back-edge
    shortcut's "target accepting" case: the edge from the stem's last state
    into the loop's first state. -/
theorem chain_append_boundary {succs : State → Array State} (l a b : List State)
    (heq : l = a ++ b) (ha : a ≠ []) (hb : b ≠ [])
    (hchain : ∀ i, (hi : i + 1 < l.length) → l[i+1] ∈ succs l[i]) :
    b.head hb ∈ succs (a.getLast ha) := by
  subst heq
  induction a with
  | nil => exact absurd rfl ha
  | cons x xs ih =>
    cases xs with
    | nil =>
      have hbl : 0 < b.length := List.length_pos_iff.mpr hb
      have h0 := hchain 0 (by simp; omega)
      simpa [List.head_eq_getElem] using h0
    | cons y ys =>
      have hxsne : (y :: ys : List State) ≠ [] := by simp
      have hgetlast_eq : (x :: y :: ys).getLast (by simp) = (y :: ys).getLast hxsne := by
        simp [List.getLast_cons]
      rw [hgetlast_eq]
      exact ih hxsne (chain_tail x ((y :: ys) ++ b) hchain)

/-- If `x` occurs in `l`, dropping elements until the first occurrence of `x`
    leaves a list whose head is `x`. Needed to identify the Schwoon-Esparza
    back-edge target's position inside `pathStack`, mirroring CAVA's
    `dropWhileNot v` (`Nested_DFS.thy`). Proved at the `head?` (`Option`)
    level throughout to avoid a Lean dependent-rewrite trap under
    `dropWhile`'s recursive unfolding (cf. `chain_take`/`chain_drop`'s own
    workaround for the analogous issue). -/
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
      simp only [List.dropWhile_cons, hax', if_true]
      exact ih hxt

/-- A length-1 list's head and last element coincide. Needed for the
    Schwoon-Esparza back-edge shortcut's degenerate case (the sliced cycle
    has only one state left). -/
theorem head_eq_getLast_of_length_eq_one {α : Type u} (l : List α) (hl : l.length = 1)
    (hne : l ≠ []) : l.head hne = l.getLast hne := by
  cases l with
  | nil => simp at hl
  | cons a t =>
    have ht : t = [] := by simpa using hl
    subst ht
    rfl

/-- Dropping a list's last element doesn't change its head (when both are
    still nonempty). -/
theorem head_dropLast_eq {α : Type u} (l : List α) (hne : l ≠ [])
    (hpne : l.dropLast ≠ []) : l.dropLast.head hpne = l.head hne := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t =>
    cases t with
    | nil => exact absurd rfl hpne
    | cons b t' => rfl

/-- Appending to a nonempty list doesn't change its head. -/
theorem head_append_singleton_eq {α : Type u} (l : List α) (x : α) (hne : l ≠ []) :
    (l ++ [x]).head (by simp) = l.head hne := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t => rfl

/-- `ReachChain succs l` holds when every element of `l` can reach the
    *previous* element (i.e. reading left-to-right, later elements reach
    earlier ones). Used for the outer-DFS stack: with the top of the stack at
    the head, this says every ancestor can reach every one of its
    descendants further down the stack — exactly the tree-path fact that
    makes reaching an ancestor via inner DFS force a self-cycle. -/
def ReachChain (succs : State → Array State) : List State → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => PathTo succs (fun _ => False) b a ∧ ReachChain succs (b :: rest)

/-- Every element in the tail of a `ReachChain` can reach the head. -/
theorem ReachChain.reaches_head {succs : State → Array State} :
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
theorem ReachChain.tail {succs : State → Array State} (hd : State) (tl : List State)
    (h : ReachChain succs (hd :: tl)) : ReachChain succs tl := by
  cases tl with
  | nil => trivial
  | cons b rest => exact h.2

/-! ## NDFSState (fuel version) -/

/-- Mutable state for the nested DFS algorithm (mirroring the private version). -/
structure FNDFSState (State : Type u) [BEq State] [Hashable State] where
  outerVisited : Std.HashSet State
  innerFinished : Std.HashSet State

/-! ## Fuel-based inner DFS

The inner DFS searches for a path from `current` back to `seed` — or, with the
Holzmann-Peled-Yannakakis shortcut, back to *any* state on the outer DFS's
current call stack (`cyan`, CAVA's `Nested_DFS.thy:54,67-74`: `λx. x = u ∨ x ∈
cyan s`). It uses `innerVisited` to track states visited in this inner search,
and `innerFinished` (in `FNDFSState`) as a cross-call optimization: states
whose inner DFS already completed without finding a cycle. See
`NestedDFSPlan.md`'s "Holzmann-Peled-Yannakakis inner-DFS shortcut" section for
the full CAVA-correspondence write-up.

Cf. Schwoon & Esparza §3, "red DFS" in CAVA terminology. -/

/-- Result type for inner DFS: `none` = out of fuel. On success, `some (path,
    target)` records both the path found *and* which state in `{seed} ∪ cyan`
    was actually hit (CAVA's `Inr (vs, v)`). -/
abbrev InnerResult (State : Type u) [BEq State] [Hashable State] :=
  Option (Option (List State × State) × Std.HashSet State × FNDFSState State)

mutual
/-- Inner DFS with fuel. Returns `none` if fuel runs out.
    Corresponds to the "red DFS" in Schwoon & Esparza's color formulation. -/
def innerDFS_fuel [BEq State] [Hashable State] [LawfulBEq State]
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
def innerDFS_fuel_fold [BEq State] [Hashable State] [LawfulBEq State]
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
          match innerDFS_fuel succs current pathStack fuel current innerVisited st with
          | none => none
          | some (some (cyclePath, target), _, st') =>
            -- Holzmann-Peled-Yannakakis shortcut: `target` may be `current`
            -- itself or any other state on `pathStack`. When `target =
            -- current` this collapses to exactly the pre-HPY formula
            -- `current :: cyclePath` (the appended stack-suffix is `[]`) —
            -- no separate degenerate case needed, see `NestedDFSPlan.md`.
            let loopTail := (pathStack.dropWhile (fun y => !(y == target))).dropLast
            some (.nonEmpty pathStack (current :: cyclePath ++ loopTail), st')
          | some (none, _, st') =>
            outerDFSLoop_fuel succs isAccepting fuel rest pathStack.dropLast st'
        else
          outerDFSLoop_fuel succs isAccepting fuel rest pathStack.dropLast st
      | succ :: remainingTail =>
        let stack' := (current, remainingTail) :: rest
        if pathStack.contains succ then
          -- Schwoon-Esparza back-edge shortcut (`se_back_edge` in CAVA's
          -- `Nested_DFS.thy`): `succ` is cyan (currently on the outer stack),
          -- so a cycle can be reported directly, without launching innerDFS.
          if isAccepting current then
            if succ == current then
              -- degenerate case: current -> current is a literal self-loop.
              -- `loop.tail` (not `loop`) is the genuine cycle, matching the
              -- innerDFS-found case's convention (`loop = current ::
              -- cyclePath`, `cyclePath.head = current` already) — so `loop`
              -- itself carries one redundant leading copy of `current`.
              some (.nonEmpty pathStack [current, current], st)
            else
              let loopTail := (pathStack.dropWhile (fun y => !(y == succ))).dropLast
              some (.nonEmpty pathStack (current :: current :: loopTail), st)
          else if isAccepting succ then
            let stem := pathStack.takeWhile (fun y => !(y == succ)) ++ [succ]
            let loop := succ :: pathStack.dropWhile (fun y => !(y == succ))
            some (.nonEmpty stem loop, st)
          else
            outerDFSLoop_fuel succs isAccepting fuel stack' pathStack st
        else if st.outerVisited.contains succ then
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

/-! ## Accepting cycle definition

`AcceptingCycle` itself now lives in `EmptinessCheck.lean` — it's the
algorithm-agnostic "lasso" witness, not specific to nested DFS, so it moved
out alongside `EmptinessResult`/`FiniteReach`/`EmptinessChecker`. Imported
transitively via `NestedDFS.lean`. -/

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

/-- Monotonicity of `innerDFS_fuel`: the inner visited set and innerFinished
    set only grow across a call that returns `some`.
    Proved by induction on fuel, using `innerDFS_fuel_fold_mono_aux`.

    Cf. `red_dfs_inv` monotonicity in the CAVA Isabelle DFS framework. -/
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

/-- After `innerDFS_fuel_fold` returns `none` (no cycle), every successor in
    `remaining` is not `seed`, is not on `cyan` (Holzmann-Peled-Yannakakis: no
    successor is any outer-stack state either — CAVA's `restr_invar`'s
    `R' ∩ Collect P = {}`, `Nested_DFS.thy:155-159,222-226`), and is blocked
    in the output state.

    This is the "complete exploration" property: every successor was either
    already blocked, or was recursively explored and added to `iv'`.
    Corresponds to the invariant that all red-DFS successors end up red or
    pink (Schwoon & Esparza §3, van de Pol (2015) invariant R2). -/
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

/-- Key theorem: when inner DFS is called from the outer DFS on an accepting
    seed with an empty `innerVisited` and returns `none`, the seed cannot reach
    itself through non-blocked intermediates.

    Precondition: seed is NOT already in `innerFinished` (guaranteed by the
    outer DFS invariant — seed is still on the stack when inner DFS is called).

    This is the direct consequence used by the outer DFS correctness argument.
    Cf. Schwoon & Esparza §3, Lemma 1: after red DFS from seed returns
    without finding a cycle, seed is not reachable from itself through
    unfinished states. -/
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

/-- After fold returns none, all states in iv' that are NOT in iv
    are in st'.innerFinished. -/
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

/-- After innerDFS from seed with empty iv returns none,
    seed has no self-cycle through st'.innerFinished.
    This strengthens `innerDFS_no_cycle_from_seed` by eliminating
    the iv' component from isBlocked, using iv' ⊆ ifin'. -/
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
    the fold (added to `iv` since the call started) has *all* its successors
    blocked in the output state — not just `current`'s own direct successors
    (`innerDFS_fuel_fold_succs_blocked` above only covers `remaining`), but
    transitively every state the recursion visited. Same fuel/fold
    double-induction template as `fold_iv_subset_finished_aux`. -/
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
    call (added to `iv`) has all its successors blocked by the end. Combines
    `innerDFS_fuel_fold_succs_blocked` (for `current`'s own direct successors)
    with `fold_new_succs_blocked_aux` (for everything visited transitively). -/
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

/-- Converse of `fold_iv_subset_finished_aux`: `innerFinished` only ever grows
    by states that were already in `iv` (the fold's `current` argument is the
    only thing inserted into `innerFinished`, and it's always already in `iv`
    by the time the fold's nil case is reached — see `innerDFS_fuel`'s
    definition, which inserts `current` into `iv` before ever calling the
    fold). Needs `iv.contains current` as an explicit precondition, since
    that's a fact about *how* the fold is invoked, not part of its type. -/
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
    already being closed to conclude the new `innerFinished` is closed too.
    This is the Lean analogue of CAVA's `red_closed`. -/
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

/-- Inner DFS never touches `outerVisited` — only `innerFinished` is ever
    updated (the fold's nil case, `{st with innerFinished := ...}`). Needed to
    know the outer-DFS bookkeeping invariant (`OuterReachClosed`) survives an
    inner-DFS call unchanged. -/
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

/-- After `innerDFS_fuel_fold` returns `none`, no state newly visited during
    the fold has `seed`, or any `cyan` state (Holzmann-Peled-Yannakakis), as a
    successor — if it did, the fold's own widened `if succ == seed ||
    cyan.contains succ then FOUND` check would have fired the moment it was
    reached, and the whole call would have returned `some (...)`, not
    `none`. -/
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
    call has `seed`, or any `cyan` state, as a successor. Combines the
    top-level `current`'s own successor list (via
    `innerDFS_fuel_fold_succs_blocked`) with everything visited transitively
    (via `fold_new_no_edge_to_seed_aux`). Needed to show nothing in the
    resulting `innerFinished` has an edge back to `seed`/`cyan`, the key fact
    `PathTo.no_self_loop_of_closed_no_incoming` needs — the Lean analogue of
    CAVA's `restr_invar`'s `R' ∩ Collect P = {}` clause
    (`Nested_DFS.thy:155-159,222-226`). -/
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
    call is reachable from `current`. Needed to show ancestors of `current`
    (which, via `ReachChain`, reach `current` back down the outer stack)
    cannot become newly finished during `current`'s own inner-DFS call —
    otherwise composing the two paths would give `current` a self-loop,
    contradicting the very fact this call establishes. -/
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
    the state actually hit (`target`, CAVA's `v` in `Inr (vs, v)`). This is
    the Lean analogue of the `finish`-case core argument in CAVA's
    `lasso_inv` (`Nested_DFS.thy`), specialized to our concrete (non-abstract)
    fold recursion: `path E (hd (stack s)) vs v` there corresponds to
    `cyclePath`'s chain property here, and `target` to CAVA's `v`.

    `hremaining` carries "every element of `remaining` is a genuine successor
    of `current`" — true at the top-level call (`remaining = (succs
    current).toList`) and preserved as `remaining` shrinks; needed to justify
    the very first edge `current → cyclePath.head`. -/
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

/-! ## Outer DFS invariants

The outer DFS (blue DFS) maintains the invariant that every accepting state
that has been fully processed (popped from the outer stack) has had its inner
DFS run, and the result was added to `innerFinished`.

The correctness argument (following CAVA's `DFS_Framework.Nested_DFS`, *not* a
CVWY-style post-order/"who finishes last" argument, which turned out to be
unnecessary): whenever an accepting `current` at the top of the stack finishes
running inner DFS with `none` (no cycle found), `innerDFS_no_cycle_from_seed_finished`
gives a *restricted* fact — no path back to `current` through never-finished
intermediates. Separately, `innerDFS_new_finished_closed` shows `innerFinished`
stays closed under `succs`. Combining the two via `PathTo.no_self_loop_of_closed`
upgrades this into the *unrestricted* fact `current` has no self-cycle at all —
a permanent, state-independent graph fact requiring no further justification as
the algorithm continues. No reasoning about *other* states on a hypothetical
cycle is ever needed. -/

section OuterCorrectness

variable [BEq State] [Hashable State] [LawfulBEq State]

/-- Outer-DFS bookkeeping closure, independent of the accepting-cycle logic:
    `outerVisited` behaves like a standard DFS discovered-set. This is the
    Lean analogue of CAVA's generic `discovered_closed` invariant, plus a
    stack-chain fact (`stack_chain`) that plays the role CAVA's `red_dfs`
    fills by directly checking against cyan/stack states — here, reaching a
    stack element via inner DFS is instead ruled out by composing this chain
    with the no-self-cycle argument (see `PathTo.no_self_loop_of_closed`). -/
structure OuterReachClosed
    (succs : State → Array State) (st : FNDFSState State)
    (stack : List (State × List State)) : Prop where
  /-- Every stack element can reach every element further down the stack —
      in particular, every element can reach the current top of the stack. -/
  stack_chain : ReachChain succs (stack.map Prod.fst)
  /-- Successors of an outer-done (visited, no longer on stack) state are
      also visited. -/
  done_closed : ∀ s, st.outerVisited.contains s → s ∉ stack.map Prod.fst →
    ∀ t ∈ succs s, st.outerVisited.contains t
  /-- Already-processed (non-pending) successors of every stack frame are
      visited. -/
  stack_processed_visited : ∀ p ∈ stack, ∀ t ∈ succs p.fst, t ∉ p.snd →
    st.outerVisited.contains t
  /-- Every frame's `remaining` list only ever holds genuine successors of
      that frame's state (true by construction: `remaining` always starts as
      the full `(succs state).toList` and is only ever shrunk from the
      front). -/
  stack_remaining_subset : ∀ p ∈ stack, ∀ t ∈ p.snd, t ∈ succs p.fst

/-- Outer DFS invariant for the CVWY algorithm. -/
structure OuterInvariant
    (succs : State → Array State) (isAccepting : State → Bool)
    (st : FNDFSState State)
    (stackStates : List State) : Prop where
  /-- Every accepting, visited, non-stack state is in innerFinished. -/
  accepting_finished : ∀ s, st.outerVisited.contains s →
    isAccepting s → s ∉ stackStates → st.innerFinished.contains s
  /-- `innerFinished` is closed under `succs`: once a state is finished, all its
      successors are finished too. Cf. CAVA `red_closed` / `restr_invar`'s first
      conjunct (`E `` R ⊆ R`). This is what lets us upgrade the *restricted*
      no-cycle fact from inner DFS into an *unrestricted* one below. -/
  finished_closed : ∀ s, st.innerFinished.contains s →
    ∀ t ∈ succs s, st.innerFinished.contains t
  /-- `innerFinished ⊆ outerVisited`. Needed to maintain `finished_stack_disjoint`
      through the "push a fresh successor" transition: a freshly-discovered
      (¬outerVisited) successor can't already be `innerFinished`. -/
  finished_subset_visited : ∀ s, st.innerFinished.contains s →
    st.outerVisited.contains s
  /-- `innerFinished` is disjoint from the current stack. This is what lets us
      conclude `current` (top of stack) is never already `innerFinished` when
      its turn comes, with no case-split needed. Cf. CAVA `red_stack_disjoint`. -/
  finished_stack_disjoint : ∀ s ∈ stackStates, ¬st.innerFinished.contains s
  /-- Every *accepting, no-longer-on-stack* state has no self-cycle at all,
      through any intermediates whatsoever — this is scoped like CAVA's
      `dom (finished s)` (which grows by exactly one state per finish-event),
      not like raw `innerFinished` (which can grow by many states per
      finish-event, via states an inner DFS call merely walks through without
      checking their own self-cycle). Once established for a state this is a
      plain, DFS-state-independent graph fact, so it never needs to be
      re-justified as the algorithm continues. Cf. CAVA `no_accpt_cycle_in_finish`. -/
  finished_no_cycle : ∀ s, isAccepting s → s ∉ stackStates →
    st.outerVisited.contains s → ¬PathTo succs (fun _ => False) s s
  /-- Every state on the stack has already been outer-discovered. Trivial by
      construction (a state is inserted into `outerVisited` at the same time
      it's pushed), but needed explicitly to know `current` itself is
      `outerVisited` when reasoning about `finished_subset_visited`. -/
  stack_subset_visited : ∀ s ∈ stackStates, st.outerVisited.contains s

/-- `outerVisited` only grows across an `outerDFSLoop_fuel` call, for any
    result (not just `.empty`). Needed to carry "already visited before this
    call" facts through to the end. -/
theorem outerDFSLoop_fuel_outerVisited_mono
    (succs : State → Array State) (isAccepting : State → Bool)
    (fuel : Nat) (stack : List (State × List State)) (pathStack : List State)
    (st : FNDFSState State)
    {result : EmptinessResult State} {st' : FNDFSState State}
    (h : outerDFSLoop_fuel succs isAccepting fuel stack pathStack st = some (result, st')) :
    ∀ s, st.outerVisited.contains s → st'.outerVisited.contains s := by
  induction fuel generalizing stack pathStack st result st' with
  | zero => simp [outerDFSLoop_fuel.eq_def] at h
  | succ m ih =>
    rw [outerDFSLoop_fuel.eq_def] at h
    simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact fun s hs => hs
    · rename_i current remaining rest
      split at h
      · split at h
        · split at h
          · simp at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            rename_i st'' heq
            intro s hs
            exact innerDFS_fuel_outerVisited_eq succs current pathStack m current _ st _ _ st'' heq ▸ hs
          · rename_i st'' heq
            intro s hs
            exact ih rest pathStack.dropLast st'' h s
              (innerDFS_fuel_outerVisited_eq succs current pathStack m current _ st none _ st'' heq ▸ hs)
        · exact ih rest pathStack.dropLast st h
      · rename_i succ remainingTail
        split at h
        · -- back edge (succ ∈ pathStack)
          split at h
          · -- isAccepting current: returns immediately either way, st unchanged
            split at h <;>
              · simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨-, rfl⟩ := h
                exact fun s hs => hs
          · -- ¬isAccepting current
            split at h
            · -- isAccepting succ: returns immediately, st unchanged
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact fun s hs => hs
            · -- neither accepting: recurse, skip
              exact ih ((current, remainingTail) :: rest) pathStack st h
        · -- ¬(succ ∈ pathStack)
          split at h
          · -- already visited: recurse, skip
            exact ih ((current, remainingTail) :: rest) pathStack st h
          · -- fresh: recurse, push
            intro s hs
            exact ih ((succ, (succs succ).toList) :: (current, remainingTail) :: rest)
              (pathStack ++ [succ]) { st with outerVisited := st.outerVisited.insert succ } h s
              (by simp [Std.HashSet.contains_insert, hs])

/-- `OuterReachClosed` is maintained across `outerDFSLoop_fuel`'s recursion.
    Proved separately from `outerDFSLoop_fuel_empty_no_cycle` since it doesn't
    depend on the accepting-cycle logic at all — purely outer-DFS bookkeeping. -/
theorem outerDFSLoop_fuel_reach_closed
    (succs : State → Array State) (isAccepting : State → Bool)
    (fuel : Nat)
    (stack : List (State × List State))
    (pathStack : List State)
    (st : FNDFSState State)
    {n : Nat} {st' : FNDFSState State}
    (hsv : ∀ s ∈ pathStack, st.outerVisited.contains s)
    (h : outerDFSLoop_fuel succs isAccepting fuel stack pathStack st =
      some (.empty n, st'))
    (hrc : OuterReachClosed succs st stack) :
    OuterReachClosed succs st' [] := by
  induction fuel generalizing stack pathStack st n st' with
  | zero => simp [outerDFSLoop_fuel.eq_def] at h
  | succ m ih =>
    rw [outerDFSLoop_fuel.eq_def] at h
    simp only at h
    split at h
    · -- stack = []
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact hrc
    · -- stack = (current, remaining) :: rest
      rename_i current remaining rest
      split at h
      · -- remaining = []
        split at h
        · -- isAccepting current = true
          split at h
          · simp at h
          · simp at h
          · -- recurse
            rename_i st'' heq
            have houter_eq : st''.outerVisited = st.outerVisited :=
              innerDFS_fuel_outerVisited_eq succs current pathStack m current _ st none _ st'' heq
            have hsv' : ∀ s ∈ pathStack.dropLast, st''.outerVisited.contains s := by
              intro s hs
              rw [houter_eq]
              exact hsv s (List.dropLast_subset _ hs)
            have hinv' : OuterReachClosed succs st'' rest := {
              stack_chain := ReachChain.tail current (rest.map Prod.fst)
                (by simpa using hrc.stack_chain)
              done_closed := by
                intro s hvis hnotmem t ht
                rw [houter_eq] at hvis ⊢
                by_cases hsc : s = current
                · have ht' : t ∈ succs current := hsc ▸ ht
                  exact hrc.stack_processed_visited (current, []) (List.mem_cons_self ..)
                    t ht' (by simp)
                · have hnotmem' : s ∉ current :: rest.map Prod.fst :=
                    fun hmem => (List.mem_cons.mp hmem).elim hsc hnotmem
                  exact hrc.done_closed s hvis hnotmem' t ht
              stack_processed_visited := by
                intro p hp t ht hpr
                rw [houter_eq]
                exact hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp) t ht hpr
              stack_remaining_subset := fun p hp t ht =>
                hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp) t ht
            }
            exact ih rest pathStack.dropLast st'' hsv' h hinv'
        · -- isAccepting current = false
          have hsv' : ∀ s ∈ pathStack.dropLast, st.outerVisited.contains s :=
            fun s hs => hsv s (List.dropLast_subset _ hs)
          have hinv' : OuterReachClosed succs st rest := {
            stack_chain := ReachChain.tail current (rest.map Prod.fst)
              (by simpa using hrc.stack_chain)
            done_closed := by
              intro s hvis hnotmem t ht
              by_cases hsc : s = current
              · have ht' : t ∈ succs current := hsc ▸ ht
                exact hrc.stack_processed_visited (current, []) (List.mem_cons_self ..)
                  t ht' (by simp)
              · have hnotmem' : s ∉ current :: rest.map Prod.fst :=
                  fun hmem => (List.mem_cons.mp hmem).elim hsc hnotmem
                exact hrc.done_closed s hvis hnotmem' t ht
            stack_processed_visited := fun p hp t ht hpr =>
              hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp) t ht hpr
            stack_remaining_subset := fun p hp t ht =>
              hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp) t ht
          }
          exact ih rest pathStack.dropLast st hsv' h hinv'
      · -- remaining = succ :: remainingTail
        rename_i succ remainingTail
        have hskip : st.outerVisited.contains succ →
            OuterReachClosed succs st ((current, remainingTail) :: rest) :=
          fun hvis_succ => {
          stack_chain := hrc.stack_chain
          done_closed := hrc.done_closed
          stack_processed_visited := by
            intro p hp t ht hpr
            rcases List.mem_cons.mp hp with rfl | hp'
            · by_cases hts : t = succ
              · exact hts ▸ hvis_succ
              · have hpr' : t ∉ succ :: remainingTail := fun hmem =>
                  (List.mem_cons.mp hmem).elim hts hpr
                exact hrc.stack_processed_visited (current, succ :: remainingTail)
                  (List.mem_cons_self ..) t ht hpr'
            · exact hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp') t ht hpr
          stack_remaining_subset := by
            intro p hp t ht
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact hrc.stack_remaining_subset (current, succ :: remainingTail)
                (List.mem_cons_self ..) t (List.mem_cons_of_mem _ ht)
            · exact hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp') t ht
        }
        split at h
        · -- back edge (succ ∈ pathStack)
          rename_i hsucc_mem
          split at h
          · -- isAccepting current: reports .nonEmpty either way, contradicts .empty
            split at h <;> simp at h
          · -- ¬isAccepting current
            split at h
            · -- isAccepting succ: reports .nonEmpty, contradicts .empty
              simp at h
            · -- neither accepting: identical bookkeeping to "already visited, skip"
              exact ih ((current, remainingTail) :: rest) pathStack st hsv h
                (hskip (hsv succ (by simpa using hsucc_mem)))
        · -- ¬(succ ∈ pathStack)
          split at h
          · -- succ already visited (not on the stack)
            rename_i hvisited
            exact ih ((current, remainingTail) :: rest) pathStack st hsv h (hskip hvisited)
          · -- succ fresh
            have hsucc_edge : succ ∈ succs current :=
              hrc.stack_remaining_subset (current, succ :: remainingTail) (List.mem_cons_self ..)
                succ (List.mem_cons_self ..)
            have hinv' : OuterReachClosed succs
                { st with outerVisited := st.outerVisited.insert succ }
                ((succ, (succs succ).toList) :: (current, remainingTail) :: rest) := {
              stack_chain := ⟨PathTo.direct hsucc_edge, hrc.stack_chain⟩
              done_closed := by
                intro s hvis hnotmem t ht
                simp only [List.map_cons] at hnotmem
                have hs_ne_succ : s ≠ succ := fun heq => hnotmem (heq ▸ List.mem_cons_self ..)
                have hnotmem' : s ∉ (current :: rest.map Prod.fst) := fun hmem =>
                  hnotmem (List.mem_cons_of_mem _ hmem)
                have hvis_old : st.outerVisited.contains s := by
                  simp [Std.HashSet.contains_insert] at hvis
                  rcases hvis with rfl | hvis
                  · exact absurd rfl hs_ne_succ
                  · exact hvis
                have ht_old := hrc.done_closed s hvis_old hnotmem' t ht
                simp [Std.HashSet.contains_insert, ht_old]
              stack_processed_visited := by
                intro p hp t ht hpr
                rcases List.mem_cons.mp hp with rfl | hp'
                · exact absurd (Array.mem_toList_iff.mpr ht) hpr
                · rcases List.mem_cons.mp hp' with rfl | hp''
                  · by_cases hts : t = succ
                    · simp [Std.HashSet.contains_insert, hts]
                    · have hpr' : t ∉ succ :: remainingTail := fun hmem =>
                        (List.mem_cons.mp hmem).elim hts hpr
                      have ht_old := hrc.stack_processed_visited (current, succ :: remainingTail)
                        (List.mem_cons_self ..) t ht hpr'
                      simp [Std.HashSet.contains_insert, ht_old]
                  · have ht_old := hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp'') t ht hpr
                    simp [Std.HashSet.contains_insert, ht_old]
              stack_remaining_subset := by
                intro p hp t ht
                rcases List.mem_cons.mp hp with rfl | hp'
                · exact Array.mem_toList_iff.mp ht
                · rcases List.mem_cons.mp hp' with rfl | hp''
                  · exact hrc.stack_remaining_subset (current, succ :: remainingTail)
                      (List.mem_cons_self ..) t (List.mem_cons_of_mem _ ht)
                  · exact hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp'') t ht
            }
            have hsv' : ∀ s ∈ pathStack ++ [succ],
                ({ st with outerVisited := st.outerVisited.insert succ } :
                  FNDFSState State).outerVisited.contains s := by
              intro s hs
              rcases List.mem_append.mp hs with hs' | hs'
              · simp [Std.HashSet.contains_insert, hsv s hs']
              · simp only [List.mem_singleton] at hs'
                simp [Std.HashSet.contains_insert, hs']
            exact ih ((succ, (succs succ).toList) :: (current, remainingTail) :: rest)
              (pathStack ++ [succ]) { st with outerVisited := st.outerVisited.insert succ }
              hsv' h hinv'

/-- If `pathStack` is a genuine `succs`-chain when `outerDFSLoop_fuel` is called,
    then whenever the call returns `.nonEmpty stem loop`, `(stem, loop)` is a
    genuine accepting-cycle witness — every `AcceptingCycle` field except
    `stem_head_initial` (which needs threading through `nestedDFS_fuel.go`'s
    `initialStates` loop, done separately below).

    `stem` is exactly `pathStack` at the moment an accepting cycle is found,
    so its chain property is the Lean analogue of CAVA's `stack_is_path`
    (`DFS_Invars_Basic.thy`). `loop`'s properties come from
    `innerDFS_fuel_cyclePath_chain` — stated about `loop.tail`, not `loop`
    itself: `loop = current :: cyclePath`, where `cyclePath` *already* starts
    with a copy of `current` (`innerDFS_fuel_cyclePath_chain`'s `hhead0`, since
    `seed` and the initial `current`-argument coincide at the top-level call).
    So `loop.tail = cyclePath` is the genuine chain; `loop` itself is not
    (`current ∈ succs current` isn't guaranteed) — matching `OutputVerify.lean`'s
    existing convention of indexing from `loop[1]`, not `loop[0]`.

    Together these are the Lean analogue of CAVA's `lasso_inv` (`Nested_DFS.thy`)
    — specifically the `finish`-case argument, since our algorithm has no
    Schwoon-Esparza back-edge shortcut — and this theorem plays the role
    CAVA's `s_lasso_inv` plays in the `Some` branch of `blue_dfs_correct`:
    unfold the invariant directly to get the witness properties, no further
    induction needed at the call site. -/
theorem outerDFSLoop_fuel_nonEmpty_witness
    (succs : State → Array State) (isAccepting : State → Bool)
    (fuel : Nat)
    (stack : List (State × List State))
    (pathStack : List State)
    (st : FNDFSState State)
    (root : State)
    {stem loop : List State} {st' : FNDFSState State}
    (hps : pathStack = (stack.map Prod.fst).reverse)
    (hchain : ∀ i, (hi : i + 1 < pathStack.length) → pathStack[i+1] ∈ succs pathStack[i])
    (hroot : ∀ (hp : pathStack ≠ []), pathStack.head hp = root)
    (hsv : ∀ s ∈ pathStack, st.outerVisited.contains s)
    (hrc : OuterReachClosed succs st stack)
    (h : outerDFSLoop_fuel succs isAccepting fuel stack pathStack st =
      some (.nonEmpty stem loop, st')) :
    (∀ (hs : stem ≠ []), stem.head hs = root) ∧
    stem.length ≥ 1 ∧
    loop.tail.length ≥ 1 ∧
    (∀ i, (hi : i + 1 < stem.length) → stem[i+1] ∈ succs stem[i]) ∧
    (∀ (hs : stem ≠ []) (hl : loop.tail ≠ []), stem.getLast hs = loop.tail.head hl) ∧
    (∀ i, (hi : i + 1 < loop.tail.length) → loop.tail[i+1] ∈ succs loop.tail[i]) ∧
    (∀ (hl : loop.tail ≠ []), loop.tail.head hl ∈ succs (loop.tail.getLast hl)) ∧
    (∀ (hl : loop.tail ≠ []), isAccepting (loop.tail.head hl) = true) := by
  induction fuel generalizing stack pathStack st stem loop st' with
  | zero => simp [outerDFSLoop_fuel.eq_def] at h
  | succ m ih =>
    rw [outerDFSLoop_fuel.eq_def] at h
    simp only at h
    split at h
    · -- stack = []
      simp at h
    · -- stack = (current, remaining) :: rest
      rename_i current remaining rest
      split at h
      · -- remaining = []
        split at h
        · -- isAccepting current = true
          rename_i hacc
          split at h
          · simp at h
          · -- found a cycle! stem = pathStack. Holzmann-Peled-Yannakakis:
            -- loop = current :: cyclePath0 ++ loopTail0, where loopTail0 is
            -- the stack tree-path segment from target0's child down to
            -- current's own stack-parent (empty when target0 = current,
            -- collapsing to the pre-HPY `current :: cyclePath0` formula).
            rename_i cyclePath0 target0 iv0 st'' heqinner
            simp only [Option.some.injEq, Prod.mk.injEq, EmptinessResult.nonEmpty.injEq] at h
            obtain ⟨⟨heq, heql⟩, -⟩ := h
            subst heq
            obtain ⟨htarget0, hlen0, hhead0, hchain0, hback0⟩ :=
              innerDFS_fuel_cyclePath_chain succs current pathStack m current
                (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heqinner
            have hne0 : cyclePath0 ≠ [] := by
              intro hcontra; rw [hcontra] at hlen0; simp at hlen0
            have hpc : pathStack = (rest.map Prod.fst).reverse ++ [current] := by simp [hps]
            have hne_path : pathStack ≠ [] := by simp [hpc]
            have hgetlast_path : pathStack.getLast hne_path = current := by simp [hpc]
            have htarget0_mem : target0 ∈ pathStack := by
              rcases htarget0 with heqt | hmem
              · rw [heqt, ← hgetlast_path]; exact List.getLast_mem hne_path
              · exact hmem
            generalize hA_def : pathStack.takeWhile (fun y => !(y == target0)) = A at ⊢
            generalize hB_def : pathStack.dropWhile (fun y => !(y == target0)) = B at heql ⊢
            have hB? : B.head? = some target0 := by
              rw [← hB_def]; exact dropWhile_ne_head?_eq_some pathStack target0 htarget0_mem
            have hBne : B ≠ [] := by intro hc; rw [hc] at hB?; simp at hB?
            have hBhead : B.head hBne = target0 := (List.head_eq_iff_head?_eq_some hBne).mpr hB?
            have heqAB : pathStack = A ++ B := by
              rw [← hA_def, ← hB_def]; exact (List.takeWhile_append_dropWhile).symm
            have hchainB := chain_append_right pathStack A B heqAB hchain
            have hBgetlast : B.getLast hBne = current := by
              have hpsGL? : pathStack.getLast? = some current := by
                rw [List.getLast?_eq_some_getLast hne_path, hgetlast_path]
              have hsplit : pathStack.getLast? = B.getLast?.or A.getLast? := by
                rw [heqAB]; exact List.getLast?_append
              rw [hpsGL?] at hsplit
              have hBsome : B.getLast? = some (B.getLast hBne) := List.getLast?_eq_some_getLast hBne
              rw [hBsome] at hsplit
              simp only [Option.some_or] at hsplit
              exact (Option.some.inj hsplit).symm
            by_cases hloopTailE : B.dropLast = []
            · -- degenerate: target0 = current, loop.tail = cyclePath0
              subst heql
              simp only [hloopTailE, List.append_nil, List.tail_cons]
              refine ⟨fun hs => hroot hs, ?_, hlen0, hchain, ?_, hchain0, ?_, ?_⟩
              · cases pathStack with
                | nil => exact absurd rfl hne_path
                | cons a l => simp
              · intro hs hl
                rw [hhead0 hl]; exact hgetlast_path
              · intro hl
                have hBlen1 : B.length = 1 := by
                  have hd := List.length_dropLast (xs := B)
                  rw [hloopTailE] at hd
                  have hge : B.length ≥ 1 := List.length_pos_iff.mpr hBne
                  simp at hd; omega
                have htarget0_eq_current : target0 = current := by
                  have hh := head_eq_getLast_of_length_eq_one B hBlen1 hBne
                  rw [hBhead, hBgetlast] at hh; exact hh
                rw [htarget0_eq_current] at hback0
                rw [hhead0 hl]
                exact hback0 hl
              · intro hl
                rw [hhead0 hl]; exact hacc
            · -- general: splice cyclePath0 with the stack-suffix B.dropLast
              subst heql
              simp only [List.cons_append, List.tail_cons]
              have hchainBdrop := chain_dropLast B hchainB
              have hedge : B.dropLast.head hloopTailE ∈ succs (cyclePath0.getLast hne0) := by
                rw [head_dropLast_eq B hBne hloopTailE, hBhead]
                exact hback0 hne0
              have hchainfull :=
                chain_append cyclePath0 B.dropLast hchain0 hchainBdrop hne0 hloopTailE hedge
              have hbackedge :
                  current ∈ succs ((cyclePath0 ++ B.dropLast).getLast (by simp [hne0])) := by
                rw [List.getLast_append_of_ne_nil _ hloopTailE]
                have hge := chain_getLast_edge B hBne hloopTailE hchainB
                rwa [hBgetlast] at hge
              refine ⟨fun hs => hroot hs, ?_, ?_, hchain, ?_, hchainfull, ?_, ?_⟩
              · cases pathStack with
                | nil => exact absurd rfl hne_path
                | cons a l => simp
              · rw [List.length_append]
                have := hlen0; omega
              · intro hs hl
                have hheadeq : (cyclePath0 ++ B.dropLast).head hl = cyclePath0.head hne0 :=
                  List.head_append_of_ne_nil hne0
                rw [hheadeq, hhead0 hne0]; exact hgetlast_path
              · intro hl
                have hheadeq : (cyclePath0 ++ B.dropLast).head hl = cyclePath0.head hne0 :=
                  List.head_append_of_ne_nil hne0
                rw [hheadeq, hhead0 hne0]
                exact hbackedge
              · intro hl
                have hheadeq : (cyclePath0 ++ B.dropLast).head hl = cyclePath0.head hne0 :=
                  List.head_append_of_ne_nil hne0
                rw [hheadeq, hhead0 hne0]; exact hacc
          · -- inner DFS returned none: recurse
            rename_i st'' heq
            have hps' : pathStack.dropLast = (rest.map Prod.fst).reverse := by
              simp [hps]
            have hchain' := chain_dropLast pathStack hchain
            have hpc : pathStack = (rest.map Prod.fst).reverse ++ [current] := by simp [hps]
            have hne_path : pathStack ≠ [] := by simp [hpc]
            have hroot' : ∀ (hp : pathStack.dropLast ≠ []), pathStack.dropLast.head hp = root :=
              fun hp => by rw [head_dropLast_eq pathStack hne_path hp]; exact hroot hne_path
            have hinv' : OuterReachClosed succs st'' rest := {
              stack_chain := ReachChain.tail current (rest.map Prod.fst)
                (by simpa using hrc.stack_chain)
              done_closed := by
                intro s hvis hnotmem t ht
                have houter_eq : st''.outerVisited = st.outerVisited :=
                  innerDFS_fuel_outerVisited_eq succs current pathStack m current _ st none _ st'' heq
                rw [houter_eq] at hvis ⊢
                by_cases hsc : s = current
                · have ht' : t ∈ succs current := hsc ▸ ht
                  exact hrc.stack_processed_visited (current, []) (List.mem_cons_self ..)
                    t ht' (by simp)
                · have hnotmem' : s ∉ current :: rest.map Prod.fst :=
                    fun hmem => (List.mem_cons.mp hmem).elim hsc hnotmem
                  exact hrc.done_closed s hvis hnotmem' t ht
              stack_processed_visited := by
                intro p hp t ht hpr
                have houter_eq : st''.outerVisited = st.outerVisited :=
                  innerDFS_fuel_outerVisited_eq succs current pathStack m current _ st none _ st'' heq
                rw [houter_eq]
                exact hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp) t ht hpr
              stack_remaining_subset := fun p hp t ht =>
                hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp) t ht
            }
            have houter_eq' : st''.outerVisited = st.outerVisited :=
              innerDFS_fuel_outerVisited_eq succs current pathStack m current _ st none _ st'' heq
            have hsv' : ∀ s ∈ pathStack.dropLast, st''.outerVisited.contains s := by
              rw [houter_eq']
              exact fun s hs => hsv s (List.dropLast_subset _ hs)
            exact ih rest pathStack.dropLast st'' hps' hchain' hroot' hsv' hinv' h
        · -- isAccepting current = false
          have hps' : pathStack.dropLast = (rest.map Prod.fst).reverse := by
            simp [hps]
          have hchain' := chain_dropLast pathStack hchain
          have hpc : pathStack = (rest.map Prod.fst).reverse ++ [current] := by simp [hps]
          have hne_path : pathStack ≠ [] := by simp [hpc]
          have hroot' : ∀ (hp : pathStack.dropLast ≠ []), pathStack.dropLast.head hp = root :=
            fun hp => by rw [head_dropLast_eq pathStack hne_path hp]; exact hroot hne_path
          have hinv' : OuterReachClosed succs st rest := {
            stack_chain := ReachChain.tail current (rest.map Prod.fst)
              (by simpa using hrc.stack_chain)
            done_closed := by
              intro s hvis hnotmem t ht
              by_cases hsc : s = current
              · have ht' : t ∈ succs current := hsc ▸ ht
                exact hrc.stack_processed_visited (current, []) (List.mem_cons_self ..)
                  t ht' (by simp)
              · have hnotmem' : s ∉ current :: rest.map Prod.fst :=
                  fun hmem => (List.mem_cons.mp hmem).elim hsc hnotmem
                exact hrc.done_closed s hvis hnotmem' t ht
            stack_processed_visited := fun p hp t ht hpr =>
              hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp) t ht hpr
            stack_remaining_subset := fun p hp t ht =>
              hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp) t ht
          }
          have hsv' : ∀ s ∈ pathStack.dropLast, st.outerVisited.contains s :=
            fun s hs => hsv s (List.dropLast_subset _ hs)
          exact ih rest pathStack.dropLast st hps' hchain' hroot' hsv' hinv' h
      · -- remaining = succ :: remainingTail
        rename_i succ remainingTail
        have hsucc_edge : succ ∈ succs current :=
          hrc.stack_remaining_subset (current, succ :: remainingTail) (List.mem_cons_self ..)
            succ (List.mem_cons_self ..)
        have hpc : pathStack = (rest.map Prod.fst).reverse ++ [current] := by
          simp [hps]
        have hne : pathStack ≠ [] := by simp [hpc]
        have hgetlast : pathStack.getLast hne = current := by simp [hpc]
        have hps_skip : pathStack = (((current, remainingTail) :: rest).map Prod.fst).reverse := by
          simpa using hps
        have hskip : st.outerVisited.contains succ →
            OuterReachClosed succs st ((current, remainingTail) :: rest) :=
          fun hvis_succ => {
          stack_chain := hrc.stack_chain
          done_closed := hrc.done_closed
          stack_processed_visited := by
            intro p hp t ht hpr
            rcases List.mem_cons.mp hp with rfl | hp'
            · by_cases hts : t = succ
              · exact hts ▸ hvis_succ
              · have hpr' : t ∉ succ :: remainingTail := fun hmem =>
                  (List.mem_cons.mp hmem).elim hts hpr
                exact hrc.stack_processed_visited (current, succ :: remainingTail)
                  (List.mem_cons_self ..) t ht hpr'
            · exact hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp') t ht hpr
          stack_remaining_subset := by
            intro p hp t ht
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact hrc.stack_remaining_subset (current, succ :: remainingTail)
                (List.mem_cons_self ..) t (List.mem_cons_of_mem _ ht)
            · exact hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp') t ht
        }
        split at h
        · -- back edge (succ ∈ pathStack): Schwoon-Esparza shortcut
          rename_i hsucc_mem'
          have hsucc_mem : succ ∈ pathStack := by simpa using hsucc_mem'
          have hsucc_vis : st.outerVisited.contains succ := hsv succ hsucc_mem
          -- Split `pathStack` at `succ`'s first occurrence: `A ++ B`, with
          -- `B.head = succ` (CAVA's `dropWhileNot v`/`takeWhileNot v`). `A`/`B`
          -- are named via `set` (not left as raw `takeWhile`/`dropWhile`
          -- expressions) so later rewrites of `pathStack` can't loop back
          -- through them.
          generalize hA_def : pathStack.takeWhile (fun y => !(y == succ)) = A at h ⊢
          generalize hB_def : pathStack.dropWhile (fun y => !(y == succ)) = B at h ⊢
          have hB? : B.head? = some succ := by
            rw [← hB_def]; exact dropWhile_ne_head?_eq_some pathStack succ hsucc_mem
          have hBne : B ≠ [] := by
            intro hc; rw [hc] at hB?; simp at hB?
          have hBhead : B.head hBne = succ := (List.head_eq_iff_head?_eq_some hBne).mpr hB?
          have heqAB : pathStack = A ++ B := by
            rw [← hA_def, ← hB_def]; exact (List.takeWhile_append_dropWhile).symm
          have hchainB := chain_append_right pathStack A B heqAB hchain
          have hBgetlast : B.getLast hBne = current := by
            have hpsGL? : pathStack.getLast? = some current := by
              rw [List.getLast?_eq_some_getLast hne, hgetlast]
            have hsplit : pathStack.getLast? = B.getLast?.or A.getLast? := by
              rw [heqAB]; exact List.getLast?_append
            rw [hpsGL?] at hsplit
            have hBsome : B.getLast? = some (B.getLast hBne) := List.getLast?_eq_some_getLast hBne
            rw [hBsome] at hsplit
            simp only [Option.some_or] at hsplit
            exact (Option.some.inj hsplit).symm
          split at h
          · -- isAccepting current
            rename_i hacc
            split at h
            · -- succ = current: literal self-loop
              rename_i hsc
              have hsc' : succ = current := by simpa using hsc
              simp only [Option.some.injEq, Prod.mk.injEq, EmptinessResult.nonEmpty.injEq] at h
              obtain ⟨heqstem, heqloop⟩ := h.1
              subst heqstem
              subst heqloop
              refine ⟨fun hs => hroot hs, List.length_pos_iff.mpr hne, by simp, hchain,
                ?_, ?_, ?_, ?_⟩
              · intro hs hl
                simpa using hgetlast
              · intro i hi
                simp at hi
              · intro hl
                simpa [← hsc'] using hsucc_edge
              · intro hl
                simpa using hacc
            · -- succ ≠ current
              rename_i hsc
              have hsc' : succ ≠ current := by simpa using hsc
              simp only [Option.some.injEq, Prod.mk.injEq, EmptinessResult.nonEmpty.injEq] at h
              obtain ⟨heqstem, heqloop⟩ := h.1
              subst heqstem
              subst heqloop
              have hBdlne : B.dropLast ≠ [] := by
                intro hc
                apply hsc'
                have hlen1 : B.length = 1 := by
                  have hd := List.length_dropLast (xs := B)
                  rw [hc] at hd
                  have hge : B.length ≥ 1 := List.length_pos_iff.mpr hBne
                  simp at hd
                  omega
                have heq := head_eq_getLast_of_length_eq_one B hlen1 hBne
                rw [hBhead, hBgetlast] at heq
                exact heq
              have hXchain := chain_dropLast B hchainB
              have hedge : B.dropLast.head hBdlne ∈ succs current := by
                rw [head_dropLast_eq B hBne hBdlne, hBhead]
                exact hsucc_edge
              have hXchainfull := chain_cons current B.dropLast hBdlne hXchain hedge
              have hbackedge : current ∈ succs (B.dropLast.getLast hBdlne) := by
                have hge := chain_getLast_edge B hBne hBdlne hchainB
                rwa [hBgetlast] at hge
              refine ⟨fun hs => hroot hs, List.length_pos_iff.mpr hne, by simp, hchain,
                ?_, ?_, ?_, ?_⟩
              · intro hs hl
                simpa using hgetlast
              · simpa using hXchainfull
              · intro hl
                have hgl : (current :: B.dropLast).getLast (by simp) = B.dropLast.getLast hBdlne :=
                  List.getLast_cons hBdlne
                simpa [hgl] using hbackedge
              · intro hl
                simpa using hacc
          · -- ¬isAccepting current
            rename_i hnacc
            split at h
            · -- isAccepting succ
              rename_i hsacc
              simp only [Option.some.injEq, Prod.mk.injEq, EmptinessResult.nonEmpty.injEq] at h
              obtain ⟨heqstem, heqloop⟩ := h.1
              subst heqstem
              subst heqloop
              have hstem_getLast : (A ++ [succ]).getLast (by simp) = succ := by simp
              by_cases hAe : A = []
              · -- A empty: stem = [succ]
                have hhead? : pathStack.head? = some succ := by
                  rw [heqAB, hAe, List.nil_append]
                  exact hB?
                have hroot_succ : root = succ := by
                  have h2 : pathStack.head? = some (pathStack.head hne) :=
                    List.head?_eq_some_head hne
                  rw [h2] at hhead?
                  rw [(Option.some.inj hhead?).symm]
                  exact (hroot hne).symm
                refine ⟨fun hs => ?_, by simp, List.length_pos_iff.mpr hBne, by simp [hAe],
                  ?_, hchainB, ?_, ?_⟩
                · simp [hAe, hroot_succ]
                · intro hs hl
                  simp [hAe, hBhead]
                · intro hl; simpa [hBhead, hBgetlast] using hsucc_edge
                · intro hl; simpa [hBhead] using hsacc
              · -- A nonempty
                have hAgetlast_edge : succ ∈ succs (A.getLast hAe) := by
                  have hbe := chain_append_boundary pathStack A B heqAB hAe hBne hchain
                  rwa [hBhead] at hbe
                have hchainA := chain_append_left pathStack A B heqAB hchain
                have hchainstem := chain_append_singleton A succ hchainA hAe hAgetlast_edge
                have hAhead? : pathStack.head? = A.head? := by
                  rw [heqAB, List.head?_append, List.head?_eq_some_head hAe]
                  simp
                have hAheadroot : A.head hAe = root := by
                  have h2 : pathStack.head? = some (pathStack.head hne) :=
                    List.head?_eq_some_head hne
                  rw [h2] at hAhead?
                  have h3 : A.head? = some (A.head hAe) := List.head?_eq_some_head hAe
                  rw [h3] at hAhead?
                  rw [(Option.some.inj hAhead?).symm]
                  exact hroot hne
                refine ⟨fun hs => ?_, by simp, List.length_pos_iff.mpr hBne, hchainstem,
                  ?_, hchainB, ?_, ?_⟩
                · rw [head_append_singleton_eq A succ hAe]
                  exact hAheadroot
                · intro hs hl
                  simp [hBhead, hstem_getLast]
                · intro hl; simpa [hBhead, hBgetlast] using hsucc_edge
                · intro hl; simpa [hBhead] using hsacc
            · -- neither accepting: identical bookkeeping to "already visited, skip"
              exact ih ((current, remainingTail) :: rest) pathStack st hps_skip hchain hroot hsv
                (hskip hsucc_vis) h
        · -- ¬(succ ∈ pathStack)
          split at h
          · -- succ already visited (not on the stack)
            rename_i hvisited
            exact ih ((current, remainingTail) :: rest) pathStack st hps_skip hchain hroot hsv
              (hskip hvisited) h
          · -- succ fresh
            have hchain' := chain_append_singleton pathStack succ hchain hne (hgetlast ▸ hsucc_edge)
            have hroot' : ∀ (hp : (pathStack ++ [succ]) ≠ []), (pathStack ++ [succ]).head hp = root :=
              fun hp => by rw [head_append_singleton_eq pathStack succ hne]; exact hroot hne
            have hps' : pathStack ++ [succ] =
                (((succ, (succs succ).toList) :: (current, remainingTail) :: rest).map
                  Prod.fst).reverse := by
              simp [hps]
            have hsv' : ∀ s ∈ pathStack ++ [succ],
                ({ st with outerVisited := st.outerVisited.insert succ } :
                  FNDFSState State).outerVisited.contains s := by
              intro s hs
              rcases List.mem_append.mp hs with hs' | hs'
              · simp [Std.HashSet.contains_insert, hsv s hs']
              · simp only [List.mem_singleton] at hs'
                simp [Std.HashSet.contains_insert, hs']
            have hinv' : OuterReachClosed succs
                { st with outerVisited := st.outerVisited.insert succ }
                ((succ, (succs succ).toList) :: (current, remainingTail) :: rest) := {
              stack_chain := ⟨PathTo.direct hsucc_edge, hrc.stack_chain⟩
              done_closed := by
                intro s hvis hnotmem t ht
                simp only [List.map_cons] at hnotmem
                have hs_ne_succ : s ≠ succ := fun heq => hnotmem (heq ▸ List.mem_cons_self ..)
                have hnotmem' : s ∉ (current :: rest.map Prod.fst) := fun hmem =>
                  hnotmem (List.mem_cons_of_mem _ hmem)
                have hvis_old : st.outerVisited.contains s := by
                  simp [Std.HashSet.contains_insert] at hvis
                  rcases hvis with rfl | hvis
                  · exact absurd rfl hs_ne_succ
                  · exact hvis
                have ht_old := hrc.done_closed s hvis_old hnotmem' t ht
                simp [Std.HashSet.contains_insert, ht_old]
              stack_processed_visited := by
                intro p hp t ht hpr
                rcases List.mem_cons.mp hp with rfl | hp'
                · exact absurd (Array.mem_toList_iff.mpr ht) hpr
                · rcases List.mem_cons.mp hp' with rfl | hp''
                  · by_cases hts : t = succ
                    · simp [Std.HashSet.contains_insert, hts]
                    · have hpr' : t ∉ succ :: remainingTail := fun hmem =>
                        (List.mem_cons.mp hmem).elim hts hpr
                      have ht_old := hrc.stack_processed_visited (current, succ :: remainingTail)
                        (List.mem_cons_self ..) t ht hpr'
                      simp [Std.HashSet.contains_insert, ht_old]
                  · have ht_old := hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp'') t ht hpr
                    simp [Std.HashSet.contains_insert, ht_old]
              stack_remaining_subset := by
                intro p hp t ht
                rcases List.mem_cons.mp hp with rfl | hp'
                · exact Array.mem_toList_iff.mp ht
                · rcases List.mem_cons.mp hp' with rfl | hp''
                  · exact hrc.stack_remaining_subset (current, succ :: remainingTail)
                      (List.mem_cons_self ..) t (List.mem_cons_of_mem _ ht)
                  · exact hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp'') t ht
            }
            exact ih ((succ, (succs succ).toList) :: (current, remainingTail) :: rest)
              (pathStack ++ [succ]) { st with outerVisited := st.outerVisited.insert succ }
              hps' hchain' hroot' hsv' hinv' h

/-- If the outer DFS returns `empty`, then the outer invariant holds with
    an empty stack (all accepting states have been processed). See the
    section docstring above for the proof strategy. -/
theorem outerDFSLoop_fuel_empty_no_cycle
    (succs : State → Array State) (isAccepting : State → Bool)
    (fuel : Nat)
    (stack : List (State × List State))
    (pathStack : List State)
    (st : FNDFSState State)
    {n : Nat} {st' : FNDFSState State}
    (hps : pathStack = (stack.map Prod.fst).reverse)
    (h : outerDFSLoop_fuel succs isAccepting fuel stack pathStack st =
      some (.empty n, st'))
    (hrc : OuterReachClosed succs st stack)
    (hinv : OuterInvariant succs isAccepting st (stack.map Prod.fst)) :
    OuterInvariant succs isAccepting st' [] := by
  induction fuel generalizing stack pathStack st n st' with
  | zero => simp [outerDFSLoop_fuel.eq_def] at h
  | succ m ih =>
    rw [outerDFSLoop_fuel.eq_def] at h
    simp only at h
    split at h
    · -- stack = []
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact hinv
    · -- stack = (current, remaining) :: rest
      rename_i current remaining rest
      split at h
      · -- remaining = []
        split at h
        · -- isAccepting current = true
          split at h
          · simp at h
          · simp at h
          · -- recurse
            rename_i st'' heq
            obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
              cases m with
              | zero => simp [innerDFS_fuel.eq_def] at heq
              | succ k => exact ⟨k, rfl⟩
            have hnotfin : ¬st.innerFinished.contains current :=
              hinv.finished_stack_disjoint current (List.mem_cons_self ..)
            -- Holzmann-Peled-Yannakakis: both facts below are now stated for
            -- *every* state on `pathStack` (CAVA's `cyan`/whole-stack scope,
            -- `restr_invar`), not just `current` — so `hno_unrestricted_all`
            -- gives "current can't reach any stack state" directly, with no
            -- separate `ReachChain`-based composition needed (contrast the
            -- old, seed-only derivation this replaces).
            have hno_restricted_all := innerDFS_no_cycle_from_seed_finished succs current pathStack k st
              (st.outerVisited.size / 2) (by simpa using hnotfin) heq
            have ht_mem_stack : ∀ t, t ∈ pathStack → t ∈ current :: rest.map Prod.fst := by
              intro t ht
              have ht' : t ∈ (current :: rest.map Prod.fst).reverse := hps ▸ ht
              simpa using List.mem_reverse.mp ht'
            have hno_edge_old_part_all : ∀ t, (t = current ∨ t ∈ pathStack) →
                ∀ x, st.innerFinished.contains x → t ∉ succs x := by
              intro t ht x hx hedge
              have ht_stack : t ∈ current :: rest.map Prod.fst := by
                rcases ht with heqt | hmemp
                · exact heqt ▸ List.mem_cons_self ..
                · exact ht_mem_stack t hmemp
              exact hinv.finished_stack_disjoint t ht_stack (hinv.finished_closed x hx t hedge)
            have hnew_no_edge_all := innerDFS_fuel_new_no_edge_to_seed succs current pathStack
              (k + 1) current (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq
            have hclosed_new : ∀ s, st''.innerFinished.contains s →
                ∀ t ∈ succs s, st''.innerFinished.contains t :=
              innerDFS_new_finished_closed succs current pathStack k st
                (st.outerVisited.size / 2) heq hinv.finished_closed
            have hno_edge_new_all : ∀ t, (t = current ∨ t ∈ pathStack) →
                ∀ x, st''.innerFinished.contains x → t ∉ succs x := by
              intro t ht x hx hedge
              by_cases hold : st.innerFinished.contains x
              · exact hno_edge_old_part_all t ht x hold hedge
              · have hx_iv := innerDFS_fuel_new_finished_subset_iv succs current pathStack (k + 1) current
                  (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq x hx hold
                exact hnew_no_edge_all x hx_iv
                  (by simp [Std.HashSet.contains_emptyWithCapacity]) t ht hedge
            have hno_unrestricted_all : ∀ t, (t = current ∨ t ∈ pathStack) →
                ¬PathTo succs (fun _ => False) current t := by
              intro t ht
              exact PathTo.no_reach_of_closed_no_incoming hclosed_new (hno_edge_new_all t ht)
                (hno_restricted_all t ht)
            have hno_unrestricted : ¬PathTo succs (fun _ => False) current current :=
              hno_unrestricted_all current (Or.inl rfl)
            have houter_eq : st''.outerVisited = st.outerVisited :=
              innerDFS_fuel_outerVisited_eq succs current pathStack (k + 1) current _ st none _ st'' heq
            have hfin_mono : ∀ s, st.innerFinished.contains s → st''.innerFinished.contains s :=
              (innerDFS_fuel_mono succs current pathStack (k + 1) current
                (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st none _ st'' heq).2
            have hcur_fin : st''.innerFinished.contains current := by
              rcases innerDFS_fuel_current_blocked succs current pathStack (k + 1) current
                (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq with hiv | hfin
              · exact innerDFS_fuel_iv_subset_finished succs current pathStack (k + 1) current
                  (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq current hiv
                  (by simp [Std.HashSet.contains_emptyWithCapacity])
              · exact hfin
            have hps' : pathStack.dropLast = (rest.map Prod.fst).reverse := by
              simp [hps]
            have hrc' : OuterReachClosed succs st'' rest := {
              stack_chain := ReachChain.tail current (rest.map Prod.fst)
                (by simpa using hrc.stack_chain)
              done_closed := by
                intro s hvis hnotmem t ht
                rw [houter_eq] at hvis ⊢
                by_cases hsc : s = current
                · have ht' : t ∈ succs current := hsc ▸ ht
                  exact hrc.stack_processed_visited (current, []) (List.mem_cons_self ..)
                    t ht' (by simp)
                · have hnotmem' : s ∉ current :: rest.map Prod.fst :=
                    fun hmem => (List.mem_cons.mp hmem).elim hsc hnotmem
                  exact hrc.done_closed s hvis hnotmem' t ht
              stack_processed_visited := by
                intro p hp t ht hpr
                rw [houter_eq]
                exact hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp) t ht hpr
              stack_remaining_subset := fun p hp t ht =>
                hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp) t ht
            }
            have hno_stack_reach : ∀ w, PathTo succs (fun _ => False) current w →
                w ∉ (current :: rest.map Prod.fst) := by
              intro w hw hmem
              rcases List.mem_cons.mp hmem with heqw | hmem'
              · exact hno_unrestricted (heqw ▸ hw)
              · exact hno_unrestricted (PathTo.trans hw
                  (ReachChain.reaches_head current (rest.map Prod.fst)
                    (by simpa using hrc.stack_chain) w hmem'))
            have hinv' : OuterInvariant succs isAccepting st'' (rest.map Prod.fst) := {
              accepting_finished := by
                intro s hvis haccept hnotmem
                by_cases hsc : s = current
                · exact hsc ▸ hcur_fin
                · have hvis_old : st.outerVisited.contains s := houter_eq ▸ hvis
                  have hnotmem' : s ∉ current :: rest.map Prod.fst :=
                    fun hmem => (List.mem_cons.mp hmem).elim hsc hnotmem
                  exact hfin_mono s (hinv.accepting_finished s hvis_old haccept hnotmem')
              finished_closed := hclosed_new
              finished_subset_visited := by
                intro s hcontra
                rw [houter_eq]
                by_cases hold : st.innerFinished.contains s
                · exact hinv.finished_subset_visited s hold
                · rcases innerDFS_fuel_new_reachable succs current pathStack (k + 1) current
                      (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq s
                      (innerDFS_fuel_new_finished_subset_iv succs current pathStack (k + 1) current
                        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq s
                        hcontra hold)
                      (by simp [Std.HashSet.contains_emptyWithCapacity]) with heqcur | hp
                  · exact heqcur ▸ hinv.stack_subset_visited current (List.mem_cons_self ..)
                  · have hCL : ∀ x, (st.outerVisited.contains x ∧
                        x ∉ (current :: rest.map Prod.fst)) →
                        ∀ y ∈ succs x, (st.outerVisited.contains y ∧
                          y ∉ (current :: rest.map Prod.fst)) ∨ y ∈ (current :: rest.map Prod.fst) := by
                      intro x hx y hy
                      by_cases hyS : y ∈ (current :: rest.map Prod.fst)
                      · exact Or.inr hyS
                      · exact Or.inl ⟨hrc.done_closed x hx.1 hx.2 y hy, hyS⟩
                    cases hp with
                    | direct ht =>
                      exact hrc.stack_processed_visited (current, []) (List.mem_cons_self ..)
                        s ht (by simp)
                    | @through _ mid _ hmid _ hrest =>
                      have hmid_vis : st.outerVisited.contains mid :=
                        hrc.stack_processed_visited (current, []) (List.mem_cons_self ..)
                          mid hmid (by simp)
                      have hmid_notstack : mid ∉ (current :: rest.map Prod.fst) :=
                        hno_stack_reach mid (PathTo.direct hmid)
                      have hmid_NR : ∀ w, PathTo succs (fun _ => False) mid w →
                          w ∉ (current :: rest.map Prod.fst) :=
                        fun w hw => hno_stack_reach w (PathTo.trans (PathTo.direct hmid) hw)
                      exact (PathTo.closed_of_no_escape hCL hrest ⟨hmid_vis, hmid_notstack⟩
                        hmid_NR).1
              finished_stack_disjoint := by
                intro s hs hcontra
                by_cases hold : st.innerFinished.contains s
                · exact hinv.finished_stack_disjoint s (List.mem_cons_of_mem _ hs) hold
                · have hs_reach_current : PathTo succs (fun _ => False) s current :=
                    ReachChain.reaches_head current (rest.map Prod.fst)
                      (by simpa using hrc.stack_chain) s hs
                  rcases innerDFS_fuel_new_reachable succs current pathStack (k + 1) current
                      (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq s
                      (innerDFS_fuel_new_finished_subset_iv succs current pathStack (k + 1) current
                        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq s
                        hcontra hold)
                      (by simp [Std.HashSet.contains_emptyWithCapacity]) with heqcur | hcur_reach_s
                  · exact hno_unrestricted (heqcur ▸ hs_reach_current)
                  · exact hno_unrestricted (PathTo.trans hcur_reach_s hs_reach_current)
              finished_no_cycle := by
                intro s haccept hnotmem hvis
                by_cases hsc : s = current
                · exact hsc ▸ hno_unrestricted
                · have hvis_old : st.outerVisited.contains s := houter_eq ▸ hvis
                  have hnotmem' : s ∉ current :: rest.map Prod.fst :=
                    fun hmem => (List.mem_cons.mp hmem).elim hsc hnotmem
                  exact hinv.finished_no_cycle s haccept hnotmem' hvis_old
              stack_subset_visited := by
                intro s hs
                rw [houter_eq]
                exact hinv.stack_subset_visited s (List.mem_cons_of_mem _ hs)
            }
            exact ih rest pathStack.dropLast st'' hps' h hrc' hinv'
        · -- isAccepting current = false
          rename_i hacc
          have hps' : pathStack.dropLast = (rest.map Prod.fst).reverse := by
            simp [hps]
          have hrc' : OuterReachClosed succs st rest := {
            stack_chain := ReachChain.tail current (rest.map Prod.fst)
              (by simpa using hrc.stack_chain)
            done_closed := by
              intro s hvis hnotmem t ht
              by_cases hsc : s = current
              · have ht' : t ∈ succs current := hsc ▸ ht
                exact hrc.stack_processed_visited (current, []) (List.mem_cons_self ..)
                  t ht' (by simp)
              · have hnotmem' : s ∉ current :: rest.map Prod.fst :=
                  fun hmem => (List.mem_cons.mp hmem).elim hsc hnotmem
                exact hrc.done_closed s hvis hnotmem' t ht
            stack_processed_visited := fun p hp t ht hpr =>
              hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp) t ht hpr
            stack_remaining_subset := fun p hp t ht =>
              hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp) t ht
          }
          have hinv' : OuterInvariant succs isAccepting st (rest.map Prod.fst) := {
            accepting_finished := by
              intro s hvis haccept hnotmem
              by_cases hsc : s = current
              · subst hsc; simp [hacc] at haccept
              · exact hinv.accepting_finished s hvis haccept (by simp [hsc, hnotmem])
            finished_closed := hinv.finished_closed
            finished_subset_visited := hinv.finished_subset_visited
            finished_stack_disjoint := fun s hs =>
              hinv.finished_stack_disjoint s (List.mem_cons_of_mem _ hs)
            finished_no_cycle := by
              intro s haccept hnotmem hvis
              by_cases hsc : s = current
              · subst hsc; simp [hacc] at haccept
              · have hnotmem' : s ∉ current :: rest.map Prod.fst :=
                  fun hmem => (List.mem_cons.mp hmem).elim hsc hnotmem
                exact hinv.finished_no_cycle s haccept hnotmem' hvis
            stack_subset_visited := fun s hs =>
              hinv.stack_subset_visited s (List.mem_cons_of_mem _ hs)
          }
          exact ih rest pathStack.dropLast st hps' h hrc' hinv'
      · -- remaining = succ :: remainingTail
        rename_i succ remainingTail
        have hps' : pathStack = (((current, remainingTail) :: rest).map Prod.fst).reverse := by
          simpa using hps
        have hskip_inv : OuterInvariant succs isAccepting st
            (((current, remainingTail) :: rest).map Prod.fst) := by
          simpa using hinv
        have hskip_rc : st.outerVisited.contains succ →
            OuterReachClosed succs st ((current, remainingTail) :: rest) :=
          fun hvis_succ => {
          stack_chain := hrc.stack_chain
          done_closed := hrc.done_closed
          stack_processed_visited := by
            intro p hp t ht hpr
            rcases List.mem_cons.mp hp with rfl | hp'
            · by_cases hts : t = succ
              · exact hts ▸ hvis_succ
              · have hpr' : t ∉ succ :: remainingTail := fun hmem =>
                  (List.mem_cons.mp hmem).elim hts hpr
                exact hrc.stack_processed_visited (current, succ :: remainingTail)
                  (List.mem_cons_self ..) t ht hpr'
            · exact hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp') t ht hpr
          stack_remaining_subset := by
            intro p hp t ht
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact hrc.stack_remaining_subset (current, succ :: remainingTail)
                (List.mem_cons_self ..) t (List.mem_cons_of_mem _ ht)
            · exact hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp') t ht
        }
        split at h
        · -- back edge (succ ∈ pathStack)
          rename_i hsucc_mem
          have hsucc_vis : st.outerVisited.contains succ := by
            have hmem_stack : succ ∈ ((current, succ :: remainingTail) :: rest).map Prod.fst := by
              have hmem_rev : succ ∈ pathStack := by simpa using hsucc_mem
              rw [hps] at hmem_rev
              simpa using List.mem_reverse.mp hmem_rev
            exact hinv.stack_subset_visited succ hmem_stack
          split at h
          · -- isAccepting current: reports .nonEmpty either way, contradicts .empty
            split at h <;> simp at h
          · -- ¬isAccepting current
            split at h
            · -- isAccepting succ: reports .nonEmpty, contradicts .empty
              simp at h
            · -- neither accepting: identical bookkeeping to "already visited, skip"
              exact ih ((current, remainingTail) :: rest) pathStack st hps' h
                (hskip_rc hsucc_vis) hskip_inv
        · -- ¬(succ ∈ pathStack)
          split at h
          · -- succ already visited (not on the stack)
            rename_i hvisited
            exact ih ((current, remainingTail) :: rest) pathStack st hps' h
              (hskip_rc hvisited) hskip_inv
          · -- succ fresh
            rename_i hnotvisited
            have hsucc_edge : succ ∈ succs current :=
              hrc.stack_remaining_subset (current, succ :: remainingTail) (List.mem_cons_self ..)
                succ (List.mem_cons_self ..)
            have hps' : pathStack ++ [succ] =
                (((succ, (succs succ).toList) :: (current, remainingTail) :: rest).map
                  Prod.fst).reverse := by
              simp [hps]
            have hrc' : OuterReachClosed succs
                { st with outerVisited := st.outerVisited.insert succ }
                ((succ, (succs succ).toList) :: (current, remainingTail) :: rest) := {
              stack_chain := ⟨PathTo.direct hsucc_edge, hrc.stack_chain⟩
              done_closed := by
                intro s hvis hnotmem t ht
                simp only [List.map_cons] at hnotmem
                have hs_ne_succ : s ≠ succ := fun heq => hnotmem (heq ▸ List.mem_cons_self ..)
                have hnotmem' : s ∉ (current :: rest.map Prod.fst) := fun hmem =>
                  hnotmem (List.mem_cons_of_mem _ hmem)
                have hvis_old : st.outerVisited.contains s := by
                  simp [Std.HashSet.contains_insert] at hvis
                  rcases hvis with rfl | hvis
                  · exact absurd rfl hs_ne_succ
                  · exact hvis
                have ht_old := hrc.done_closed s hvis_old hnotmem' t ht
                simp [Std.HashSet.contains_insert, ht_old]
              stack_processed_visited := by
                intro p hp t ht hpr
                rcases List.mem_cons.mp hp with rfl | hp'
                · exact absurd (Array.mem_toList_iff.mpr ht) hpr
                · rcases List.mem_cons.mp hp' with rfl | hp''
                  · by_cases hts : t = succ
                    · simp [Std.HashSet.contains_insert, hts]
                    · have hpr' : t ∉ succ :: remainingTail := fun hmem =>
                        (List.mem_cons.mp hmem).elim hts hpr
                      have ht_old := hrc.stack_processed_visited (current, succ :: remainingTail)
                        (List.mem_cons_self ..) t ht hpr'
                      simp [Std.HashSet.contains_insert, ht_old]
                  · have ht_old := hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp'') t ht hpr
                    simp [Std.HashSet.contains_insert, ht_old]
              stack_remaining_subset := by
                intro p hp t ht
                rcases List.mem_cons.mp hp with rfl | hp'
                · exact Array.mem_toList_iff.mp ht
                · rcases List.mem_cons.mp hp' with rfl | hp''
                  · exact hrc.stack_remaining_subset (current, succ :: remainingTail)
                      (List.mem_cons_self ..) t (List.mem_cons_of_mem _ ht)
                  · exact hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp'') t ht
            }
            have hinv' : OuterInvariant succs isAccepting
                { st with outerVisited := st.outerVisited.insert succ }
                (((succ, (succs succ).toList) :: (current, remainingTail) :: rest).map
                  Prod.fst) := {
              accepting_finished := by
                intro s hvis haccept hnotmem
                simp only [List.map_cons] at hnotmem
                have hs_ne : s ≠ succ := fun heq => hnotmem (heq ▸ List.mem_cons_self ..)
                have hnotmem' : s ∉ (current :: rest.map Prod.fst) := fun hmem =>
                  hnotmem (List.mem_cons_of_mem _ hmem)
                have hvis_old : st.outerVisited.contains s := by
                  simp [Std.HashSet.contains_insert] at hvis
                  rcases hvis with rfl | hvis
                  · exact absurd rfl hs_ne
                  · exact hvis
                exact hinv.accepting_finished s hvis_old haccept hnotmem'
              finished_closed := hinv.finished_closed
              finished_subset_visited := by
                intro s hs
                have hold := hinv.finished_subset_visited s hs
                simp [Std.HashSet.contains_insert, hold]
              finished_stack_disjoint := by
                intro s hs
                simp only [List.map_cons] at hs
                rcases List.mem_cons.mp hs with heq | hs'
                · intro hcontra
                  have hcontra' := heq ▸ hcontra
                  exact absurd (hinv.finished_subset_visited succ hcontra') hnotvisited
                · exact hinv.finished_stack_disjoint s (by simpa using hs')
              finished_no_cycle := by
                intro s haccept hnotmem hvis
                simp only [List.map_cons] at hnotmem
                have hs_ne : s ≠ succ := fun heq => hnotmem (heq ▸ List.mem_cons_self ..)
                have hnotmem' : s ∉ (current :: rest.map Prod.fst) := fun hmem =>
                  hnotmem (List.mem_cons_of_mem _ hmem)
                have hvis_old : st.outerVisited.contains s := by
                  simp [Std.HashSet.contains_insert] at hvis
                  rcases hvis with rfl | hvis
                  · exact absurd rfl hs_ne
                  · exact hvis
                exact hinv.finished_no_cycle s haccept hnotmem' hvis_old
              stack_subset_visited := by
                intro s hs
                simp only [List.map_cons] at hs
                rcases List.mem_cons.mp hs with rfl | hs'
                · simp [Std.HashSet.contains_insert]
                · have hold := hinv.stack_subset_visited s (by simpa using hs')
                  simp [Std.HashSet.contains_insert, hold]
            }
            exact ih ((succ, (succs succ).toList) :: (current, remainingTail) :: rest)
              (pathStack ++ [succ]) { st with outerVisited := st.outerVisited.insert succ }
              hps' h hrc' hinv'

end OuterCorrectness

section GoCorrectness

variable [BEq State] [Hashable State] [LawfulBEq State]

/-- `nestedDFS_fuel.go`'s loop over `initialStates`, composed across the whole
    loop: if it returns `.empty`, there is a final internal state
    simultaneously satisfying `OuterReachClosed`/`OuterInvariant` (both with
    an empty stack) — carrying forward everything already visited, and
    additionally covering every element of `remaining`. This is the Lean
    analogue of CAVA's `nc_finished_eq_reachable`, adapted to our explicit
    `initialStates` loop (CAVA's generic multi-root DFS framework handles the
    looping internally, so they don't need a separate composed theorem like
    this one). -/
theorem nestedDFS_fuel_go_correct
    (succs : State → Array State) (isAccepting : State → Bool)
    (remaining : List State) (st : FNDFSState State) (fuel : Nat) {n : Nat}
    (h : nestedDFS_fuel.go succs isAccepting remaining st fuel = some (.empty n))
    (hrc : OuterReachClosed succs st [])
    (hinv : OuterInvariant succs isAccepting st []) :
    ∃ st', OuterReachClosed succs st' [] ∧ OuterInvariant succs isAccepting st' [] ∧
      (∀ s, st.outerVisited.contains s → st'.outerVisited.contains s) ∧
      (∀ i ∈ remaining, st'.outerVisited.contains i) := by
  induction fuel generalizing remaining st with
  | zero => simp [nestedDFS_fuel.go.eq_def] at h
  | succ m ih =>
    rw [nestedDFS_fuel.go.eq_def] at h
    simp only at h
    split at h
    · -- remaining = []
      simp only [Option.some.injEq] at h
      exact ⟨st, hrc, hinv, fun s hs => hs, by simp⟩
    · -- remaining = init :: rest
      rename_i init rest
      split at h
      · -- init already visited
        rename_i hvisited
        obtain ⟨st', hrc', hinv', hmono, hroots⟩ := ih rest st h hrc hinv
        refine ⟨st', hrc', hinv', hmono, ?_⟩
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi'
        · exact hmono i hvisited
        · exact hroots i hi'
      · -- init fresh
        rename_i hnotvisited
        split at h
        · simp at h
        · simp at h
        · rename_i st'' heq
          have hrc_pushed : OuterReachClosed succs
              { st with outerVisited := st.outerVisited.insert init }
              [(init, (succs init).toList)] := {
            stack_chain := trivial
            done_closed := by
              intro s hvis hnotmem t ht
              have hs_ne : s ≠ init := fun heq' => hnotmem (heq' ▸ List.mem_cons_self ..)
              have hvis_old : st.outerVisited.contains s := by
                simp [Std.HashSet.contains_insert] at hvis
                rcases hvis with rfl | hvis
                · exact absurd rfl hs_ne
                · exact hvis
              have ht_old := hrc.done_closed s hvis_old (by simp) t ht
              simp [Std.HashSet.contains_insert, ht_old]
            stack_processed_visited := by
              intro p hp t ht hpr
              rcases List.mem_cons.mp hp with rfl | hp'
              · exact absurd (Array.mem_toList_iff.mpr ht) hpr
              · simp at hp'
            stack_remaining_subset := by
              intro p hp t ht
              rcases List.mem_cons.mp hp with rfl | hp'
              · exact Array.mem_toList_iff.mp ht
              · simp at hp'
          }
          have hinv_pushed : OuterInvariant succs isAccepting
              { st with outerVisited := st.outerVisited.insert init } [init] := {
            accepting_finished := by
              intro s hvis haccept hnotmem
              have hs_ne : s ≠ init := fun heq' => hnotmem (heq' ▸ List.mem_cons_self ..)
              have hvis_old : st.outerVisited.contains s := by
                simp [Std.HashSet.contains_insert] at hvis
                rcases hvis with rfl | hvis
                · exact absurd rfl hs_ne
                · exact hvis
              exact hinv.accepting_finished s hvis_old haccept (by simp)
            finished_closed := hinv.finished_closed
            finished_subset_visited := by
              intro s hs
              have hold := hinv.finished_subset_visited s hs
              simp [Std.HashSet.contains_insert, hold]
            finished_stack_disjoint := by
              intro s hs
              rcases List.mem_cons.mp hs with heq' | hs'
              · intro hcontra
                have hcontra' := heq' ▸ hcontra
                exact absurd (hinv.finished_subset_visited init hcontra') hnotvisited
              · simp at hs'
            finished_no_cycle := by
              intro s haccept hnotmem hvis
              have hs_ne : s ≠ init := fun heq' => hnotmem (heq' ▸ List.mem_cons_self ..)
              have hvis_old : st.outerVisited.contains s := by
                simp [Std.HashSet.contains_insert] at hvis
                rcases hvis with rfl | hvis
                · exact absurd rfl hs_ne
                · exact hvis
              exact hinv.finished_no_cycle s haccept (by simp) hvis_old
            stack_subset_visited := by
              intro s hs
              rcases List.mem_cons.mp hs with rfl | hs'
              · simp [Std.HashSet.contains_insert]
              · simp at hs'
          }
          have hps_pushed : ([init] : List State) =
              ([(init, (succs init).toList)].map Prod.fst).reverse := by simp
          have hrc'' : OuterReachClosed succs st'' [] :=
            outerDFSLoop_fuel_reach_closed succs isAccepting m
              [(init, (succs init).toList)] [init]
              { st with outerVisited := st.outerVisited.insert init }
              (by intro s hs; simp only [List.mem_singleton] at hs; subst hs
                  simp [Std.HashSet.contains_insert])
              heq hrc_pushed
          have hinv'' : OuterInvariant succs isAccepting st'' [] :=
            outerDFSLoop_fuel_empty_no_cycle succs isAccepting m
              [(init, (succs init).toList)] [init]
              { st with outerVisited := st.outerVisited.insert init }
              hps_pushed heq hrc_pushed hinv_pushed
          have hmono_push : ∀ s, st.outerVisited.contains s → st''.outerVisited.contains s := by
            intro s hs
            exact outerDFSLoop_fuel_outerVisited_mono succs isAccepting m
              [(init, (succs init).toList)] [init]
              { st with outerVisited := st.outerVisited.insert init } heq s
              (by simp [Std.HashSet.contains_insert, hs])
          obtain ⟨st', hrc', hinv', hmono', hroots'⟩ := ih rest st'' h hrc'' hinv''
          refine ⟨st', hrc', hinv', fun s hs => hmono' s (hmono_push s hs), ?_⟩
          intro i hi
          rcases List.mem_cons.mp hi with heqi | hi'
          · have hinit_vis : st''.outerVisited.contains init :=
              outerDFSLoop_fuel_outerVisited_mono succs isAccepting m
                [(init, (succs init).toList)] [init]
                { st with outerVisited := st.outerVisited.insert init } heq init
                (by simp [Std.HashSet.contains_insert])
            exact heqi ▸ hmono' init hinit_vis
          · exact hroots' i hi'

/-- If `nestedDFS_fuel.go` returns `.nonEmpty stem loop`, `(stem, loop)` is a
    genuine accepting-cycle witness rooted at one of `remaining`'s states.
    Composes `outerDFSLoop_fuel_nonEmpty_witness` across the `initialStates`
    loop, exactly as `nestedDFS_fuel_go_correct` does for the `.empty` case —
    the CAVA analogue is the same asymmetry noted there: CAVA's generic
    multi-root framework gets this for free from `lasso_inv` being a
    `param_DFS`-level invariant (covering `new_root` transitions
    automatically), whereas our concrete `initialStates` recursion needs its
    own composition theorem. -/
theorem nestedDFS_fuel_go_nonEmpty_witness
    (succs : State → Array State) (isAccepting : State → Bool)
    (remaining : List State) (st : FNDFSState State) (fuel : Nat)
    {stem loop : List State}
    (h : nestedDFS_fuel.go succs isAccepting remaining st fuel = some (.nonEmpty stem loop))
    (hrc : OuterReachClosed succs st [])
    (hinv : OuterInvariant succs isAccepting st []) :
    (∀ (hs : stem ≠ []), stem.head hs ∈ remaining) ∧
    stem.length ≥ 1 ∧
    loop.tail.length ≥ 1 ∧
    (∀ i, (hi : i + 1 < stem.length) → stem[i+1] ∈ succs stem[i]) ∧
    (∀ (hs : stem ≠ []) (hl : loop.tail ≠ []), stem.getLast hs = loop.tail.head hl) ∧
    (∀ i, (hi : i + 1 < loop.tail.length) → loop.tail[i+1] ∈ succs loop.tail[i]) ∧
    (∀ (hl : loop.tail ≠ []), loop.tail.head hl ∈ succs (loop.tail.getLast hl)) ∧
    (∀ (hl : loop.tail ≠ []), isAccepting (loop.tail.head hl) = true) := by
  induction fuel generalizing remaining st with
  | zero => simp [nestedDFS_fuel.go.eq_def] at h
  | succ m ih =>
    rw [nestedDFS_fuel.go.eq_def] at h
    simp only at h
    split at h
    · -- remaining = []
      simp at h
    · -- remaining = init :: rest
      rename_i init rest
      split at h
      · -- init already visited
        obtain ⟨hmem, hrest⟩ := ih rest st h hrc hinv
        exact ⟨fun hs => List.mem_cons_of_mem _ (hmem hs), hrest⟩
      · -- init fresh
        rename_i hnotvisited
        have hrc_pushed : OuterReachClosed succs
            { st with outerVisited := st.outerVisited.insert init }
            [(init, (succs init).toList)] := {
          stack_chain := trivial
          done_closed := by
            intro s hvis hnotmem t ht
            have hs_ne : s ≠ init := fun heq' => hnotmem (heq' ▸ List.mem_cons_self ..)
            have hvis_old : st.outerVisited.contains s := by
              simp [Std.HashSet.contains_insert] at hvis
              rcases hvis with rfl | hvis
              · exact absurd rfl hs_ne
              · exact hvis
            have ht_old := hrc.done_closed s hvis_old (by simp) t ht
            simp [Std.HashSet.contains_insert, ht_old]
          stack_processed_visited := by
            intro p hp t ht hpr
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact absurd (Array.mem_toList_iff.mpr ht) hpr
            · simp at hp'
          stack_remaining_subset := by
            intro p hp t ht
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact Array.mem_toList_iff.mp ht
            · simp at hp'
        }
        have hinv_pushed : OuterInvariant succs isAccepting
            { st with outerVisited := st.outerVisited.insert init } [init] := {
          accepting_finished := by
            intro s hvis haccept hnotmem
            have hs_ne : s ≠ init := fun heq' => hnotmem (heq' ▸ List.mem_cons_self ..)
            have hvis_old : st.outerVisited.contains s := by
              simp [Std.HashSet.contains_insert] at hvis
              rcases hvis with rfl | hvis
              · exact absurd rfl hs_ne
              · exact hvis
            exact hinv.accepting_finished s hvis_old haccept (by simp)
          finished_closed := hinv.finished_closed
          finished_subset_visited := by
            intro s hs
            have hold := hinv.finished_subset_visited s hs
            simp [Std.HashSet.contains_insert, hold]
          finished_stack_disjoint := by
            intro s hs
            rcases List.mem_cons.mp hs with heq' | hs'
            · intro hcontra
              have hcontra' := heq' ▸ hcontra
              exact absurd (hinv.finished_subset_visited init hcontra') hnotvisited
            · simp at hs'
          finished_no_cycle := by
            intro s haccept hnotmem hvis
            have hs_ne : s ≠ init := fun heq' => hnotmem (heq' ▸ List.mem_cons_self ..)
            have hvis_old : st.outerVisited.contains s := by
              simp [Std.HashSet.contains_insert] at hvis
              rcases hvis with rfl | hvis
              · exact absurd rfl hs_ne
              · exact hvis
            exact hinv.finished_no_cycle s haccept (by simp) hvis_old
          stack_subset_visited := by
            intro s hs
            rcases List.mem_cons.mp hs with rfl | hs'
            · simp [Std.HashSet.contains_insert]
            · simp at hs'
        }
        have hps_pushed : ([init] : List State) =
            ([(init, (succs init).toList)].map Prod.fst).reverse := by simp
        have hchain_pushed : ∀ i, (hi : i + 1 < ([init] : List State).length) →
            ([init] : List State)[i+1] ∈ succs ([init] : List State)[i] := by
          intro i hi; simp at hi
        have hroot_pushed : ∀ (hp : ([init] : List State) ≠ []),
            ([init] : List State).head hp = init := fun _ => rfl
        have hsv_pushed : ∀ s ∈ ([init] : List State),
            ({ st with outerVisited := st.outerVisited.insert init } :
              FNDFSState State).outerVisited.contains s := by
          intro s hs
          simp only [List.mem_singleton] at hs
          subst hs
          simp [Std.HashSet.contains_insert]
        split at h
        · -- fuel ran out inside outerDFSLoop_fuel
          simp at h
        · -- found directly
          rename_i stem0 loop0 st'0 heq
          simp only [Option.some.injEq, EmptinessResult.nonEmpty.injEq] at h
          obtain ⟨heqs, heql⟩ := h
          subst heqs
          subst heql
          obtain ⟨hroot8, hlen, hltail, hchainstem, hoverlap, hchainloop, hback, haccept⟩ :=
            outerDFSLoop_fuel_nonEmpty_witness succs isAccepting m
              [(init, (succs init).toList)] [init]
              { st with outerVisited := st.outerVisited.insert init } init
              hps_pushed hchain_pushed hroot_pushed hsv_pushed hrc_pushed heq
          refine ⟨fun hs => ?_, hlen, hltail, hchainstem, hoverlap, hchainloop, hback, haccept⟩
          rw [hroot8 hs]
          exact List.mem_cons_self ..
        · -- empty, recurse
          rename_i st'' heq
          have hrc'' : OuterReachClosed succs st'' [] :=
            outerDFSLoop_fuel_reach_closed succs isAccepting m
              [(init, (succs init).toList)] [init]
              { st with outerVisited := st.outerVisited.insert init }
              (by intro s hs; simp only [List.mem_singleton] at hs; subst hs
                  simp [Std.HashSet.contains_insert])
              heq hrc_pushed
          have hinv'' : OuterInvariant succs isAccepting st'' [] :=
            outerDFSLoop_fuel_empty_no_cycle succs isAccepting m
              [(init, (succs init).toList)] [init]
              { st with outerVisited := st.outerVisited.insert init }
              hps_pushed heq hrc_pushed hinv_pushed
          obtain ⟨hmem, hrest⟩ := ih rest st'' h hrc'' hinv''
          exact ⟨fun hs => List.mem_cons_of_mem _ (hmem hs), hrest⟩

end GoCorrectness

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
  rintro ⟨ac, -⟩
  rw [nestedDFS_fuel] at h
  have hrc₀ : OuterReachClosed succs
      ({ outerVisited := Std.HashSet.emptyWithCapacity 1024
         innerFinished := Std.HashSet.emptyWithCapacity 1024 } : FNDFSState State) [] := {
    stack_chain := trivial
    done_closed := fun s hs => absurd hs (by simp [Std.HashSet.contains_emptyWithCapacity])
    stack_processed_visited := fun p hp => absurd hp (by simp)
    stack_remaining_subset := fun p hp => absurd hp (by simp)
  }
  have hinv₀ : OuterInvariant succs isAccepting
      ({ outerVisited := Std.HashSet.emptyWithCapacity 1024
         innerFinished := Std.HashSet.emptyWithCapacity 1024 } : FNDFSState State) [] := {
    accepting_finished := fun s hs => absurd hs (by simp [Std.HashSet.contains_emptyWithCapacity])
    finished_closed := fun s hs => absurd hs (by simp [Std.HashSet.contains_emptyWithCapacity])
    finished_subset_visited := fun s hs =>
      absurd hs (by simp [Std.HashSet.contains_emptyWithCapacity])
    finished_stack_disjoint := fun s hs => absurd hs (by simp)
    finished_no_cycle := fun s _ _ hs =>
      absurd hs (by simp [Std.HashSet.contains_emptyWithCapacity])
    stack_subset_visited := fun s hs => absurd hs (by simp)
  }
  obtain ⟨st', hrc', hinv', -, hroots⟩ :=
    nestedDFS_fuel_go_correct succs isAccepting initialStates _ fuel h hrc₀ hinv₀
  have hstem_ne : ac.stem ≠ [] := List.ne_nil_of_length_pos (by have := ac.stem_nonempty; omega)
  have hcycle_ne : ac.cycle ≠ [] :=
    List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)
  have hstem_head_vis : st'.outerVisited.contains (ac.stem.head hstem_ne) :=
    hroots _ ac.stem_head_initial
  have hCL : ∀ x, st'.outerVisited.contains x →
      ∀ y ∈ succs x, st'.outerVisited.contains y ∨ False :=
    fun x hx y hy => Or.inl (hrc'.done_closed x hx (by simp) y hy)
  have hcyclehead_vis : st'.outerVisited.contains (ac.cycle.head hcycle_ne) := by
    rcases chain_reaches ac.stem ac.stem_chain hstem_ne with heq | hp
    · have : ac.stem.getLast hstem_ne = ac.cycle.head hcycle_ne := ac.overlap
      exact this ▸ heq ▸ hstem_head_vis
    · have hp' : PathTo succs (fun _ => False) (ac.stem.head hstem_ne)
          (ac.cycle.head hcycle_ne) := ac.overlap ▸ hp
      exact PathTo.closed_of_no_escape hCL hp' hstem_head_vis (fun _ _ h => h)
  have hcyclehead_fin : st'.innerFinished.contains (ac.cycle.head hcycle_ne) :=
    hinv'.accepting_finished _ hcyclehead_vis ac.cycle_head_accepting (by simp)
  have hself_loop : PathTo succs (fun _ => False) (ac.cycle.head hcycle_ne)
      (ac.cycle.head hcycle_ne) := by
    rcases chain_reaches ac.cycle ac.cycle_chain hcycle_ne with heq | hp
    · exact heq ▸ PathTo.direct (heq ▸ ac.cycle_back)
    · exact PathTo.trans hp (PathTo.direct ac.cycle_back)
  exact hinv'.finished_no_cycle _ ac.cycle_head_accepting (by simp) hcyclehead_vis hself_loop

/-- If the fuel-based nested DFS returns `nonEmpty stem loop`, then `(stem,
    loop.tail)` is a genuine accepting cycle: `stem` is a real path from an
    initial state to an accepting state, and `loop.tail` is a real cycle from
    that state back to itself.

    This is the soundness direction of the emptiness check — the CAVA
    analogue is the `Some` branch of `blue_dfs_correct` (`Nested_DFS.thy`),
    proved there directly from `lasso_inv`. Combined with
    `nestedDFS_fuel_empty_no_cycle` above (the completeness direction, CAVA's
    `None` branch), `nestedDFS_fuel` is a fully verified decision procedure
    for accepting-cycle existence (modulo the not-yet-proved
    termination/finiteness, Phase 2). -/
theorem nestedDFS_fuel_nonEmpty_valid [BEq State] [Hashable State] [LawfulBEq State]
    {initialStates : List State}
    {succs : State → Array State} {isAccepting : State → Bool}
    {fuel : Nat} {stem loop : List State}
    (h : nestedDFS_fuel initialStates succs isAccepting fuel = some (.nonEmpty stem loop)) :
    ∃ ac : AcceptingCycle initialStates succs isAccepting,
      ac.stem = stem ∧ ac.cycle = loop.tail := by
  rw [nestedDFS_fuel] at h
  have hrc₀ : OuterReachClosed succs
      ({ outerVisited := Std.HashSet.emptyWithCapacity 1024
         innerFinished := Std.HashSet.emptyWithCapacity 1024 } : FNDFSState State) [] := {
    stack_chain := trivial
    done_closed := fun s hs => absurd hs (by simp [Std.HashSet.contains_emptyWithCapacity])
    stack_processed_visited := fun p hp => absurd hp (by simp)
    stack_remaining_subset := fun p hp => absurd hp (by simp)
  }
  have hinv₀ : OuterInvariant succs isAccepting
      ({ outerVisited := Std.HashSet.emptyWithCapacity 1024
         innerFinished := Std.HashSet.emptyWithCapacity 1024 } : FNDFSState State) [] := {
    accepting_finished := fun s hs => absurd hs (by simp [Std.HashSet.contains_emptyWithCapacity])
    finished_closed := fun s hs => absurd hs (by simp [Std.HashSet.contains_emptyWithCapacity])
    finished_subset_visited := fun s hs =>
      absurd hs (by simp [Std.HashSet.contains_emptyWithCapacity])
    finished_stack_disjoint := fun s hs => absurd hs (by simp)
    finished_no_cycle := fun s _ _ hs =>
      absurd hs (by simp [Std.HashSet.contains_emptyWithCapacity])
    stack_subset_visited := fun s hs => absurd hs (by simp)
  }
  obtain ⟨hroot, hlen, hltail, hchainstem, hoverlap, hchainloop, hback, haccept⟩ :=
    nestedDFS_fuel_go_nonEmpty_witness succs isAccepting initialStates _ fuel h hrc₀ hinv₀
  have hstem_ne : stem ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hloop_ne : loop.tail ≠ [] := List.ne_nil_of_length_pos (by omega)
  exact ⟨{
    stem := stem
    cycle := loop.tail
    stem_nonempty := hlen
    cycle_nonempty := hltail
    stem_head_initial := hroot hstem_ne
    stem_chain := hchainstem
    overlap := hoverlap hstem_ne hloop_ne
    cycle_chain := hchainloop
    cycle_back := hback hloop_ne
    cycle_head_accepting := haccept hloop_ne
  }, rfl, rfl⟩

end LTLLib
