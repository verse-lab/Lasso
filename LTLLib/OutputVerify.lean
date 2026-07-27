/-
  Output verification for the nested DFS emptiness check.

  Given that `nestedDFS` returns `nonEmpty stem loop`, we verify that the
  stem + cycle form a valid lasso witnessing an accepting run of the BA.

  The cycle is `loop.tail` (the raw loop has a duplicated seed at the front).

  This connects the computational output to the abstract `ValidLasso` theory
  in `Lasso.lean`, which proves that a valid lasso implies an accepting run.
-/
import LTLLib.Lasso
import LTLLib.BA
import LTLLib.NestedDFSCorrectness

namespace LTLLib

/-! ## Converting computational checks to ValidLasso -/

/-- If `Array.contains` returns true, then the element is a member. -/
private theorem array_contains_mem {α : Type u} [BEq α] [LawfulBEq α]
    {arr : Array α} {x : α} (h : arr.contains x = true) : x ∈ arr :=
  Array.mem_of_contains_eq_true h

/-- A valid lasso for `BA.toSpec`, stated in terms of computational checks.

    `stem` is the path from an initial state to an accepting state (inclusive).
    `cycle` is the cycle starting and ending at the accepting state.
    In the nestedDFS output, `cycle = loop.tail` (dropping the duplicate seed). -/
theorem ba_hasAcceptingRun_of_lasso [BEq α] [Hashable α]
    (ba : BA α) (stem cycle : List BAState)
    (hstem_ne : stem.length ≥ 1)
    (hcycle_ne : cycle.length ≥ 1)
    (hinit : ba.initialStates.contains
      (stem.head (List.ne_nil_of_length_pos (by omega))) = true)
    (hstem_chain : ∀ (i : Nat), (hi : i + 1 < stem.length) →
      (ba.getSuccessors (stem[i]'(by omega))).contains (stem[i + 1]'(by omega)) = true)
    (hoverlap : stem.getLast (List.ne_nil_of_length_pos (by omega)) =
                cycle.head (List.ne_nil_of_length_pos (by omega)))
    (hcycle_chain : ∀ (i : Nat), (hi : i + 1 < cycle.length) →
      (ba.getSuccessors (cycle[i]'(by omega))).contains (cycle[i + 1]'(by omega)) = true)
    (hback : (ba.getSuccessors (cycle.getLast (List.ne_nil_of_length_pos (by omega)))).contains
      (cycle.head (List.ne_nil_of_length_pos (by omega))) = true)
    (haccepting : ba.isAccepting
      (cycle.head (List.ne_nil_of_length_pos (by omega))) = true) :
    ∃ σ, (ba.toSpec).isRun σ ∧ (ba.toSpec).isAcceptingRun σ := by
  -- Construct ValidLasso from computational checks
  have hv : ValidLasso (ba.toSpec) stem cycle := {
    stem_nonempty := hstem_ne
    cycle_nonempty := hcycle_ne
    stem_initial := hinit
    stem_chain := fun i hi => array_contains_mem (hstem_chain i hi)
    overlap := hoverlap
    cycle_chain := fun i hi => array_contains_mem (hcycle_chain i hi)
    cycle_back := array_contains_mem hback
    cycle_accepting := haccepting
  }
  exact ⟨hv.run, hv.run_isRun, hv.run_isAccepting⟩

/-! ## Connecting nestedDFS raw output to the lasso -/

/-- The raw nestedDFS output has `loop = [seed, seed, ...]` or `loop = [seed, last]`
    where `last` has `seed` as successor. The cycle is `loop.tail`. -/
theorem ba_hasAcceptingRun_of_ndfs_output [BEq α] [Hashable α]
    (ba : BA α) (stem loop : List BAState)
    (hstem_ne : stem.length ≥ 1)
    (hloop_ge : loop.length ≥ 2)
    (hinit : ba.initialStates.contains
      (stem.head (List.ne_nil_of_length_pos (by omega))) = true)
    (hstem_chain : ∀ (i : Nat), (hi : i + 1 < stem.length) →
      (ba.getSuccessors (stem[i]'(by omega))).contains (stem[i + 1]'(by omega)) = true)
    (hoverlap : stem.getLast (List.ne_nil_of_length_pos (by omega)) =
                loop[1]'(by omega))
    (hloop_tail_chain : ∀ (i : Nat), (hi : i + 1 < loop.tail.length) →
      (ba.getSuccessors ((loop.tail)[i]'(by omega))).contains
        ((loop.tail)[i + 1]'(by omega)) = true)
    (hloop_back : (ba.getSuccessors (loop.getLast (List.ne_nil_of_length_pos (by omega)))).contains
      (loop[1]'(by omega)) = true)
    (haccepting : ba.isAccepting (loop[1]'(by omega)) = true) :
    ∃ σ, (ba.toSpec).isRun σ ∧ (ba.toSpec).isAcceptingRun σ := by
  -- cycle = loop.tail
  have hcycle_ne : loop.tail.length ≥ 1 := by simp [List.length_tail]; omega
  have hhead : loop.tail.head (List.ne_nil_of_length_pos (by omega)) =
      loop[1]'(by omega) := by
    simp [List.head_eq_getElem, List.getElem_tail]
  have hlast : loop.tail.getLast (List.ne_nil_of_length_pos (by omega)) =
      loop.getLast (List.ne_nil_of_length_pos (by omega)) := by
    simp [List.getLast_eq_getElem, List.getElem_tail, List.length_tail]; congr 1; omega
  -- Apply the cleaned-up theorem
  exact ba_hasAcceptingRun_of_lasso ba stem loop.tail
    hstem_ne hcycle_ne
    hinit hstem_chain
    (by rw [hhead]; exact hoverlap)
    hloop_tail_chain
    (by rw [hlast, hhead]; exact hloop_back)
    (by rw [hhead]; exact haccepting)

/-! ## Connecting `nestedDFSWF`'s raw `AcceptingCycle` output to `ValidLasso`

Track B item 2 (`ProofPlan.md`) — CAVA's own move here (`CAVA_Impl.thy`'s
`ndfs_find_ce`, `RETURN (Some (Some (map_lasso fst (lasso_of_prpl l))))`) is
a one-line repackaging of the raw `(pr, pl)` witness into a `lasso` record.
`AcceptingCycle` (`NestedDFSCorrectness.lean`) is already field-for-field the
same shape as CAVA's `is_lasso_prpl_pre`, so the Lean analogue is just as
mechanical: convert each field into `ValidLasso`'s vocabulary. -/

/-- An `AcceptingCycle` over a concrete `BA`'s own successor/initial/accepting
functions is exactly a `ValidLasso` for that `BA`'s `toSpec` — pure
repackaging, no new mathematical content (mirrors CAVA's `lasso_of_prpl`). -/
def AcceptingCycle.toValidLasso [BEq α] [Hashable α] {ba : BA α}
    (ac : AcceptingCycle ba.initialStates.toList ba.getSuccessors ba.isAccepting) :
    ValidLasso ba.toSpec ac.stem ac.cycle where
  stem_nonempty := ac.stem_nonempty
  cycle_nonempty := ac.cycle_nonempty
  stem_initial :=
    Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp ac.stem_head_initial)
  stem_chain := ac.stem_chain
  overlap := ac.overlap
  cycle_chain := ac.cycle_chain
  cycle_back := ac.cycle_back
  cycle_accepting := ac.cycle_head_accepting

/-! ## Every state on the cycle stays inside a well-formed `BA`'s state set

Needed to invoke `canonicalLabel` compatibility (Track B item 3's deferred
step 4, `ProofPlan.md`) at each point of the lasso-derived run. Direct
analogue of `DegeneralBridge.lean`'s `run_states_mem`, over `AcceptingCycle`'s
explicit list-index chain instead of an abstract `Nat`-indexed run. -/

theorem AcceptingCycle.stem_states_mem [BEq α] [Hashable α] {ba : BA α}
    (hwf : ba.WellFormed)
    (ac : AcceptingCycle ba.initialStates.toList ba.getSuccessors ba.isAccepting) :
    ∀ (i : Nat) (hi : i < ac.stem.length), ba.states.contains (ac.stem[i]'hi) = true := by
  intro i
  induction i with
  | zero =>
    intro hi
    have h0 : ac.stem[0]'hi = ac.stem.head (List.ne_nil_of_length_pos (by omega)) := by
      rw [List.head_eq_getElem]
    rw [h0]
    exact hwf.initial_mem _
      (Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp ac.stem_head_initial))
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    have hchain := ac.stem_chain i (by omega)
    exact hwf.succ_mem _ _ hprev hchain

theorem AcceptingCycle.cycle_states_mem [BEq α] [Hashable α] {ba : BA α}
    (hwf : ba.WellFormed)
    (ac : AcceptingCycle ba.initialStates.toList ba.getSuccessors ba.isAccepting) :
    ∀ (i : Nat) (hi : i < ac.cycle.length), ba.states.contains (ac.cycle[i]'hi) = true := by
  have hsn := ac.stem_nonempty
  have hcn := ac.cycle_nonempty
  have hhead : ba.states.contains
      (ac.cycle.head (List.ne_nil_of_length_pos (by omega))) = true := by
    rw [← ac.overlap]
    have hlast : ac.stem[ac.stem.length - 1]'(by omega) =
        ac.stem.getLast (List.ne_nil_of_length_pos (by omega)) := by
      rw [List.getLast_eq_getElem]
    rw [← hlast]
    exact AcceptingCycle.stem_states_mem hwf ac (ac.stem.length - 1) (by omega)
  intro i
  induction i with
  | zero =>
    intro hi
    have h0 : ac.cycle[0]'hi = ac.cycle.head (List.ne_nil_of_length_pos (by omega)) := by
      rw [List.head_eq_getElem]
    rw [h0]; exact hhead
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    have hchain := ac.cycle_chain i (by omega)
    exact hwf.succ_mem _ _ hprev hchain

/-- Every position of the lasso-derived run stays inside a well-formed `BA`'s
state set — combines `stem_states_mem`/`cycle_states_mem` across
`lassoRun`'s own case split. The fact Track B item 3's deferred step 4
(`ProofPlan.md`) actually needs to invoke `canonicalLabel` compatibility at
every point of the run. -/
theorem AcceptingCycle.run_states_mem [BEq α] [Hashable α] {ba : BA α}
    (hwf : ba.WellFormed)
    (ac : AcceptingCycle ba.initialStates.toList ba.getSuccessors ba.isAccepting) (n : Nat) :
    ba.states.contains (ac.toValidLasso.run n) = true := by
  simp only [ValidLasso.run, lassoRun]
  split
  · next h => exact ac.stem_states_mem hwf n (by omega)
  · split
    · next h2 => exact ac.cycle_states_mem hwf _ (Nat.mod_lt _ h2)
    · next h h2 => exact absurd ac.cycle_nonempty (by omega)

end LTLLib
