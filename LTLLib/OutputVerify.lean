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

end LTLLib
