/-
  Correctness of the edge-aware nested DFS `nestedDFST_fuel` against `TAcceptingCycle` with a single mark.
  The inner-DFS lemmas of `NestedDFSCorrectness.lean` are reused unchanged, the outer-DFS invariants are re-derived for
  the three-tuple stack `(State × List State × Bool)` and the algorithm's three cases (back edge, postorder-triggered
  tree edge, immediate forward/cross edge).

  Defines:
  - `TStackMarked`: each frame's `marked` bit reflects whether its tree edge is marked
  - `TOuterReachClosed`: `outerVisited` behaves like a DFS discovered-set
  - `TOuterInvariant`: the acceptance-agnostic outer-DFS invariant
  - `TStackPending`: non-parent ancestors with an edge to a frame still have it pending
  - `TStackBackUnmarked`: already-examined edges into the stack are unmarked

  Proves:
  - `outerDFST_fuel_reach_closed`: `TOuterReachClosed` is maintained by the outer DFS
  - `outerDFST_fuel_nonEmpty_witness`: a `.nonEmpty stem loop` result is a stem and a cycle with a marked edge
  - `outerDFST_fuel_empty_no_cycle`: after `.empty`, no marked edge has a path back from its target to its source
  - `nestedDFST_fuel_empty_no_cycle`: if the nested DFS returns `.empty`, no `TAcceptingCycle` exists
  - `nestedDFST_fuel_nonEmpty_valid`: if it returns `.nonEmpty stem loop`, then `(stem, loop.tail)` is a `TAcceptingCycle`

  Sections:
  - Outer DFS reachability closure
  - Nonempty-witness soundness
  - Empty-result soundness
  - Top-level composition across roots
  - Top-level correctness theorem
-/
import LTLLib.AbstractSpec.GraphPaths
import LTLLib.NestedDFS.NestedDFSCorrectness
import LTLLib.TGBABased.AbstractSpec.EmptinessCheck
import LTLLib.TGBABased.NestedDFS.NestedDFST
import LTLLib.Tactic.Set

namespace LTLLib

/-! ## Outer DFS reachability closure -/

section OuterCorrectness

variable {State} [BEq State] [Hashable State] [LawfulBEq State]

/-- Every stack frame's `marked` bit is set iff the tree edge from the frame below it carries mark 0. -/
def TStackMarked (edgeMarks : State → State → Std.HashSet Nat) (stack : List (State × List State × Bool)) : Prop :=
  ∀ i, (hi : i + 1 < stack.length) →
    ((stack[i]'(by omega)).2.2 = true ↔ 0 ∈ edgeMarks (stack[i + 1]'hi).1 (stack[i]'(by omega)).1)

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- Dropping the top frame off a marked stack leaves a marked stack. -/
theorem TStackMarked.tail (edgeMarks : State → State → Std.HashSet Nat) (a : State × List State × Bool)
    (stack : List (State × List State × Bool)) (h : TStackMarked edgeMarks (a :: stack)) :
    TStackMarked edgeMarks stack := by
  intro i hi
  have := h (i + 1) (by simpa using hi)
  simpa using this

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- Replacing the top frame's `remaining` list preserves `TStackMarked`. -/
theorem TStackMarked.of_remaining_eq (edgeMarks : State → State → Std.HashSet Nat) (s : State) (r r' : List State)
    (marked : Bool) (stack : List (State × List State × Bool))
    (h : TStackMarked edgeMarks ((s, r, marked) :: stack)) :
    TStackMarked edgeMarks ((s, r', marked) :: stack) := by
  intro i hi
  match i, hi with
  | 0, hi => exact h 0 (by simpa using hi)
  | i + 1, hi => exact h (i + 1) (by simpa using hi)

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- Pushing a frame whose `marked` bit reflects its tree edge keeps the stack marked. -/
theorem TStackMarked.cons (edgeMarks : State → State → Std.HashSet Nat) (parent : State × List State × Bool)
    (stack : List (State × List State × Bool)) (s : State) (r : List State)
    (h : TStackMarked edgeMarks (parent :: stack)) :
    TStackMarked edgeMarks ((s, r, (edgeMarks parent.1 s).contains 0) :: parent :: stack) := by
  intro i hi
  match i, hi with
  | 0, hi => simp
  | i + 1, hi => exact h i (by simpa using hi)

/-- Outer-DFS bookkeeping independent of acceptance, `outerVisited` behaves like a DFS discovered-set.
The edge-aware analogue of `OuterReachClosed`. -/
structure TOuterReachClosed
    (succs : State → Array State) (st : FNDFSState State)
    (stack : List (State × List State × Bool)) : Prop where
  -- Every stack element can reach every element further down the stack.
  stack_chain : ReachChain succs (stack.map Prod.fst)
  -- Successors of an outer-done (visited, no longer on stack) state are also visited.
  done_closed : ∀ s, st.outerVisited.contains s → s ∉ stack.map Prod.fst →
    ∀ t ∈ succs s, st.outerVisited.contains t
  -- Already-processed (non-pending) successors of every stack frame are visited.
  stack_processed_visited : ∀ p ∈ stack, ∀ t ∈ succs p.1, t ∉ p.2.1 →
    st.outerVisited.contains t
  -- Every frame's `remaining` list only ever holds genuine successors of that frame's state.
  stack_remaining_subset : ∀ p ∈ stack, ∀ t ∈ p.2.1, t ∈ succs p.1

/-- `TOuterReachClosed` only depends on `st.outerVisited`. -/
def TOuterReachClosed.of_outerVisited_eq {succs : State → Array State} {st st'' : FNDFSState State}
    {stack : List (State × List State × Bool)}
    (heq : st''.outerVisited = st.outerVisited) (h : TOuterReachClosed succs st stack) :
    TOuterReachClosed succs st'' stack where
  stack_chain := h.stack_chain
  done_closed := fun s hvis hnotmem t ht => heq ▸ h.done_closed s (heq ▸ hvis) hnotmem t ht
  stack_processed_visited := fun p hp t ht hpr => heq ▸ h.stack_processed_visited p hp t ht hpr
  stack_remaining_subset := h.stack_remaining_subset

/-- `outerVisited` only grows across an `outerDFST_fuel` call, for any result. -/
theorem outerDFST_fuel_outerVisited_mono
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (fuel : Nat) (stack : List (State × List State × Bool)) (pathStack : List State)
    (st : FNDFSState State)
    {result : EmptinessResult State} {st' : FNDFSState State}
    (h : outerDFST_fuel succs edgeMarks fuel stack pathStack st = some (result, st')) :
    ∀ s, st.outerVisited.contains s → st'.outerVisited.contains s := by
  induction fuel generalizing stack pathStack st result st' with
  | zero => simp [outerDFST_fuel.eq_def] at h
  | succ m ih =>
    rw [outerDFST_fuel.eq_def] at h
    simp only at h
    split at h
    · -- stack = []
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact fun s hs => hs
    · rename_i current remaining marked rest
      split at h
      · -- remaining = []
        split at h
        · -- marked = true, rest = (parent, _, _) :: _
          rename_i parent parentRem parentMarked tail
          split at h
          · simp at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            rename_i st'' heq
            intro s hs
            exact innerDFS_fuel_outerVisited_eq succs parent pathStack.dropLast m current _ st
              _ _ st'' heq ▸ hs
          · rename_i st'' heq
            intro s hs
            exact ih ((parent, parentRem, parentMarked) :: tail) pathStack.dropLast st'' h s
              (innerDFS_fuel_outerVisited_eq succs parent pathStack.dropLast m current _ st
                none _ st'' heq ▸ hs)
        · -- marked = false, or rest = []
          exact ih rest pathStack.dropLast st h
      · -- remaining = succ :: remainingTail
        rename_i succ remainingTail
        split at h
        · -- back edge (succ ∈ pathStack)
          split at h
          · -- marked edge: returns immediately, st unchanged
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact fun s hs => hs
          · -- unmarked: recurse, skip
            exact ih ((current, remainingTail, marked) :: rest) pathStack st h
        · split at h
          · -- forward/cross edge (already visited, not cyan)
            split at h
            · -- marked
              split at h
              · simp at h
              · simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨-, rfl⟩ := h
                rename_i st'' heq
                intro s hs
                exact innerDFS_fuel_outerVisited_eq succs current pathStack m succ _ st
                  _ _ st'' heq ▸ hs
              · rename_i st'' heq
                intro s hs
                exact ih ((current, remainingTail, marked) :: rest) pathStack st'' h s
                  (innerDFS_fuel_outerVisited_eq succs current pathStack m succ _ st
                    none _ st'' heq ▸ hs)
            · -- unmarked: recurse, skip
              exact ih ((current, remainingTail, marked) :: rest) pathStack st h
          · -- fresh: recurse, push
            intro s hs
            exact ih ((succ, (succs succ).toList, (edgeMarks current succ).contains 0) ::
                (current, remainingTail, marked) :: rest)
              (pathStack ++ [succ]) { st with outerVisited := st.outerVisited.insert succ } h s
              (by simp [Std.HashSet.contains_insert, hs])

/-- `TOuterReachClosed` is maintained across `outerDFST_fuel`, ending with an empty stack when it returns `.empty`. -/
theorem outerDFST_fuel_reach_closed
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (fuel : Nat)
    (stack : List (State × List State × Bool))
    (pathStack : List State)
    (st : FNDFSState State)
    {n : Nat} {st' : FNDFSState State}
    (hsv : ∀ s ∈ pathStack, st.outerVisited.contains s)
    (h : outerDFST_fuel succs edgeMarks fuel stack pathStack st = some (.empty n, st'))
    (hrc : TOuterReachClosed succs st stack) :
    TOuterReachClosed succs st' [] := by
  induction fuel generalizing stack pathStack st n st' with
  | zero => simp [outerDFST_fuel.eq_def] at h
  | succ m ih =>
    rw [outerDFST_fuel.eq_def] at h
    simp only at h
    split at h
    · -- stack = []
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact hrc
    · -- stack = (current, remaining, marked) :: rest
      rename_i current remaining marked rest
      split at h
      · -- remaining = []
        split at h
        · -- marked = true, rest = (parent, _, _) :: tail
          rename_i parent parentRem parentMarked tail
          split at h
          · simp at h
          · simp at h
          · -- inner DFS found none: recurse
            rename_i st'' heq
            have houter_eq : st''.outerVisited = st.outerVisited :=
              innerDFS_fuel_outerVisited_eq succs parent pathStack.dropLast m current _ st
                none _ st'' heq
            have hsv' : ∀ s ∈ pathStack.dropLast, st''.outerVisited.contains s := by
              intro s hs
              rw [houter_eq]
              exact hsv s (List.dropLast_subset _ hs)
            have hrc' : TOuterReachClosed succs st'' ((parent, parentRem, parentMarked) :: tail) := {
              stack_chain := ReachChain.tail current (((parent, parentRem, parentMarked) :: tail).map Prod.fst)
                (by simpa using hrc.stack_chain)
              done_closed := by
                intro s hvis hnotmem t ht
                rw [houter_eq] at hvis ⊢
                by_cases hsc : s = current
                · have ht' : t ∈ succs current := hsc ▸ ht
                  exact hrc.stack_processed_visited (current, [], true) (List.mem_cons_self ..)
                    t ht' (by simp)
                · have hnotmem' : s ∉ current :: ((parent, parentRem, parentMarked) :: tail).map Prod.fst :=
                    fun hmem => (List.mem_cons.mp hmem).elim hsc hnotmem
                  exact hrc.done_closed s hvis hnotmem' t ht
              stack_processed_visited := by
                intro p hp t ht hpr
                rw [houter_eq]
                exact hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp) t ht hpr
              stack_remaining_subset := fun p hp t ht =>
                hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp) t ht
            }
            exact ih ((parent, parentRem, parentMarked) :: tail) pathStack.dropLast st'' hsv' h hrc'
        · -- marked = false, or rest = []
          have hsv' : ∀ s ∈ pathStack.dropLast, st.outerVisited.contains s :=
            fun s hs => hsv s (List.dropLast_subset _ hs)
          have hrc' : TOuterReachClosed succs st rest := {
            stack_chain := ReachChain.tail current (rest.map Prod.fst)
              (by simpa using hrc.stack_chain)
            done_closed := by
              intro s hvis hnotmem t ht
              by_cases hsc : s = current
              · have ht' : t ∈ succs current := hsc ▸ ht
                exact hrc.stack_processed_visited (current, [], marked) (List.mem_cons_self ..)
                  t ht' (by simp)
              · have hnotmem' : s ∉ current :: rest.map Prod.fst :=
                  fun hmem => (List.mem_cons.mp hmem).elim hsc hnotmem
                exact hrc.done_closed s hvis hnotmem' t ht
            stack_processed_visited := fun p hp t ht hpr =>
              hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp) t ht hpr
            stack_remaining_subset := fun p hp t ht =>
              hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp) t ht
          }
          exact ih rest pathStack.dropLast st hsv' h hrc'
      · -- remaining = succ :: remainingTail
        rename_i succ remainingTail
        have hskip : st.outerVisited.contains succ →
            TOuterReachClosed succs st ((current, remainingTail, marked) :: rest) :=
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
                exact hrc.stack_processed_visited (current, succ :: remainingTail, marked)
                  (List.mem_cons_self ..) t ht hpr'
            · exact hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp') t ht hpr
          stack_remaining_subset := by
            intro p hp t ht
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact hrc.stack_remaining_subset (current, succ :: remainingTail, marked)
                (List.mem_cons_self ..) t (List.mem_cons_of_mem _ ht)
            · exact hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp') t ht
        }
        split at h
        · -- back edge (succ ∈ pathStack)
          rename_i hsucc_mem
          split at h
          · -- marked: reports .nonEmpty, contradicts .empty
            simp at h
          · -- unmarked: identical bookkeeping to "already visited, skip"
            exact ih ((current, remainingTail, marked) :: rest) pathStack st hsv h
              (hskip (hsv succ (by simpa using hsucc_mem)))
        · split at h
          · -- forward/cross edge (already visited, not cyan)
            rename_i hvisited
            split at h
            · -- marked
              split at h
              · simp at h
              · simp at h
              · -- inner DFS found none: recurse
                rename_i st'' heq
                have houter_eq : st''.outerVisited = st.outerVisited :=
                  innerDFS_fuel_outerVisited_eq succs current pathStack m succ _ st none _ st'' heq
                have hsv' : ∀ s ∈ pathStack, st''.outerVisited.contains s := by
                  intro s hs; rw [houter_eq]; exact hsv s hs
                have hrc' : TOuterReachClosed succs st''
                    ((current, remainingTail, marked) :: rest) :=
                  TOuterReachClosed.of_outerVisited_eq houter_eq (hskip hvisited)
                exact ih ((current, remainingTail, marked) :: rest) pathStack st'' hsv' h hrc'
            · -- unmarked: recurse, skip
              exact ih ((current, remainingTail, marked) :: rest) pathStack st hsv h (hskip hvisited)
          · -- fresh: recurse, push
            rename_i hnotvisited
            have hsucc_edge : succ ∈ succs current :=
              hrc.stack_remaining_subset (current, succ :: remainingTail, marked) (List.mem_cons_self ..)
                succ (List.mem_cons_self ..)
            have hrc' : TOuterReachClosed succs
                { st with outerVisited := st.outerVisited.insert succ }
                ((succ, (succs succ).toList, (edgeMarks current succ).contains 0) ::
                  (current, remainingTail, marked) :: rest) := {
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
                      have ht_old := hrc.stack_processed_visited (current, succ :: remainingTail, marked)
                        (List.mem_cons_self ..) t ht hpr'
                      simp [Std.HashSet.contains_insert, ht_old]
                  · have ht_old := hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp'') t ht hpr
                    simp [Std.HashSet.contains_insert, ht_old]
              stack_remaining_subset := by
                intro p hp t ht
                rcases List.mem_cons.mp hp with rfl | hp'
                · exact Array.mem_toList_iff.mp ht
                · rcases List.mem_cons.mp hp' with rfl | hp''
                  · exact hrc.stack_remaining_subset (current, succ :: remainingTail, marked)
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
            exact ih ((succ, (succs succ).toList, (edgeMarks current succ).contains 0) ::
                (current, remainingTail, marked) :: rest)
              (pathStack ++ [succ]) { st with outerVisited := st.outerVisited.insert succ }
              hsv' h hrc'

end OuterCorrectness

/-! ## Nonempty-witness soundness -/

-- A marked wraparound edge of `l` (last back to head) is a mark witness at index `l.length - 1`.
private theorem wraparound_mark_witness {State : Type u} (edgeMarks : State → State → Std.HashSet Nat)
    (l : List State) (hne : l ≠ []) (hm : 0 ∈ edgeMarks (l.getLast hne) (l.head hne)) :
    ∃ (i : Nat) (hi : i < l.length), 0 ∈ edgeMarks (l[i]) (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))) := by
  have hpos : 0 < l.length := List.length_pos_iff.mpr hne
  have hlt : l.length - 1 < l.length := by omega
  refine ⟨l.length - 1, hlt, ?_⟩
  have h1 : l[l.length - 1]'hlt = l.getLast hne := by rw [← List.getLast_eq_getElem]
  have h2 : (l.length - 1 + 1) % l.length = 0 := by
    have h2' : l.length - 1 + 1 = l.length := by omega
    rw [h2', Nat.mod_self]
  have h3 : l[(l.length - 1 + 1) % l.length]'(Nat.mod_lt _ (by omega)) = l[0]'(by omega) := by
    simp only [h2]
  rw [h1, h3, List.getElem_zero]
  exact hm

-- A marked first edge `l[0] → l[1]` is a mark witness at index `0`.
private theorem head_mark_witness {State : Type u} (edgeMarks : State → State → Std.HashSet Nat)
    (l : List State) (hlen2 : l.length ≥ 2) (hm : 0 ∈ edgeMarks (l[0]'(by omega)) (l[1]'(by omega))) :
    ∃ (i : Nat) (hi : i < l.length), 0 ∈ edgeMarks (l[i]) (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))) := by
  refine ⟨0, by omega, ?_⟩
  have h1 : (0 + 1) % l.length = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : l[(0 + 1) % l.length]'(Nat.mod_lt _ (by omega)) = l[1]'(by omega) := by simp only [h1]
  rw [h2]
  exact hm

section NonEmptyWitness

variable {State} [BEq State] [Hashable State] [LawfulBEq State]

/-- If `pathStack` is a `succs`-chain from `root` and `outerDFST_fuel` returns `.nonEmpty stem loop`, then `stem` is a chain
from `root` and `loop.tail` a cycle with a marked edge, the edge-aware analogue of `outerDFSLoop_fuel_nonEmpty_witness`. -/
theorem outerDFST_fuel_nonEmpty_witness
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (fuel : Nat)
    (stack : List (State × List State × Bool))
    (pathStack : List State)
    (st : FNDFSState State)
    (root : State)
    {stem loop : List State} {st' : FNDFSState State}
    (hps : pathStack = (stack.map Prod.fst).reverse)
    (hchain : ∀ i, (hi : i + 1 < pathStack.length) → pathStack[i+1] ∈ succs pathStack[i])
    (hroot : ∀ (hp : pathStack ≠ []), pathStack.head hp = root)
    (hsv : ∀ s ∈ pathStack, st.outerVisited.contains s)
    (hnodup : pathStack.Nodup)
    (hrc : TOuterReachClosed succs st stack)
    (hmarked : TStackMarked edgeMarks stack)
    (h : outerDFST_fuel succs edgeMarks fuel stack pathStack st =
      some (.nonEmpty stem loop, st')) :
    (∀ (hs : stem ≠ []), stem.head hs = root) ∧
    stem.length ≥ 1 ∧
    loop.tail.length ≥ 1 ∧
    (∀ i, (hi : i + 1 < stem.length) → stem[i+1] ∈ succs stem[i]) ∧
    (∀ (hs : stem ≠ []) (hl : loop.tail ≠ []), stem.getLast hs = loop.tail.head hl) ∧
    (∀ i, (hi : i + 1 < loop.tail.length) → loop.tail[i+1] ∈ succs loop.tail[i]) ∧
    (∀ (hl : loop.tail ≠ []), loop.tail.head hl ∈ succs (loop.tail.getLast hl)) ∧
    (∃ (i : Nat) (hi : i < loop.tail.length),
      0 ∈ edgeMarks (loop.tail[i]) (loop.tail[(i + 1) % loop.tail.length]'(Nat.mod_lt _ (by omega)))) := by
  induction fuel generalizing stack pathStack st stem loop st' with
  | zero => simp [outerDFST_fuel.eq_def] at h
  | succ m ih =>
    rw [outerDFST_fuel.eq_def] at h
    simp only at h
    split at h
    · -- stack = []
      simp at h
    · -- stack = (current, remaining, marked) :: rest
      rename_i current remaining marked rest
      split at h
      · -- remaining = []
        split at h
        · -- marked = true, rest = (parent, _, _) :: tail
          rename_i parent parentRem parentMarked tail
          split at h
          · simp at h
          · -- inner DFS found a cycle back to `parent` (or an ancestor): terminal
            rename_i cyclePath target _iv st'' heq
            simp only [Option.some.injEq, Prod.mk.injEq, EmptinessResult.nonEmpty.injEq] at h
            obtain ⟨⟨heqstem, heqloop⟩, -⟩ := h
            subst heqstem
            subst heqloop
            obtain ⟨htarget0, hlen0, hhead0, hchain0, hback0⟩ :=
              innerDFS_fuel_cyclePath_chain succs parent pathStack.dropLast m current
                (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq
            have hne0 : cyclePath ≠ [] := by intro hcontra; rw [hcontra] at hlen0; simp at hlen0
            have hpc3 : pathStack = (tail.map Prod.fst).reverse ++ [parent, current] := by simp [hps]
            have hne_path : pathStack ≠ [] := by simp [hpc3]
            have hgetlast_path : pathStack.getLast hne_path = current := by simp [hpc3]
            have hne_anc : pathStack.dropLast ≠ [] := by simp [hpc3]
            have hgetlast_anc : pathStack.dropLast.getLast hne_anc = parent := by simp [hpc3]
            have htarget_mem : target ∈ pathStack.dropLast := by
              rcases htarget0 with heqt | hmem
              · rw [heqt, ← hgetlast_anc]; exact List.getLast_mem hne_anc
              · exact hmem
            have htarget_mem' : target ∈ pathStack := List.dropLast_subset _ htarget_mem
            generalize hA_def : pathStack.takeWhile (fun y => !(y == target)) = A at ⊢
            generalize hB_def : pathStack.dropWhile (fun y => !(y == target)) = B at ⊢
            have hB? : B.head? = some target := by
              rw [← hB_def]; exact dropWhile_ne_head?_eq_some pathStack target htarget_mem'
            have hBne : B ≠ [] := by intro hc; rw [hc] at hB?; simp at hB?
            have hBhead : B.head hBne = target := (List.head_eq_iff_head?_eq_some hBne).mpr hB?
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
            -- `current` is `pathStack`'s last element, so by `Nodup` it is not `target`, which lies in the `dropLast` prefix.
            have hcurrent_notmem_anc : current ∉ pathStack.dropLast := by
              have heq : pathStack = pathStack.dropLast ++ [pathStack.getLast hne_path] :=
                (List.dropLast_concat_getLast hne_path).symm
              rw [hgetlast_path] at heq
              have hnd := heq ▸ hnodup
              rw [List.nodup_append] at hnd
              intro hmem
              exact hnd.2.2 current hmem current (List.mem_singleton_self _) rfl
            have htarget_ne_current : target ≠ current := fun heq => hcurrent_notmem_anc (heq ▸ htarget_mem)
            have hBlen2 : B.length ≥ 2 := by
              by_contra hc
              have hBlen1 : B.length = 1 := by
                have := List.length_pos_iff.mpr hBne; omega
              have hh := head_eq_getLast_of_length_eq_one B hBlen1 hBne
              rw [hBhead, hBgetlast] at hh
              exact htarget_ne_current hh
            have hBdropLastNe : B.dropLast ≠ [] := by
              intro hc
              have hd := List.length_dropLast (xs := B)
              rw [hc] at hd; simp at hd; omega
            have hBdropLastGetLast : B.dropLast.getLast hBdropLastNe = parent := by
              have hpsdl_eq : pathStack.dropLast = A ++ B.dropLast := by
                rw [heqAB]
                exact List.dropLast_append_of_ne_nil hBne
              have hsplit : pathStack.dropLast.getLast? = (B.dropLast).getLast?.or A.getLast? := by
                rw [hpsdl_eq]; exact List.getLast?_append
              rw [List.getLast?_eq_some_getLast hne_anc, hgetlast_anc] at hsplit
              have hBdlsome : B.dropLast.getLast? = some (B.dropLast.getLast hBdropLastNe) :=
                List.getLast?_eq_some_getLast hBdropLastNe
              rw [hBdlsome] at hsplit
              simp only [Option.some_or] at hsplit
              exact (Option.some.inj hsplit).symm
            have hBdropLastHead : B.dropLast.head hBdropLastNe = target := by
              rw [head_dropLast_eq B hBne hBdropLastNe]; exact hBhead
            have hedge : current ∈ succs parent := hgetlast_anc ▸ hgetlast_path ▸
              chain_getLast_edge pathStack hne_path hne_anc hchain
            have hstackmark : 0 ∈ edgeMarks parent current := (hmarked 0 (by simp)).mp (by simp)
            have hchainBdrop1 := chain_dropLast B hchainB
            by_cases hloopTailE : B.dropLast.dropLast = []
            · -- degenerate: target = parent, B = [parent, current]
              have hBdlLen1 : B.dropLast.length = 1 := by
                have hd1 := List.length_dropLast (xs := B)
                have hd2 := List.length_dropLast (xs := B.dropLast)
                rw [hloopTailE] at hd2
                simp at hd2
                omega
              have htarget_eq_parent : target = parent := by
                have hh := head_eq_getLast_of_length_eq_one B.dropLast hBdlLen1 hBdropLastNe
                rw [hBdropLastHead, hBdropLastGetLast] at hh
                exact hh
              simp only [List.tail_cons, hloopTailE, List.append_nil]
              refine ⟨fun hs => ?_, ?_, by simp, chain_dropLast pathStack hchain,
                ?_, chain_cons parent cyclePath hne0 hchain0 (hhead0 hne0 ▸ hedge), ?_, ?_⟩
              · rw [head_dropLast_eq pathStack hne_path hs]; exact hroot hne_path
              · exact List.length_pos_iff.mpr hne_anc
              · intro hs hl; exact hgetlast_anc
              · intro hl
                simp only [List.getLast_cons hne0, List.head_cons]
                rw [← htarget_eq_parent]
                exact hback0 hne0
              · exact head_mark_witness edgeMarks (parent :: cyclePath)
                  (by have := List.length_pos_iff.mpr hne0; simp; omega)
                  (by simp only [List.getElem_cons_succ, List.getElem_zero, hhead0 hne0]; exact hstackmark)
            · -- general: splice cyclePath with the stack-suffix B.dropLast.dropLast
              have hedgemid : B.dropLast.dropLast.head hloopTailE ∈ succs (cyclePath.getLast hne0) := by
                rw [head_dropLast_eq B.dropLast hBdropLastNe hloopTailE, hBdropLastHead]
                exact hback0 hne0
              have hchainBdrop2 := chain_dropLast B.dropLast hchainBdrop1
              have hchainfull :=
                chain_append cyclePath B.dropLast.dropLast hchain0 hchainBdrop2 hne0 hloopTailE hedgemid
              have hne_full : cyclePath ++ B.dropLast.dropLast ≠ [] := by simp [hne0]
              have hbackedge : parent ∈ succs ((cyclePath ++ B.dropLast.dropLast).getLast hne_full) := by
                rw [List.getLast_append_of_ne_nil _ hloopTailE]
                have hge := chain_getLast_edge B.dropLast hBdropLastNe hloopTailE hchainBdrop1
                rwa [hBdropLastGetLast] at hge
              simp only [List.cons_append, List.tail_cons]
              refine ⟨fun hs => ?_, ?_, by simp, chain_dropLast pathStack hchain,
                ?_, chain_cons parent (cyclePath ++ B.dropLast.dropLast) hne_full hchainfull
                  (by rw [List.head_append_of_ne_nil hne0, hhead0 hne0]; exact hedge),
                ?_, ?_⟩
              · rw [head_dropLast_eq pathStack hne_path hs]; exact hroot hne_path
              · exact List.length_pos_iff.mpr hne_anc
              · intro hs hl; exact hgetlast_anc
              · intro hl
                rw [List.getLast_cons hne_full]
                exact hbackedge
              · have hcyc0 : 0 < cyclePath.length := List.length_pos_iff.mpr hne0
                have h2 : (parent :: (cyclePath ++ B.dropLast.dropLast)).length ≥ 2 := by simp; omega
                have hidx1 : (1:Nat) < (parent :: (cyclePath ++ B.dropLast.dropLast)).length := by omega
                have hheadeq : (parent :: (cyclePath ++ B.dropLast.dropLast))[1]'hidx1 = current := by
                  simp only [List.getElem_cons_succ, List.getElem_append_left hcyc0]
                  rw [← hhead0 hne0, List.head_eq_getElem]
                refine head_mark_witness edgeMarks (parent :: (cyclePath ++ B.dropLast.dropLast)) h2 ?_
                simp only [List.getElem_cons_zero, hheadeq]
                exact hstackmark
          · -- inner DFS found none: recurse
            rename_i st'' heq
            have houter_eq : st''.outerVisited = st.outerVisited :=
              innerDFS_fuel_outerVisited_eq succs parent pathStack.dropLast m current _ st
                none _ st'' heq
            have hps' : pathStack.dropLast = (((parent, parentRem, parentMarked) :: tail).map Prod.fst).reverse := by
              simp [hps]
            have hchain' := chain_dropLast pathStack hchain
            have hpc : pathStack = (((parent, parentRem, parentMarked) :: tail).map Prod.fst).reverse ++ [current] :=
              by simp [hps]
            have hne_path : pathStack ≠ [] := by simp [hpc]
            have hroot' : ∀ (hp : pathStack.dropLast ≠ []), pathStack.dropLast.head hp = root :=
              fun hp => by rw [head_dropLast_eq pathStack hne_path hp]; exact hroot hne_path
            have hsv' : ∀ s ∈ pathStack.dropLast, st''.outerVisited.contains s := by
              rw [houter_eq]
              exact fun s hs => hsv s (List.dropLast_subset _ hs)
            have hrc' : TOuterReachClosed succs st'' ((parent, parentRem, parentMarked) :: tail) := {
              stack_chain := ReachChain.tail current (((parent, parentRem, parentMarked) :: tail).map Prod.fst)
                (by simpa using hrc.stack_chain)
              done_closed := by
                intro s hvis hnotmem t ht
                rw [houter_eq] at hvis ⊢
                by_cases hsc : s = current
                · have ht' : t ∈ succs current := hsc ▸ ht
                  exact hrc.stack_processed_visited (current, [], true) (List.mem_cons_self ..)
                    t ht' (by simp)
                · have hnotmem' : s ∉ current :: ((parent, parentRem, parentMarked) :: tail).map Prod.fst :=
                    fun hmem => (List.mem_cons.mp hmem).elim hsc hnotmem
                  exact hrc.done_closed s hvis hnotmem' t ht
              stack_processed_visited := by
                intro p hp t ht hpr
                rw [houter_eq]
                exact hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp) t ht hpr
              stack_remaining_subset := fun p hp t ht =>
                hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp) t ht
            }
            have hnodup' : pathStack.dropLast.Nodup := hnodup.sublist (List.dropLast_sublist pathStack)
            have hmarked' := TStackMarked.tail edgeMarks (current, [], true) _ hmarked
            exact ih ((parent, parentRem, parentMarked) :: tail) pathStack.dropLast st''
              hps' hchain' hroot' hsv' hnodup' hrc' hmarked' h
        · -- marked = false, or rest = []
          have hps' : pathStack.dropLast = (rest.map Prod.fst).reverse := by simp [hps]
          have hchain' := chain_dropLast pathStack hchain
          have hpc : pathStack = (rest.map Prod.fst).reverse ++ [current] := by simp [hps]
          have hne_path : pathStack ≠ [] := by simp [hpc]
          have hroot' : ∀ (hp : pathStack.dropLast ≠ []), pathStack.dropLast.head hp = root :=
            fun hp => by rw [head_dropLast_eq pathStack hne_path hp]; exact hroot hne_path
          have hrc' : TOuterReachClosed succs st rest := {
            stack_chain := ReachChain.tail current (rest.map Prod.fst)
              (by simpa using hrc.stack_chain)
            done_closed := by
              intro s hvis hnotmem t ht
              by_cases hsc : s = current
              · have ht' : t ∈ succs current := hsc ▸ ht
                exact hrc.stack_processed_visited (current, [], marked) (List.mem_cons_self ..)
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
          have hnodup' : pathStack.dropLast.Nodup := hnodup.sublist (List.dropLast_sublist pathStack)
          have hmarked' := TStackMarked.tail edgeMarks (current, [], marked) rest hmarked
          exact ih rest pathStack.dropLast st hps' hchain' hroot' hsv' hnodup' hrc' hmarked' h
      · -- remaining = succ :: remainingTail
        rename_i succ remainingTail
        have hsucc_edge : succ ∈ succs current :=
          hrc.stack_remaining_subset (current, succ :: remainingTail, marked) (List.mem_cons_self ..)
            succ (List.mem_cons_self ..)
        have hpc : pathStack = (rest.map Prod.fst).reverse ++ [current] := by simp [hps]
        have hne : pathStack ≠ [] := by simp [hpc]
        have hgetlast : pathStack.getLast hne = current := by simp [hpc]
        have hps_skip : pathStack = (((current, remainingTail, marked) :: rest).map Prod.fst).reverse := by
          simpa using hps
        have hskip : st.outerVisited.contains succ →
            TOuterReachClosed succs st ((current, remainingTail, marked) :: rest) :=
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
                exact hrc.stack_processed_visited (current, succ :: remainingTail, marked)
                  (List.mem_cons_self ..) t ht hpr'
            · exact hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp') t ht hpr
          stack_remaining_subset := by
            intro p hp t ht
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact hrc.stack_remaining_subset (current, succ :: remainingTail, marked)
                (List.mem_cons_self ..) t (List.mem_cons_of_mem _ ht)
            · exact hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp') t ht
        }
        split at h
        · -- back edge (succ ∈ pathStack)
          rename_i hsucc_mem
          split at h
          · -- marked: terminal
            rename_i hedgemarked
            simp only [Option.some.injEq, Prod.mk.injEq, EmptinessResult.nonEmpty.injEq] at h
            obtain ⟨⟨heqstem, heqloop⟩, -⟩ := h
            subst heqstem
            subst heqloop
            simp only [List.tail_cons]
            have hsucc_mem' : succ ∈ pathStack := by simpa using hsucc_mem
            generalize hA_def : pathStack.takeWhile (fun y => !(y == succ)) = A at ⊢
            generalize hB_def : pathStack.dropWhile (fun y => !(y == succ)) = B at ⊢
            have hB? : B.head? = some succ := by
              rw [← hB_def]; exact dropWhile_ne_head?_eq_some pathStack succ hsucc_mem'
            have hBne : B ≠ [] := by intro hc; rw [hc] at hB?; simp at hB?
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
            have hmarkwit : ∃ (i : Nat) (hi : i < B.length),
                0 ∈ edgeMarks (B[i]) (B[(i + 1) % B.length]'(Nat.mod_lt _ (by omega))) :=
              wraparound_mark_witness edgeMarks B hBne (by rw [hBgetlast, hBhead]; exact hedgemarked)
            by_cases hAe : A = []
            · -- A empty: stem = [succ]
              have hhead? : pathStack.head? = some succ := by
                rw [heqAB, hAe, List.nil_append]; exact hB?
              have hroot_succ : root = succ := by
                have h2 : pathStack.head? = some (pathStack.head hne) := List.head?_eq_some_head hne
                rw [h2] at hhead?
                rw [(Option.some.inj hhead?).symm]
                exact (hroot hne).symm
              refine ⟨fun hs => ?_, by simp, List.length_pos_iff.mpr hBne, by simp [hAe],
                ?_, hchainB, ?_, hmarkwit⟩
              · simp [hAe, hroot_succ]
              · intro hs hl; simp [hAe, hBhead]
              · intro hl; simpa [hBhead, hBgetlast] using hsucc_edge
            · -- A nonempty
              have hAgetlast_edge : succ ∈ succs (A.getLast hAe) := by
                have hbe := chain_append_boundary pathStack A B heqAB hAe hBne hchain
                rwa [hBhead] at hbe
              have hchainA := chain_append_left pathStack A B heqAB hchain
              have hchainstem := chain_append_singleton A succ hchainA hAe hAgetlast_edge
              have hAhead? : pathStack.head? = A.head? := by
                rw [heqAB, List.head?_append, List.head?_eq_some_head hAe]; simp
              have hAheadroot : A.head hAe = root := by
                have h2 : pathStack.head? = some (pathStack.head hne) := List.head?_eq_some_head hne
                rw [h2] at hAhead?
                have h3 : A.head? = some (A.head hAe) := List.head?_eq_some_head hAe
                rw [h3] at hAhead?
                rw [(Option.some.inj hAhead?).symm]
                exact hroot hne
              refine ⟨fun hs => ?_, by simp, List.length_pos_iff.mpr hBne, hchainstem,
                ?_, hchainB, ?_, hmarkwit⟩
              · rw [head_append_singleton_eq A succ hAe]; exact hAheadroot
              · intro hs hl; simp [hBhead]
              · intro hl; simpa [hBhead, hBgetlast] using hsucc_edge
          · -- unmarked: recurse, skip
            have hmarked' := TStackMarked.of_remaining_eq edgeMarks current (succ :: remainingTail)
              remainingTail marked rest hmarked
            exact ih ((current, remainingTail, marked) :: rest) pathStack st hps_skip hchain hroot hsv
              hnodup (hskip (hsv succ (by simpa using hsucc_mem))) hmarked' h
        · split at h
          · -- forward/cross edge (already visited, not cyan)
            rename_i hvisited
            have hmarked' := TStackMarked.of_remaining_eq edgeMarks current (succ :: remainingTail)
              remainingTail marked rest hmarked
            split at h
            · -- marked
              rename_i hedgemarked
              split at h
              · simp at h
              · -- inner DFS found a cycle back to `current` (or an ancestor): terminal
                rename_i cyclePath target _iv st'' heq
                simp only [Option.some.injEq, Prod.mk.injEq, EmptinessResult.nonEmpty.injEq] at h
                obtain ⟨⟨heqstem, heqloop⟩, -⟩ := h
                subst heqstem
                subst heqloop
                obtain ⟨htarget0, hlen0, hhead0, hchain0, hback0⟩ :=
                  innerDFS_fuel_cyclePath_chain succs current pathStack m succ
                    (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq
                have hne0 : cyclePath ≠ [] := by intro hcontra; rw [hcontra] at hlen0; simp at hlen0
                have hstackmark : 0 ∈ edgeMarks current succ := hedgemarked
                have hchainB1 := chain_dropLast pathStack hchain
                have htarget_mem : target ∈ pathStack := by
                  rcases htarget0 with heqt | hmem
                  · rw [heqt, ← hgetlast]; exact List.getLast_mem hne
                  · exact hmem
                generalize hA_def : pathStack.takeWhile (fun y => !(y == target)) = A at ⊢
                generalize hB_def : pathStack.dropWhile (fun y => !(y == target)) = B at ⊢
                have hB? : B.head? = some target := by
                  rw [← hB_def]; exact dropWhile_ne_head?_eq_some pathStack target htarget_mem
                have hBne : B ≠ [] := by intro hc; rw [hc] at hB?; simp at hB?
                have hBhead : B.head hBne = target := (List.head_eq_iff_head?_eq_some hBne).mpr hB?
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
                by_cases hloopTailE : B.dropLast = []
                · -- degenerate: target = current, B = [current] (singleton)
                  have hBlen1 : B.length = 1 := by
                    have hd := List.length_dropLast (xs := B)
                    rw [hloopTailE] at hd
                    have hge : B.length ≥ 1 := List.length_pos_iff.mpr hBne
                    simp at hd; omega
                  have htarget_eq_current : target = current := by
                    have hh := head_eq_getLast_of_length_eq_one B hBlen1 hBne
                    rw [hBhead, hBgetlast] at hh; exact hh
                  simp only [List.tail_cons, hloopTailE, List.append_nil]
                  refine ⟨fun hs => hroot hs, List.length_pos_iff.mpr hne, by simp, hchain,
                    ?_, chain_cons current cyclePath hne0 hchain0 (hhead0 hne0 ▸ hsucc_edge), ?_, ?_⟩
                  · intro hs hl; exact hgetlast
                  · intro hl
                    simp only [List.getLast_cons hne0, List.head_cons]
                    rw [← htarget_eq_current]
                    exact hback0 hne0
                  · exact head_mark_witness edgeMarks (current :: cyclePath)
                      (by have := List.length_pos_iff.mpr hne0; simp; omega)
                      (by simp only [List.getElem_cons_succ, List.getElem_zero, hhead0 hne0]
                          exact hstackmark)
                · -- general: splice cyclePath with the stack-suffix B.dropLast
                  have hchainBdrop := chain_dropLast B hchainB
                  have hedgemid : B.dropLast.head hloopTailE ∈ succs (cyclePath.getLast hne0) := by
                    rw [head_dropLast_eq B hBne hloopTailE, hBhead]
                    exact hback0 hne0
                  have hchainfull :=
                    chain_append cyclePath B.dropLast hchain0 hchainBdrop hne0 hloopTailE hedgemid
                  have hne_full : cyclePath ++ B.dropLast ≠ [] := by simp [hne0]
                  have hbackedge : current ∈ succs ((cyclePath ++ B.dropLast).getLast hne_full) := by
                    rw [List.getLast_append_of_ne_nil _ hloopTailE]
                    have hge := chain_getLast_edge B hBne hloopTailE hchainB
                    rwa [hBgetlast] at hge
                  simp only [List.cons_append, List.tail_cons]
                  refine ⟨fun hs => hroot hs, List.length_pos_iff.mpr hne, by simp, hchain,
                    ?_, chain_cons current (cyclePath ++ B.dropLast) hne_full hchainfull
                      (by rw [List.head_append_of_ne_nil hne0, hhead0 hne0]; exact hsucc_edge), ?_, ?_⟩
                  · intro hs hl; exact hgetlast
                  · intro hl
                    rw [List.getLast_cons hne_full]
                    exact hbackedge
                  · have hcyc0 : 0 < cyclePath.length := List.length_pos_iff.mpr hne0
                    have h2 : (current :: (cyclePath ++ B.dropLast)).length ≥ 2 := by simp; omega
                    have hidx1 : (1:Nat) < (current :: (cyclePath ++ B.dropLast)).length := by omega
                    have hheadeq : (current :: (cyclePath ++ B.dropLast))[1]'hidx1 = succ := by
                      simp only [List.getElem_cons_succ, List.getElem_append_left hcyc0]
                      rw [← hhead0 hne0, List.head_eq_getElem]
                    refine head_mark_witness edgeMarks (current :: (cyclePath ++ B.dropLast)) h2 ?_
                    simp only [List.getElem_cons_zero, hheadeq]
                    exact hstackmark
              · -- inner DFS found none: recurse
                rename_i st'' heq
                have houter_eq : st''.outerVisited = st.outerVisited :=
                  innerDFS_fuel_outerVisited_eq succs current pathStack m succ _ st none _ st'' heq
                have hsv' : ∀ s ∈ pathStack, st''.outerVisited.contains s := by
                  intro s hs; rw [houter_eq]; exact hsv s hs
                have hrc' : TOuterReachClosed succs st''
                    ((current, remainingTail, marked) :: rest) :=
                  TOuterReachClosed.of_outerVisited_eq houter_eq (hskip hvisited)
                exact ih ((current, remainingTail, marked) :: rest) pathStack st'' hps_skip hchain
                  hroot hsv' hnodup hrc' hmarked' h
            · -- unmarked: recurse, skip
              exact ih ((current, remainingTail, marked) :: rest) pathStack st hps_skip hchain hroot hsv
                hnodup (hskip hvisited) hmarked' h
          · -- fresh: recurse, push
            rename_i hnotvisited
            have hchain' := chain_append_singleton pathStack succ hchain hne (hgetlast ▸ hsucc_edge)
            have hroot' : ∀ (hp : (pathStack ++ [succ]) ≠ []), (pathStack ++ [succ]).head hp = root :=
              fun hp => by rw [head_append_singleton_eq pathStack succ hne]; exact hroot hne
            have hps' : pathStack ++ [succ] =
                (((succ, (succs succ).toList, (edgeMarks current succ).contains 0) ::
                  (current, remainingTail, marked) :: rest).map Prod.fst).reverse := by
              simp [hps]
            have hrc' : TOuterReachClosed succs
                { st with outerVisited := st.outerVisited.insert succ }
                ((succ, (succs succ).toList, (edgeMarks current succ).contains 0) ::
                  (current, remainingTail, marked) :: rest) := {
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
                      have ht_old := hrc.stack_processed_visited (current, succ :: remainingTail, marked)
                        (List.mem_cons_self ..) t ht hpr'
                      simp [Std.HashSet.contains_insert, ht_old]
                  · have ht_old := hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp'') t ht hpr
                    simp [Std.HashSet.contains_insert, ht_old]
              stack_remaining_subset := by
                intro p hp t ht
                rcases List.mem_cons.mp hp with rfl | hp'
                · exact Array.mem_toList_iff.mp ht
                · rcases List.mem_cons.mp hp' with rfl | hp''
                  · exact hrc.stack_remaining_subset (current, succ :: remainingTail, marked)
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
            have hsucc_notmem : succ ∉ pathStack := fun hmem => hnotvisited (hsv succ hmem)
            have hnodup' : (pathStack ++ [succ]).Nodup := by
              rw [List.nodup_append]
              refine ⟨hnodup, List.pairwise_singleton _ succ, ?_⟩
              intro a ha b hb heq
              subst heq
              simp only [List.mem_singleton] at hb
              subst hb
              exact hsucc_notmem ha
            have hmarked'' := TStackMarked.of_remaining_eq edgeMarks current (succ :: remainingTail)
              remainingTail marked rest hmarked
            have hmarked' := TStackMarked.cons edgeMarks (current, remainingTail, marked) rest succ
              (succs succ).toList hmarked''
            exact ih ((succ, (succs succ).toList, (edgeMarks current succ).contains 0) ::
                (current, remainingTail, marked) :: rest)
              (pathStack ++ [succ]) { st with outerVisited := st.outerVisited.insert succ }
              hps' hchain' hroot' hsv' hnodup' hrc' hmarked' h

end NonEmptyWitness

/-! ## Empty-result soundness -/

section EmptyNoCycle

variable {State} [BEq State] [Hashable State] [LawfulBEq State]

/-- Acceptance-agnostic outer-DFS invariant of the edge-aware CVWY algorithm, the bookkeeping fields of `OuterInvariant`.
The no-cycle fact for marked edges is not a field, since tree and forward/cross edges resolve while their source is on the stack. -/
structure TOuterInvariant
    (succs : State → Array State) (st : FNDFSState State) (stackStates : List State) : Prop where
  -- `innerFinished` is closed under `succs`.
  finished_closed : ∀ s, st.innerFinished.contains s → ∀ t ∈ succs s, st.innerFinished.contains t
  -- `innerFinished ⊆ outerVisited`.
  finished_subset_visited : ∀ s, st.innerFinished.contains s → st.outerVisited.contains s
  -- `innerFinished` is disjoint from the current stack.
  finished_stack_disjoint : ∀ s ∈ stackStates, ¬st.innerFinished.contains s
  -- Every state on the stack has already been outer-discovered.
  stack_subset_visited : ∀ s ∈ stackStates, st.outerVisited.contains s

/-- `innerDFS_no_cycle_from_seed` for a search starting at a `position` separate from `seed`. -/
theorem innerDFS_no_cycle_from_position (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (position : State) (st : FNDFSState State) (cap : Nat)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (hnotfin : st.innerFinished.contains position = false)
    (h : innerDFS_fuel succs seed cyan (fuel + 1) position
      (Std.HashSet.emptyWithCapacity cap) st = some (none, iv', st')) :
    ∀ t, (t = seed ∨ t ∈ cyan) →
      ¬PathTo succs (isBlocked iv' st'.innerFinished) position t := by
  rw [innerDFS_fuel.eq_def] at h
  simp only at h
  split at h
  · simp_all
  · split at h
    · have : (Std.HashSet.emptyWithCapacity cap : Std.HashSet State).contains position = false :=
        Std.HashSet.contains_emptyWithCapacity
      simp_all
    · have hsb := innerDFS_fuel_fold_succs_blocked succs seed cyan fuel position _ _ st
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

/-- The `_finished` upgrade of `innerDFS_no_cycle_from_position`, mirroring `innerDFS_no_cycle_from_seed_finished`. -/
theorem innerDFS_no_cycle_from_position_finished (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (position : State) (st : FNDFSState State) (cap : Nat)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (hnotfin : st.innerFinished.contains position = false)
    (h : innerDFS_fuel succs seed cyan (fuel + 1) position
      (Std.HashSet.emptyWithCapacity cap) st = some (none, iv', st')) :
    ∀ t, (t = seed ∨ t ∈ cyan) →
      ¬PathTo succs (fun x => st'.innerFinished.contains x) position t := by
  have hno := innerDFS_no_cycle_from_position succs seed cyan fuel position st cap hnotfin h
  have hiv_sub := innerDFS_fuel_iv_subset_finished succs seed cyan (fuel + 1) position
    (Std.HashSet.emptyWithCapacity cap) st h
  intro t ht hpath
  apply hno t ht
  exact hpath.weaken fun x (hblk : isBlocked iv' st'.innerFinished x) => by
    rcases hblk with hiv | hfin
    · exact hiv_sub x hiv (by simp [Std.HashSet.contains_emptyWithCapacity])
    · exact hfin

/-- `innerDFS_new_finished_closed` for a search starting at a `position` separate from `seed`. -/
theorem innerDFS_new_finished_closed_position (succs : State → Array State) (seed : State) (position : State)
    (cyan : List State) (fuel : Nat) (st : FNDFSState State) (cap : Nat)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel succs seed cyan (fuel + 1) position
      (Std.HashSet.emptyWithCapacity cap) st = some (none, iv', st'))
    (hold_closed : ∀ s, st.innerFinished.contains s →
      ∀ t ∈ succs s, st.innerFinished.contains t) :
    ∀ s, st'.innerFinished.contains s → ∀ t ∈ succs s, st'.innerFinished.contains t := by
  have ⟨_, hfin_mono⟩ := innerDFS_fuel_mono succs seed cyan (fuel + 1) position
    (Std.HashSet.emptyWithCapacity cap) st none iv' st' h
  have hnew := innerDFS_fuel_new_succs_blocked succs seed cyan (fuel + 1) position
    (Std.HashSet.emptyWithCapacity cap) st h
  have hiv_sub := innerDFS_fuel_iv_subset_finished succs seed cyan (fuel + 1) position
    (Std.HashSet.emptyWithCapacity cap) st h
  have hnew_fin_iv := innerDFS_fuel_new_finished_subset_iv succs seed cyan (fuel + 1) position
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

-- The fold-level version of `innerDFS_fuel_seed_cyan_iv_unchanged`.
private theorem fold_seed_cyan_iv_unchanged_aux (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State)
    (ih_inner : ∀ curr, curr ≠ seed → curr ∉ cyan → ∀ (iv₀ : Std.HashSet State) (st₀ : FNDFSState State)
      (iv₁ : Std.HashSet State) (st₁ : FNDFSState State),
      innerDFS_fuel succs seed cyan fuel curr iv₀ st₀ = some (none, iv₁, st₁) →
      ∀ t, (t = seed ∨ t ∈ cyan) → iv₁.contains t → iv₀.contains t) :
    ∀ (remaining : List State) (iv : Std.HashSet State) (st : FNDFSState State) {iv' : Std.HashSet State}
      {st' : FNDFSState State}, innerDFS_fuel_fold succs seed cyan fuel current remaining iv st =
        some (none, iv', st') → ∀ t, (t = seed ∨ t ∈ cyan) → iv'.contains t → iv.contains t := by
  intro remaining
  induction remaining with
  | nil =>
    intro iv st iv' st' h t ht htiv
    rw [innerDFS_fuel_fold.eq_def] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact htiv
  | cons succ' rest ih_rem =>
    intro iv st iv' st' h t ht htiv
    rw [innerDFS_fuel_fold.eq_def] at h; simp only at h
    split at h
    · simp at h
    · rename_i hse
      have hsucc'_ne_seed : succ' ≠ seed := by intro heq; subst heq; simp_all
      have hsucc'_notin_cyan : succ' ∉ cyan := by intro hmem; simp_all
      generalize hm : innerDFS_fuel succs seed cyan fuel succ' iv st = r at h
      match r, h with
      | none, h => simp at h
      | some (some _, _, _), h => simp at h
      | some (none, iv_mid, st_mid), h =>
        exact ih_inner succ' hsucc'_ne_seed hsucc'_notin_cyan iv st iv_mid st_mid hm t ht
          (ih_rem iv_mid st_mid h t ht htiv)

/-- A `none`-returning search that does not start at a seed or cyan state never adds a seed or cyan state to `iv`. -/
theorem innerDFS_fuel_seed_cyan_iv_unchanged (succs : State → Array State) (seed : State) (cyan : List State)
    (fuel : Nat) (current : State) (hcur : current ≠ seed ∧ current ∉ cyan)
    (iv : Std.HashSet State) (st : FNDFSState State)
    {iv' : Std.HashSet State} {st' : FNDFSState State}
    (h : innerDFS_fuel succs seed cyan fuel current iv st = some (none, iv', st')) :
    ∀ t, (t = seed ∨ t ∈ cyan) → iv'.contains t → iv.contains t := by
  induction fuel generalizing current iv st iv' st' with
  | zero => simp [innerDFS_fuel.eq_def] at h
  | succ n ih =>
    rw [innerDFS_fuel.eq_def] at h; simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      intro t _ htiv; exact htiv
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        intro t _ htiv; exact htiv
      · intro t ht htiv
        have hfold := fold_seed_cyan_iv_unchanged_aux succs seed cyan n current
          (fun curr hne hnc iv₀ st₀ iv₁ st₁ h' => ih curr ⟨hne, hnc⟩ iv₀ st₀ h')
          (succs current).toList (iv.insert current) st h t ht htiv
        by_cases hteq : t = current
        · subst hteq
          rcases ht with heq | hmem
          · exact absurd heq hcur.1
          · exact absurd hmem hcur.2
        · simp [Std.HashSet.contains_insert, Ne.symm hteq] at hfold
          exact hfold

/-- Every ancestor beyond a frame's immediate parent that has an edge to the frame's state still has it pending in its
remaining list. -/
def TStackPending (succs : State → Array State) : List (State × List State × Bool) → Prop
  | [] => True
  | [_] => True
  | (top, _, _) :: (parent, prem, pmarked) :: rest =>
      (∀ p ∈ rest, top ∈ succs p.1 → top ∈ p.2.1) ∧ TStackPending succs ((parent, prem, pmarked) :: rest)

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- Dropping the top frame off a pending-respecting stack leaves one. -/
theorem TStackPending.tail (succs : State → Array State) (top : State × List State × Bool)
    (stack : List (State × List State × Bool)) (h : TStackPending succs (top :: stack)) :
    TStackPending succs stack := by
  cases stack with
  | nil => trivial
  | cons parent tail => exact h.2

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- Replacing the top frame's `remaining` list preserves `TStackPending`. -/
theorem TStackPending.of_remaining_eq (succs : State → Array State) (s : State) (r r' : List State) (marked : Bool)
    (stack : List (State × List State × Bool)) (h : TStackPending succs ((s, r, marked) :: stack)) :
    TStackPending succs ((s, r', marked) :: stack) := by
  cases stack with
  | nil => trivial
  | cons parent tail => exact h

/-- Pushing a fresh, not yet visited frame keeps the stack pending-respecting. -/
theorem TStackPending.cons {succs : State → Array State} {st : FNDFSState State}
    (stack : List (State × List State × Bool))
    (hpv : ∀ p ∈ stack.tail, ∀ t ∈ succs p.1, t ∉ p.2.1 → st.outerVisited.contains t)
    (s : State) (r : List State) (marked : Bool) (hfresh : st.outerVisited.contains s = false)
    (h : TStackPending succs stack) :
    TStackPending succs ((s, r, marked) :: stack) := by
  cases stack with
  | nil => trivial
  | cons parent tail =>
    refine ⟨fun p hp hsucc => ?_, h⟩
    by_contra hc
    have := hpv p (by simpa using hp) s hsucc hc
    simp [hfresh] at this

/-- Every frame's already-examined edges into itself or an ancestor (self-loops and back edges) are unmarked, since a
marked one returns `.nonEmpty` immediately. -/
def TStackBackUnmarked (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat) :
    List (State × List State × Bool) → Prop
  | [] => True
  | (top, rem, _) :: rest =>
      (∀ t ∈ succs top, t ∉ rem → t ∈ top :: rest.map Prod.fst → 0 ∉ edgeMarks top t) ∧
        TStackBackUnmarked succs edgeMarks rest

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- Dropping the top frame off a back-unmarked stack leaves one. -/
theorem TStackBackUnmarked.tail (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (s : State) (r : List State) (marked : Bool) (stack : List (State × List State × Bool))
    (h : TStackBackUnmarked succs edgeMarks ((s, r, marked) :: stack)) :
    TStackBackUnmarked succs edgeMarks stack :=
  h.2

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- Examining `succ` from the top frame keeps the stack back-unmarked if the edge to `succ` is unmarked whenever `succ` is on the stack. -/
theorem TStackBackUnmarked.extend (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (s succ : State) (remainingTail : List State) (marked : Bool) (stack : List (State × List State × Bool))
    (h : TStackBackUnmarked succs edgeMarks ((s, succ :: remainingTail, marked) :: stack))
    (hnew : succ ∈ s :: stack.map Prod.fst → 0 ∉ edgeMarks s succ) :
    TStackBackUnmarked succs edgeMarks ((s, remainingTail, marked) :: stack) := by
  refine ⟨fun t ht htr htmem => ?_, h.2⟩
  by_cases hts : t = succ
  · exact hts ▸ hnew (hts ▸ htmem)
  · exact h.1 t ht (fun hmem => (List.mem_cons.mp hmem).elim hts htr) htmem

omit [BEq State] [Hashable State] [LawfulBEq State] in
/-- Pushing a fresh frame, with no examined edges yet, keeps the stack back-unmarked. -/
theorem TStackBackUnmarked.cons (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (s : State) (marked : Bool) (stack : List (State × List State × Bool))
    (h : TStackBackUnmarked succs edgeMarks stack) :
    TStackBackUnmarked succs edgeMarks ((s, (succs s).toList, marked) :: stack) :=
  ⟨fun _ ht htr _ => absurd (Array.mem_toList_iff.mpr ht) htr, h⟩

/-- If the outer DFS returns `.empty`, then `TOuterInvariant` holds with an empty stack and no marked edge out of a visited state
has a path back from its target to its source. Facts carried from before the call:
- `hpre_stack`: a marked, already-examined edge from a frame to an off-stack state has no path back
- `hpre_back`: already-examined edges into the stack are unmarked
- `hpre_done`: a marked edge out of a finished state has no path back -/
theorem outerDFST_fuel_empty_no_cycle
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (fuel : Nat)
    (stack : List (State × List State × Bool))
    (pathStack : List State)
    (st : FNDFSState State)
    {n : Nat} {st' : FNDFSState State}
    (hps : pathStack = (stack.map Prod.fst).reverse)
    (hnodup : pathStack.Nodup)
    (hsv : ∀ s ∈ pathStack, st.outerVisited.contains s)
    (h : outerDFST_fuel succs edgeMarks fuel stack pathStack st = some (.empty n, st'))
    (hrc : TOuterReachClosed succs st stack)
    (hmarked : TStackMarked edgeMarks stack)
    (hpending : TStackPending succs stack)
    (hinv : TOuterInvariant succs st (stack.map Prod.fst))
    (hpre_stack : ∀ p ∈ stack, ∀ t, t ∈ succs p.1 → t ∉ p.2.1 → t ∉ stack.map Prod.fst →
      0 ∈ edgeMarks p.1 t → ¬PathTo succs (fun _ => False) t p.1)
    (hpre_back : TStackBackUnmarked succs edgeMarks stack)
    (hpre_done : ∀ s, st.outerVisited.contains s → s ∉ stack.map Prod.fst →
      ∀ t ∈ succs s, 0 ∈ edgeMarks s t → ¬PathTo succs (fun _ => False) t s) :
    TOuterInvariant succs st' [] ∧
    (∀ s t, st'.outerVisited.contains s → t ∈ succs s → 0 ∈ edgeMarks s t →
      ¬PathTo succs (fun _ => False) t s) := by
  induction fuel generalizing stack pathStack st n st' with
  | zero => simp [outerDFST_fuel.eq_def] at h
  | succ m ih =>
    rw [outerDFST_fuel.eq_def] at h
    simp only at h
    split at h
    · -- stack = []
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨hinv, fun s t hs ht hm => hpre_done s hs (by simp) t ht hm⟩
    · -- stack = (current, remaining, marked) :: rest
      rename_i current remaining marked rest
      split at h
      · -- remaining = []
        split at h
        · -- marked = true, rest = (parent, _, _) :: tail
          rename_i parent parentRem parentMarked tail
          split at h
          · simp at h
          · -- inner DFS found a cycle: contradicts .empty
            simp at h
          · -- inner DFS found none: recurse, extends `edge_no_cycle` with the pair (parent, current)
            rename_i st'' heq
            obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
              cases m with
              | zero => simp [innerDFS_fuel.eq_def] at heq
              | succ k => exact ⟨k, rfl⟩
            have houter_eq : st''.outerVisited = st.outerVisited :=
              innerDFS_fuel_outerVisited_eq succs parent pathStack.dropLast (k + 1) current _ st
                none _ st'' heq
            have hps' : pathStack.dropLast = (((parent, parentRem, parentMarked) :: tail).map Prod.fst).reverse := by
              simp [hps]
            have hrc' : TOuterReachClosed succs st'' ((parent, parentRem, parentMarked) :: tail) := {
              stack_chain := ReachChain.tail current (((parent, parentRem, parentMarked) :: tail).map Prod.fst)
                (by simpa using hrc.stack_chain)
              done_closed := by
                intro s hvis hnotmem t ht
                rw [houter_eq] at hvis ⊢
                by_cases hsc : s = current
                · have ht' : t ∈ succs current := hsc ▸ ht
                  exact hrc.stack_processed_visited (current, [], true) (List.mem_cons_self ..)
                    t ht' (by simp)
                · have hnotmem' : s ∉ current :: ((parent, parentRem, parentMarked) :: tail).map Prod.fst :=
                    fun hmem => (List.mem_cons.mp hmem).elim hsc hnotmem
                  exact hrc.done_closed s hvis hnotmem' t ht
              stack_processed_visited := by
                intro p hp t ht hpr
                rw [houter_eq]
                exact hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp) t ht hpr
              stack_remaining_subset := fun p hp t ht =>
                hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp) t ht
            }
            have hnodup' : pathStack.dropLast.Nodup := hnodup.sublist (List.dropLast_sublist pathStack)
            have hsv' : ∀ s ∈ pathStack.dropLast, st''.outerVisited.contains s := by
              rw [houter_eq]
              exact fun s hs => hsv s (List.dropLast_subset _ hs)
            have hmarked' := TStackMarked.tail edgeMarks (current, [], true) _ hmarked
            have hpending' := TStackPending.tail succs (current, [], true)
              ((parent, parentRem, parentMarked) :: tail) hpending
            have hnotfin : st.innerFinished.contains current = false :=
              by simpa using hinv.finished_stack_disjoint current (List.mem_cons_self ..)
            have hno_restricted_all := innerDFS_no_cycle_from_position_finished succs parent pathStack.dropLast k
              current st (st.outerVisited.size / 2) hnotfin heq
            have hanc_mem : ∀ t, t ∈ pathStack.dropLast →
                t ∈ ((parent, parentRem, parentMarked) :: tail).map Prod.fst := by
              intro t ht
              have ht' : t ∈ (((parent, parentRem, parentMarked) :: tail).map Prod.fst).reverse := hps' ▸ ht
              simpa using List.mem_reverse.mp ht'
            have hno_edge_old_part_all : ∀ t, (t = parent ∨ t ∈ pathStack.dropLast) →
                ∀ x, st.innerFinished.contains x → t ∉ succs x := by
              intro t ht x hx hedge
              have ht_stack : t ∈ current :: ((parent, parentRem, parentMarked) :: tail).map Prod.fst := by
                rcases ht with heqt | hmemp
                · exact heqt ▸ List.mem_cons_of_mem _ (by simp)
                · exact List.mem_cons_of_mem _ (hanc_mem t hmemp)
              exact hinv.finished_stack_disjoint t ht_stack (hinv.finished_closed x hx t hedge)
            have hnew_no_edge_all := innerDFS_fuel_new_no_edge_to_seed succs parent pathStack.dropLast
              (k + 1) current (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq
            have hclosed_new : ∀ s, st''.innerFinished.contains s →
                ∀ t ∈ succs s, st''.innerFinished.contains t :=
              innerDFS_new_finished_closed_position succs parent current pathStack.dropLast k st
                (st.outerVisited.size / 2) heq hinv.finished_closed
            have hno_edge_new_all : ∀ t, (t = parent ∨ t ∈ pathStack.dropLast) →
                ∀ x, st''.innerFinished.contains x → t ∉ succs x := by
              intro t ht x hx hedge
              by_cases hold : st.innerFinished.contains x
              · exact hno_edge_old_part_all t ht x hold hedge
              · have hx_iv := innerDFS_fuel_new_finished_subset_iv succs parent pathStack.dropLast (k + 1) current
                  (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq x hx hold
                exact hnew_no_edge_all x hx_iv
                  (by simp [Std.HashSet.contains_emptyWithCapacity]) t ht hedge
            have hno_unrestricted_all : ∀ t, (t = parent ∨ t ∈ pathStack.dropLast) →
                ¬PathTo succs (fun _ => False) current t := by
              intro t ht
              exact PathTo.no_reach_of_closed_no_incoming hclosed_new (hno_edge_new_all t ht)
                (hno_restricted_all t ht)
            have hno_stack_reach : ∀ w, PathTo succs (fun _ => False) current w →
                w ∉ ((parent, parentRem, parentMarked) :: tail).map Prod.fst := by
              intro w hw hmem
              simp only [List.map_cons, List.mem_cons] at hmem
              rcases hmem with heqw | hmem'
              · exact hno_unrestricted_all parent (Or.inl rfl) (heqw ▸ hw)
              · have hw_anc : w ∈ pathStack.dropLast := by
                  rw [hps']; exact List.mem_reverse.mpr (List.mem_cons_of_mem _ hmem')
                exact hno_unrestricted_all w (Or.inr hw_anc) hw
            have hCL : ∀ x, (st.outerVisited.contains x ∧
                x ∉ ((parent, parentRem, parentMarked) :: tail).map Prod.fst) →
                ∀ y ∈ succs x, (st.outerVisited.contains y ∧
                  y ∉ ((parent, parentRem, parentMarked) :: tail).map Prod.fst) ∨
                  y ∈ ((parent, parentRem, parentMarked) :: tail).map Prod.fst := by
              intro x hx y hy
              by_cases hyS : y ∈ ((parent, parentRem, parentMarked) :: tail).map Prod.fst
              · exact Or.inr hyS
              · by_cases hxc : x = current
                · rw [hxc] at hy
                  exact Or.inl ⟨hrc.stack_processed_visited (current, [], true) (List.mem_cons_self ..)
                    y hy (by simp), hyS⟩
                · have hx_notstack : x ∉ current :: ((parent, parentRem, parentMarked) :: tail).map Prod.fst :=
                    fun hmem => (List.mem_cons.mp hmem).elim hxc hx.2
                  exact Or.inl ⟨hrc.done_closed x hx.1 hx_notstack y hy, hyS⟩
            have hcurrent_notmem : current ∉ ((parent, parentRem, parentMarked) :: tail).map Prod.fst := by
              have hnd : (current :: ((parent, parentRem, parentMarked) :: tail).map Prod.fst).Nodup := by
                rw [hps] at hnodup
                exact (List.pairwise_reverse.mp hnodup).imp Ne.symm
              exact (List.nodup_cons.mp hnd).1
            have hcur : current ≠ parent ∧ current ∉ pathStack.dropLast :=
              ⟨fun heq' => hcurrent_notmem (heq' ▸ by simp),
               fun hmem => hcurrent_notmem (by rw [hps'] at hmem; exact List.mem_reverse.mp hmem)⟩
            have hinv' : TOuterInvariant succs st'' (((parent, parentRem, parentMarked) :: tail).map Prod.fst) := {
              finished_closed := hclosed_new
              finished_subset_visited := by
                intro s hcontra
                rw [houter_eq]
                by_cases hold : st.innerFinished.contains s
                · exact hinv.finished_subset_visited s hold
                · rcases innerDFS_fuel_new_reachable succs parent pathStack.dropLast (k + 1) current
                      (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq s
                      (innerDFS_fuel_new_finished_subset_iv succs parent pathStack.dropLast (k + 1) current
                        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq s hcontra hold)
                      (by simp [Std.HashSet.contains_emptyWithCapacity]) with heqcur | hp
                  · exact heqcur ▸ hinv.stack_subset_visited current (List.mem_cons_self ..)
                  · cases hp with
                    | direct ht =>
                      exact hrc.stack_processed_visited (current, [], true) (List.mem_cons_self ..) s ht (by simp)
                    | @through _ mid _ hmid _ hrest =>
                      have hmid_vis : st.outerVisited.contains mid :=
                        hrc.stack_processed_visited (current, [], true) (List.mem_cons_self ..)
                          mid hmid (by simp)
                      have hmid_notstack : mid ∉ ((parent, parentRem, parentMarked) :: tail).map Prod.fst :=
                        hno_stack_reach mid (PathTo.direct hmid)
                      have hmid_NR : ∀ w, PathTo succs (fun _ => False) mid w →
                          w ∉ ((parent, parentRem, parentMarked) :: tail).map Prod.fst :=
                        fun w hw => hno_stack_reach w (PathTo.trans (PathTo.direct hmid) hw)
                      exact (PathTo.closed_of_no_escape hCL hrest ⟨hmid_vis, hmid_notstack⟩ hmid_NR).1
              finished_stack_disjoint := by
                intro s hs hcontra
                by_cases hold : st.innerFinished.contains s
                · exact hinv.finished_stack_disjoint s (List.mem_cons_of_mem _ hs) hold
                · have hs_seed_cyan : s = parent ∨ s ∈ pathStack.dropLast := by
                    rcases List.mem_cons.mp hs with rfl | hs'
                    · exact Or.inl rfl
                    · exact Or.inr (by rw [hps']; exact List.mem_reverse.mpr (List.mem_cons_of_mem _ hs'))
                  have hs_iv' : (Std.HashSet.emptyWithCapacity (α := State)
                      (st.outerVisited.size / 2)).contains s :=
                    innerDFS_fuel_seed_cyan_iv_unchanged succs parent pathStack.dropLast (k + 1) current hcur
                      (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq s hs_seed_cyan
                      (innerDFS_fuel_new_finished_subset_iv succs parent pathStack.dropLast (k + 1) current
                        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq s hcontra hold)
                  simp [Std.HashSet.contains_emptyWithCapacity] at hs_iv'
              stack_subset_visited := by
                intro s hs
                rw [houter_eq]
                exact hinv.stack_subset_visited s (List.mem_cons_of_mem _ hs)
            }
            have hpre_stack' : ∀ p ∈ (parent, parentRem, parentMarked) :: tail, ∀ t, t ∈ succs p.1 → t ∉ p.2.1 →
                t ∉ (((parent, parentRem, parentMarked) :: tail).map Prod.fst) → 0 ∈ edgeMarks p.1 t →
                ¬PathTo succs (fun _ => False) t p.1 := by
              intro p hp t ht htr htnmem hm
              by_cases hts : t = current
              · subst hts
                rcases List.mem_cons.mp hp with rfl | hp'
                · exact hno_unrestricted_all parent (Or.inl rfl)
                · exact absurd (hpending.1 p hp' ht) htr
              · exact hpre_stack p (List.mem_cons_of_mem _ hp) t ht htr
                  (fun hmem => (List.mem_cons.mp hmem).elim hts htnmem) hm
            have hpre_back' := TStackBackUnmarked.tail succs edgeMarks current [] true
              ((parent, parentRem, parentMarked) :: tail) hpre_back
            have hpre_done' : ∀ s, st''.outerVisited.contains s →
                s ∉ ((parent, parentRem, parentMarked) :: tail).map Prod.fst →
                ∀ t ∈ succs s, 0 ∈ edgeMarks s t → ¬PathTo succs (fun _ => False) t s := by
              intro s hvis hnotmem t ht hm
              rw [houter_eq] at hvis
              by_cases hsc : s = current
              · rw [hsc] at ht hm ⊢
                by_cases htmem : t ∈ current :: ((parent, parentRem, parentMarked) :: tail).map Prod.fst
                · exact absurd hm (hpre_back.1 t ht (by simp) htmem)
                · exact hpre_stack (current, [], true) (List.mem_cons_self ..) t ht (by simp) htmem hm
              · have hnotmem' : s ∉ current :: ((parent, parentRem, parentMarked) :: tail).map Prod.fst :=
                  fun hmem => (List.mem_cons.mp hmem).elim hsc hnotmem
                exact hpre_done s hvis hnotmem' t ht hm
            exact ih ((parent, parentRem, parentMarked) :: tail) pathStack.dropLast st''
              hps' hnodup' hsv' h hrc' hmarked' hpending' hinv' hpre_stack' hpre_back' hpre_done'
        · -- marked = false, or rest = []
          rename_i hnotresolve
          have hps' : pathStack.dropLast = (rest.map Prod.fst).reverse := by simp [hps]
          have hrc' : TOuterReachClosed succs st rest := {
            stack_chain := ReachChain.tail current (rest.map Prod.fst) (by simpa using hrc.stack_chain)
            done_closed := by
              intro s hvis hnotmem t ht
              by_cases hsc : s = current
              · have ht' : t ∈ succs current := hsc ▸ ht
                exact hrc.stack_processed_visited (current, [], marked) (List.mem_cons_self ..)
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
          have hnodup' : pathStack.dropLast.Nodup := hnodup.sublist (List.dropLast_sublist pathStack)
          have hmarked' := TStackMarked.tail edgeMarks (current, [], marked) rest hmarked
          have hpending' := TStackPending.tail succs (current, [], marked) rest hpending
          have hinv' : TOuterInvariant succs st (rest.map Prod.fst) := {
            finished_closed := hinv.finished_closed
            finished_subset_visited := hinv.finished_subset_visited
            finished_stack_disjoint := fun s hs => hinv.finished_stack_disjoint s (List.mem_cons_of_mem _ hs)
            stack_subset_visited := fun s hs => hinv.stack_subset_visited s (List.mem_cons_of_mem _ hs)
          }
          have hpre_stack' : ∀ p ∈ rest, ∀ t, t ∈ succs p.1 → t ∉ p.2.1 → t ∉ rest.map Prod.fst →
              0 ∈ edgeMarks p.1 t → ¬PathTo succs (fun _ => False) t p.1 := by
            intro p hp t ht htr htnmem hm
            by_cases hts : t = current
            · subst hts
              rcases rest with _ | ⟨⟨parent, parentRem, parentMarked⟩, tail⟩
              · simp at hp
              · rcases List.mem_cons.mp hp with rfl | hp'
                · have hmarked_false : marked = false := by
                    by_contra hc
                    exact hnotresolve parent parentRem parentMarked tail (by simpa using hc) rfl
                  exact absurd ((hmarked 0 (by simp)).mpr hm) (by simp [hmarked_false])
                · exact absurd (hpending.1 p hp' ht) htr
            · exact hpre_stack p (List.mem_cons_of_mem _ hp) t ht htr
                (fun hmem => (List.mem_cons.mp hmem).elim hts htnmem) hm
          have hpre_back' := TStackBackUnmarked.tail succs edgeMarks current [] marked rest hpre_back
          have hpre_done' : ∀ s, st.outerVisited.contains s → s ∉ rest.map Prod.fst →
              ∀ t ∈ succs s, 0 ∈ edgeMarks s t → ¬PathTo succs (fun _ => False) t s := by
            intro s hvis hnotmem t ht hm
            by_cases hsc : s = current
            · rw [hsc] at ht hm ⊢
              by_cases htmem : t ∈ current :: rest.map Prod.fst
              · exact absurd hm (hpre_back.1 t ht (by simp) htmem)
              · exact hpre_stack (current, [], marked) (List.mem_cons_self ..) t ht (by simp) htmem hm
            · have hnotmem' : s ∉ current :: rest.map Prod.fst :=
                fun hmem => (List.mem_cons.mp hmem).elim hsc hnotmem
              exact hpre_done s hvis hnotmem' t ht hm
          exact ih rest pathStack.dropLast st hps' hnodup' hsv' h hrc' hmarked' hpending' hinv'
            hpre_stack' hpre_back' hpre_done'
      · -- remaining = succ :: remainingTail
        rename_i succ remainingTail
        have hskip : st.outerVisited.contains succ →
            TOuterReachClosed succs st ((current, remainingTail, marked) :: rest) :=
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
                exact hrc.stack_processed_visited (current, succ :: remainingTail, marked)
                  (List.mem_cons_self ..) t ht hpr'
            · exact hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp') t ht hpr
          stack_remaining_subset := by
            intro p hp t ht
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact hrc.stack_remaining_subset (current, succ :: remainingTail, marked)
                (List.mem_cons_self ..) t (List.mem_cons_of_mem _ ht)
            · exact hrc.stack_remaining_subset p (List.mem_cons_of_mem _ hp') t ht
        }
        have hps' : pathStack = (((current, remainingTail, marked) :: rest).map Prod.fst).reverse := by
          simpa using hps
        have hpre_stack_skip : ∀ t ∈ succs current, t ≠ succ →
            t ∉ remainingTail → t ∉ current :: rest.map Prod.fst → 0 ∈ edgeMarks current t →
            ¬PathTo succs (fun _ => False) t current := fun t ht hts htr => hpre_stack
          (current, succ :: remainingTail, marked) (List.mem_cons_self ..) t ht
          (fun hmem => (List.mem_cons.mp hmem).elim hts htr)
        split at h
        · -- back edge (succ ∈ pathStack)
          rename_i hsucc_mem
          have hsucc_stack : succ ∈ current :: rest.map Prod.fst := by
            have hmem : succ ∈ pathStack := by simpa using hsucc_mem
            rw [hps, List.mem_reverse] at hmem
            exact hmem
          split at h
          · -- marked: reports .nonEmpty, contradicts .empty
            simp at h
          · -- unmarked: recurse, skip
            rename_i hunmarked
            have hvis_succ : st.outerVisited.contains succ := hsv succ (by simpa using hsucc_mem)
            have hpre_stack' : ∀ p ∈ (current, remainingTail, marked) :: rest, ∀ t, t ∈ succs p.1 →
                t ∉ p.2.1 → t ∉ ((current, remainingTail, marked) :: rest).map Prod.fst →
                0 ∈ edgeMarks p.1 t → ¬PathTo succs (fun _ => False) t p.1 := by
              intro p hp t ht htr htnmem hm
              simp only [List.map_cons] at htnmem
              rcases List.mem_cons.mp hp with rfl | hp'
              · by_cases hts : t = succ
                · exact absurd (hts ▸ hsucc_stack) (by simpa using htnmem)
                · exact hpre_stack_skip t ht hts htr (by simpa using htnmem) hm
              · exact hpre_stack p (List.mem_cons_of_mem _ hp') t ht htr (by simpa using htnmem) hm
            have hpre_back' : TStackBackUnmarked succs edgeMarks
                ((current, remainingTail, marked) :: rest) :=
              TStackBackUnmarked.extend succs edgeMarks current succ remainingTail marked rest hpre_back
                (fun _ => by simpa using hunmarked)
            have hpending' : TStackPending succs ((current, remainingTail, marked) :: rest) :=
              TStackPending.of_remaining_eq succs current (succ :: remainingTail) remainingTail marked rest
                hpending
            have hmarked' := TStackMarked.of_remaining_eq edgeMarks current (succ :: remainingTail)
              remainingTail marked rest hmarked
            exact ih ((current, remainingTail, marked) :: rest) pathStack st hps' hnodup hsv h
              (hskip hvis_succ) hmarked' hpending' (by simpa using hinv) hpre_stack' hpre_back'
              (by simpa using hpre_done)
        · rename_i hnotpath
          split at h
          · -- forward/cross edge (already visited, not cyan)
            rename_i hvisited
            split at h
            · -- marked
              split at h
              · simp at h
              · -- inner DFS found a cycle: contradicts .empty
                simp at h
              · -- inner DFS found none: recurse, extends `edge_no_cycle` with the pair (current, succ)
                rename_i st'' heq
                obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
                  cases m with
                  | zero => simp [innerDFS_fuel.eq_def] at heq
                  | succ k => exact ⟨k, rfl⟩
                have hsp : succ ∉ pathStack := by simpa using hnotpath
                have hcur_mem : current ∈ pathStack := by
                  rw [hps]; exact List.mem_reverse.mpr (List.mem_cons_self ..)
                have hsucc_notstack : succ ∉ current :: rest.map Prod.fst := by
                  intro hmem
                  exact hsp (by rw [hps]; exact List.mem_reverse.mpr hmem)
                by_cases hsuccfin : st.innerFinished.contains succ
                · -- succ already finished: search is a no-op, extend via `finished_closed`
                  simp only [innerDFS_fuel.eq_def, hsuccfin] at heq
                  obtain ⟨-, rfl⟩ := heq
                  have hedge_no_cycle : ¬PathTo succs (fun _ => False) succ current := by
                    intro hpath
                    exact hinv.finished_stack_disjoint current (List.mem_cons_self ..)
                      (PathTo.closed (P := fun x => st.innerFinished.contains x = true)
                        hpath hsuccfin hinv.finished_closed)
                  have hpre_stack' : ∀ p ∈ (current, remainingTail, marked) :: rest, ∀ t, t ∈ succs p.1 →
                      t ∉ p.2.1 → t ∉ ((current, remainingTail, marked) :: rest).map Prod.fst →
                      0 ∈ edgeMarks p.1 t → ¬PathTo succs (fun _ => False) t p.1 := by
                    intro p hp t ht htr htnmem hm
                    simp only [List.map_cons] at htnmem
                    rcases List.mem_cons.mp hp with rfl | hp'
                    · by_cases hts : t = succ
                      · exact hts ▸ hedge_no_cycle
                      · exact hpre_stack_skip t ht hts htr (by simpa using htnmem) hm
                    · exact hpre_stack p (List.mem_cons_of_mem _ hp') t ht htr (by simpa using htnmem) hm
                  have hpre_back' : TStackBackUnmarked succs edgeMarks
                      ((current, remainingTail, marked) :: rest) :=
                    TStackBackUnmarked.extend succs edgeMarks current succ remainingTail marked rest hpre_back
                      (fun hmem => absurd hmem hsucc_notstack)
                  have hpending' : TStackPending succs ((current, remainingTail, marked) :: rest) :=
                    TStackPending.of_remaining_eq succs current (succ :: remainingTail) remainingTail marked rest
                      hpending
                  have hmarked' := TStackMarked.of_remaining_eq edgeMarks current (succ :: remainingTail)
                    remainingTail marked rest hmarked
                  exact ih ((current, remainingTail, marked) :: rest) pathStack st hps' hnodup hsv h
                    (hskip hvisited) hmarked' hpending' (by simpa using hinv) hpre_stack' hpre_back'
                    (by simpa using hpre_done)
                · -- succ genuinely fresh to the search: full closure argument
                  have hnotfin : st.innerFinished.contains succ = false := by simpa using hsuccfin
                  have houter_eq : st''.outerVisited = st.outerVisited :=
                    innerDFS_fuel_outerVisited_eq succs current pathStack (k + 1) succ _ st none _ st'' heq
                  have hno_restricted_all := innerDFS_no_cycle_from_position_finished succs current pathStack k
                    succ st (st.outerVisited.size / 2) hnotfin heq
                  have hno_edge_old_part_all : ∀ t, (t = current ∨ t ∈ pathStack) →
                      ∀ x, st.innerFinished.contains x → t ∉ succs x := by
                    intro t ht x hx hedge
                    have ht_stack : t ∈ current :: rest.map Prod.fst := by
                      rcases ht with heqt | hmemp
                      · exact heqt ▸ List.mem_cons_self ..
                      · have := hps ▸ hmemp
                        simpa using List.mem_reverse.mp this
                    exact hinv.finished_stack_disjoint t ht_stack (hinv.finished_closed x hx t hedge)
                  have hnew_no_edge_all := innerDFS_fuel_new_no_edge_to_seed succs current pathStack
                    (k + 1) succ (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq
                  have hclosed_new : ∀ s, st''.innerFinished.contains s →
                      ∀ t ∈ succs s, st''.innerFinished.contains t :=
                    innerDFS_new_finished_closed_position succs current succ pathStack k st
                      (st.outerVisited.size / 2) heq hinv.finished_closed
                  have hno_edge_new_all : ∀ t, (t = current ∨ t ∈ pathStack) →
                      ∀ x, st''.innerFinished.contains x → t ∉ succs x := by
                    intro t ht x hx hedge
                    by_cases hold : st.innerFinished.contains x
                    · exact hno_edge_old_part_all t ht x hold hedge
                    · have hx_iv := innerDFS_fuel_new_finished_subset_iv succs current pathStack (k + 1) succ
                        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq x hx hold
                      exact hnew_no_edge_all x hx_iv
                        (by simp [Std.HashSet.contains_emptyWithCapacity]) t ht hedge
                  have hno_unrestricted_all : ∀ t, (t = current ∨ t ∈ pathStack) →
                      ¬PathTo succs (fun _ => False) succ t := by
                    intro t ht
                    exact PathTo.no_reach_of_closed_no_incoming hclosed_new (hno_edge_new_all t ht)
                      (hno_restricted_all t ht)
                  have hedge_no_cycle : ¬PathTo succs (fun _ => False) succ current :=
                    hno_unrestricted_all current (Or.inl rfl)
                  have hno_stack_reach : ∀ w, PathTo succs (fun _ => False) succ w →
                      w ∉ current :: rest.map Prod.fst := by
                    intro w hw hmem
                    rcases List.mem_cons.mp hmem with heqw | hmem'
                    · exact hno_unrestricted_all current (Or.inl rfl) (heqw ▸ hw)
                    · have hw_path : w ∈ pathStack := by
                        rw [hps]; exact List.mem_reverse.mpr (List.mem_cons_of_mem _ hmem')
                      exact hno_unrestricted_all w (Or.inr hw_path) hw
                  have hCL : ∀ x, (st.outerVisited.contains x ∧ x ∉ current :: rest.map Prod.fst) →
                      ∀ y ∈ succs x, (st.outerVisited.contains y ∧ y ∉ current :: rest.map Prod.fst) ∨
                        y ∈ current :: rest.map Prod.fst := by
                    intro x hx y hy
                    by_cases hyS : y ∈ current :: rest.map Prod.fst
                    · exact Or.inr hyS
                    · exact Or.inl ⟨hrc.done_closed x hx.1 hx.2 y hy, hyS⟩
                  have hcur : succ ≠ current ∧ succ ∉ pathStack :=
                    ⟨fun heq' => hsp (heq' ▸ hcur_mem), hsp⟩
                  have hinv' : TOuterInvariant succs st'' (current :: rest.map Prod.fst) := {
                    finished_closed := hclosed_new
                    finished_subset_visited := by
                      intro s hcontra
                      rw [houter_eq]
                      by_cases hold : st.innerFinished.contains s
                      · exact hinv.finished_subset_visited s hold
                      · rcases innerDFS_fuel_new_reachable succs current pathStack (k + 1) succ
                            (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq s
                            (innerDFS_fuel_new_finished_subset_iv succs current pathStack (k + 1) succ
                              (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq s hcontra hold)
                            (by simp [Std.HashSet.contains_emptyWithCapacity]) with heqsucc | hp
                        · exact heqsucc ▸ hvisited
                        · exact (PathTo.closed_of_no_escape hCL hp ⟨hvisited, hsucc_notstack⟩
                            hno_stack_reach).1
                    finished_stack_disjoint := by
                      intro s hs hcontra
                      by_cases hold : st.innerFinished.contains s
                      · exact hinv.finished_stack_disjoint s hs hold
                      · have hs_seed_cyan : s = current ∨ s ∈ pathStack := by
                          rcases List.mem_cons.mp hs with rfl | hs'
                          · exact Or.inl rfl
                          · exact Or.inr (by rw [hps]; exact List.mem_reverse.mpr (List.mem_cons_of_mem _ hs'))
                        have hs_iv' : (Std.HashSet.emptyWithCapacity (α := State)
                            (st.outerVisited.size / 2)).contains s :=
                          innerDFS_fuel_seed_cyan_iv_unchanged succs current pathStack (k + 1) succ hcur
                            (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq s hs_seed_cyan
                            (innerDFS_fuel_new_finished_subset_iv succs current pathStack (k + 1) succ
                              (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st heq s hcontra hold)
                        simp [Std.HashSet.contains_emptyWithCapacity] at hs_iv'
                    stack_subset_visited := by
                      intro s hs
                      rw [houter_eq]
                      exact hinv.stack_subset_visited s hs
                  }
                  have hpre_stack' : ∀ p ∈ (current, remainingTail, marked) :: rest, ∀ t, t ∈ succs p.1 →
                      t ∉ p.2.1 → t ∉ ((current, remainingTail, marked) :: rest).map Prod.fst →
                      0 ∈ edgeMarks p.1 t → ¬PathTo succs (fun _ => False) t p.1 := by
                    intro p hp t ht htr htnmem hm
                    simp only [List.map_cons] at htnmem
                    rcases List.mem_cons.mp hp with rfl | hp'
                    · by_cases hts : t = succ
                      · exact hts ▸ hedge_no_cycle
                      · exact hpre_stack_skip t ht hts htr (by simpa using htnmem) hm
                    · exact hpre_stack p (List.mem_cons_of_mem _ hp') t ht htr (by simpa using htnmem) hm
                  have hpre_back' : TStackBackUnmarked succs edgeMarks
                      ((current, remainingTail, marked) :: rest) :=
                    TStackBackUnmarked.extend succs edgeMarks current succ remainingTail marked rest hpre_back
                      (fun hmem => absurd hmem hsucc_notstack)
                  have hpending' : TStackPending succs ((current, remainingTail, marked) :: rest) :=
                    TStackPending.of_remaining_eq succs current (succ :: remainingTail) remainingTail marked rest
                      hpending
                  have hmarked' := TStackMarked.of_remaining_eq edgeMarks current (succ :: remainingTail)
                    remainingTail marked rest hmarked
                  have hrc' : TOuterReachClosed succs st'' ((current, remainingTail, marked) :: rest) :=
                    TOuterReachClosed.of_outerVisited_eq houter_eq (hskip hvisited)
                  have hpre_done' : ∀ s, st''.outerVisited.contains s → s ∉ current :: rest.map Prod.fst →
                      ∀ t ∈ succs s, 0 ∈ edgeMarks s t → ¬PathTo succs (fun _ => False) t s := by
                    intro s hvis hnotmem t ht hm
                    rw [houter_eq] at hvis
                    exact hpre_done s hvis hnotmem t ht hm
                  exact ih ((current, remainingTail, marked) :: rest) pathStack st'' hps' hnodup
                    (fun s hs => houter_eq ▸ hsv s hs) h hrc' hmarked' hpending' hinv' hpre_stack' hpre_back'
                    hpre_done'
            · -- unmarked: recurse, skip
              rename_i hunmarked
              have hpre_stack' : ∀ p ∈ (current, remainingTail, marked) :: rest, ∀ t, t ∈ succs p.1 →
                  t ∉ p.2.1 → t ∉ ((current, remainingTail, marked) :: rest).map Prod.fst →
                  0 ∈ edgeMarks p.1 t → ¬PathTo succs (fun _ => False) t p.1 := by
                intro p hp t ht htr htnmem hm
                simp only [List.map_cons] at htnmem
                rcases List.mem_cons.mp hp with rfl | hp'
                · by_cases hts : t = succ
                  · exact absurd (hts ▸ hm) (by simpa using hunmarked)
                  · exact hpre_stack_skip t ht hts htr (by simpa using htnmem) hm
                · exact hpre_stack p (List.mem_cons_of_mem _ hp') t ht htr (by simpa using htnmem) hm
              have hpre_back' : TStackBackUnmarked succs edgeMarks
                  ((current, remainingTail, marked) :: rest) :=
                TStackBackUnmarked.extend succs edgeMarks current succ remainingTail marked rest hpre_back
                  (fun _ => by simpa using hunmarked)
              have hpending' : TStackPending succs ((current, remainingTail, marked) :: rest) :=
                TStackPending.of_remaining_eq succs current (succ :: remainingTail) remainingTail marked rest
                  hpending
              have hmarked' := TStackMarked.of_remaining_eq edgeMarks current (succ :: remainingTail)
                remainingTail marked rest hmarked
              exact ih ((current, remainingTail, marked) :: rest) pathStack st hps' hnodup hsv h
                (hskip hvisited) hmarked' hpending' (by simpa using hinv) hpre_stack' hpre_back'
                (by simpa using hpre_done)
          · -- fresh: recurse, push
            rename_i hnotvisited
            have hsucc_edge : succ ∈ succs current :=
              hrc.stack_remaining_subset (current, succ :: remainingTail, marked) (List.mem_cons_self ..)
                succ (List.mem_cons_self ..)
            have hps' : pathStack ++ [succ] =
                (((succ, (succs succ).toList, (edgeMarks current succ).contains 0) ::
                  (current, remainingTail, marked) :: rest).map Prod.fst).reverse := by
              simp [hps]
            have hrc' : TOuterReachClosed succs
                { st with outerVisited := st.outerVisited.insert succ }
                ((succ, (succs succ).toList, (edgeMarks current succ).contains 0) ::
                  (current, remainingTail, marked) :: rest) := {
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
                      have ht_old := hrc.stack_processed_visited (current, succ :: remainingTail, marked)
                        (List.mem_cons_self ..) t ht hpr'
                      simp [Std.HashSet.contains_insert, ht_old]
                  · have ht_old := hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp'') t ht hpr
                    simp [Std.HashSet.contains_insert, ht_old]
              stack_remaining_subset := by
                intro p hp t ht
                rcases List.mem_cons.mp hp with rfl | hp'
                · exact Array.mem_toList_iff.mp ht
                · rcases List.mem_cons.mp hp' with rfl | hp''
                  · exact hrc.stack_remaining_subset (current, succ :: remainingTail, marked)
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
            have hsucc_notmem : succ ∉ pathStack := fun hmem => hnotvisited (hsv succ hmem)
            have hnodup' : (pathStack ++ [succ]).Nodup := by
              rw [List.nodup_append]
              refine ⟨hnodup, List.pairwise_singleton _ succ, ?_⟩
              intro a ha b hb heq
              subst heq
              simp only [List.mem_singleton] at hb
              subst hb
              exact hsucc_notmem ha
            have hmarked'' := TStackMarked.of_remaining_eq edgeMarks current (succ :: remainingTail)
              remainingTail marked rest hmarked
            have hmarked' := TStackMarked.cons edgeMarks (current, remainingTail, marked) rest succ
              (succs succ).toList hmarked''
            have hpending_mid : TStackPending succs ((current, remainingTail, marked) :: rest) :=
              TStackPending.of_remaining_eq succs current (succ :: remainingTail) remainingTail marked rest
                hpending
            have hpending' : TStackPending succs
                ((succ, (succs succ).toList, (edgeMarks current succ).contains 0) ::
                  (current, remainingTail, marked) :: rest) :=
              TStackPending.cons ((current, remainingTail, marked) :: rest)
                (fun p hp t ht htr => hrc.stack_processed_visited p (List.mem_cons_of_mem _ hp) t ht htr)
                succ (succs succ).toList ((edgeMarks current succ).contains 0)
                (by simpa using hnotvisited) hpending_mid
            have hinv' : TOuterInvariant succs { st with outerVisited := st.outerVisited.insert succ }
                (succ :: current :: rest.map Prod.fst) := {
              finished_closed := hinv.finished_closed
              finished_subset_visited := by
                intro s hs
                simp [Std.HashSet.contains_insert, hinv.finished_subset_visited s hs]
              finished_stack_disjoint := by
                intro s hs
                rcases List.mem_cons.mp hs with rfl | hs'
                · intro hfin
                  exact absurd (hinv.finished_subset_visited s hfin) (by simpa using hnotvisited)
                · exact hinv.finished_stack_disjoint s hs'
              stack_subset_visited := by
                intro s hs
                rcases List.mem_cons.mp hs with rfl | hs'
                · simp [Std.HashSet.contains_insert]
                · simp [Std.HashSet.contains_insert, hinv.stack_subset_visited s hs']
            }
            have hsucc_notstack : succ ∉ current :: rest.map Prod.fst := fun hmem =>
              hnotvisited (hinv.stack_subset_visited succ hmem)
            have hpre_stack' : ∀ p ∈ (succ, (succs succ).toList, (edgeMarks current succ).contains 0) ::
                (current, remainingTail, marked) :: rest, ∀ t, t ∈ succs p.1 → t ∉ p.2.1 →
                t ∉ (((succ, (succs succ).toList, (edgeMarks current succ).contains 0) ::
                  (current, remainingTail, marked) :: rest).map Prod.fst) → 0 ∈ edgeMarks p.1 t →
                ¬PathTo succs (fun _ => False) t p.1 := by
              intro p hp t ht htr htnmem hm
              simp only [List.map_cons] at htnmem
              rcases List.mem_cons.mp hp with rfl | hp'
              · exact absurd (Array.mem_toList_iff.mpr ht) htr
              · rcases List.mem_cons.mp hp' with rfl | hp''
                · by_cases hts : t = succ
                  · exact absurd (hts ▸ List.mem_cons_self ..) htnmem
                  · have htnmem' : t ∉ current :: rest.map Prod.fst := fun hmem =>
                      htnmem (List.mem_cons_of_mem _ hmem)
                    exact hpre_stack_skip t ht hts htr htnmem' hm
                · exact hpre_stack p (List.mem_cons_of_mem _ hp'') t ht htr
                    (fun hmem => htnmem (List.mem_cons_of_mem _ hmem)) hm
            have hpre_back_mid : TStackBackUnmarked succs edgeMarks ((current, remainingTail, marked) :: rest) :=
              TStackBackUnmarked.extend succs edgeMarks current succ remainingTail marked rest hpre_back
                (fun hmem => absurd hmem hsucc_notstack)
            have hpre_back' : TStackBackUnmarked succs edgeMarks
                ((succ, (succs succ).toList, (edgeMarks current succ).contains 0) ::
                  (current, remainingTail, marked) :: rest) :=
              TStackBackUnmarked.cons succs edgeMarks succ ((edgeMarks current succ).contains 0)
                ((current, remainingTail, marked) :: rest) hpre_back_mid
            have hpre_done' : ∀ s, ({ st with outerVisited := st.outerVisited.insert succ } :
                FNDFSState State).outerVisited.contains s → s ∉ succ :: current :: rest.map Prod.fst →
                ∀ t ∈ succs s, 0 ∈ edgeMarks s t → ¬PathTo succs (fun _ => False) t s := by
              intro s hvis hnotmem t ht hm
              have hs_ne_succ : s ≠ succ := fun heq => hnotmem (heq ▸ List.mem_cons_self ..)
              have hvis_old : st.outerVisited.contains s := by
                simp [Std.HashSet.contains_insert] at hvis
                rcases hvis with rfl | hvis
                · exact absurd rfl hs_ne_succ
                · exact hvis
              have hnotmem' : s ∉ current :: rest.map Prod.fst := fun hmem => hnotmem (List.mem_cons_of_mem _ hmem)
              exact hpre_done s hvis_old hnotmem' t ht hm
            exact ih ((succ, (succs succ).toList, (edgeMarks current succ).contains 0) ::
                (current, remainingTail, marked) :: rest)
              (pathStack ++ [succ]) { st with outerVisited := st.outerVisited.insert succ }
              hps' hnodup' hsv' h hrc' hmarked' hpending' hinv' hpre_stack' hpre_back' hpre_done'

end EmptyNoCycle

/-! ## Top-level composition across roots -/

section GoCorrectness

variable {State} [BEq State] [Hashable State] [LawfulBEq State]

/-- If `nestedDFST_fuel.go` returns `.empty`, its final state satisfies the invariants of `outerDFST_fuel_empty_no_cycle`
with an empty stack, extends the initial visited set, and has visited every state of `remaining`. -/
theorem nestedDFST_fuel_go_correct
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (remaining : List State) (st : FNDFSState State) (fuel : Nat) {n : Nat}
    (h : nestedDFST_fuel.go succs edgeMarks remaining st fuel = some (.empty n))
    (hrc : TOuterReachClosed succs st [])
    (hinv : TOuterInvariant succs st [])
    (hpre_done : ∀ s t, st.outerVisited.contains s → t ∈ succs s → 0 ∈ edgeMarks s t →
      ¬PathTo succs (fun _ => False) t s) :
    ∃ st', TOuterReachClosed succs st' [] ∧ TOuterInvariant succs st' [] ∧
      (∀ s t, st'.outerVisited.contains s → t ∈ succs s → 0 ∈ edgeMarks s t →
        ¬PathTo succs (fun _ => False) t s) ∧
      (∀ s, st.outerVisited.contains s → st'.outerVisited.contains s) ∧
      (∀ i ∈ remaining, st'.outerVisited.contains i) := by
  induction fuel generalizing remaining st with
  | zero => simp [nestedDFST_fuel.go.eq_def] at h
  | succ m ih =>
    rw [nestedDFST_fuel.go.eq_def] at h
    simp only at h
    split at h
    · -- remaining = []
      simp only [Option.some.injEq] at h
      exact ⟨st, hrc, hinv, hpre_done, fun s hs => hs, by simp⟩
    · -- remaining = init :: rest
      rename_i init rest
      split at h
      · -- init already visited
        rename_i hvisited
        obtain ⟨st', hrc', hinv', hpd', hmono, hroots⟩ := ih rest st h hrc hinv hpre_done
        refine ⟨st', hrc', hinv', hpd', hmono, ?_⟩
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi'
        · exact hmono i hvisited
        · exact hroots i hi'
      · -- init fresh
        rename_i hnotvisited
        have hnodup_pushed : ([init] : List State).Nodup := List.pairwise_singleton _ init
        have hps_pushed : ([init] : List State) =
            ([(init, (succs init).toList, false)].map Prod.fst).reverse := by simp
        have hsv_pushed : ∀ s ∈ ([init] : List State),
            ({ st with outerVisited := st.outerVisited.insert init } :
              FNDFSState State).outerVisited.contains s := by
          intro s hs; simp only [List.mem_singleton] at hs; subst hs
          simp [Std.HashSet.contains_insert]
        have hrc_pushed : TOuterReachClosed succs
            { st with outerVisited := st.outerVisited.insert init }
            [(init, (succs init).toList, false)] := {
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
        have hmarked_pushed : TStackMarked edgeMarks [(init, (succs init).toList, false)] :=
          fun i hi => absurd hi (by simp)
        have hpending_pushed : TStackPending succs [(init, (succs init).toList, false)] := trivial
        have hpre_stack_pushed : ∀ p ∈ [(init, (succs init).toList, false)], ∀ t, t ∈ succs p.1 →
            t ∉ p.2.1 → t ∉ [(init, (succs init).toList, false)].map Prod.fst →
            0 ∈ edgeMarks p.1 t → ¬PathTo succs (fun _ => False) t p.1 := by
          intro p hp t ht htr _ _
          simp only [List.mem_singleton] at hp
          subst hp
          exact absurd (Array.mem_toList_iff.mpr ht) htr
        have hpre_back_pushed : TStackBackUnmarked succs edgeMarks
            [(init, (succs init).toList, false)] :=
          ⟨fun _ ht htr _ => absurd (Array.mem_toList_iff.mpr ht) htr, trivial⟩
        have hinv_pushed : TOuterInvariant succs
            { st with outerVisited := st.outerVisited.insert init } [init] := {
          finished_closed := hinv.finished_closed
          finished_subset_visited := by
            intro s hs
            have hold := hinv.finished_subset_visited s hs
            simp [Std.HashSet.contains_insert, hold]
          finished_stack_disjoint := by
            intro s hs
            rcases List.mem_cons.mp hs with heq' | hs'
            · intro hcontra
              exact absurd (hinv.finished_subset_visited init (heq' ▸ hcontra)) hnotvisited
            · simp at hs'
          stack_subset_visited := by
            intro s hs
            rcases List.mem_cons.mp hs with rfl | hs'
            · simp [Std.HashSet.contains_insert]
            · simp at hs'
        }
        have hpre_done_pushed : ∀ s, ({ st with outerVisited := st.outerVisited.insert init } :
              FNDFSState State).outerVisited.contains s →
            s ∉ [(init, (succs init).toList, false)].map Prod.fst →
            ∀ t ∈ succs s, 0 ∈ edgeMarks s t → ¬PathTo succs (fun _ => False) t s := by
          intro s hs hnotmem t ht hm
          have hs_ne : s ≠ init := fun heq' => hnotmem (by simp [heq'])
          have hvis_old : st.outerVisited.contains s := by
            simp [Std.HashSet.contains_insert] at hs
            rcases hs with rfl | hs
            · exact absurd rfl hs_ne
            · exact hs
          exact hpre_done s t hvis_old ht hm
        split at h
        · -- fuel ran out inside outerDFST_fuel
          simp at h
        · -- nonEmpty result, contradicts .empty overall
          simp at h
        · -- empty, recurse
          rename_i st'' heq
          have hrc'' : TOuterReachClosed succs st'' [] :=
            outerDFST_fuel_reach_closed succs edgeMarks m
              [(init, (succs init).toList, false)] [init]
              { st with outerVisited := st.outerVisited.insert init } hsv_pushed heq hrc_pushed
          obtain ⟨hinv'', hpd''⟩ :=
            outerDFST_fuel_empty_no_cycle succs edgeMarks m
              [(init, (succs init).toList, false)] [init]
              { st with outerVisited := st.outerVisited.insert init }
              hps_pushed hnodup_pushed hsv_pushed heq hrc_pushed hmarked_pushed hpending_pushed
              hinv_pushed hpre_stack_pushed hpre_back_pushed hpre_done_pushed
          have hmono_push : ∀ s, st.outerVisited.contains s → st''.outerVisited.contains s := by
            intro s hs
            exact outerDFST_fuel_outerVisited_mono succs edgeMarks m
              [(init, (succs init).toList, false)] [init]
              { st with outerVisited := st.outerVisited.insert init } heq s
              (by simp [Std.HashSet.contains_insert, hs])
          obtain ⟨st', hrc', hinv', hpd', hmono', hroots'⟩ := ih rest st'' h hrc'' hinv'' hpd''
          refine ⟨st', hrc', hinv', hpd', fun s hs => hmono' s (hmono_push s hs), ?_⟩
          intro i hi
          rcases List.mem_cons.mp hi with heqi | hi'
          · have hinit_vis : st''.outerVisited.contains init :=
              outerDFST_fuel_outerVisited_mono succs edgeMarks m
                [(init, (succs init).toList, false)] [init]
                { st with outerVisited := st.outerVisited.insert init } heq init
                (by simp [Std.HashSet.contains_insert])
            exact heqi ▸ hmono' init hinit_vis
          · exact hroots' i hi'

/-- If `nestedDFST_fuel.go` returns `.nonEmpty stem loop`, then `(stem, loop.tail)` is an accepting-cycle witness rooted at a
state of `remaining`. -/
theorem nestedDFST_fuel_go_nonEmpty_witness
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (remaining : List State) (st : FNDFSState State) (fuel : Nat)
    {stem loop : List State}
    (h : nestedDFST_fuel.go succs edgeMarks remaining st fuel = some (.nonEmpty stem loop))
    (hrc : TOuterReachClosed succs st [])
    (hinv : TOuterInvariant succs st [])
    (hpre_done : ∀ s t, st.outerVisited.contains s → t ∈ succs s → 0 ∈ edgeMarks s t →
      ¬PathTo succs (fun _ => False) t s) :
    (∀ (hs : stem ≠ []), stem.head hs ∈ remaining) ∧
    stem.length ≥ 1 ∧
    loop.tail.length ≥ 1 ∧
    (∀ i, (hi : i + 1 < stem.length) → stem[i+1] ∈ succs stem[i]) ∧
    (∀ (hs : stem ≠ []) (hl : loop.tail ≠ []), stem.getLast hs = loop.tail.head hl) ∧
    (∀ i, (hi : i + 1 < loop.tail.length) → loop.tail[i+1] ∈ succs loop.tail[i]) ∧
    (∀ (hl : loop.tail ≠ []), loop.tail.head hl ∈ succs (loop.tail.getLast hl)) ∧
    (∃ (i : Nat) (hi : i < loop.tail.length),
      0 ∈ edgeMarks (loop.tail[i]) (loop.tail[(i + 1) % loop.tail.length]'(Nat.mod_lt _ (by omega)))) := by
  induction fuel generalizing remaining st with
  | zero => simp [nestedDFST_fuel.go.eq_def] at h
  | succ m ih =>
    rw [nestedDFST_fuel.go.eq_def] at h
    simp only at h
    split at h
    · -- remaining = []
      simp at h
    · -- remaining = init :: rest
      rename_i init rest
      split at h
      · -- init already visited
        obtain ⟨hmem, hrest⟩ := ih rest st h hrc hinv hpre_done
        exact ⟨fun hs => List.mem_cons_of_mem _ (hmem hs), hrest⟩
      · -- init fresh
        rename_i hnotvisited
        have hnodup_pushed : ([init] : List State).Nodup := List.pairwise_singleton _ init
        have hps_pushed : ([init] : List State) =
            ([(init, (succs init).toList, false)].map Prod.fst).reverse := by simp
        have hchain_pushed : ∀ i, (hi : i + 1 < ([init] : List State).length) →
            ([init] : List State)[i+1] ∈ succs (([init] : List State)[i]) := by
          intro i hi; simp at hi
        have hroot_pushed : ∀ (hp : ([init] : List State) ≠ []),
            ([init] : List State).head hp = init := fun _ => rfl
        have hsv_pushed : ∀ s ∈ ([init] : List State),
            ({ st with outerVisited := st.outerVisited.insert init } :
              FNDFSState State).outerVisited.contains s := by
          intro s hs; simp only [List.mem_singleton] at hs; subst hs
          simp [Std.HashSet.contains_insert]
        have hrc_pushed : TOuterReachClosed succs
            { st with outerVisited := st.outerVisited.insert init }
            [(init, (succs init).toList, false)] := {
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
        have hmarked_pushed : TStackMarked edgeMarks [(init, (succs init).toList, false)] :=
          fun i hi => absurd hi (by simp)
        split at h
        · -- fuel ran out inside outerDFST_fuel
          simp at h
        · -- found directly
          rename_i stem0 loop0 st'0 heq
          simp only [Option.some.injEq, EmptinessResult.nonEmpty.injEq] at h
          obtain ⟨heqs, heql⟩ := h
          subst heqs
          subst heql
          obtain ⟨hroot8, hlen, hltail, hchainstem, hoverlap, hchainloop, hback, hmarks⟩ :=
            outerDFST_fuel_nonEmpty_witness succs edgeMarks m
              [(init, (succs init).toList, false)] [init]
              { st with outerVisited := st.outerVisited.insert init } init
              hps_pushed hchain_pushed hroot_pushed hsv_pushed hnodup_pushed hrc_pushed
              hmarked_pushed heq
          refine ⟨fun hs => ?_, hlen, hltail, hchainstem, hoverlap, hchainloop, hback, hmarks⟩
          rw [hroot8 hs]
          exact List.mem_cons_self ..
        · -- empty, recurse
          rename_i st'' heq
          have hinv_pushed : TOuterInvariant succs
              { st with outerVisited := st.outerVisited.insert init } [init] := {
            finished_closed := hinv.finished_closed
            finished_subset_visited := by
              intro s hs
              have hold := hinv.finished_subset_visited s hs
              simp [Std.HashSet.contains_insert, hold]
            finished_stack_disjoint := by
              intro s hs
              rcases List.mem_cons.mp hs with heq' | hs'
              · intro hcontra
                exact absurd (hinv.finished_subset_visited init (heq' ▸ hcontra)) hnotvisited
              · simp at hs'
            stack_subset_visited := by
              intro s hs
              rcases List.mem_cons.mp hs with rfl | hs'
              · simp [Std.HashSet.contains_insert]
              · simp at hs'
          }
          have hpending_pushed : TStackPending succs [(init, (succs init).toList, false)] := trivial
          have hpre_stack_pushed : ∀ p ∈ [(init, (succs init).toList, false)], ∀ t, t ∈ succs p.1 →
              t ∉ p.2.1 → t ∉ [(init, (succs init).toList, false)].map Prod.fst →
              0 ∈ edgeMarks p.1 t → ¬PathTo succs (fun _ => False) t p.1 := by
            intro p hp t ht htr _ _
            simp only [List.mem_singleton] at hp
            subst hp
            exact absurd (Array.mem_toList_iff.mpr ht) htr
          have hpre_back_pushed : TStackBackUnmarked succs edgeMarks
              [(init, (succs init).toList, false)] :=
            ⟨fun _ ht htr _ => absurd (Array.mem_toList_iff.mpr ht) htr, trivial⟩
          have hpre_done_pushed : ∀ s, ({ st with outerVisited := st.outerVisited.insert init } :
                FNDFSState State).outerVisited.contains s →
              s ∉ [(init, (succs init).toList, false)].map Prod.fst →
              ∀ t ∈ succs s, 0 ∈ edgeMarks s t → ¬PathTo succs (fun _ => False) t s := by
            intro s hs hnotmem t ht hm
            have hs_ne : s ≠ init := fun heq' => hnotmem (by simp [heq'])
            have hvis_old : st.outerVisited.contains s := by
              simp [Std.HashSet.contains_insert] at hs
              rcases hs with rfl | hs
              · exact absurd rfl hs_ne
              · exact hs
            exact hpre_done s t hvis_old ht hm
          have hrc'' : TOuterReachClosed succs st'' [] :=
            outerDFST_fuel_reach_closed succs edgeMarks m
              [(init, (succs init).toList, false)] [init]
              { st with outerVisited := st.outerVisited.insert init } hsv_pushed heq hrc_pushed
          obtain ⟨hinv'', hpd''⟩ :=
            outerDFST_fuel_empty_no_cycle succs edgeMarks m
              [(init, (succs init).toList, false)] [init]
              { st with outerVisited := st.outerVisited.insert init }
              hps_pushed hnodup_pushed hsv_pushed heq hrc_pushed hmarked_pushed hpending_pushed
              hinv_pushed hpre_stack_pushed hpre_back_pushed hpre_done_pushed
          obtain ⟨hmem, hrest⟩ := ih rest st'' h hrc'' hinv'' hpd''
          exact ⟨fun hs => List.mem_cons_of_mem _ (hmem hs), hrest⟩

end GoCorrectness

/-! ## Top-level correctness theorem -/

section TopLevelCorrectness

variable {State} [BEq State] [Hashable State] [LawfulBEq State]

omit [BEq State] [Hashable State] [LawfulBEq State] in
-- The successor of every state on a `succs`-cycle reaches that state around the cycle.
private theorem cycle_wraparound_reach (succs : State → Array State) (cycle : List State)
    (hchain : ∀ i, (hi : i + 1 < cycle.length) → cycle[i+1] ∈ succs cycle[i])
    (hback : ∀ (hne : cycle ≠ []), cycle.head hne ∈ succs (cycle.getLast hne))
    (i : Nat) (hi : i < cycle.length) :
    PathTo succs (fun _ => False) (cycle[(i + 1) % cycle.length]'(Nat.mod_lt _ (by omega))) (cycle[i]'hi) := by
  have hne : cycle ≠ [] := List.ne_nil_of_length_pos (by omega)
  by_cases hlast : i = cycle.length - 1
  · have hj : (i + 1) % cycle.length = 0 := by
      have hi1 : i + 1 = cycle.length := by omega
      simp [hi1]
    have heq0 : (cycle[(i + 1) % cycle.length]'(Nat.mod_lt _ (by omega))) = cycle[0]'(by omega) := by
      simp only [hj]
    have heqi : cycle[i]'hi = cycle.getLast hne := by
      rw [List.getLast_eq_getElem]; congr 1
    rw [heq0, heqi]
    have hhead0 : cycle[(0 : Nat)]'(by omega) = cycle.head hne := (List.head_eq_getElem ..).symm
    rw [hhead0]
    rcases chain_reaches cycle hchain hne with heq | hp
    · exact heq ▸ PathTo.direct (heq ▸ hback hne)
    · exact hp
  · have hj : (i + 1) % cycle.length = i + 1 := Nat.mod_eq_of_lt (by omega)
    have heqj : (cycle[(i + 1) % cycle.length]'(Nat.mod_lt _ (by omega))) = cycle[i+1]'(by omega) := by
      simp only [hj]
    rw [heqj]
    have hsuf_chain := chain_drop cycle (i + 1) hchain
    have hsuf_ne : cycle.drop (i + 1) ≠ [] :=
      List.ne_nil_of_length_pos (by simp only [List.length_drop]; omega)
    have hsuf_head : (cycle.drop (i + 1)).head hsuf_ne = cycle[i+1]'(by omega) := by
      rw [List.head_eq_getElem, List.getElem_drop]
    have hsuf_last : (cycle.drop (i + 1)).getLast hsuf_ne = cycle.getLast hne := by
      rw [List.getLast_eq_getElem, List.getLast_eq_getElem, List.getElem_drop]
      congr 1
      simp only [List.length_drop]
      omega
    have hp1 : cycle[i+1]'(by omega) = cycle.getLast hne ∨
        PathTo succs (fun _ => False) (cycle[i+1]'(by omega)) (cycle.getLast hne) := by
      rw [← hsuf_head, ← hsuf_last]
      exact chain_reaches (cycle.drop (i + 1)) hsuf_chain hsuf_ne
    have hpre_chain := chain_take cycle (i + 1) hchain
    have hpre_ne : cycle.take (i + 1) ≠ [] :=
      List.ne_nil_of_length_pos (by simp only [List.length_take]; omega)
    have hpre_head : (cycle.take (i + 1)).head hpre_ne = cycle[0]'(by omega) := by
      rw [List.head_eq_getElem, List.getElem_take]
    have hpre_last : (cycle.take (i + 1)).getLast hpre_ne = cycle[i]'hi := by
      rw [List.getLast_eq_getElem, List.getElem_take]
      congr 1
      simp only [List.length_take]
      omega
    have hp2 : cycle[(0 : Nat)]'(by omega) = cycle[i]'hi ∨
        PathTo succs (fun _ => False) (cycle[(0 : Nat)]'(by omega)) (cycle[i]'hi) := by
      rw [← hpre_head, ← hpre_last]
      exact chain_reaches (cycle.take (i + 1)) hpre_chain hpre_ne
    have hback' : cycle[(0 : Nat)]'(by omega) ∈ succs (cycle.getLast hne) := by
      rw [show cycle[(0 : Nat)]'(by omega) = cycle.head hne from (List.head_eq_getElem ..).symm]
      exact hback hne
    have hmid : PathTo succs (fun _ => False) (cycle[i+1]'(by omega)) (cycle[(0 : Nat)]'(by omega)) := by
      rcases hp1 with heq1 | hp1
      · rw [heq1]; exact PathTo.direct hback'
      · exact PathTo.trans hp1 (PathTo.direct hback')
    rcases hp2 with heq2 | hp2
    · rw [← heq2]; exact hmid
    · exact PathTo.trans hmid hp2

/-- If the fuel-based nested DFS returns `.empty`, no `TAcceptingCycle` with one mark exists. -/
theorem nestedDFST_fuel_empty_no_cycle
    {initialStates : List State} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {fuel n : Nat}
    (h : nestedDFST_fuel initialStates succs edgeMarks fuel = some (.empty n)) :
    ¬∃ _ : TAcceptingCycle initialStates succs edgeMarks 1, True := by
  rintro ⟨ac, -⟩
  rw [nestedDFST_fuel] at h
  set st0 : FNDFSState State :=
    { outerVisited := Std.HashSet.emptyWithCapacity 1024, innerFinished := Std.HashSet.emptyWithCapacity 1024 }
    with hst0
  have hrc₀ : TOuterReachClosed succs st0 [] := {
    stack_chain := trivial
    done_closed := fun s hs => absurd hs (by simp [hst0, Std.HashSet.contains_emptyWithCapacity])
    stack_processed_visited := fun p hp => absurd hp (by simp)
    stack_remaining_subset := fun p hp => absurd hp (by simp)
  }
  have hinv₀ : TOuterInvariant succs st0 [] := {
    finished_closed := fun s hs => absurd hs (by simp [hst0, Std.HashSet.contains_emptyWithCapacity])
    finished_subset_visited := fun s hs => absurd hs (by simp [hst0, Std.HashSet.contains_emptyWithCapacity])
    finished_stack_disjoint := fun s hs => absurd hs (by simp)
    stack_subset_visited := fun s hs => absurd hs (by simp)
  }
  have hpre_done₀ : ∀ s t, st0.outerVisited.contains s →
      t ∈ succs s → 0 ∈ edgeMarks s t → ¬PathTo succs (fun _ => False) t s :=
    fun s _ hs _ _ => absurd hs (by simp [hst0, Std.HashSet.contains_emptyWithCapacity])
  obtain ⟨st', hrc', hinv', hpd', -, hroots⟩ :=
    nestedDFST_fuel_go_correct succs edgeMarks initialStates _ fuel h hrc₀ hinv₀ hpre_done₀
  have hstem_ne : ac.stem ≠ [] := List.ne_nil_of_length_pos (by have := ac.stem_nonempty; omega)
  have hcycle_ne : ac.cycle ≠ [] := List.ne_nil_of_length_pos (by have := ac.cycle_nonempty; omega)
  have hstem_head_vis : st'.outerVisited.contains (ac.stem.head hstem_ne) :=
    hroots _ ac.stem_head_initial
  have hCL : ∀ x, st'.outerVisited.contains x → ∀ y ∈ succs x, st'.outerVisited.contains y :=
    fun x hx y hy => hrc'.done_closed x hx (by simp) y hy
  have hcyclehead_vis : st'.outerVisited.contains (ac.cycle.head hcycle_ne) := by
    rcases chain_reaches ac.stem ac.stem_chain hstem_ne with heq | hp
    · have heq2 : ac.stem.getLast hstem_ne = ac.cycle.head hcycle_ne := ac.overlap
      rw [← heq2, ← heq]
      exact hstem_head_vis
    · have hp' : PathTo succs (fun _ => False) (ac.stem.head hstem_ne) (ac.cycle.head hcycle_ne) :=
        ac.overlap ▸ hp
      exact @PathTo.closed State succs (fun x => st'.outerVisited.contains x) _ _ hp' hstem_head_vis hCL
  obtain ⟨i, hi, hmark⟩ := ac.cycle_covers_marks 0 (by omega)
  have hcyclei_vis : st'.outerVisited.contains (ac.cycle[i]'hi) := by
    by_cases hi0 : i = 0
    · subst hi0
      rwa [List.head_eq_getElem] at hcyclehead_vis
    · have hpre_chain := chain_take ac.cycle (i + 1) ac.cycle_chain
      have hpre_ne : ac.cycle.take (i + 1) ≠ [] :=
        List.ne_nil_of_length_pos (by simp only [List.length_take]; omega)
      have hpre_head : (ac.cycle.take (i + 1)).head hpre_ne = ac.cycle[(0 : Nat)]'(by omega) := by
        rw [List.head_eq_getElem, List.getElem_take]
      have hpre_last : (ac.cycle.take (i + 1)).getLast hpre_ne = ac.cycle[i]'hi := by
        rw [List.getLast_eq_getElem, List.getElem_take]
        congr 1
        simp only [List.length_take]
        omega
      have hp2 : ac.cycle[(0 : Nat)]'(by omega) = ac.cycle[i]'hi ∨
          PathTo succs (fun _ => False) (ac.cycle[(0 : Nat)]'(by omega)) (ac.cycle[i]'hi) := by
        rw [← hpre_head, ← hpre_last]
        exact chain_reaches (ac.cycle.take (i + 1)) hpre_chain hpre_ne
      have hhead_eq : ac.cycle[(0 : Nat)]'(by omega) = ac.cycle.head hcycle_ne :=
        (List.head_eq_getElem ..).symm
      rw [hhead_eq] at hp2
      rcases hp2 with heq2 | hp2
      · rw [← heq2]; exact hcyclehead_vis
      · exact @PathTo.closed State succs (fun x => st'.outerVisited.contains x) _ _ hp2 hcyclehead_vis hCL
  have hedge : ac.cycle[(i + 1) % ac.cycle.length]'(Nat.mod_lt _ (by omega)) ∈ succs (ac.cycle[i]'hi) := by
    by_cases hlast : i = ac.cycle.length - 1
    · have hj : (i + 1) % ac.cycle.length = 0 := by
        have hi1 : i + 1 = ac.cycle.length := by omega
        simp [hi1]
      have heq0 : ac.cycle[(i + 1) % ac.cycle.length]'(Nat.mod_lt _ (by omega)) =
          ac.cycle[(0 : Nat)]'(by omega) := by simp only [hj]
      have heqi : ac.cycle[i]'hi = ac.cycle.getLast hcycle_ne := by
        rw [List.getLast_eq_getElem]; congr 1
      rw [heq0, heqi, show ac.cycle[(0 : Nat)]'(by omega) = ac.cycle.head hcycle_ne from
        (List.head_eq_getElem ..).symm]
      exact ac.cycle_back
    · have hj : (i + 1) % ac.cycle.length = i + 1 := Nat.mod_eq_of_lt (by omega)
      have heqj : ac.cycle[(i + 1) % ac.cycle.length]'(Nat.mod_lt _ (by omega)) =
          ac.cycle[i + 1]'(by omega) := by simp only [hj]
      rw [heqj]
      exact ac.cycle_chain i (by omega)
  exact hpd' (ac.cycle[i]'hi) (ac.cycle[(i + 1) % ac.cycle.length]'(Nat.mod_lt _ (by omega)))
    hcyclei_vis hedge hmark
    (cycle_wraparound_reach succs ac.cycle ac.cycle_chain (fun _ => ac.cycle_back) i hi)

/-- If the fuel-based nested DFS returns `.nonEmpty stem loop`, then `(stem, loop.tail)` is a `TAcceptingCycle` with one mark. -/
theorem nestedDFST_fuel_nonEmpty_valid
    {initialStates : List State} {succs : State → Array State}
    {edgeMarks : State → State → Std.HashSet Nat} {fuel : Nat} {stem loop : List State}
    (h : nestedDFST_fuel initialStates succs edgeMarks fuel = some (.nonEmpty stem loop)) :
    ∃ ac : TAcceptingCycle initialStates succs edgeMarks 1,
      ac.stem = stem ∧ ac.cycle = loop.tail := by
  rw [nestedDFST_fuel] at h
  set st0 : FNDFSState State :=
    { outerVisited := Std.HashSet.emptyWithCapacity 1024, innerFinished := Std.HashSet.emptyWithCapacity 1024 }
    with hst0
  have hrc₀ : TOuterReachClosed succs st0 [] := {
    stack_chain := trivial
    done_closed := fun s hs => absurd hs (by simp [hst0, Std.HashSet.contains_emptyWithCapacity])
    stack_processed_visited := fun p hp => absurd hp (by simp)
    stack_remaining_subset := fun p hp => absurd hp (by simp)
  }
  have hinv₀ : TOuterInvariant succs st0 [] := {
    finished_closed := fun s hs => absurd hs (by simp [hst0, Std.HashSet.contains_emptyWithCapacity])
    finished_subset_visited := fun s hs => absurd hs (by simp [hst0, Std.HashSet.contains_emptyWithCapacity])
    finished_stack_disjoint := fun s hs => absurd hs (by simp)
    stack_subset_visited := fun s hs => absurd hs (by simp)
  }
  have hpre_done₀ : ∀ s t, st0.outerVisited.contains s →
      t ∈ succs s → 0 ∈ edgeMarks s t → ¬PathTo succs (fun _ => False) t s :=
    fun s _ hs _ _ => absurd hs (by simp [hst0, Std.HashSet.contains_emptyWithCapacity])
  obtain ⟨hroot, hlen, hltail, hchainstem, hoverlap, hchainloop, hback, hmarks⟩ :=
    nestedDFST_fuel_go_nonEmpty_witness succs edgeMarks initialStates _ fuel h hrc₀ hinv₀ hpre_done₀
  have hstem_ne : stem ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hloop_ne : loop.tail ≠ [] := List.ne_nil_of_length_pos (by omega)
  refine ⟨{
    stem := stem
    cycle := loop.tail
    stem_nonempty := hlen
    cycle_nonempty := hltail
    stem_head_initial := hroot hstem_ne
    stem_chain := hchainstem
    overlap := hoverlap hstem_ne hloop_ne
    cycle_chain := hchainloop
    cycle_back := hback hloop_ne
    cycle_covers_marks := by
      intro m hm
      have hm0 : m = 0 := by omega
      subst hm0
      exact hmarks
  }, rfl, rfl⟩

end TopLevelCorrectness

end LTLLib
