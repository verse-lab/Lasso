module

/-
  Well-founded executable version of the edge-aware nested DFS, terminating by a `reachCount` measure, and the fuel bridge
  transporting the correctness theorems of `NestedDFSTCorrectness.lean` onto it.

  The inner DFS and its lemmas from `InnerDFSTermination.lean` are reused unchanged, as are that file's `RFrame`
  stack and lexicographic measure, reachable minus `outerVisited` paired with the pending count, with the per-frame
  `marked` bit paired in externally. Correctness is stated for a single mark, the shape `TGBA.degeneralize` produces.

  Defines:
  - `outerDFSTWF`: the well-founded edge-aware outer DFS
  - `nestedDFSTWF`: the well-founded edge-aware nested DFS emptiness check

  Proves:
  - `outerDFST_fuel_eq_outerDFSTWF`, `nestedDFST_fuel_eq_nestedDFSTWF`: some fuel makes the fuel version agree with the well-founded one
  - `nestedDFSTWF_empty_no_cycle`: an `.empty` result rules out every `TAcceptingCycle` with one mark
  - `nestedDFSTWF_nonEmpty_valid`: a `.nonEmpty stem loop` result gives a `TAcceptingCycle` with one mark

  References:
  - Holzmann, Peled & Yannakakis: "On Nested Depth First Search" (SPIN 1996) — the accepting-leaf shortcut,
    `target` may be any state on `pathStack`, not just `current`.
  - Schwoon & Esparza: "A Note on On-The-Fly Verification Algorithms" (TACAS 2005) — the back-edge shortcut that
    reports a cycle from `pathStack.contains succ` alone, without launching an inner DFS.

  Sections:
  - Well-founded `outerDFST`
  - Fuel ↔ well-founded bridge, outer half
  - Top-level `nestedDFST`, well-founded
  - Fuel ↔ well-founded bridge, top level
-/
public import Lasso.NestedDFS.InnerDFSTermination
-- The TGBA termination proof reuses the private fuel bridge.
import all Lasso.NestedDFS.InnerDFSTermination
public import Lasso.NestedDFS.NestedDFSTCorrectness

public section

namespace Lasso

/-! ## Well-founded `outerDFST` -/

section OuterDFSTWellFounded

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-- Well-founded `outerDFST`, `RFrame`-based with the per-frame `marked` bit paired in externally,
and the same three cases as `outerDFST_fuel` (back edge, postorder-triggered tree edge, immediate forward/cross edge). -/
def outerDFSTWF [LawfulHashable State] {initialStates : List State}
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (fr : FiniteReach initialStates succs)
    (stack : List (RFrame initialStates succs × Bool × List (Std.HashSet Nat)))
    (pathStack : List State)
    (st : FNDFSState State)
    : EmptinessResult State × FNDFSState State :=
  match stack with
  | [] => (.empty st.outerVisited.size, st)
  | (frame, marked, marksRem) :: rest =>
    match hrem : frame.remaining with
    | [] =>
      match _hrest : rest with
      | [] => outerDFSTWF succs edgeMarks expand fr rest pathStack.dropLast st
      | (parentFrame, _, _) :: _ =>
        if marked then
          let ancestors := pathStack.dropLast
          let innerVisited := Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)
          match _hr : innerDFSWF succs fr parentFrame.state ancestors frame.state frame.hreach
              innerVisited st with
          | (some (cyclePath, target), _, st') =>
            let loopTail := (pathStack.dropWhile (fun y => !(y == target))).dropLast.dropLast
            (.nonEmpty ancestors (parentFrame.state :: parentFrame.state :: cyclePath ++ loopTail), st')
          | (none, _, st') =>
            outerDFSTWF succs edgeMarks expand fr rest ancestors st'
        else
          outerDFSTWF succs edgeMarks expand fr rest pathStack.dropLast st
    | succ :: remainingTail =>
      have hmemrem : succ ∈ frame.remaining := hrem ▸ List.mem_cons_self
      have hmemsuccs : succ ∈ succs frame.state :=
        Array.mem_toList_iff.mp (frame.hsuffix.mem hmemrem)
      -- PERF: the edge's marks are read off the frame's cached `marksRem` rather than recomputed by
      -- `edgeMarks frame.state succ`. `marksRem` is filled once per pushed frame from `(expand _).2.1`, so the
      -- caller's per-source work is paid once per state instead of once per outgoing edge. Under `ExpandCoherent`
      -- the invariant `marksRem = frame.remaining.map (edgeMarks frame.state)` holds, so the head is exactly
      -- `edgeMarks frame.state succ` and the `[]` branch is unreachable.
      let marksHead := marksRem.head?.getD (Std.HashSet.emptyWithCapacity 0)
      let marksTail := marksRem.tail
      let stack' := (frame.consumeOne succ remainingTail hrem, marked, marksTail) :: rest
      let edgeMarked := marksHead.contains 0
      if pathStack.contains succ then
        if edgeMarked then
          let stem := pathStack.takeWhile (fun y => !(y == succ)) ++ [succ]
          let loop := succ :: pathStack.dropWhile (fun y => !(y == succ))
          (.nonEmpty stem loop, st)
        else
          outerDFSTWF succs edgeMarks expand fr stack' pathStack st
      else if _hvis : st.outerVisited.contains succ then
        if edgeMarked then
          let innerVisited := Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)
          match _hr : innerDFSWF succs fr frame.state pathStack succ
              (Reachable.step frame.hreach hmemsuccs) innerVisited st with
          | (some (cyclePath, target), _, st') =>
            let loopTail := (pathStack.dropWhile (fun y => !(y == target))).dropLast
            (.nonEmpty pathStack (frame.state :: frame.state :: cyclePath ++ loopTail), st')
          | (none, _, st') =>
            outerDFSTWF succs edgeMarks expand fr stack' pathStack st'
        else
          outerDFSTWF succs edgeMarks expand fr stack' pathStack st
      else
        let st2 := { st with outerVisited := st.outerVisited.insert succ }
        outerDFSTWF succs edgeMarks expand fr
          ((frame.push succ hmemsuccs, edgeMarked, (expand succ).2.1.toList) :: stack')
          (pathStack ++ [succ]) st2
termination_by
  (reachCount initialStates succs (fun x => st.outerVisited.contains x = false),
   pendingSum (stack.map Prod.fst) + stack.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp [pendingSum_cons, hrem, _hrest])
  · have hst'_eq : st'.outerVisited = st.outerVisited := by
      have hr2 := innerDFSWF_outerVisited_pres succs fr parentFrame.state ancestors frame.state
        frame.hreach innerVisited st
      rw [_hr] at hr2
      exact hr2
    rw [hst'_eq]
    exact Prod.Lex.right _ (by simp [pendingSum_cons, hrem, _hrest])
  · exact Prod.Lex.right _ (by simp [pendingSum_cons, hrem, _hrest])
  · exact Prod.Lex.right _ (by simp [pendingSum_cons, RFrame.consumeOne, hrem])
  · have hst'_eq : st'.outerVisited = st.outerVisited := by
      have hr2 := innerDFSWF_outerVisited_pres succs fr frame.state pathStack succ
        (Reachable.step frame.hreach hmemsuccs) innerVisited st
      rw [_hr] at hr2
      exact hr2
    rw [hst'_eq]
    exact Prod.Lex.right _ (by simp [pendingSum_cons, RFrame.consumeOne, hrem])
  · exact Prod.Lex.right _ (by simp [pendingSum_cons, RFrame.consumeOne, hrem])
  · have hsucc_niv : st.outerVisited.contains succ = false := by simpa using _hvis
    exact Prod.Lex.left _ _ (Reachable.reachCount_insert_lt fr
      (Reachable.step frame.hreach hmemsuccs) hsucc_niv)

end OuterDFSTWellFounded

/-! ## Fuel ↔ well-founded bridge, outer half -/

section OuterFuelBridge

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-! One-step unfolding equations for `outerDFST_fuel` -/

theorem outerDFST_fuel_nil (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (fuel : Nat) (pathStack : List State) (st : FNDFSState State) :
    outerDFST_fuel succs edgeMarks (fuel + 1) [] pathStack st =
      some (.empty st.outerVisited.size, st) := by
  unfold outerDFST_fuel
  rfl

theorem outerDFST_fuel_postorder_skip_norest (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (fuel : Nat) (current : State) (marked : Bool)
    (pathStack : List State) (st : FNDFSState State) :
    outerDFST_fuel succs edgeMarks (fuel + 1) [(current, [], marked)] pathStack st =
      outerDFST_fuel succs edgeMarks fuel [] pathStack.dropLast st := by
  conv => lhs; rw [outerDFST_fuel.eq_def]
  cases marked <;> simp

theorem outerDFST_fuel_postorder_skip_unmarked (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (fuel : Nat) (current parent : State)
    (parentRem : List State) (parentMarked : Bool) (tail : List (State × List State × Bool))
    (pathStack : List State) (st : FNDFSState State) :
    outerDFST_fuel succs edgeMarks (fuel + 1)
        ((current, [], false) :: (parent, parentRem, parentMarked) :: tail) pathStack st =
      outerDFST_fuel succs edgeMarks fuel ((parent, parentRem, parentMarked) :: tail)
        pathStack.dropLast st := by
  conv => lhs; rw [outerDFST_fuel.eq_def]

theorem outerDFST_fuel_postorder_none (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (fuel : Nat) (current parent : State)
    (parentRem : List State) (parentMarked : Bool) (tail : List (State × List State × Bool))
    (pathStack : List State) (st : FNDFSState State)
    (hinner : innerDFS_fuel succs parent pathStack.dropLast fuel current
        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st = none) :
    outerDFST_fuel succs edgeMarks (fuel + 1)
        ((current, [], true) :: (parent, parentRem, parentMarked) :: tail) pathStack st = none := by
  unfold outerDFST_fuel
  simp [hinner]

theorem outerDFST_fuel_postorder_found (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (fuel : Nat) (current parent : State)
    (parentRem : List State) (parentMarked : Bool) (tail : List (State × List State × Bool))
    (pathStack : List State) (st : FNDFSState State)
    (cyclePath : List State) (target : State) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (hinner : innerDFS_fuel succs parent pathStack.dropLast fuel current
        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st =
      some (some (cyclePath, target), iv', st')) :
    outerDFST_fuel succs edgeMarks (fuel + 1)
        ((current, [], true) :: (parent, parentRem, parentMarked) :: tail) pathStack st =
      some (.nonEmpty pathStack.dropLast (parent :: parent :: cyclePath ++
        (pathStack.dropWhile (fun y => !(y == target))).dropLast.dropLast), st') := by
  unfold outerDFST_fuel
  simp [hinner]

theorem outerDFST_fuel_postorder_not_found (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (fuel : Nat) (current parent : State)
    (parentRem : List State) (parentMarked : Bool) (tail : List (State × List State × Bool))
    (pathStack : List State) (st : FNDFSState State)
    (iv' : Std.HashSet State) (st' : FNDFSState State)
    (hinner : innerDFS_fuel succs parent pathStack.dropLast fuel current
        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st = some (none, iv', st')) :
    outerDFST_fuel succs edgeMarks (fuel + 1)
        ((current, [], true) :: (parent, parentRem, parentMarked) :: tail) pathStack st =
      outerDFST_fuel succs edgeMarks fuel ((parent, parentRem, parentMarked) :: tail)
        pathStack.dropLast st' := by
  conv => lhs; rw [outerDFST_fuel.eq_def]
  simp [hinner]

theorem outerDFST_fuel_back_edge_marked (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (fuel : Nat) (current succ : State)
    (remainingTail : List State) (marked : Bool) (rest : List (State × List State × Bool))
    (pathStack : List State) (st : FNDFSState State)
    (hb : succ ∈ pathStack) (hm : (edgeMarks current succ).contains 0 = true) :
    outerDFST_fuel succs edgeMarks (fuel + 1)
        ((current, succ :: remainingTail, marked) :: rest) pathStack st =
      some (.nonEmpty (pathStack.takeWhile (fun y => !(y == succ)) ++ [succ])
        (succ :: pathStack.dropWhile (fun y => !(y == succ))), st) := by
  unfold outerDFST_fuel
  simp [hb, hm]

theorem outerDFST_fuel_back_edge_skip (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (fuel : Nat) (current succ : State)
    (remainingTail : List State) (marked : Bool) (rest : List (State × List State × Bool))
    (pathStack : List State) (st : FNDFSState State)
    (hb : succ ∈ pathStack) (hm : (edgeMarks current succ).contains 0 = false) :
    outerDFST_fuel succs edgeMarks (fuel + 1)
        ((current, succ :: remainingTail, marked) :: rest) pathStack st =
      outerDFST_fuel succs edgeMarks fuel ((current, remainingTail, marked) :: rest) pathStack st := by
  conv => lhs; rw [outerDFST_fuel.eq_def]
  simp [hb, hm]

theorem outerDFST_fuel_forward_none (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (fuel : Nat) (current succ : State)
    (remainingTail : List State) (marked : Bool) (rest : List (State × List State × Bool))
    (pathStack : List State) (st : FNDFSState State)
    (hnb : succ ∉ pathStack) (hvis : st.outerVisited.contains succ = true)
    (hm : (edgeMarks current succ).contains 0 = true)
    (hinner : innerDFS_fuel succs current pathStack fuel succ
        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st = none) :
    outerDFST_fuel succs edgeMarks (fuel + 1)
        ((current, succ :: remainingTail, marked) :: rest) pathStack st = none := by
  unfold outerDFST_fuel
  simp [hnb, hvis, hm, hinner]

theorem outerDFST_fuel_forward_found (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (fuel : Nat) (current succ : State)
    (remainingTail : List State) (marked : Bool) (rest : List (State × List State × Bool))
    (pathStack : List State) (st : FNDFSState State)
    (hnb : succ ∉ pathStack) (hvis : st.outerVisited.contains succ = true)
    (hm : (edgeMarks current succ).contains 0 = true)
    (cyclePath : List State) (target : State) (iv' : Std.HashSet State) (st' : FNDFSState State)
    (hinner : innerDFS_fuel succs current pathStack fuel succ
        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st =
      some (some (cyclePath, target), iv', st')) :
    outerDFST_fuel succs edgeMarks (fuel + 1)
        ((current, succ :: remainingTail, marked) :: rest) pathStack st =
      some (.nonEmpty pathStack (current :: current :: cyclePath ++
        (pathStack.dropWhile (fun y => !(y == target))).dropLast), st') := by
  unfold outerDFST_fuel
  simp [hnb, hvis, hm, hinner]

theorem outerDFST_fuel_forward_not_found (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (fuel : Nat) (current succ : State)
    (remainingTail : List State) (marked : Bool) (rest : List (State × List State × Bool))
    (pathStack : List State) (st : FNDFSState State)
    (hnb : succ ∉ pathStack) (hvis : st.outerVisited.contains succ = true)
    (hm : (edgeMarks current succ).contains 0 = true)
    (iv' : Std.HashSet State) (st' : FNDFSState State)
    (hinner : innerDFS_fuel succs current pathStack fuel succ
        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st = some (none, iv', st')) :
    outerDFST_fuel succs edgeMarks (fuel + 1)
        ((current, succ :: remainingTail, marked) :: rest) pathStack st =
      outerDFST_fuel succs edgeMarks fuel ((current, remainingTail, marked) :: rest) pathStack st' := by
  conv => lhs; rw [outerDFST_fuel.eq_def]
  simp [hnb, hvis, hm, hinner]

theorem outerDFST_fuel_forward_skip (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (fuel : Nat) (current succ : State)
    (remainingTail : List State) (marked : Bool) (rest : List (State × List State × Bool))
    (pathStack : List State) (st : FNDFSState State)
    (hnb : succ ∉ pathStack) (hvis : st.outerVisited.contains succ = true)
    (hm : (edgeMarks current succ).contains 0 = false) :
    outerDFST_fuel succs edgeMarks (fuel + 1)
        ((current, succ :: remainingTail, marked) :: rest) pathStack st =
      outerDFST_fuel succs edgeMarks fuel ((current, remainingTail, marked) :: rest) pathStack st := by
  conv => lhs; rw [outerDFST_fuel.eq_def]
  simp [hnb, hvis, hm]

theorem outerDFST_fuel_push (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (fuel : Nat) (current succ : State)
    (remainingTail : List State) (marked : Bool) (rest : List (State × List State × Bool))
    (pathStack : List State) (st : FNDFSState State)
    (hnb : succ ∉ pathStack) (hvis : st.outerVisited.contains succ = false) :
    outerDFST_fuel succs edgeMarks (fuel + 1)
        ((current, succ :: remainingTail, marked) :: rest) pathStack st =
      outerDFST_fuel succs edgeMarks fuel
        ((succ, (succs succ).toList, (edgeMarks current succ).contains 0) ::
          (current, remainingTail, marked) :: rest) (pathStack ++ [succ])
        { st with outerVisited := st.outerVisited.insert succ } := by
  conv => lhs; rw [outerDFST_fuel.eq_def]
  simp [hnb, hvis]

/-- Fuel-increase preserves a successful `outerDFST_fuel` result. -/
theorem outerDFST_fuel_add_preserves (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (extra fuel : Nat)
    (stack : List (State × List State × Bool)) (pathStack : List State) (st : FNDFSState State)
    (result : EmptinessResult State) (st' : FNDFSState State)
    (h : outerDFST_fuel succs edgeMarks fuel stack pathStack st = some (result, st')) :
    outerDFST_fuel succs edgeMarks (fuel + extra) stack pathStack st = some (result, st') := by
  induction fuel generalizing stack pathStack st result st' with
  | zero => simp [outerDFST_fuel.eq_def] at h
  | succ n ih =>
    rw [show n + 1 + extra = (n + extra) + 1 by omega]
    match stack with
    | [] =>
      rw [outerDFST_fuel_nil] at h
      rw [outerDFST_fuel_nil]
      exact h
    | (current, remaining, marked) :: rest =>
      match remaining with
      | [] =>
        match rest with
        | [] =>
          rw [outerDFST_fuel_postorder_skip_norest] at h
          rw [outerDFST_fuel_postorder_skip_norest]
          exact ih [] pathStack.dropLast st result st' h
        | (parent, parentRem, parentMarked) :: tail =>
          by_cases hmk : marked = true
          · subst hmk
            cases hinner : innerDFS_fuel succs parent pathStack.dropLast n current
                (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st with
            | none =>
              rw [outerDFST_fuel_postorder_none succs edgeMarks n current parent parentRem
                  parentMarked tail pathStack st hinner] at h
              exact absurd h (by simp)
            | some val =>
              obtain ⟨cyc, iv', st''⟩ := val
              cases cyc with
              | some val2 =>
                obtain ⟨cyclePath, target⟩ := val2
                rw [outerDFST_fuel_postorder_found succs edgeMarks n current parent parentRem
                    parentMarked tail pathStack st cyclePath target iv' st'' hinner] at h
                rw [outerDFST_fuel_postorder_found succs edgeMarks (n + extra) current parent
                    parentRem parentMarked tail pathStack st cyclePath target iv' st''
                    (innerDFS_fuel_add_preserves succs parent pathStack.dropLast extra n current
                      (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st
                      (some (cyclePath, target)) iv' st'' hinner)]
                exact h
              | none =>
                rw [outerDFST_fuel_postorder_not_found succs edgeMarks n current parent parentRem
                    parentMarked tail pathStack st iv' st'' hinner] at h
                rw [outerDFST_fuel_postorder_not_found succs edgeMarks (n + extra) current parent
                    parentRem parentMarked tail pathStack st iv' st''
                    (innerDFS_fuel_add_preserves succs parent pathStack.dropLast extra n current
                      (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st none iv' st''
                      hinner)]
                exact ih ((parent, parentRem, parentMarked) :: tail) pathStack.dropLast st'' result
                  st' h
          · simp only [Bool.not_eq_true] at hmk
            rw [hmk] at h ⊢
            rw [outerDFST_fuel_postorder_skip_unmarked] at h
            rw [outerDFST_fuel_postorder_skip_unmarked]
            exact ih ((parent, parentRem, parentMarked) :: tail) pathStack.dropLast st result
              st' h
      | succ :: remainingTail =>
        by_cases hb : succ ∈ pathStack
        · by_cases hm : (edgeMarks current succ).contains 0 = true
          · rw [outerDFST_fuel_back_edge_marked succs edgeMarks n current succ remainingTail
                marked rest pathStack st hb hm] at h
            rw [outerDFST_fuel_back_edge_marked succs edgeMarks (n + extra) current succ
                remainingTail marked rest pathStack st hb hm]
            exact h
          · simp only [Bool.not_eq_true] at hm
            rw [outerDFST_fuel_back_edge_skip succs edgeMarks n current succ remainingTail marked
                rest pathStack st hb hm] at h
            rw [outerDFST_fuel_back_edge_skip succs edgeMarks (n + extra) current succ
                remainingTail marked rest pathStack st hb hm]
            exact ih ((current, remainingTail, marked) :: rest) pathStack st result st' h
        · by_cases hvis : st.outerVisited.contains succ = true
          · by_cases hm : (edgeMarks current succ).contains 0 = true
            · cases hinner : innerDFS_fuel succs current pathStack n succ
                  (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st with
              | none =>
                rw [outerDFST_fuel_forward_none succs edgeMarks n current succ remainingTail
                    marked rest pathStack st hb hvis hm hinner] at h
                exact absurd h (by simp)
              | some val =>
                obtain ⟨cyc, iv', st''⟩ := val
                cases cyc with
                | some val2 =>
                  obtain ⟨cyclePath, target⟩ := val2
                  rw [outerDFST_fuel_forward_found succs edgeMarks n current succ remainingTail
                      marked rest pathStack st hb hvis hm cyclePath target iv' st'' hinner] at h
                  rw [outerDFST_fuel_forward_found succs edgeMarks (n + extra) current succ
                      remainingTail marked rest pathStack st hb hvis hm cyclePath target iv' st''
                      (innerDFS_fuel_add_preserves succs current pathStack extra n succ
                        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st
                        (some (cyclePath, target)) iv' st'' hinner)]
                  exact h
                | none =>
                  rw [outerDFST_fuel_forward_not_found succs edgeMarks n current succ
                      remainingTail marked rest pathStack st hb hvis hm iv' st'' hinner] at h
                  rw [outerDFST_fuel_forward_not_found succs edgeMarks (n + extra) current succ
                      remainingTail marked rest pathStack st hb hvis hm iv' st''
                      (innerDFS_fuel_add_preserves succs current pathStack extra n succ
                        (Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)) st none iv' st''
                        hinner)]
                  exact ih ((current, remainingTail, marked) :: rest) pathStack st'' result st' h
            · simp only [Bool.not_eq_true] at hm
              rw [outerDFST_fuel_forward_skip succs edgeMarks n current succ remainingTail marked
                  rest pathStack st hb hvis hm] at h
              rw [outerDFST_fuel_forward_skip succs edgeMarks (n + extra) current succ
                  remainingTail marked rest pathStack st hb hvis hm]
              exact ih ((current, remainingTail, marked) :: rest) pathStack st result st' h
          · simp only [Bool.not_eq_true] at hvis
            rw [outerDFST_fuel_push succs edgeMarks n current succ remainingTail marked rest
                pathStack st hb hvis] at h
            rw [outerDFST_fuel_push succs edgeMarks (n + extra) current succ remainingTail marked
                rest pathStack st hb hvis]
            exact ih ((succ, (succs succ).toList, (edgeMarks current succ).contains 0) ::
                (current, remainingTail, marked) :: rest) (pathStack ++ [succ])
              { st with outerVisited := st.outerVisited.insert succ } result st' h

variable {initialStates : List State} [LawfulHashable State] (succs : State → Array State)
  (fr : FiniteReach initialStates succs) (edgeMarks : State → State → Std.HashSet Nat)
  (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)

omit [BEq State] [Hashable State] [LawfulBEq State] [LawfulHashable State] in
/-- The marks cached when a frame is pushed are exactly the marks of that state's outgoing edges. -/
theorem expand_snd_toList (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)
    (hexp : ExpandCoherent succs edgeMarks expand) (s : State) :
    (expand s).2.1.toList = (succs s).toList.map (edgeMarks s) := by
  rw [hexp.snd s]; simp

/-- For a suitable `stack`, `pathStack` and `st`, some fuel makes `outerDFST_fuel` succeed and agree with
`outerDFSTWF`.

`hmarks` is the frame-cache invariant: every frame's cached `marksRem` is exactly the marks of its own remaining
successors. -/
theorem outerDFST_fuel_eq_outerDFSTWF
    (hexp : ExpandCoherent succs edgeMarks expand)
    (stack : List (RFrame initialStates succs × Bool × List (Std.HashSet Nat)))
    (hmarks : ∀ f ∈ stack, f.2.2 = f.1.remaining.map (edgeMarks f.1.state))
    (pathStack : List State) (st : FNDFSState State)
    (hfin : ∀ x, st.innerFinished.contains x → Reachable initialStates succs x) :
    ∃ fuel result st', outerDFST_fuel succs edgeMarks fuel
        (stack.map (fun f => (f.1.state, f.1.remaining, f.2.1))) pathStack st =
        some (result, st') ∧
      (∀ x, st'.innerFinished.contains x → Reachable initialStates succs x) ∧
      (result, st') = outerDFSTWF succs edgeMarks expand fr stack pathStack st := by
  induction stack, pathStack, st using outerDFSTWF.induct (succs := succs)
      (expand := expand) (fr := fr) with
  | case1 =>
    rename_i pathStack st
    refine ⟨1, .empty st.outerVisited.size, st,
      outerDFST_fuel_nil succs edgeMarks 0 pathStack st, hfin, ?_⟩
    unfold outerDFSTWF
    rfl
  | case2 =>
    rename_i pathStack st frame marked marksRem hrem ih1
    obtain ⟨fuel2, result2, st2, heq2, hfin2, heqC2⟩ := ih1 (by simp) hfin
    refine ⟨fuel2 + 1, result2, st2, ?_, hfin2, ?_⟩
    · simp only [List.map_cons, List.map_nil, hrem]
      exact outerDFST_fuel_postorder_skip_norest succs edgeMarks fuel2 frame.state marked
        pathStack st ▸ heq2
    · unfold outerDFSTWF
      grind
  | case3 =>
    rename_i pathStack st frame marksRem hrem parentFrame snd pmarks tail ancestors innerVisited
      cyclePath target fst st' hr
    have hiv : ∀ x, innerVisited.contains x → Reachable initialStates succs x := by
      simp [innerVisited, Std.HashSet.contains_emptyWithCapacity]
    obtain ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩ :=
      innerDFS_fuel_eq_innerDFSWF succs fr parentFrame.state ancestors
        (reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1) frame.state frame.hreach innerVisited st
        hiv hfin (Nat.le_refl _)
    rw [hr] at heqC
    simp only [Prod.mk.injEq] at heqC
    obtain ⟨rfl, rfl, rfl⟩ := heqC
    refine ⟨reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1 + 1,
      .nonEmpty ancestors (parentFrame.state :: parentFrame.state :: cyclePath ++
        (pathStack.dropWhile (fun y => !(y == target))).dropLast.dropLast), st₁, ?_, hfin1, ?_⟩
    · simp only [List.map_cons, hrem]
      exact outerDFST_fuel_postorder_found succs edgeMarks
        (reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1) frame.state parentFrame.state
        parentFrame.remaining snd (List.map (fun f => (f.1.state, f.1.remaining, f.2.1)) tail)
        pathStack st cyclePath target iv₁ st₁ heq
    · unfold outerDFSTWF
      grind
  | case4 =>
    rename_i pathStack st frame marksRem hrem parentFrame snd pmarks tail ancestors innerVisited
      fst st' hr ih1
    have hiv : ∀ x, innerVisited.contains x → Reachable initialStates succs x := by
      simp [innerVisited, Std.HashSet.contains_emptyWithCapacity]
    obtain ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩ :=
      innerDFS_fuel_eq_innerDFSWF succs fr parentFrame.state ancestors
        (reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1) frame.state frame.hreach innerVisited st
        hiv hfin (Nat.le_refl _)
    rw [hr] at heqC
    simp only [Prod.mk.injEq] at heqC
    obtain ⟨rfl, rfl, rfl⟩ := heqC
    obtain ⟨fuel2, result2, st2, heq2, hfin2, heqC2⟩ := ih1 (fun f hf => hmarks f (List.mem_cons_of_mem _ hf)) hfin1
    simp only [List.map_cons] at heq2
    let m := max (reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1) fuel2
    have heqm : innerDFS_fuel succs parentFrame.state ancestors m frame.state innerVisited st =
        some (none, iv₁, st₁) := by
      rw [show m = (reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1) +
          (m - (reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1)) by simp only [m]; omega]
      exact innerDFS_fuel_add_preserves succs parentFrame.state ancestors _
        (reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1) frame.state innerVisited st none iv₁ st₁ heq
    have heq2m : outerDFST_fuel succs edgeMarks m
        ((parentFrame.state, parentFrame.remaining, snd) ::
          List.map (fun f => (f.1.state, f.1.remaining, f.2.1)) tail) ancestors st₁ =
        some (result2, st2) := by
      rw [show m = fuel2 + (m - fuel2) by simp only [m]; omega]
      exact outerDFST_fuel_add_preserves succs edgeMarks _ fuel2 _ ancestors st₁ result2 st2 heq2
    refine ⟨m + 1, result2, st2, ?_, hfin2, ?_⟩
    · simp only [List.map_cons, hrem]
      exact (outerDFST_fuel_postorder_not_found succs edgeMarks m frame.state parentFrame.state
        parentFrame.remaining snd (List.map (fun f => (f.1.state, f.1.remaining, f.2.1)) tail)
        pathStack st iv₁ st₁ heqm).trans heq2m
    · unfold outerDFSTWF
      grind
  | case5 =>
    rename_i pathStack st frame marked marksRem hrem parentFrame snd pmarks tail hmk ih1
    have hmk' : marked = false := by simpa using hmk
    obtain ⟨fuel2, result2, st2, heq2, hfin2, heqC2⟩ :=
      ih1 (fun f hf => hmarks f (List.mem_cons_of_mem _ hf)) hfin
    refine ⟨fuel2 + 1, result2, st2, ?_, hfin2, ?_⟩
    · simp only [List.map_cons, hrem, hmk']
      exact outerDFST_fuel_postorder_skip_unmarked succs edgeMarks fuel2 frame.state
        parentFrame.state parentFrame.remaining snd
        (List.map (fun f => (f.1.state, f.1.remaining, f.2.1)) tail) pathStack st ▸ heq2
    · unfold outerDFSTWF
      grind
  | case6 =>
    rename_i pathStack st frame marked marksRem rest succ remainingTail hrem hmemrem hmemsuccs
      marksHead _edgeMarked hb hm
    have hbase : marksRem = edgeMarks frame.state succ :: remainingTail.map (edgeMarks frame.state) := by
      have h := hmarks (frame, marked, marksRem) List.mem_cons_self
      simpa only [hrem, List.map_cons] using h
    have hmh : marksHead = edgeMarks frame.state succ := by simp [marksHead, hbase]
    refine ⟨1, .nonEmpty (pathStack.takeWhile (fun y => !(y == succ)) ++ [succ])
      (succ :: pathStack.dropWhile (fun y => !(y == succ))), st, ?_, hfin, ?_⟩
    · simp only [List.map_cons, hrem]
      exact outerDFST_fuel_back_edge_marked succs edgeMarks 0 frame.state succ remainingTail
        marked (List.map (fun f => (f.1.state, f.1.remaining, f.2.1)) rest) pathStack st
        (by simpa using hb) (by simpa [_edgeMarked, hmh] using hm)
    · unfold outerDFSTWF
      grind
  | case7 =>
    rename_i pathStack st frame marked marksRem rest succ remainingTail hrem hmemrem hmemsuccs
      marksHead marksTail stack' _edgeMarked hb hm ih1
    have hbase : marksRem = edgeMarks frame.state succ :: remainingTail.map (edgeMarks frame.state) := by
      have h := hmarks (frame, marked, marksRem) List.mem_cons_self
      simpa only [hrem, List.map_cons] using h
    have hmh : marksHead = edgeMarks frame.state succ := by simp [marksHead, hbase]
    have hmt : marksTail = remainingTail.map (edgeMarks frame.state) := by simp [marksTail, hbase]
    have hmarks' : ∀ f ∈ stack', f.2.2 = f.1.remaining.map (edgeMarks f.1.state) := by
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · simpa [RFrame.consumeOne] using hmt
      · exact hmarks f (List.mem_cons_of_mem _ hf)
    have hb' : succ ∈ pathStack := by simpa using hb
    have hm' : (edgeMarks frame.state succ).contains 0 = false := by simpa [_edgeMarked, hmh] using hm
    obtain ⟨fuel2, result2, st2, heq2, hfin2, heqC2⟩ := ih1 hmarks' hfin
    simp only [stack', RFrame.consumeOne, List.map_cons] at heq2
    refine ⟨fuel2 + 1, result2, st2, ?_, hfin2, ?_⟩
    · simp only [List.map_cons, hrem]
      exact outerDFST_fuel_back_edge_skip succs edgeMarks fuel2 frame.state succ remainingTail
        marked (List.map (fun f => (f.1.state, f.1.remaining, f.2.1)) rest) pathStack st hb' hm' ▸ heq2
    · unfold outerDFSTWF
      grind
  | case8 =>
    rename_i pathStack st frame marked marksRem rest succ remainingTail hrem hmemrem hmemsuccs
      marksHead _edgeMarked hnb hvis hm innerVisited cyclePath target fst st' hr
    have hbase : marksRem = edgeMarks frame.state succ :: remainingTail.map (edgeMarks frame.state) := by
      have h := hmarks (frame, marked, marksRem) List.mem_cons_self
      simpa only [hrem, List.map_cons] using h
    have hmh : marksHead = edgeMarks frame.state succ := by simp [marksHead, hbase]
    have hnb' : succ ∉ pathStack := by simpa using hnb
    have hvis' : st.outerVisited.contains succ = true := hvis
    have hm' : (edgeMarks frame.state succ).contains 0 = true := by simpa [_edgeMarked, hmh] using hm
    have hiv : ∀ x, innerVisited.contains x → Reachable initialStates succs x := by
      simp [innerVisited, Std.HashSet.contains_emptyWithCapacity]
    obtain ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩ :=
      innerDFS_fuel_eq_innerDFSWF succs fr frame.state pathStack
        (reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1) succ (Reachable.step frame.hreach hmemsuccs)
        innerVisited st hiv hfin (Nat.le_refl _)
    rw [hr] at heqC
    simp only [Prod.mk.injEq] at heqC
    obtain ⟨rfl, rfl, rfl⟩ := heqC
    refine ⟨reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1 + 1,
      .nonEmpty pathStack (frame.state :: frame.state :: cyclePath ++
        (pathStack.dropWhile (fun y => !(y == target))).dropLast), st₁, ?_, hfin1, ?_⟩
    · simp only [List.map_cons, hrem]
      exact outerDFST_fuel_forward_found succs edgeMarks
        (reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1) frame.state succ remainingTail marked
        (List.map (fun f => (f.1.state, f.1.remaining, f.2.1)) rest) pathStack st hnb' hvis' hm'
        cyclePath target iv₁ st₁ heq
    · unfold outerDFSTWF
      grind
  | case9 =>
    rename_i pathStack st frame marked marksRem rest succ remainingTail hrem hmemrem hmemsuccs
      marksHead marksTail stack' _edgeMarked hnb hvis hm innerVisited fst st' hr ih1
    have hbase : marksRem = edgeMarks frame.state succ :: remainingTail.map (edgeMarks frame.state) := by
      have h := hmarks (frame, marked, marksRem) List.mem_cons_self
      simpa only [hrem, List.map_cons] using h
    have hmh : marksHead = edgeMarks frame.state succ := by simp [marksHead, hbase]
    have hmt : marksTail = remainingTail.map (edgeMarks frame.state) := by simp [marksTail, hbase]
    have hmarks' : ∀ f ∈ stack', f.2.2 = f.1.remaining.map (edgeMarks f.1.state) := by
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · simpa [RFrame.consumeOne] using hmt
      · exact hmarks f (List.mem_cons_of_mem _ hf)
    have hnb' : succ ∉ pathStack := by simpa using hnb
    have hvis' : st.outerVisited.contains succ = true := hvis
    have hm' : (edgeMarks frame.state succ).contains 0 = true := by simpa [_edgeMarked, hmh] using hm
    have hiv : ∀ x, innerVisited.contains x → Reachable initialStates succs x := by
      simp [innerVisited, Std.HashSet.contains_emptyWithCapacity]
    obtain ⟨result, iv₁, st₁, heq, hiv1, hfin1, heqC⟩ :=
      innerDFS_fuel_eq_innerDFSWF succs fr frame.state pathStack
        (reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1) succ (Reachable.step frame.hreach hmemsuccs)
        innerVisited st hiv hfin (Nat.le_refl _)
    rw [hr] at heqC
    simp only [Prod.mk.injEq] at heqC
    obtain ⟨rfl, rfl, rfl⟩ := heqC
    obtain ⟨fuel2, result2, st2, heq2, hfin2, heqC2⟩ := ih1 hmarks' hfin1
    simp only [stack', RFrame.consumeOne, List.map_cons] at heq2
    let m := max (reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1) fuel2
    have heqm : innerDFS_fuel succs frame.state pathStack m succ innerVisited st =
        some (none, iv₁, st₁) := by
      rw [show m = (reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1) +
          (m - (reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1)) by simp only [m]; omega]
      exact innerDFS_fuel_add_preserves succs frame.state pathStack _
        (reachCount initialStates succs (fun x => innerVisited.contains x = false) + 1) succ innerVisited st none iv₁ st₁ heq
    have heq2m : outerDFST_fuel succs edgeMarks m
        ((frame.state, remainingTail, marked) ::
          List.map (fun f => (f.1.state, f.1.remaining, f.2.1)) rest) pathStack st₁ =
        some (result2, st2) := by
      rw [show m = fuel2 + (m - fuel2) by simp only [m]; omega]
      exact outerDFST_fuel_add_preserves succs edgeMarks _ fuel2 _ pathStack st₁ result2 st2 heq2
    refine ⟨m + 1, result2, st2, ?_, hfin2, ?_⟩
    · simp only [List.map_cons, hrem]
      exact (outerDFST_fuel_forward_not_found succs edgeMarks m frame.state succ remainingTail
        marked (List.map (fun f => (f.1.state, f.1.remaining, f.2.1)) rest) pathStack st hnb' hvis'
        hm' iv₁ st₁ heqm).trans heq2m
    · unfold outerDFSTWF
      grind
  | case10 =>
    rename_i pathStack st frame marked marksRem rest succ remainingTail hrem hmemrem hmemsuccs
      marksHead marksTail stack' _edgeMarked hnb hvis hm ih1
    have hbase : marksRem = edgeMarks frame.state succ :: remainingTail.map (edgeMarks frame.state) := by
      have h := hmarks (frame, marked, marksRem) List.mem_cons_self
      simpa only [hrem, List.map_cons] using h
    have hmh : marksHead = edgeMarks frame.state succ := by simp [marksHead, hbase]
    have hmt : marksTail = remainingTail.map (edgeMarks frame.state) := by simp [marksTail, hbase]
    have hmarks' : ∀ f ∈ stack', f.2.2 = f.1.remaining.map (edgeMarks f.1.state) := by
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · simpa [RFrame.consumeOne] using hmt
      · exact hmarks f (List.mem_cons_of_mem _ hf)
    have hnb' : succ ∉ pathStack := by simpa using hnb
    have hvis' : st.outerVisited.contains succ = true := hvis
    have hm' : (edgeMarks frame.state succ).contains 0 = false := by simpa [_edgeMarked, hmh] using hm
    obtain ⟨fuel2, result2, st2, heq2, hfin2, heqC2⟩ := ih1 hmarks' hfin
    simp only [stack', RFrame.consumeOne, List.map_cons] at heq2
    refine ⟨fuel2 + 1, result2, st2, ?_, hfin2, ?_⟩
    · simp only [List.map_cons, hrem]
      exact outerDFST_fuel_forward_skip succs edgeMarks fuel2 frame.state succ remainingTail
        marked (List.map (fun f => (f.1.state, f.1.remaining, f.2.1)) rest) pathStack st hnb' hvis'
        hm' ▸ heq2
    · unfold outerDFSTWF
      grind
  | case11 =>
    rename_i pathStack st frame marked marksRem rest succ remainingTail hrem hmemrem hmemsuccs
      marksHead marksTail stack' _edgeMarked hnb hvis st2 ih1
    have hbase : marksRem = edgeMarks frame.state succ :: remainingTail.map (edgeMarks frame.state) := by
      have h := hmarks (frame, marked, marksRem) List.mem_cons_self
      simpa only [hrem, List.map_cons] using h
    have hmh : marksHead = edgeMarks frame.state succ := by simp [marksHead, hbase]
    have hmt : marksTail = remainingTail.map (edgeMarks frame.state) := by simp [marksTail, hbase]
    have hmarks' : ∀ f ∈ stack', f.2.2 = f.1.remaining.map (edgeMarks f.1.state) := by
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · simpa [RFrame.consumeOne] using hmt
      · exact hmarks f (List.mem_cons_of_mem _ hf)
    have hnb' : succ ∉ pathStack := by simpa using hnb
    have hvis' : st.outerVisited.contains succ = false := by simpa using hvis
    have hfin2' : ∀ x, st2.innerFinished.contains x → Reachable initialStates succs x := by
      simp only [st2]; exact hfin
    have hmarksPush : ∀ f ∈ (frame.push succ hmemsuccs, _edgeMarked, (expand succ).2.1.toList) :: stack',
        f.2.2 = f.1.remaining.map (edgeMarks f.1.state) := by
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · simpa [RFrame.push] using expand_snd_toList succs edgeMarks expand hexp succ
      · exact hmarks' f hf
    obtain ⟨fuel2, result2, st2', heq2, hfin2, heqC2⟩ := ih1 hmarksPush hfin2'
    simp only [stack', st2, _edgeMarked, hmh, RFrame.push, RFrame.consumeOne, List.map_cons] at heq2
    refine ⟨fuel2 + 1, result2, st2', ?_, hfin2, ?_⟩
    · simp only [List.map_cons, hrem]
      exact outerDFST_fuel_push succs edgeMarks fuel2 frame.state succ remainingTail marked
        (List.map (fun f => (f.1.state, f.1.remaining, f.2.1)) rest) pathStack st hnb' hvis' ▸ heq2
    · unfold outerDFSTWF
      grind

end OuterFuelBridge

/-! ## Top-level `nestedDFST`, well-founded -/

section TopLevelWF

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

/-- Well-founded top-level edge-aware nested DFS emptiness check. -/
@[expose] def nestedDFSTWF [LawfulHashable State] (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) (initialStates : List State)
    (fr : FiniteReach initialStates succs) : EmptinessResult State :=
  let st : FNDFSState State := {
    outerVisited := Std.HashSet.emptyWithCapacity 1024
    innerFinished := Std.HashSet.emptyWithCapacity 1024
  }
  nestedDFSTWF.go succs edgeMarks expand initialStates fr initialStates (List.suffix_refl _) st
where
  go [LawfulHashable State] (succs : State → Array State)
      (edgeMarks : State → State → Std.HashSet Nat)
      (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat) (initialStates : List State)
      (fr : FiniteReach initialStates succs)
      (remaining : List State) (hsub : remaining <:+ initialStates) (st : FNDFSState State) :
      EmptinessResult State :=
    match remaining with
    | [] => .empty st.outerVisited.size
    | init :: rest =>
      if st.outerVisited.contains init then
        go succs edgeMarks expand initialStates fr rest ((List.suffix_cons init rest).trans hsub) st
      else
        let st := { st with outerVisited := st.outerVisited.insert init }
        have hinit_reach : Reachable initialStates succs init :=
          .base (hsub.mem List.mem_cons_self)
        let succsList := (succs init).toList
        match outerDFSTWF succs edgeMarks expand fr
            [({ state := init, hreach := hinit_reach, remaining := succsList,
                hsuffix := List.suffix_refl _ }, false, (expand init).2.1.toList)]
            [init] st with
        | (.nonEmpty stem loop, _) => .nonEmpty stem loop
        | (.empty _, st') =>
          go succs edgeMarks expand initialStates fr rest ((List.suffix_cons init rest).trans hsub) st'

end TopLevelWF

/-! ## Fuel ↔ well-founded bridge, top level -/

section TopLevelFuelBridge

variable {State : Type u} [BEq State] [Hashable State] [LawfulBEq State]

theorem nestedDFST_fuel_go_nil (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (st : FNDFSState State) (fuel : Nat) :
    nestedDFST_fuel.go succs edgeMarks [] st (fuel + 1) = some (.empty st.outerVisited.size) := by
  unfold nestedDFST_fuel.go
  rfl

theorem nestedDFST_fuel_go_skip (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (init : State) (rest : List State)
    (st : FNDFSState State) (fuel : Nat) (hvis : st.outerVisited.contains init = true) :
    nestedDFST_fuel.go succs edgeMarks (init :: rest) st (fuel + 1) =
      nestedDFST_fuel.go succs edgeMarks rest st fuel := by
  conv => lhs; rw [nestedDFST_fuel.go.eq_def]
  simp [hvis]

theorem nestedDFST_fuel_go_none (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (init : State) (rest : List State)
    (st : FNDFSState State) (fuel : Nat) (hvis : st.outerVisited.contains init = false)
    (houter : outerDFST_fuel succs edgeMarks fuel [(init, (succs init).toList, false)] [init]
        { st with outerVisited := st.outerVisited.insert init } = none) :
    nestedDFST_fuel.go succs edgeMarks (init :: rest) st (fuel + 1) = none := by
  unfold nestedDFST_fuel.go
  simp [hvis, houter]

theorem nestedDFST_fuel_go_nonEmpty (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (init : State) (rest : List State)
    (st : FNDFSState State) (fuel : Nat) (hvis : st.outerVisited.contains init = false)
    (stem loop : List State) (st'' : FNDFSState State)
    (houter : outerDFST_fuel succs edgeMarks fuel [(init, (succs init).toList, false)] [init]
        { st with outerVisited := st.outerVisited.insert init } = some (.nonEmpty stem loop, st'')) :
    nestedDFST_fuel.go succs edgeMarks (init :: rest) st (fuel + 1) = some (.nonEmpty stem loop) := by
  unfold nestedDFST_fuel.go
  simp [hvis, houter]

theorem nestedDFST_fuel_go_continue (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (init : State) (rest : List State)
    (st : FNDFSState State) (fuel : Nat) (hvis : st.outerVisited.contains init = false)
    (m : Nat) (st' : FNDFSState State)
    (houter : outerDFST_fuel succs edgeMarks fuel [(init, (succs init).toList, false)] [init]
        { st with outerVisited := st.outerVisited.insert init } = some (.empty m, st')) :
    nestedDFST_fuel.go succs edgeMarks (init :: rest) st (fuel + 1) =
      nestedDFST_fuel.go succs edgeMarks rest st' fuel := by
  conv => lhs; rw [nestedDFST_fuel.go.eq_def]
  simp [hvis, houter]

/-- Fuel-increase preserves a successful `nestedDFST_fuel.go` result. -/
theorem nestedDFST_fuel_go_add_preserves (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat) (extra fuel : Nat) (remaining : List State)
    (st : FNDFSState State) (result : EmptinessResult State)
    (h : nestedDFST_fuel.go succs edgeMarks remaining st fuel = some result) :
    nestedDFST_fuel.go succs edgeMarks remaining st (fuel + extra) = some result := by
  induction fuel generalizing remaining st result with
  | zero => simp [nestedDFST_fuel.go.eq_def] at h
  | succ n ih =>
    rw [show n + 1 + extra = (n + extra) + 1 by omega]
    match remaining with
    | [] =>
      rw [nestedDFST_fuel_go_nil] at h
      rw [nestedDFST_fuel_go_nil]
      exact h
    | init :: rest =>
      by_cases hvis : st.outerVisited.contains init = true
      · rw [nestedDFST_fuel_go_skip succs edgeMarks init rest st n hvis] at h
        rw [nestedDFST_fuel_go_skip succs edgeMarks init rest st (n + extra) hvis]
        exact ih rest st result h
      · simp only [Bool.not_eq_true] at hvis
        cases houter : outerDFST_fuel succs edgeMarks n [(init, (succs init).toList, false)] [init]
            { st with outerVisited := st.outerVisited.insert init } with
        | none =>
          rw [nestedDFST_fuel_go_none succs edgeMarks init rest st n hvis houter] at h
          exact absurd h (by simp)
        | some val =>
          obtain ⟨res, st'⟩ := val
          cases res with
          | nonEmpty stem loop =>
            rw [nestedDFST_fuel_go_nonEmpty succs edgeMarks init rest st n hvis stem loop st'
                houter] at h
            rw [nestedDFST_fuel_go_nonEmpty succs edgeMarks init rest st (n + extra) hvis stem loop
                st'
                (outerDFST_fuel_add_preserves succs edgeMarks extra n
                  [(init, (succs init).toList, false)] [init]
                  { st with outerVisited := st.outerVisited.insert init }
                  (.nonEmpty stem loop) st' houter)]
            exact h
          | empty m =>
            rw [nestedDFST_fuel_go_continue succs edgeMarks init rest st n hvis m st' houter] at h
            rw [nestedDFST_fuel_go_continue succs edgeMarks init rest st (n + extra) hvis m st'
                (outerDFST_fuel_add_preserves succs edgeMarks extra n
                  [(init, (succs init).toList, false)] [init]
                  { st with outerVisited := st.outerVisited.insert init }
                  (.empty m) st' houter)]
            exact ih rest st' result h

variable {initialStates : List State} [LawfulHashable State] (succs : State → Array State)
  (fr : FiniteReach initialStates succs) (edgeMarks : State → State → Std.HashSet Nat)
  (expand : State → Array State × Array (Std.HashSet Nat) × Array Nat)

/-- For a suitable `remaining` and `st`, some fuel makes `nestedDFST_fuel.go` succeed and agree with `nestedDFSTWF.go`. -/
theorem nestedDFST_fuel_go_eq_nestedDFSTWF_go
    (hexp : ExpandCoherent succs edgeMarks expand)
    (remaining : List State) (hsub : remaining <:+ initialStates) (st : FNDFSState State)
    (hfin : ∀ x, st.innerFinished.contains x → Reachable initialStates succs x) :
    ∃ fuel result, nestedDFST_fuel.go succs edgeMarks remaining st fuel = some result ∧
      result = nestedDFSTWF.go succs edgeMarks expand initialStates fr remaining hsub st := by
  induction remaining generalizing st with
  | nil =>
    refine ⟨1, .empty st.outerVisited.size, nestedDFST_fuel_go_nil succs edgeMarks st 0, ?_⟩
    unfold nestedDFSTWF.go
    rfl
  | cons init rest ih =>
    have hinit_reach : Reachable initialStates succs init := .base (hsub.mem List.mem_cons_self)
    have hsub_rest : rest <:+ initialStates := (List.suffix_cons init rest).trans hsub
    by_cases hvis : st.outerVisited.contains init = true
    · obtain ⟨fuel2, result2, heq2, heqC2⟩ := ih hsub_rest st hfin
      refine ⟨fuel2 + 1, result2, ?_, ?_⟩
      · rw [nestedDFST_fuel_go_skip succs edgeMarks init rest st fuel2 hvis]
        exact heq2
      · unfold nestedDFSTWF.go
        simp only [hvis]
        exact heqC2
    · simp only [Bool.not_eq_true] at hvis
      let st2 := { st with outerVisited := st.outerVisited.insert init }
      have hfin2 : ∀ x, st2.innerFinished.contains x → Reachable initialStates succs x := hfin
      obtain ⟨fuelI, resultI, stI, heqI, hfinI, heqCI⟩ :=
        outerDFST_fuel_eq_outerDFSTWF succs fr edgeMarks expand hexp
          [({ state := init, hreach := hinit_reach, remaining := (succs init).toList,
              hsuffix := List.suffix_refl _ }, false, (expand init).2.1.toList)]
          (by
            intro f hf
            simp only [List.mem_singleton] at hf
            subst hf
            simpa using expand_snd_toList succs edgeMarks expand hexp init)
          [init] st2 hfin2
      simp only [List.map] at heqI
      cases resultI with
      | nonEmpty stem loop =>
        refine ⟨fuelI + 1, .nonEmpty stem loop, ?_, ?_⟩
        · exact nestedDFST_fuel_go_nonEmpty succs edgeMarks init rest st fuelI hvis stem loop stI
            heqI
        · unfold nestedDFSTWF.go
          have heqCI' : (EmptinessResult.nonEmpty stem loop, stI) =
              outerDFSTWF succs edgeMarks expand fr
                [({ state := init, hreach := hinit_reach, remaining := (succs init).toList,
                    hsuffix := List.suffix_refl _ }, false, (expand init).2.1.toList)]
                [init] { st with outerVisited := st.outerVisited.insert init } := by
            simpa only [st2] using heqCI
          rw [if_neg (by simp [hvis])]
          show EmptinessResult.nonEmpty stem loop =
              match outerDFSTWF succs edgeMarks expand fr
                  [({ state := init, hreach := hinit_reach, remaining := (succs init).toList,
                      hsuffix := List.suffix_refl _ }, false, (expand init).2.1.toList)]
                  [init] { st with outerVisited := st.outerVisited.insert init } with
              | (EmptinessResult.nonEmpty stem loop, _) => EmptinessResult.nonEmpty stem loop
              | (EmptinessResult.empty _, st') =>
                nestedDFSTWF.go succs edgeMarks expand initialStates fr rest hsub_rest st'
          rw [← heqCI']
      | empty m =>
        obtain ⟨fuelR, resultR, heqR, heqCR⟩ := ih hsub_rest stI hfinI
        have heqI' : outerDFST_fuel succs edgeMarks (max fuelI fuelR)
            [(init, (succs init).toList, false)] [init] st2 = some (.empty m, stI) := by
          rw [show max fuelI fuelR = fuelI + (max fuelI fuelR - fuelI) by omega]
          exact outerDFST_fuel_add_preserves succs edgeMarks _ fuelI
            [(init, (succs init).toList, false)] [init] st2 (.empty m) stI heqI
        have heqR' : nestedDFST_fuel.go succs edgeMarks rest stI (max fuelI fuelR) =
            some resultR := by
          rw [show max fuelI fuelR = fuelR + (max fuelI fuelR - fuelR) by omega]
          exact nestedDFST_fuel_go_add_preserves succs edgeMarks _ fuelR rest stI resultR heqR
        refine ⟨max fuelI fuelR + 1, resultR, ?_, ?_⟩
        · rw [nestedDFST_fuel_go_continue succs edgeMarks init rest st (max fuelI fuelR) hvis m stI
              heqI']
          exact heqR'
        · unfold nestedDFSTWF.go
          simp only [hvis, st2] at heqCI ⊢
          rw [← heqCI]
          exact heqCR

/-- Some fuel makes `nestedDFST_fuel` succeed and agree with `nestedDFSTWF`. -/
theorem nestedDFST_fuel_eq_nestedDFSTWF (hexp : ExpandCoherent succs edgeMarks expand) :
    ∃ fuel, nestedDFST_fuel initialStates succs edgeMarks fuel =
      some (nestedDFSTWF succs edgeMarks expand initialStates fr) := by
  unfold nestedDFST_fuel nestedDFSTWF
  obtain ⟨fuel, result, heq, heqC⟩ :=
    nestedDFST_fuel_go_eq_nestedDFSTWF_go succs fr edgeMarks expand hexp initialStates
      (List.suffix_refl _)
      { outerVisited := Std.HashSet.emptyWithCapacity 1024
        innerFinished := Std.HashSet.emptyWithCapacity 1024 }
      (fun x hx => absurd hx (by simp [Std.HashSet.contains_emptyWithCapacity]))
  exact ⟨fuel, heqC ▸ heq⟩

/-- If `nestedDFSTWF` returns `.empty`, no `TAcceptingCycle` with one mark exists. -/
theorem nestedDFSTWF_empty_no_cycle (hexp : ExpandCoherent succs edgeMarks expand)
    (n : Nat) (h : nestedDFSTWF succs edgeMarks expand initialStates fr = .empty n) :
    ¬∃ _ac : TAcceptingCycle initialStates succs edgeMarks 1, True := by
  obtain ⟨fuel, heq⟩ := nestedDFST_fuel_eq_nestedDFSTWF succs fr edgeMarks expand hexp
  rw [h] at heq
  exact nestedDFST_fuel_empty_no_cycle heq

/-- If `nestedDFSTWF` returns `.nonEmpty stem loop`, then `(stem, loop.tail)` is a `TAcceptingCycle` with one mark. -/
theorem nestedDFSTWF_nonEmpty_valid (hexp : ExpandCoherent succs edgeMarks expand)
    (stem loop : List State)
    (h : nestedDFSTWF succs edgeMarks expand initialStates fr = .nonEmpty stem loop) :
    ∃ ac : TAcceptingCycle initialStates succs edgeMarks 1,
      ac.stem = stem ∧ ac.cycle = loop.tail := by
  obtain ⟨fuel, heq⟩ := nestedDFST_fuel_eq_nestedDFSTWF succs fr edgeMarks expand hexp
  rw [h] at heq
  exact nestedDFST_fuel_nonEmpty_valid heq

end TopLevelFuelBridge

end Lasso
