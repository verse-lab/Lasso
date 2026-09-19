/-
  Edge-aware nested DFS, the executable algorithm with fuel. Acceptance lives on edges (the single mark 0 after
  degeneralization), so the CVWY/Schwoon-Esparza algorithm is retargeted at marked tree edges. When a stack frame's
  incoming tree edge is marked, the inner DFS starts at that state and searches back for the edge's source,
  and the back-edge shortcut fires on the traversed edge's own mark.

  The inner DFS (`innerDFS_fuel`, `FNDFSState`) is reused from `NestedDFS/NestedDFSCorrectness.lean`, with the seed
  being the marked edge's source and the start state its target.

  Defines:
  - `outerDFST_fuel`: the edge-aware outer DFS
  - `nestedDFST_fuel`: the edge-aware nested DFS over all initial states

  Sections:
  - Fuel-based outer DFS, edge-aware
-/
import LTLLib.NestedDFS.NestedDFSCorrectness

namespace LTLLib

/-! ## Fuel-based outer DFS, edge-aware -/

/-- Edge-aware outer DFS loop with fuel. Each stack frame also records whether its incoming tree edge carries mark 0. -/
def outerDFST_fuel {State} [BEq State] [Hashable State] [LawfulBEq State]
    (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
    (fuel : Nat)
    (stack : List (State × List State × Bool))
    (pathStack : List State)
    (st : FNDFSState State)
    : Option (EmptinessResult State × FNDFSState State) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match stack with
    | [] => some (.empty st.outerVisited.size, st)
    | (current, remaining, marked) :: rest =>
      match remaining with
      | [] =>
        match marked, rest with
        | true, (parent, _, _) :: _ =>
          -- The tree edge `parent → current` is marked, so search from `current` for `parent` or any ancestor above it
          -- (Holzmann-Peled-Yannakakis), excluding `current` itself so a self-loop on `current` does not count.
          let ancestors := pathStack.dropLast
          let innerVisited := Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)
          match innerDFS_fuel succs parent ancestors fuel current innerVisited st with
          | none => none
          | some (some (cyclePath, target), _, st') =>
            -- `parent` twice, once as the cycle's first element so the marked edge `parent → current` lies in `loop.tail`,
            -- and once more so `loop.tail` returns to it.
            let loopTail := (pathStack.dropWhile (fun y => !(y == target))).dropLast.dropLast
            some (.nonEmpty ancestors (parent :: parent :: cyclePath ++ loopTail), st')
          | some (none, _, st') =>
            outerDFST_fuel succs edgeMarks fuel rest ancestors st'
        | _, _ =>
          outerDFST_fuel succs edgeMarks fuel rest pathStack.dropLast st
      | succ :: remainingTail =>
        let stack' := (current, remainingTail, marked) :: rest
        let edgeMarked := (edgeMarks current succ).contains 0
        if pathStack.contains succ then
          -- Back-edge shortcut, fired by the edge's own mark
          if edgeMarked then
            let stem := pathStack.takeWhile (fun y => !(y == succ)) ++ [succ]
            let loop := succ :: pathStack.dropWhile (fun y => !(y == succ))
            some (.nonEmpty stem loop, st)
          else
            outerDFST_fuel succs edgeMarks fuel stack' pathStack st
        else if st.outerVisited.contains succ then
          -- Forward or cross edge to a finished `succ`, whose postorder launch only covered its own tree edge,
          -- so a marked edge is searched from `succ` right away.
          if edgeMarked then
            let innerVisited := Std.HashSet.emptyWithCapacity (st.outerVisited.size / 2)
            match innerDFS_fuel succs current pathStack fuel succ innerVisited st with
            | none => none
            | some (some (cyclePath, target), _, st') =>
              -- `current` twice as in the postorder branch, since `cyclePath` starts at `succ`.
              let loopTail := (pathStack.dropWhile (fun y => !(y == target))).dropLast
              some (.nonEmpty pathStack (current :: current :: cyclePath ++ loopTail), st')
            | some (none, _, st') =>
              outerDFST_fuel succs edgeMarks fuel stack' pathStack st'
          else
            outerDFST_fuel succs edgeMarks fuel stack' pathStack st
        else
          let st := { st with outerVisited := st.outerVisited.insert succ }
          let succChildren := (succs succ).toList
          let stack'' := (succ, succChildren, edgeMarked) :: stack'
          outerDFST_fuel succs edgeMarks fuel stack'' (pathStack ++ [succ]) st

/-- Edge-aware nested DFS with fuel over all initial states. Root frames have no incoming tree edge, so they start unmarked. -/
def nestedDFST_fuel {State} [BEq State] [Hashable State] [LawfulBEq State]
    (initialStates : List State)
    (succs : State → Array State)
    (edgeMarks : State → State → Std.HashSet Nat)
    (fuel : Nat)
    : Option (EmptinessResult State) :=
  let st : FNDFSState State := {
    outerVisited := Std.HashSet.emptyWithCapacity 1024
    innerFinished := Std.HashSet.emptyWithCapacity 1024
  }
  nestedDFST_fuel.go succs edgeMarks initialStates st fuel
where
  go (succs : State → Array State) (edgeMarks : State → State → Std.HashSet Nat)
      (remaining : List State) (st : FNDFSState State) (fuel : Nat)
      : Option (EmptinessResult State) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match remaining with
      | [] => some (.empty st.outerVisited.size)
      | init :: rest =>
        if st.outerVisited.contains init then
          go succs edgeMarks rest st fuel
        else
          let st := { st with outerVisited := st.outerVisited.insert init }
          let succsList := (succs init).toList
          match outerDFST_fuel succs edgeMarks fuel [(init, succsList, false)] [init] st with
          | none => none
          | some (.nonEmpty stem loop, _) => some (.nonEmpty stem loop)
          | some (.empty _, st') => go succs edgeMarks rest st' fuel

end LTLLib
