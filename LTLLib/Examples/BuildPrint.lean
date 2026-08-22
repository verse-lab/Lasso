/-
  Reusable "build and print" pipeline for the examples: given a
  surface `Formula α`, compiles it to NNF, runs it through
  `createGraph → constructGBA → GBA.degeneralize`, and renders the tableau,
  the GBA, and the degeneralized BA.
-/
import LTLLib

namespace LTLLib.Examples

variable {α : Type u} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
  [DecidableEq α] [ToString α]

abbrev S (α : Type u) [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] :=
  Std.HashSet (NNF α)

def buildAll (φNNF : NNF α) :
    Option (ExpandState α (S α) × GBA α × BA α) :=
  match createGraph (S := S α) φNNF with
  | some st =>
    let gba := constructGBA φNNF st
    some (st, gba, gba.degeneralize)
  | none => none

/-- Render the tableau: each finished node's name, predecessors (`incoming`),
and the formulas decided to hold at that node (`old`) / pushed to its
successor (`next`). -/
def printTableau (st : ExpandState α (S α)) : String :=
  let nodeLines := (st.nodes.toList.map fun (name, node) =>
    s!"  node {name}: incoming={node.incoming.toList} old={node.old.toList} \
next={node.next.toList}").mergeSort (· < ·)
  String.intercalate "\n" ([s!"tableau nodes ({st.nodes.size}):"] ++ nodeLines)

/-- Render a `GBA`'s states, acceptance sets, transitions, and labeling. -/
def printGBA (gba : GBA α) : String :=
  let stateLine := s!"states ({gba.states.size}): {gba.states.toList}"
  let initLine := s!"initial: {gba.initialStates.toList}"
  let acceptLines := gba.acceptSets.toList.zipIdx.map fun (s, i) =>
    s!"  F{i} = {s.toList}"
  let transLines := (gba.successors.toList.map fun (s, succs) =>
    s!"  {s} -> {succs.toList}").mergeSort (· < ·)
  let labelLines := (gba.labeling.toList.map fun (q, (pos, neg)) =>
    s!"  {q}: +{pos.toList} -{neg.toList}").mergeSort (· < ·)
  String.intercalate "\n"
    ([ stateLine, initLine, s!"acceptance sets ({gba.acceptSets.size}):" ] ++ acceptLines
     ++ ["transitions:"] ++ transLines ++ ["labeling:"] ++ labelLines)

/-- Render a `BA`'s states, transitions, and labeling. -/
def printBA (ba : BA α) : String :=
  let stateLine := s!"states ({ba.states.size}): {ba.states.toList}"
  let initLine := s!"initial: {ba.initialStates.toList}"
  let acceptLine := s!"accepting: {ba.acceptingStates.toList}"
  let transLines := (ba.successors.toList.map fun (s, succs) =>
    s!"  {s} -> {succs.toList}").mergeSort (· < ·)
  let labelLines := (ba.labeling.toList.map fun (q, (pos, neg)) =>
    s!"  {q}: +{pos.toList} -{neg.toList}").mergeSort (· < ·)
  String.intercalate "\n"
    ([stateLine, initLine, acceptLine, "transitions:"] ++ transLines
     ++ ["labeling (by GBA state):"] ++ labelLines)

/-- Compile `φ` to NNF, build the tableau/GBA/BA, and print all of it. -/
def runExample (φ : Formula α) : IO Unit := do
  let φNNF := φ.toNNF true
  match buildAll φNNF with
  | some (st, gba, ba) =>
    IO.println s!"φ = {φ}"
    IO.println s!"φ (NNF) = {φNNF}"
    IO.println "\n== Tableau (createGraph) =="
    IO.println (printTableau st)
    IO.println "\n== GBA (before degeneralization) =="
    IO.println (printGBA gba)
    IO.println "\n== BA (after degeneralization) =="
    IO.println (printBA ba)
  | none => IO.println "createGraph failed (unexpected: createGraph_term guarantees success)"

end LTLLib.Examples
