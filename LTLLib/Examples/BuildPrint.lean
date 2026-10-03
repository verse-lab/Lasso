module

/-
  Reusable "build and print" pipeline for the examples: given a surface `Formula α`, compile it to NNF, run it
  through `createGraph → constructGBA`, and render the tableau, the GBA, and both ways of resolving the GBA's
  generalized acceptance, `GBA.degeneralize` into a `BA` and `GBA.toTGBA` onto transitions.

  The two are worth seeing side by side: degeneralization multiplies the state space by the number of
  acceptance sets, whereas `toTGBA` is a pure edge relabeling and leaves the states alone.
-/
public import LTLLib

public section

namespace LTLLib.Examples

variable {α : Type u} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
  [DecidableEq α] [ToString α]

abbrev S (α : Type u) [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] :=
  Std.HashSet (NNF α)

def buildAll (φNNF : NNF α) :
    Option (ExpandState α (S α) × GBA α × BA α × TGBA α) :=
  match createGraph (S := S α) φNNF with
  | some st =>
    let gba := constructGBA φNNF st
    some (st, gba, gba.degeneralize, gba.toTGBA)
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

/-- Render one transition: its target, propositional guard, and acceptance marks. -/
def showTransition (t : TGBA.Transition α) : String :=
  let pos := (t.positiveProps.toList.map toString).mergeSort (· < ·)
  let neg := (t.negativeProps.toList.map toString).mergeSort (· < ·)
  s!"-> {t.target}  +{pos} -{neg}  marks={t.acceptMarks.toList.mergeSort (· < ·)}"

/-- Render a `TGBA`. Unlike a `GBA` or `BA` there is no separate labeling or acceptance table, both live on
the transitions, so the label and marks are printed inline with each edge. Rows out of state `0` are the
`expandInit` sentinel's, which is why it is not in `states`, the same as `printGBA` shows. -/
def printTGBA (tgba : TGBA α) : String :=
  let stateLine := s!"states ({tgba.states.size}): {tgba.states.toList.mergeSort (· < ·)}"
  let initLine := s!"initial: {tgba.initialStates.toList.mergeSort (· < ·)}"
  let markLine := s!"acceptance marks: {tgba.numAcceptSets}"
  let transLines := (tgba.successors.toList.flatMap fun (q, ts) =>
    ts.toList.map fun t => s!"  {q} {showTransition t}").mergeSort (· < ·)
  String.intercalate "\n" ([stateLine, initLine, markLine, "transitions:"] ++ transLines)

/-- The `edgeMarks q q'` view the SCC-based emptiness checks actually consume: marks unioned over every
parallel `q → q'` transition. Only the marked pairs are listed. -/
def printEdgeMarks (tgba : TGBA α) : String :=
  let pairs := tgba.states.toList.flatMap fun q =>
    (tgba.succStates q).toList.map fun q' => (q, q')
  let lines := (pairs.eraseDups.filterMap fun (q, q') =>
    let ms := (tgba.edgeMarks q q').toList.mergeSort (· < ·)
    if ms.isEmpty then none else some s!"  {q} -> {q'}: {ms}").mergeSort (· < ·)
  String.intercalate "\n" (["marked edges:"] ++ (if lines.isEmpty then ["  (none)"] else lines))

/-- Compile `φ` to NNF, build the tableau/GBA/BA/TGBA, and print all of it. -/
def runExample (φ : Formula α) : IO Unit := do
  let φNNF := φ.toNNF true
  match buildAll φNNF with
  | some (st, gba, ba, tgba) =>
    IO.println s!"φ = {φ}"
    IO.println s!"φ (NNF) = {φNNF}"
    IO.println "\n== Tableau (createGraph) =="
    IO.println (printTableau st)
    IO.println "\n== GBA (before degeneralization) =="
    IO.println (printGBA gba)
    IO.println "\n== BA (after degeneralization) =="
    IO.println (printBA ba)
    IO.println "\n== TGBA (marks pushed onto transitions) =="
    IO.println (printTGBA tgba)
    IO.println (printEdgeMarks tgba)
  | none => IO.println "createGraph failed (unexpected: createGraph_term guarantees success)"

/-- Just the TGBA half, for examples that do not need the tableau or the degeneralized `BA`. -/
def runTGBAExample (φ : Formula α) : IO Unit := do
  let φNNF := φ.toNNF true
  match buildAll φNNF with
  | some (_, _, _, tgba) =>
    IO.println s!"φ = {φ}"
    IO.println s!"φ (NNF) = {φNNF}"
    IO.println (printTGBA tgba)
    IO.println (printEdgeMarks tgba)
  | none => IO.println "createGraph failed (unexpected: createGraph_term guarantees success)"

end LTLLib.Examples
