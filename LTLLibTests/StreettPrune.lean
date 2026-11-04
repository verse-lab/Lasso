module

/-
  Differential test of `modelCheckUnderFairnessPrune` against `modelCheckUnderFairness` on generated models, crossed with
  formulas exercising strong, weak and nested fairness and a property whose own fair half hoists.

  Every counterexample of the prune must project to a real lasso of the system whose cycle satisfies every hoisted
  conjunct through one of its options, so a cycle covering the property's marks but missing the assumption's fails.
  Hand-built cases pin a verdict only reachable by recursing into a sub-SCC, and the explored count of an `.empty`
  answer, which must be the sum over every search the prune runs. A hub with `k` spokes bounds the searches when one conjunct
  has `k` options with both a region and a mark.

  Sections:
  - Generated models
  - Formulas
  - Witness validation
  - Agreement
  - Hand-built cases
  - Explored counts
  - One branch per conjunct and path
-/
import LTLLib.Fairness.FairRouter
import LTLLibTests.TestUtil
meta import LTLLib.Fairness.FairRouter
meta import LTLLibTests.TestUtil

namespace LTLLib.Tests.StreettPruneTest

open LTLLib LTLLib.Tests

abbrev S := Std.HashSet (NNF String)
abbrev St := Fin 6

private def mix (a b c : Nat) : Nat := (a * 1103515245 + b * 12345 + c * 2654435761) % 1000003

private def fin6 (n : Nat) : St := ⟨n % 6, Nat.mod_lt _ (by decide)⟩

/-! ## Generated models -/

/-- Two or three outgoing edges per state, so the models carry a mixture of trivial and nested SCCs. -/
def genSucc (seed : Nat) (s : St) : Array St :=
  #[fin6 (mix s.val seed 1), fin6 (mix s.val seed 2), fin6 (mix s.val seed 3)]

/-- Atoms `a`, `b` and `c` placed by a second hash, so a state can carry any subset of them. -/
def genLabel (seed : Nat) (s : St) : Std.HashSet String :=
  let bits := mix s.val seed 7 % 8
  (if bits % 2 == 1 then ({"a"} : Std.HashSet String) else ∅) ∪
  (if bits / 2 % 2 == 1 then ({"b"} : Std.HashSet String) else ∅) ∪
  (if bits / 4 % 2 == 1 then ({"c"} : Std.HashSet String) else ∅)

def genInit : List St := [fin6 0]

theorem genFR (seed : Nat) : FiniteReach genInit (genSucc seed) :=
  .of_forall_mem (List.finRange 6) List.mem_finRange

/-! ## Formulas -/

private def atomA : Formula String := .atom "a"
private def atomB : Formula String := .atom "b"
private def atomC : Formula String := .atom "c"
private def gf (f : Formula String) : Formula String := .always (.eventually f)
private def fg (f : Formula String) : Formula String := .eventually (.always f)

/-- One strong pair, one weak pair, one nested cycle fairness, one property whose fair half hoists, and two
without any assumption at all. -/
def formulas : List (String × Formula String) :=
  [ ("GF c", gf atomC),
    ("G a", .always atomA),
    ("(GF a -> GF b) -> GF c", .implies (.implies (gf atomA) (gf atomB)) (gf atomC)),
    ("(GF a -> GF b) -> GF a", .implies (.implies (gf atomA) (gf atomB)) (gf atomA)),
    ("(FG a -> GF b) -> GF c", .implies (.implies (fg atomA) (gf atomB)) (gf atomC)),
    ("GF(a & F b) -> GF c", .implies (gf (.and atomA (.eventually atomB))) (gf atomC)),
    ("two strong pairs -> GF c",
      .implies (.and (.implies (gf atomA) (gf atomB)) (.implies (gf atomB) (gf atomC))) (gf atomC)),
    ("(GF a -> GF b) -> (G c -> GF a)",
      .implies (.implies (gf atomA) (gf atomB)) (.implies (.always atomC) (gf atomA))) ]

def seeds : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-! ## Witness validation -/

/-- The cycle satisfies a hoisted conjunct when one of its options has its region everywhere on the cycle and
each of its marks somewhere on it, which is `FairDisjunct.holds` read on an ultimately periodic word. -/
def cycleFair (label : St → Std.HashSet String) (dss : List (List (NNF.FairDisjunct String)))
    (cyc : List St) : Bool :=
  dss.all fun ds => ds.any fun d =>
    cyc.all (fun s => d.1.eval (label s)) && d.2.all fun g => cyc.any fun s => g.eval (label s)

/-- Re-check one reported counterexample: the projection onto the system is a real lasso, and its cycle
satisfies every hoisted conjunct. -/
def validWitness (seed : Nat) (φ : Formula String) : EmptinessResult (St × Nat) → Bool
  | .empty _ => true
  | .nonEmpty stem loop =>
    let succs := genSucc seed
    let label := genLabel seed
    let sysStem := stem.map (·.1)
    let sysCyc := (loop.tail).map (·.1)
    let dss := (hoistFairness (φ.toNNF false).splitConj).1
    (match sysStem.head? with | some h => genInit.contains h | none => false) &&
    pathRespectsEdges succs sysStem &&
    cycleRespectsEdges succs sysCyc &&
    (match sysStem.getLast?, sysCyc.head? with
      | some a, some b => a == b
      | _, _ => false) &&
    cycleFair label dss sysCyc

/-! ## Agreement -/

def crossOf (seed : Nat) (φ : Formula String) : EmptinessResult ((St × Nat) × Bool) :=
  modelCheckUnderFairness φ genInit (LSys.unlabelled (genSucc seed)) (genLabel seed)

def pruneOf (seed : Nat) (φ : Formula String) : EmptinessResult (St × Nat) :=
  modelCheckUnderFairnessPrune φ genInit (LSys.unlabelled (genSucc seed)) (genLabel seed)

/-- Every generated case meets the prune counterexample theorem's region hypothesis. -/
theorem genRegions_stateOnly (seed : Nat) (φ : Formula String) :
    ∀ ds ∈ (hoistFairness (φ.toNNF false).splitConj).1, ∀ d ∈ ds,
      LSys.StateOnly (LSys.unlabelled (genSucc seed)) (genLabel seed) d.1.eval :=
  fun _ _ d _ => LSys.stateOnly_of_unlabelled (genSucc seed) (genLabel seed) d.1.eval

def cases : List (Nat × String × Formula String) :=
  seeds.flatMap fun seed => formulas.map fun (name, φ) => (seed, name, φ)

def agrees (c : Nat × String × Formula String) : Bool :=
  isEmptyResult (crossOf c.1 c.2.2) == isEmptyResult (pruneOf c.1 c.2.2)

/-- How many generated cases report a counterexample, so an agreement of "all empty" cannot pass by accident. -/
def nonEmptyCount : Nat := (cases.filter fun c => ! isEmptyResult (pruneOf c.1 c.2.2)).length

/-! ## Hand-built cases

`pruneForcing` is `s → t`, `t → s`, `t → t` with `a` only at `s` and `b` nowhere. Its one maximal SCC has `a`
without `b`, so the strong pair fails on it, and the only fair cycle is the self-loop at `t`, which is reached
by pruning to the `FG ¬a` region and searching again. -/

abbrev Two := Fin 2

def pfSucc (s : Two) : Array Two := if s == 0 then #[1] else #[0, 1]
def pfLabel (s : Two) : Std.HashSet String := if s == 0 then {"a"} else ∅
def pfInit : List Two := [0]
theorem pfFR : FiniteReach pfInit pfSucc :=
  .of_forall_mem (List.finRange 2) List.mem_finRange

def pfStrong : Formula String := .implies (gf atomA) (gf atomB)

def pfCross (φ : Formula String) : EmptinessResult ((Two × Nat) × Bool) :=
  modelCheckUnderFairness φ pfInit (LSys.unlabelled pfSucc) pfLabel

def pfPrune (φ : Formula String) : EmptinessResult (Two × Nat) :=
  modelCheckUnderFairnessPrune φ pfInit (LSys.unlabelled pfSucc) pfLabel

/-- The hand-built model also has only state labels, including after totalization. -/
theorem pfRegions_stateOnly (φ : Formula String) :
    ∀ ds ∈ (hoistFairness (φ.toNNF false).splitConj).1, ∀ d ∈ ds,
      LSys.StateOnly (LSys.unlabelled pfSucc) pfLabel d.1.eval :=
  fun _ _ d _ => LSys.stateOnly_of_unlabelled pfSucc pfLabel d.1.eval

/-! ## Explored counts

`0 → 1 → 2 → 0` with a second edge `2 → 1`, the only acceptance mark on `2 → 0`, and one conjunct whose single
option is the region "not state 0". The maximal SCC covers the mark but violates the region. The pruned search
keeps the candidate's states but removes the outgoing edges of `0`, leaving a dead end at `0` and an SCC `{1, 2}`
whose internal edges no longer carry the mark. Both searches run, so the reported count has to be their sum. -/

def accSuccs : Nat → Array Nat
  | 0 => #[1]
  | 1 => #[2]
  | _ => #[0, 1]

def accMarks (s t : Nat) : Std.HashSet Nat := if s == 2 && t == 0 then {0} else ∅

/-- A step reads its source state; restricting it removes both its successor and its marks together. -/
def accSpec : RStreettSpec Nat Nat where
  numMarks := 1
  regionSuccs := fun r s => if r s then accSuccs s else #[]
  regionMarks := fun r s t => if r s then accMarks s t else ∅
  conjuncts := #[#[{ region := fun s => s != 0, marks := #[] }]]
  regionExpand_coherent := fun _ => derivedExpand_coherent _ _

def accCompiled : CompiledSpec Nat Nat := CompiledSpec.of accSpec

/-- The count each search contributes on its own. -/
def accParts : Nat × Nat :=
  let (_, aux) := streettRun accCompiled 0 accSuccs accMarks (accSpec.regionExpand (fun _ => true)) [0]
  let top := aux.live.size + aux.dead.size
  match pruneLoop accCompiled accSpec 0 aux.pending.toList with
  | some (_, n) => (top, n)
  | none => (top, 0)

def accTotal : Nat :=
  match streettCheck accCompiled accSuccs accMarks (accSpec.regionExpand (fun _ => true)) [0] with
  | .empty n => n
  | .nonEmpty _ _ => 0

/-! ## One branch per conjunct and path

`hubSucc k` is a hub `0` with `k` spokes `1+2j ⇄ 2+2j`, each returning to the hub from `1+2j`, every state labelled by its own
number. The negated property `⋀ⱼ (GF (2+2j) → GF (1+2j))` is one conjunct with an option `FG ¬(1+2j) ∧ GF (2+2j)` per spoke.
Each branch loses its own spoke's mark, so the prune runs at most `k + 1` searches of at most `2k + 1` states. -/

def hubSucc (k : Nat) (s : Nat) : Array Nat :=
  if s == 0 then #[0] ++ (Array.range k).map (1 + 2 * ·)
  else if s % 2 == 1 then #[s + 1, 0] else #[s - 1]

def hubLabel (s : Nat) : Std.HashSet String := {toString s}

def hubProperty (k : Nat) : Formula String :=
  Formula.conj ((List.range k).map fun j =>
    .implies (gf (.atom (toString (2 + 2 * j)))) (gf (.atom (toString (1 + 2 * j)))))

def hubPrune (k : Nat) : EmptinessResult (Nat × Nat) :=
  modelCheckUnderFairnessPrune (hubProperty k) [0] (LSys.unlabelled (hubSucc k)) hubLabel

def hubExplored (k : Nat) : Nat :=
  match hubPrune k with
  | .empty n => n
  | .nonEmpty _ _ => 0

def report : IO Unit :=
  verdict "the SCC prune against the disjunct crossing" do
    let a ← check s!"{cases.length} generated cases agree on emptiness" (cases.all agrees)
    let b ← check s!"{nonEmptyCount} of them report a counterexample" (nonEmptyCount > 0)
    let c ← check "every reported counterexample is a real lasso whose cycle is fair"
      (cases.all fun c => validWitness c.1 c.2.2 (pruneOf c.1 c.2.2))
    -- only reachable by pruning the failing maximal SCC down to its fair self-loop
    let d ← check "a fair run avoiding `a` forever violates `GF a`"
      (! isEmptyResult (pfPrune (.implies pfStrong (gf atomA))))
    let e ← check "the same verdict as the crossing route"
      (isEmptyResult (pfCross (.implies pfStrong (gf atomA)))
        == isEmptyResult (pfPrune (.implies pfStrong (gf atomA))))
    let f ← check "that counterexample is a real fair lasso"
      (match pfPrune (.implies pfStrong (gf atomA)) with
        | .empty _ => false
        | .nonEmpty stem loop =>
          pathRespectsEdges pfSucc (stem.map (·.1)) &&
          cycleRespectsEdges pfSucc ((loop.tail).map (·.1)) &&
          ((loop.tail).map (·.1)).all fun s => ! (pfLabel s).contains "a")
    let g ← check "every fair run does eventually avoid `a`"
      (isEmptyResult (pfPrune (.implies pfStrong (fg (.not atomA)))))
    IO.println s!"  explored: top-level {accParts.1}, pruned runs {accParts.2}, reported {accTotal}"
    let h ← check "the pruned candidate really is searched" (accParts.2 > 0)
    let i ← check "the reported count is the sum over every search"
      (accTotal == accParts.1 + accParts.2)
    IO.println s!"  explored on the hub with 5 spokes: {hubExplored 5}"
    let j ← check "a conjunct with 5 options is branched on once per path, 6 searches of at most 11 states"
      (isEmptyResult (hubPrune 5) && hubExplored 5 ≤ 6 * 11)
    return [a, b, c, d, e, f, g, h, i, j]

#eval report

end LTLLib.Tests.StreettPruneTest
