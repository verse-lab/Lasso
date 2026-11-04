module

/-
  Tests `modelCheckFairRoutedOfStep`, the default entry point that chooses between the prune and the crossing
  from a predicate marking the atoms a *step* may contribute.

  `tk` is an edge atom: it is read by steps, never by a state's label. Two assumptions put it in different
  places of the hoisted split:
  - `□◇tk → ◇g` hoists `□◇tk` to the region `⊤` with `tk` as a *mark*, so no region mentions an edge atom
    and the prune keeps the property. This is the shape per-action strong and weak fairness take when
    written as an assumption, so the common case pays nothing.
  - `◇□tk → ◇g` hoists `◇□tk` to the *region* `tk`, which a source state cannot decide — two parallel steps
    out of one state disagree on it — so the route falls back to the crossing, which latches the region into
    the product instead (`EdgeLabels.md` §12.4, §12.6).

  Two systems: `trap`, where a `tk` self-loop at a `¬g` state gives both assumptions a counterexample, and
  `plain`, where `tk` is read once so neither assumption is satisfiable and `◇g` holds vacuously. Every
  routed verdict is checked against the crossing, which is the correctness oracle here
  (`PruneJointRegions.lean`): agreement on the prune-routed cases is the real assertion, since the prune is
  the route whose witness contract the decision discharges.

  A system with no edge atoms passes `fun _ => false`, and both assumptions then keep the prune.
-/
import LTLLib.ModelCheck
import LTLLibTests.TestUtil
meta import LTLLib.ModelCheck
meta import LTLLibTests.TestUtil

namespace LTLLib.Tests.FairRouted

open LTLLib LTLLib.Tests

/-! ## Two systems over one labelling

State `1` is the only one labelled `g`. `tk` is contributed by steps alone, so it is an edge atom and
`isTk` is the classification a front end supplies. -/

def label : Nat → Std.HashSet String
  | 1 => {"g"}
  | _ => ∅

/-- `0 →{tk} 2`, `2 →{tk} 2`, `0 → 1`, `1 → 1`. The `tk` self-loop at `2` never reaches `g`. -/
def trapSteps : Nat → Array (LStep String Nat)
  | 0 => #[({"tk"}, 2), (∅, 1)]
  | 1 => #[(∅, 1)]
  | _ => #[({"tk"}, 2)]

/-- The same without the `tk` loop: `tk` is read on the single step `0 →{tk} 2`, and `2` then stalls. -/
def plainSteps : Nat → Array (LStep String Nat)
  | 0 => #[({"tk"}, 2), (∅, 1)]
  | 1 => #[(∅, 1)]
  | _ => #[(∅, 2)]

def trap : LSys.StepFn String Nat := fun s => (trapSteps s, label s)
def plain : LSys.StepFn String Nat := fun s => (plainSteps s, label s)

def init : List Nat := [0]

/-- The classification: `tk` is the only atom a step contributes. -/
def isTk (a : String) : Bool := a == "tk"

/-! ## Two assumptions over the edge atom -/

/-- `□◇tk → ◇g`: the edge atom becomes a mark, the region is `⊤`. -/
def gfTkImpliesG : Formula String :=
  .implies (.always (.eventually (.atom "tk"))) (.eventually (.atom "g"))

/-- `◇□tk → ◇g`: the edge atom becomes the region. -/
def fgTkImpliesG : Formula String :=
  .implies (.eventually (.always (.atom "tk"))) (.eventually (.atom "g"))

/-- The crossing, with the latch projected away so the two routes are comparable. -/
def crossing (sys : LSys.StepFn String Nat) (φ : Formula String) : EmptinessResult (Nat × Nat) :=
  (modelCheckFairFNFCrossOfStep φ init sys).map Prod.fst

def routed (sys : LSys.StepFn String Nat) (φ : Formula String) : EmptinessResult (Nat × Nat) :=
  modelCheckFairRoutedOfStep φ init sys isTk

/-! ## The certificate is owed only on the fallback branch

`modelCheckFairRoutedOfStep_nonEmpty_sat` takes finiteness as a consequence of `pruneApplicable … = false`,
so a prune-routed property's witness needs none. The theorem below is that fact, checked by the
elaborator: it produces a run from a `.nonEmpty` answer with no `FiniteReach` in sight. -/

/-- Every letter `trapSteps` offers is `{tk}` or empty, so `tk` is the only atom a step contributes. -/
theorem letters_trap {s : Nat} {st : LStep String Nat} (h : st ∈ trapSteps s) :
    ∀ a ∈ st.1, a = "tk" := by
  match s with
  | 0 => simp only [trapSteps] at h; simp at h; rcases h with rfl | rfl <;> simp
  | 1 => simp only [trapSteps] at h; simp at h; subst h; simp
  | (_ + 2) => simp only [trapSteps] at h; simp at h; subst h; simp

/-- `tk` really is the only atom a step of `trap` contributes, which is `hsteps`. -/
theorem steps_isTk : ∀ s, ∀ st ∈ LSys.totalize (fun s => (trap s).1) s, ∀ a ∈ st.1, isTk a = true := by
  intro s st hst a ha
  rcases LSys.mem_totalize.mp hst with h
  split at h
  · -- the totalizing self-loop carries the empty letter, so there is nothing to classify
    rw [h] at ha; simp at ha
  · simpa [isTk] using letters_trap (s := s) (by simpa [trap] using h) a ha

/-- Completeness on a prune-routed property, with **no** finiteness certificate: the route fact alone
discharges the hypothesis. `report` establishes `pruneApplicable isTk gfTkImpliesG` computationally. -/
theorem nonEmpty_sat_without_finiteReach
    (hprune : pruneApplicable isTk gfTkImpliesG = true)
    {stem loop : List (Nat × Nat)}
    (h : modelCheckFairRoutedOfStep gfTkImpliesG init trap isTk = .nonEmpty stem loop) :
    ∃ ρ : Nat → LSys.Edge String Nat,
      (LSys.toSpec (fun s => (trap s).1) init (fun s => (trap s).2)).isRun ρ ∧
      ¬ Formula.directSatisfies (LSys.valuation (fun s => (trap s).2) ρ) gfTkImpliesG ∧
      (∀ n, (lassoAt stem loop.tail n).map Prod.fst = some (ρ n).1) :=
  modelCheckFairRoutedOfStep_nonEmpty_sat gfTkImpliesG init trap isTk steps_isTk
    (fun hfalse => absurd hfalse (by rw [hprune]; decide)) h

def report : IO Unit :=
  verdict "the default route chooses the prune or the crossing from the edge-atom classification" do
    -- The decision, which is syntactic and does not run a search.
    let a ← check "□◇tk → ◇g keeps the prune: the edge atom is a mark, not a region"
      (pruneApplicable isTk gfTkImpliesG)
    let b ← check "◇□tk → ◇g falls back: the hoisted ◇□ region mentions the edge atom"
      (! pruneApplicable isTk fgTkImpliesG)
    let c ← check "with no edge atoms declared, both keep the prune"
      (pruneApplicable (fun _ => false) gfTkImpliesG &&
        pruneApplicable (fun _ => false) fgTkImpliesG)
    -- The verdicts. `trap`'s tk self-loop at a ¬g state violates both assumptions' conclusion.
    let d ← check "□◇tk → ◇g fails on the trap, found through the prune"
      (! isEmptyResult (routed trap gfTkImpliesG))
    let e ← check "◇□tk → ◇g fails on the trap, found through the crossing"
      (! isEmptyResult (routed trap fgTkImpliesG))
    -- `plain` reads tk once, so neither assumption is satisfiable and ◇g holds vacuously.
    let f ← check "□◇tk → ◇g holds on the plain system, through the prune"
      (isEmptyResult (routed plain gfTkImpliesG))
    let g ← check "◇□tk → ◇g holds on the plain system, through the crossing"
      (isEmptyResult (routed plain fgTkImpliesG))
    -- Agreement with the oracle. On the two prune-routed cases this is the assertion that the
    -- decision was sound; on the other two the routed call *is* the crossing.
    let agrees (nm : String) (sys : LSys.StepFn String Nat) (φ : Formula String) : IO Bool :=
      check nm (isEmptyResult (routed sys φ) == isEmptyResult (crossing sys φ))
    let h ← agrees "prune and crossing agree: □◇tk → ◇g on the trap" trap gfTkImpliesG
    let i ← agrees "prune and crossing agree: □◇tk → ◇g on the plain system" plain gfTkImpliesG
    let j ← agrees "the fallback agrees with the crossing: ◇□tk → ◇g on the trap" trap fgTkImpliesG
    let k ← agrees "the fallback agrees with the crossing: ◇□tk → ◇g on the plain system"
      plain fgTkImpliesG
    -- The routed witness reports in the prune's product, latch dropped, on either branch.
    let witnessShape (r : EmptinessResult (Nat × Nat)) : Bool :=
      match r with
      | .empty _ => false
      | .nonEmpty stem loop => stem.head? == some (0, 0) && ! loop.isEmpty
    let l ← check "the prune branch reports a lasso from the initial product state"
      (witnessShape (routed trap gfTkImpliesG))
    let m ← check "the crossing branch reports one too, with the region latch projected away"
      (witnessShape (routed trap fgTkImpliesG))
    return [a, b, c, d, e, f, g, h, i, j, k, l, m]

#eval report

end LTLLib.Tests.FairRouted
