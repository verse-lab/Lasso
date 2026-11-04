module

/-
  Reconstructed from the current FairRouter/StreettSCCRegion contracts, not recovered from history.

  One state has an a-only and a b-only self-loop. FG a and FG b are separately feasible, but no run
  satisfies both: beyond both eventual cutoffs every step would have to read a and b together.
  The unchecked prune tests options separately and can report a spurious witness here. This records
  its documented StateOnly boundary, the crossing route remains the correctness oracle.

  Controls add an a-and-b edge, remove an individually required region, or move both atoms to the state.
-/
import LTLLib.Fairness.FairRouter
import LTLLibTests.TestUtil
meta import LTLLib.Fairness.FairRouter
meta import LTLLibTests.TestUtil

namespace LTLLib.Tests.PruneJointRegions

open LTLLib LTLLib.Tests

def splitSteps (_ : Nat) : Array (LStep String Nat) := #[({"a"}, 0), ({"b"}, 0)]
def noLabel (_ : Nat) : Std.HashSet String := ∅

/-- Supply the split directly so preprocessing cannot merge away the two independent conjuncts. -/
def regions : List (List (NNF.FairDisjunct String)) :=
  [[(.prop "a", [])], [(.prop "b", [])]]

def joint (letter : Std.HashSet String) : Bool := letter.contains "a" && letter.contains "b"

/-- No actual step can witness the conjunction, despite their identical endpoints. -/
theorem no_joint_step (s : Nat) (st : LStep String Nat) (h : st ∈ splitSteps s) :
    joint (LSys.letter (noLabel s) st.1) = false := by
  simp [splitSteps] at h
  rcases h with rfl | rfl <;> simp [joint, noLabel, LSys.letter]

/-- The hypothesis needed by the prune's nonempty correctness theorem really fails on this model. -/
theorem not_stateOnly : ¬ LSys.StateOnly splitSteps noLabel (BoolFormula.prop "a").eval := by
  intro h
  have bad := h 0 (({"a"} : Std.HashSet String), 0)
    (LSys.mem_totalize_of_mem (by simp [splitSteps]))
  simp [BoolFormula.eval, noLabel, LSys.letter] at bad

def bothSteps (s : Nat) : Array (LStep String Nat) := (splitSteps s).push ({"a", "b"}, 0)
def stateSteps : Nat → Array (LStep String Nat) := LSys.unlabelled (fun _ => #[0])
def stateLabel (_ : Nat) : Std.HashSet String := {"a", "b"}

/-- Within the supported state-labelled fragment both regions satisfy the premise. -/
theorem regions_stateOnly : ∀ ds ∈ regions, ∀ d ∈ ds,
    LSys.StateOnly stateSteps stateLabel d.1.eval :=
  fun _ _ d _ => LSys.stateOnly_of_unlabelled (fun _ => #[0]) stateLabel d.1.eval

/-- A cycle with an actual joint-labelled realization at every step, the stem need not be in-region. -/
def jointLasso (succs : Nat → Array (LStep String Nat)) (label : Nat → Std.HashSet String)
    (stem cycle : List Nat) : Bool :=
  stem.head? == some 0 && pathRespectsEdges (LSys.targets succs) stem &&
    cycleRespectsEdges (LSys.targets succs) cycle && stem.getLast? == cycle.head? &&
    (cyclicPairs cycle).all (fun (s, t) =>
      (succs s).any fun st => st.2 == t && joint (LSys.letter (label s) st.1))

def crossWitness (succs : Nat → Array (LStep String Nat)) (label : Nat → Std.HashSet String) :
    EmptinessResult ((Nat × Nat) × Bool) → Bool
  | .empty _ => false
  | .nonEmpty stem loop => jointLasso succs label (stem.map (·.1.1)) (loop.tail.map (·.1.1))

def pruneWitness (succs : Nat → Array (LStep String Nat)) (label : Nat → Std.HashSet String) :
    EmptinessResult (Nat × Nat) → Bool
  | .empty _ => false
  | .nonEmpty stem loop => jointLasso succs label (stem.map (·.1)) (loop.tail.map (·.1))

def report : IO Unit :=
  verdict "separate regions do not imply a joint edge realization" do
    let separate ← [splitSteps, fun s => (splitSteps s).reverse].mapM fun succs => do
      let a ← check "FG a alone is feasible"
        (!isEmptyResult (modelCheckTGBADisjunct (.ff : Formula String) (.prop "a") [] [0] succs noLabel))
      let b ← check "FG b alone is feasible"
        (!isEmptyResult (modelCheckTGBADisjunct (.ff : Formula String) (.prop "b") [] [0] succs noLabel))
      let c ← check "crossing rejects FG a and FG b together"
        (isEmptyResult (modelCheckCrossSplit (.ff : Formula String) regions [0] succs noLabel))
      let noJointRun : Formula String := .not (.and
        (.eventually (.always (.atom "a"))) (.eventually (.always (.atom "b"))))
      let d ← check "the ordinary TGBA route also rules out every joint run"
        (isEmptyResult (modelCheckTGBA noJointRun [0] succs noLabel))
      let unchecked := modelCheckPruneSplit (.ff : Formula String) regions [0] succs noLabel
      let e ← check "outside StateOnly, the unchecked prune reports the documented spurious witness"
        (!isEmptyResult unchecked && !pruneWitness succs noLabel unchecked)
      return [a, b, c, d, e]
    let positive ← [(bothSteps, noLabel), (stateSteps, stateLabel)].mapM fun (succs, label) => do
      let cross := modelCheckCrossSplit (.ff : Formula String) regions [0] succs label
      let prune := modelCheckPruneSplit (.ff : Formula String) regions [0] succs label
      let a ← check "a real joint realization makes crossing and prune nonempty"
        (!isEmptyResult cross && !isEmptyResult prune)
      let b ← check "the crossing witness has a real joint-labelled cycle" (crossWitness succs label cross)
      let c ← check "the prune witness has a real joint-labelled cycle" (pruneWitness succs label prune)
      return [a, b, c]
    let missing : Nat → Array (LStep String Nat) := fun _ => #[({"a"}, 0)]
    let negative ← check "when even FG b is impossible, both routes reject"
      (isEmptyResult (modelCheckCrossSplit (.ff : Formula String) regions [0] missing noLabel) &&
        isEmptyResult (modelCheckPruneSplit (.ff : Formula String) regions [0] missing noLabel))
    return separate.flatten ++ positive.flatten ++ [negative]

#eval report

end LTLLib.Tests.PruneJointRegions
