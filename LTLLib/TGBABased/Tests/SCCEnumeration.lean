/-
  Proof-level tests, checked at elaboration time, that the flush-enumeration interface `LowlinkView` fits both
  refinements that instantiate it. UPDATE and the merging POP rewrite the innermost lowlink only when the frame stack
  has an entry to rewrite, so those two laws are guarded on `back?`, and the cases below pin both sides of the guard.

  Sections:
  - Status
  - PUSH
  - UPDATE
  - POP
  - Initial state
-/
import LTLLib.TGBABased.SCC.SCCEnumeration
import LTLLib.TGBABased.SCC.StreettPrune
import LTLLib.TGBABased.SCC.TarjanSCC

namespace LTLLib.Tests.SCCEnumerationTest

open LTLLib

variable {State : Type u} {L : Type w} [BEq State] [Hashable State]
  [LawfulBEq State] [LawfulHashable State] [Inhabited State]

/-! ## Status -/

example (cs : CompiledSpec State L) (aux) (q : State) :
    (streettOps cs).getStatus aux q =
      liveStatusOf ((streettView cs).liveIndex aux) ((streettView cs).dead aux) q := rfl

example (numMarks : Nat) (aux : TarjanAux State) (q : State) :
    (tarjanOps numMarks).getStatus aux q =
      liveStatusOf ((tarjanView numMarks).liveIndex aux) ((tarjanView numMarks).dead aux) q := rfl

/-! ## PUSH -/

example (cs : CompiledSpec State L) (aux) (q : State) (m) :
    (streettView cs).live ((streettOps cs).push aux q m).1 = ((streettView cs).live aux).push q := rfl

example (cs : CompiledSpec State L) (aux) (q : State) (m) :
    (streettView cs).posNat ((streettOps cs).push aux q m).2 = ((streettView cs).live aux).size := rfl

example (cs : CompiledSpec State L) (aux) (q : State) (m) :
    (streettView cs).lowlinks ((streettOps cs).push aux q m).1 =
      ((streettView cs).lowlinks aux).push ((streettView cs).live aux).size := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  simp [streettView, streettOps, streettPush]

example (numMarks : Nat) (aux : TarjanAux State) (q : State) (m) :
    (tarjanView numMarks).lowlinks ((tarjanOps numMarks).push aux q m).1 =
      ((tarjanView numMarks).lowlinks aux).push ((tarjanView numMarks).live aux).size := by
  simp [tarjanView, tarjanOps, tarjanPush]

/-! ## UPDATE -/

example (cs : CompiledSpec State L) (aux) (m) (d : State) (ll)
    (h : ((streettView cs).lowlinks aux).back? = some ll) :
    (streettView cs).lowlinks ((streettOps cs).update aux m d).1 =
      ((streettView cs).lowlinks aux).pop.push
        (min ll (((streettView cs).liveIndex aux).getD d 0)) := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  simp only [streettView, Array.back?_map, Option.map_eq_some_iff] at h
  obtain ⟨⟨ll', acc⟩, hb, rfl⟩ := h
  simp [streettView, streettOps, streettUpdate, hb, Array.map_pop]

example (numMarks : Nat) (aux : TarjanAux State) (m) (d : State) (ll)
    (h : ((tarjanView numMarks).lowlinks aux).back? = some ll) :
    (tarjanView numMarks).lowlinks ((tarjanOps numMarks).update aux m d).1 =
      ((tarjanView numMarks).lowlinks aux).pop.push
        (min ll (((tarjanView numMarks).liveIndex aux).getD d 0)) := by
  simp only [tarjanView, Array.back?_map, Option.map_eq_some_iff] at h
  obtain ⟨⟨ll', acc⟩, hb, rfl⟩ := h
  simp [tarjanView, tarjanOps, tarjanUpdate, hb, Array.map_pop]

-- An empty frame stack is the case the guard exists for, both refinements leaving the state untouched.
example (cs : CompiledSpec State L) (aux) (m) (d : State)
    (h : ((streettView cs).lowlinks aux).back? = none) :
    (streettView cs).lowlinks ((streettOps cs).update aux m d).1 = (streettView cs).lowlinks aux := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  simp only [streettView, Array.back?_map, Option.map_eq_none_iff] at h
  simp [streettView, streettOps, streettUpdate, h]

/-! ## POP -/

example (cs : CompiledSpec State L) (succs edgeMarks) (aux) (step)
    (h : (streettView cs).closes aux step) :
    (streettView cs).lowlinks ((streettOps cs).pop succs edgeMarks aux step).1 =
      ((streettView cs).lowlinks aux).pop := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  simp only [LowlinkView.closes, streettView, Array.back?_map, beq_iff_eq,
    Option.map_eq_some_iff] at h
  obtain ⟨⟨ll, acc⟩, hb, hll⟩ := h
  have hll' : ll = step.pos := by simpa using hll
  subst hll'
  grind [streettPop, Array.map_pop, streettView, streettOps]

-- The triple is flushed at the closing position, whichever of POP's six branches ran.
example (cs : CompiledSpec State L) (succs edgeMarks) (aux) (step)
    (h : (streettView cs).closes aux step) :
    ((streettView cs).live ((streettOps cs).pop succs edgeMarks aux step).1,
        (streettView cs).liveIndex ((streettOps cs).pop succs edgeMarks aux step).1,
        (streettView cs).dead ((streettOps cs).pop succs edgeMarks aux step).1) =
      liveFlush ((streettView cs).live aux) ((streettView cs).liveIndex aux)
        ((streettView cs).dead aux) ((streettView cs).posNat step.pos) := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  simp only [LowlinkView.closes, streettView, Array.back?_map, beq_iff_eq,
    Option.map_eq_some_iff] at h
  obtain ⟨⟨ll, acc⟩, hb, hll⟩ := h
  have hll' : ll = step.pos := by simpa using hll
  by_cases hacc : acc != fullAccMask cs.numMarks
  · simp only [streettView, streettOps, streettPop, hb, if_pos hll', if_pos hacc]; rfl
  · rcases hfu : firstUnsatisfied cs (scanOptions cs live step.pos).1
        (scanOptions cs live step.pos).2 with _ | opts
    · simp only [streettView, streettOps, streettPop, hb, if_pos hll', if_neg hacc, hfu]; rfl
    · simp only [streettView, streettOps, streettPop, hb, if_pos hll', if_neg hacc, hfu]; rfl

-- The merging POP, both branches. With no parent frame the closing lowlink is dropped rather than folded.
example (cs : CompiledSpec State L) (succs edgeMarks) (aux) (step) (ll)
    (hclose : (streettView cs).closes aux step = false)
    (hb : ((streettView cs).lowlinks aux).back? = some ll) :
    (streettView cs).lowlinks ((streettOps cs).pop succs edgeMarks aux step).1 =
      match ((streettView cs).lowlinks aux).pop.back? with
      | none => ((streettView cs).lowlinks aux).pop
      | some pll => ((streettView cs).lowlinks aux).pop.pop.push (min pll ll) := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  simp only [streettView, Array.back?_map, Option.map_eq_some_iff] at hb
  obtain ⟨⟨ll', acc⟩, hbk, hll⟩ := hb
  simp only at hll
  subst hll
  have hne : ll' ≠ step.pos := by
    intro hEq
    simp only [LowlinkView.closes, streettView, Array.back?_map, hbk, hEq] at hclose
    simp at hclose
  have hmb : ((dstack.map (·.1)).pop).back? = Option.map (·.1) (dstack.pop.back?) := by
    rw [← Array.map_pop, Array.back?_map]
  rcases hb2 : dstack.pop.back? with _ | ⟨pll, pacc⟩
  · simp only [streettView, streettOps, streettPop, hbk, if_neg hne, hb2, hmb,
      Option.map_none, Array.map_pop]
  · simp only [streettView, streettOps, streettPop, hbk, if_neg hne, hb2, hmb,
      Option.map_some, Array.map_pop, Array.map_push]

/-! ## Initial state -/

-- `init_status` is what makes every state start `.unknown`, so it is pinned at both.
example (cs : CompiledSpec State L) :
    (streettView cs).live (streettOps cs).initAux = #[] ∧
      (∀ s, s ∉ (streettView cs).dead (streettOps cs).initAux) ∧
      (streettView cs).lowlinks (streettOps cs).initAux = #[] ∧
      (∀ q, (streettOps cs).getStatus (streettOps cs).initAux q = .unknown) :=
  ⟨rfl, by simp [streettView, streettOps, streettInitAux],
   by simp [streettView, streettOps, streettInitAux],
   by simp [streettOps, streettGetStatus, liveStatusOf, streettInitAux]⟩

example (numMarks : Nat) :
    (tarjanView numMarks).live (tarjanOps numMarks (State := State)).initAux = #[] ∧
      (∀ s, s ∉ (tarjanView numMarks).dead (tarjanOps numMarks (State := State)).initAux) ∧
      (tarjanView numMarks).lowlinks (tarjanOps numMarks (State := State)).initAux = #[] ∧
      (∀ q, (tarjanOps numMarks).getStatus (tarjanOps numMarks (State := State)).initAux q = .unknown) :=
  ⟨rfl, by simp [tarjanView, tarjanOps, tarjanInitAux],
   by simp [tarjanView, tarjanOps, tarjanInitAux],
   by simp [tarjanOps, tarjanGetStatus, tarjanInitAux]⟩

end LTLLib.Tests.SCCEnumerationTest
