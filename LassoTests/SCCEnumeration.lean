module

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
import Lasso.SCC.SCCEnumeration
import Lasso.SCC.StreettPrune
import Lasso.SCC.TarjanSCC

namespace Lasso.Tests.SCCEnumerationTest

open Lasso

variable {State : Type u} {L : Type w} [BEq State] [Hashable State]
  [LawfulBEq State] [LawfulHashable State] [Inhabited State]

/-! ## Status -/

example (cs : CompiledSpec State L) (curRegions : Nat) (aux) (q : State) :
    (streettOps cs curRegions).getStatus aux q =
      liveStatusOf ((streettView cs curRegions).liveIndex aux) ((streettView cs curRegions).dead aux) q := rfl

example (numMarks : Nat) (aux : TarjanAux State) (q : State) :
    (tarjanOps numMarks).getStatus aux q =
      liveStatusOf ((tarjanView numMarks).liveIndex aux) ((tarjanView numMarks).dead aux) q := rfl

/-! ## PUSH -/

example (cs : CompiledSpec State L) (curRegions : Nat) (aux) (q : State) (m) :
    (streettView cs curRegions).live ((streettOps cs curRegions).push aux q m).1 =
      ((streettView cs curRegions).live aux).push q := rfl

example (cs : CompiledSpec State L) (curRegions : Nat) (aux) (q : State) (m) :
    (streettView cs curRegions).posNat ((streettOps cs curRegions).push aux q m).2 =
      ((streettView cs curRegions).live aux).size := rfl

example (cs : CompiledSpec State L) (curRegions : Nat) (aux) (q : State) (m) :
    (streettView cs curRegions).lowlinks ((streettOps cs curRegions).push aux q m).1 =
      ((streettView cs curRegions).lowlinks aux).push ((streettView cs curRegions).live aux).size := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  simp [streettView, streettOps, streettPush]

example (numMarks : Nat) (aux : TarjanAux State) (q : State) (m) :
    (tarjanView numMarks).lowlinks ((tarjanOps numMarks).push aux q m).1 =
      ((tarjanView numMarks).lowlinks aux).push ((tarjanView numMarks).live aux).size := by
  simp [tarjanView, tarjanOps, tarjanPush]

/-! ## UPDATE -/

example (cs : CompiledSpec State L) (curRegions : Nat) (aux) (m) (d : State) (ll)
    (h : ((streettView cs curRegions).lowlinks aux).back? = some ll) :
    (streettView cs curRegions).lowlinks ((streettOps cs curRegions).update aux m d).1 =
      ((streettView cs curRegions).lowlinks aux).pop.push
        (min ll (((streettView cs curRegions).liveIndex aux).getD d 0)) := by
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
example (cs : CompiledSpec State L) (curRegions : Nat) (aux) (m) (d : State)
    (h : ((streettView cs curRegions).lowlinks aux).back? = none) :
    (streettView cs curRegions).lowlinks ((streettOps cs curRegions).update aux m d).1 =
      (streettView cs curRegions).lowlinks aux := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  simp only [streettView, Array.back?_map, Option.map_eq_none_iff] at h
  simp [streettView, streettOps, streettUpdate, h]

/-! ## POP -/

example (cs : CompiledSpec State L) (curRegions : Nat) (succs edgeMarks) (aux) (step)
    (h : (streettView cs curRegions).closes aux step) :
    (streettView cs curRegions).lowlinks ((streettOps cs curRegions).pop succs edgeMarks aux step).1 =
      ((streettView cs curRegions).lowlinks aux).pop := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  simp only [LowlinkView.closes, streettView, Array.back?_map, beq_iff_eq,
    Option.map_eq_some_iff] at h
  obtain ⟨⟨ll, acc⟩, hb, hll⟩ := h
  have hll' : ll = step.pos := by simpa using hll
  subst hll'
  grind [streettPop, Array.map_pop, streettView, streettOps]

-- A closing SCC is flushed whether discarded, accepted, or queued for pruning.
example (cs : CompiledSpec State L) (curRegions : Nat) (succs edgeMarks) (aux) (step)
    (h : (streettView cs curRegions).closes aux step) :
    ((streettView cs curRegions).live ((streettOps cs curRegions).pop succs edgeMarks aux step).1,
        (streettView cs curRegions).liveIndex ((streettOps cs curRegions).pop succs edgeMarks aux step).1,
        (streettView cs curRegions).dead ((streettOps cs curRegions).pop succs edgeMarks aux step).1) =
      liveFlush ((streettView cs curRegions).live aux) ((streettView cs curRegions).liveIndex aux)
        ((streettView cs curRegions).dead aux) ((streettView cs curRegions).posNat step.pos) := by
  obtain ⟨live, liveIndex, dead, dstack, wit, wopts, pending⟩ := aux
  simp only [LowlinkView.closes, streettView, Array.back?_map, beq_iff_eq,
    Option.map_eq_some_iff] at h
  obtain ⟨⟨ll, acc⟩, hb, hll⟩ := h
  have hll' : ll = step.pos := by simpa using hll
  by_cases hacc : acc != fullAccMask cs.numMarks
  · simp only [streettView, streettOps, streettPop, hb, if_pos hll', if_pos hacc]; rfl
  · rcases hfu : firstUnsatisfied cs curRegions (scanFrame cs succs live step.pos).1
        (scanFrame cs succs live step.pos).2 with _ | opts
    · simp only [streettView, streettOps, streettPop, hb, if_pos hll', if_neg hacc, hfu]; rfl
    · simp only [streettView, streettOps, streettPop, hb, if_pos hll', if_neg hacc, hfu]; rfl

-- The merging POP, both branches. With no parent frame the closing lowlink is dropped rather than folded.
example (cs : CompiledSpec State L) (curRegions : Nat) (succs edgeMarks) (aux) (step) (ll)
    (hclose : (streettView cs curRegions).closes aux step = false)
    (hb : ((streettView cs curRegions).lowlinks aux).back? = some ll) :
    (streettView cs curRegions).lowlinks ((streettOps cs curRegions).pop succs edgeMarks aux step).1 =
      match ((streettView cs curRegions).lowlinks aux).pop.back? with
      | none => ((streettView cs curRegions).lowlinks aux).pop
      | some pll => ((streettView cs curRegions).lowlinks aux).pop.pop.push (min pll ll) := by
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
example (cs : CompiledSpec State L) (curRegions : Nat) :
    (streettView cs curRegions).live (streettOps cs curRegions).initAux = #[] ∧
      (∀ s, s ∉ (streettView cs curRegions).dead (streettOps cs curRegions).initAux) ∧
      (streettView cs curRegions).lowlinks (streettOps cs curRegions).initAux = #[] ∧
      (∀ q, (streettOps cs curRegions).getStatus (streettOps cs curRegions).initAux q = .unknown) :=
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

end Lasso.Tests.SCCEnumerationTest
