module

/-
  A posteriori TGBA simplification, generic over how the TGBA was built. SCCs come from Tarjan's enumeration, and the
  proofs only need it to be sound (`SCCEnumerationSound`). A round runs, in order:
  - mark erasure on transitions that leave their SCC or lie inside an SCC whose internal transitions do not cover every
    mark, such a mark being used only finitely often by any accepting run (`[SB00]` §6)
  - implied-transition removal keyed on exact target equality (`[HOL4-ltl]` `REDUCE_IS_CORRECT`)
  - state merging into an earlier state with the same outgoing transitions, or the same up to marks when the merged
    state lies on no cycle (`[GO01]` §6 with `[LTL2BA-1.3]`'s SCC relaxation)
  - removal of states without transitions and of everything left unreachable from the initial states
  `simplifyTGBA` repeats rounds until the part after mark erasure changes nothing, terminating on `measureTGBA`. Removing
  terminal bad SCCs (`[SB00]` §6) needs no step of its own, mark erasure and dead-state removal cover it here.

  Defines:
  - `eraseMarks`: mark erasure over the enumerated SCCs `tgbaSCCs`
  - `dropImpliedAll`: implied-transition removal, `dropImpliedTrans` at every state
  - `mergeEquivalentStates`: state merging, redirecting merged states with `redirectTGBA`
  - `pruneDeadAndUnreachable`: removal of dead and unreachable states
  - `trueSCC`: the states mutually reachable with a state
  - `measureTGBA`: states plus transitions plus marks, with `measureTGBAFast` its executable version, proven equal
  - `reduceRound`, `simplifyTGBA`: the part of a round after mark erasure, and the loop

  Proves:
  - `eraseMarks_correct`, `dropImpliedAll_correct`, `mergeEquivalentStates_correct`, `pruneDeadAndUnreachable_correct`:
    each step preserves the accepted language, together with its `_wellFormed` and `_marks_lt`
  - `redirectTGBA_spec`: merging states into representatives whose transitions match both ways preserves the
    language, with marks allowed to differ at states every infinite path leaves for good
  - `eventually_not_transient`: an infinite path visits transient states only finitely often
  - `measureTGBA_*_le`: no step increases the measure
  - `simplifyTGBA_correct`, `simplifyTGBA_wellFormed`, `simplifyTGBA_marks_lt`: the loop preserves the language,
    well-formedness and the mark bound

  References:
  - `[SB00]` Somenzi, Bloem. Efficient Büchi Automata from LTL Formulae. CAV'00, §6.
  - `[GO01]` Gastin, Oddoux. Fast LTL to Büchi Automata Translation. CAV'01, §6.
  - `[LTL2BA-1.3]` Gastin, Oddoux. LTL2BA 1.3, `simplify_gstates`' SCC-aware state merge.
  - `[HOL4-ltl]` Jantsch, Norrish. The HOL4 formalisation behind `[JN18]`, `examples/logic/ltl`.
  - `[Tar72]` Tarjan. Depth-First Search and Linear Graph Algorithms. SIAM J. Comput. 1972.

  Sections:
  - Reachability and SCCs
  - Termination measure
  - Mark erasure
  - Mark erasure correctness
  - Implied-transition removal
  - Implied-transition removal correctness
  - State merge
  - State merge correctness
  - Dead and unreachable states
  - The fixpoint loop
  - Correctness of the simplification loop
-/
public import LTLLib.TGBA
public import LTLLib.LTLtoTGBA.Label
public import LTLLib.LTLtoTGBA.Reachability
public import LTLLib.LTLtoTGBA.VWAA
public import LTLLib.AbstractSpec.GraphPaths
public import LTLLib.AbstractSpec.EmptinessCheck
public import LTLLib.AbstractSpec.SCCTheory
public import LTLLib.SCC.TarjanSCC
public import LTLLib.Data.Nat
public import LTLLib.Data.List
meta import LTLLib.Tactic.Set
public import LTLLib.Data.FinSet

import Batteries.Data.List.Lemmas

public section

namespace LTLLib

open scoped FinSet

variable {α : Type u} [BEq α] [Hashable α]

/-! ## Reachability and SCCs -/

/-- The maximal SCCs of `tgba`'s graph, by Tarjan's algorithm. -/
def tgbaSCCs (tgba : TGBA α) : Array (Std.HashSet Nat) :=
  (tarjanSCCs tgba.succStates tgba.states.toList).toArray

/-- For every state, the indices of the enumerated sets containing it. -/
def sccIndex (sccs : Array (Std.HashSet Nat)) : Std.HashMap Nat (List Nat) :=
  (List.range sccs.size).foldl (fun m i => (sccs.getD i (Std.HashSet.emptyWithCapacity 0)).toList.foldl
    (fun m s => m.insert s (i :: m.getD s [])) m) (Std.HashMap.emptyWithCapacity 16)

/-- The union of marks over every transition with both endpoints inside `scc`. -/
def sccInternalMarks (tgba : TGBA α) (scc : Std.HashSet Nat) : Std.HashSet Nat :=
  scc.toList.foldl (fun acc q => (tgba.getSuccessors q).foldl
    (fun acc t => if scc.contains t.target then acc.union t.acceptMarks else acc) acc)
    (Std.HashSet.emptyWithCapacity 0)

/-- `scc`'s internal transitions do not, between them, carry every acceptance mark. -/
def sccIsBad (tgba : TGBA α) (scc : Std.HashSet Nat) : Bool :=
  !(List.range tgba.numAcceptSets).all fun m => (sccInternalMarks tgba scc).contains m

/-- Keep the marks of a transition from `q` to `t` iff some enumerated set containing `q` is not bad and contains `t`. -/
def keepMarks (sccs : Array (Std.HashSet Nat)) (bad : Array Bool) (idx : Std.HashMap Nat (List Nat)) (q t : Nat) :
    Bool :=
  (idx.getD q []).any fun i => !bad.getD i true && (sccs.getD i (Std.HashSet.emptyWithCapacity 0)).contains t

/-! ## Termination measure -/

/-- Folding `insert` over a list that never revisits `x` leaves `x`'s entry exactly as `m0` had it. -/
theorem getElem?_foldl_insert_of_not_mem {β γ} [BEq β] [Hashable β] [LawfulBEq β] (g : β → γ) (x : β) :
    ∀ (l : List β) (m0 : Std.HashMap β γ), x ∉ l → (l.foldl (fun m y => m.insert y (g y)) m0)[x]? = m0[x]? := by
  intro l
  induction l with
  | nil => intro m0 _; rfl
  | cons a rest ih =>
    intro m0 hx
    rw [List.mem_cons, not_or] at hx
    rw [List.foldl_cons, ih (m0.insert a (g a)) hx.2, Std.HashMap.getElem?_insert]
    simp [beq_iff_eq, Ne.symm hx.1]

/-- A map built by inserting `g q` at every element of a nodup list, in order, agrees with `g` on it. -/
theorem getElem?_foldl_insert_of_mem {β γ} [BEq β] [Hashable β] [LawfulBEq β] (g : β → γ) (x : β) :
    ∀ (l : List β), l.Nodup → x ∈ l → ∀ (m0 : Std.HashMap β γ),
      (l.foldl (fun m y => m.insert y (g y)) m0)[x]? = some (g x) := by
  intro l
  induction l with
  | nil => intro _ hx; simp at hx
  | cons a rest ih =>
    intro hl hx m0
    rw [List.nodup_cons] at hl
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with heq | hx'
    · subst heq
      rw [getElem?_foldl_insert_of_not_mem g x rest (m0.insert x (g x)) hl.1, Std.HashMap.getElem?_insert]
      simp
    · exact ih hl.2 hx' (m0.insert a (g a))

/-- An array built by conditionally pushing from a source list, in order, adds at most the source's own
weight to the starting array's. -/
theorem sum_foldl_condPush_le {β} (w : β → Nat) (p : Array β → β → Bool) :
    ∀ (l : List β) (acc0 : Array β),
      ((l.foldl (fun acc x => if p acc x then acc else acc.push x) acc0).toList.map w).sum
        ≤ (acc0.toList.map w).sum + (l.map w).sum := by
  intro l
  induction l with
  | nil => intro acc0; simp
  | cons a rest ih =>
    intro acc0
    rw [List.foldl_cons]
    by_cases h : p acc0 a = true
    · rw [if_pos h]
      have := ih acc0
      simp only [List.map_cons, List.sum_cons]
      omega
    · rw [if_neg h]
      have := ih (acc0.push a)
      rw [Array.toList_push, List.map_append, List.sum_append] at this
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this ⊢
      omega

/-- A transition weighs one plus one per acceptance mark it carries, so mark erasure strictly decreases the measure. -/
def transWeight (ts : Array (TGBA.Transition α)) : Nat :=
  (ts.toList.map fun t => 1 + t.acceptMarks.size).sum

/-- Dropping transitions can only lower the weight. -/
theorem transWeight_filter_le (p : TGBA.Transition α → Bool) (ts : Array (TGBA.Transition α)) :
    transWeight (ts.filter p) ≤ transWeight ts := by
  unfold transWeight
  rw [Array.toList_filter]
  exact List.sum_le_sum_of_sublist (List.filter_sublist.map _)

/-- Rewriting transitions without adding marks can only lower the weight. -/
theorem transWeight_map_le {f : TGBA.Transition α → TGBA.Transition α}
    (h : ∀ t, (f t).acceptMarks.size ≤ t.acceptMarks.size) (ts : Array (TGBA.Transition α)) :
    transWeight (ts.map f) ≤ transWeight ts := by
  unfold transWeight
  rw [Array.toList_map, List.map_map]
  exact List.sum_map_le_sum_map fun t _ => Nat.add_le_add_left (h t) 1

/-- Rewriting transitions without touching their marks leaves the weight alone. -/
theorem transWeight_map_marks_eq {f : TGBA.Transition α → TGBA.Transition α}
    (h : ∀ t, (f t).acceptMarks = t.acceptMarks) (ts : Array (TGBA.Transition α)) :
    transWeight (ts.map f) = transWeight ts := by
  unfold transWeight
  rw [Array.toList_map, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun t _ => by simp [h t])

/-- States plus transitions plus acceptance marks, `simplifyTGBA`'s termination measure. -/
noncomputable def measureTGBA (tgba : TGBA α) : Nat :=
  tgba.states.size + ∑ q ∈ tgba.states.toList.toFinSet, transWeight (tgba.getSuccessors q)

/-- `tgba.states.toList` has no repeats. -/
theorem states_toList_nodup (tgba : TGBA α) : tgba.states.toList.Nodup :=
  tgba.states.distinct_toList.imp fun {a b} h => by simpa [beq_iff_eq] using h

/-- Executable version of `measureTGBA`, proven equal. -/
def measureTGBAFast (tgba : TGBA α) : Nat :=
  tgba.states.fold (fun acc q => acc + transWeight (tgba.getSuccessors q)) tgba.states.size

theorem foldl_add_weight {β : Type w} (w : β → Nat) :
    ∀ (l : List β) (init : Nat), l.foldl (fun acc q => acc + w q) init = init + (l.map w).sum
  | [], init => by simp
  | a :: l, init => by rw [List.foldl_cons, foldl_add_weight w l, List.map_cons, List.sum_cons]; omega

@[csimp] theorem measureTGBA_eq_measureTGBAFast : @measureTGBA.{u} = @measureTGBAFast.{u} := by
  funext α _ _ tgba
  unfold measureTGBA measureTGBAFast
  rw [Std.HashSet.fold_eq_foldl_toList, foldl_add_weight, List.sum_toFinSet _ (states_toList_nodup tgba)]

/-! ## Mark erasure -/

/-- Mark erasure: a transition that leaves every enumerated SCC of its source, or whose enumerated SCCs are all bad, is
used by an accepting run only finitely often, so its marks can be replaced by `∅`. -/
@[expose] def eraseMarks (tgba : TGBA α) (sccs : Array (Std.HashSet Nat)) : TGBA α :=
  let bad := sccs.map (sccIsBad tgba)
  let idx := sccIndex sccs
  { tgba with
    successors := tgba.states.toList.foldl (fun m q =>
      m.insert q ((tgba.getSuccessors q).map fun t =>
        if keepMarks sccs bad idx q t.target then t else { t with acceptMarks := Std.HashSet.emptyWithCapacity 0 }))
      (Std.HashMap.emptyWithCapacity tgba.states.size) }

/-- Mark erasure never increases the measure. -/
theorem measureTGBA_eraseMarks_le (tgba : TGBA α) (sccs : Array (Std.HashSet Nat)) :
    measureTGBA (eraseMarks tgba sccs) ≤ measureTGBA tgba := by
  have hnd := states_toList_nodup tgba
  have hst : (eraseMarks tgba sccs).states = tgba.states := rfl
  have hgs : ∀ q ∈ tgba.states.toList.toFinSet,
      transWeight ((eraseMarks tgba sccs).getSuccessors q) ≤ transWeight (tgba.getSuccessors q) := by
    intro q hq
    rw [List.mem_toFinSet] at hq
    unfold eraseMarks
    unfold TGBA.getSuccessors
    rw [getElem?_foldl_insert_of_mem _ q tgba.states.toList hnd hq]
    simp only [Option.getD_some]
    exact transWeight_map_le (fun t => by split <;> simp) _
  unfold measureTGBA
  rw [hst]
  exact Nat.add_le_add_left (FinSet.sum_le_sum hgs) _

/-! ## Mark erasure correctness -/

/-- A pointwise non-increasing `Nat` sequence is eventually constant. -/
theorem antitone_nat_eventually_const (f : Nat → Nat) (hf : ∀ n, f (n + 1) ≤ f n) :
    ∃ N, ∀ n, N ≤ n → f n = f N := by
  classical
  have hanti : ∀ m n, m ≤ n → f n ≤ f m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact Nat.le_refl _
    | succ n _ ih => exact Nat.le_trans (hf n) ih
  obtain ⟨v, -, ⟨N, hN⟩, hvmin⟩ := LentilLib.Nat.find_min (p := fun v => ∃ a, f a = v) (f 0) ⟨0, rfl⟩
  have hmin : ∀ a, f N ≤ f a := fun a =>
    Nat.not_lt.mp fun h => hvmin (f a) (by omega) ⟨a, rfl⟩
  exact ⟨N, fun n hn => Nat.le_antisymm (hanti _ n hn) (hmin n)⟩

section MarkErasureCorrect

private theorem mem_sccIndex_inner (i : Nat) (l : List Nat) (m : Std.HashMap Nat (List Nat)) (x j : Nat) :
    j ∈ (l.foldl (fun m s => m.insert s (i :: m.getD s [])) m).getD x [] ↔ j ∈ m.getD x [] ∨ (j = i ∧ x ∈ l) := by
  induction l generalizing m with
  | nil => simp
  | cons s l ih =>
    rw [List.foldl_cons, ih, Std.HashMap.getD_insert]
    by_cases hsx : s = x
    · subst hsx; simp only [beq_self_eq_true, if_true, List.mem_cons]; grind
    · simp only [beq_iff_eq, hsx, if_false, List.mem_cons]; grind

private theorem mem_sccIndex_outer (sccs : Array (Std.HashSet Nat)) (l : List Nat) (m : Std.HashMap Nat (List Nat))
    (x j : Nat) :
    j ∈ (l.foldl (fun m i => (sccs.getD i (Std.HashSet.emptyWithCapacity 0)).toList.foldl
        (fun m s => m.insert s (i :: m.getD s [])) m) m).getD x [] ↔
      j ∈ m.getD x [] ∨ (j ∈ l ∧ x ∈ sccs.getD j (Std.HashSet.emptyWithCapacity 0)) := by
  induction l generalizing m with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons, ih, mem_sccIndex_inner, Std.HashSet.mem_toList, List.mem_cons]
    grind

/-- `sccIndex` lists, for every state, exactly the indices of the enumerated sets containing it. -/
theorem mem_sccIndex (sccs : Array (Std.HashSet Nat)) (x j : Nat) :
    j ∈ (sccIndex sccs).getD x [] ↔ j < sccs.size ∧ x ∈ sccs.getD j (Std.HashSet.emptyWithCapacity 0) := by
  unfold sccIndex
  rw [mem_sccIndex_outer, List.mem_range]
  simp

/-- Mark erasure keeps a transition's marks whenever some enumerated set containing its source is not bad and contains
its target. -/
theorem keepMarks_of (tgba : TGBA α) (sccs : Array (Std.HashSet Nat)) {q t i : Nat} (hi : i < sccs.size)
    (hq : q ∈ sccs[i]) (hbad : sccIsBad tgba sccs[i] = false) (ht : t ∈ sccs[i]) :
    keepMarks sccs (sccs.map (sccIsBad tgba)) (sccIndex sccs) q t = true := by
  unfold keepMarks
  rw [List.any_eq_true]
  have hget : sccs.getD i (Std.HashSet.emptyWithCapacity 0) = sccs[i] := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  refine ⟨i, (mem_sccIndex sccs q i).mpr ⟨hi, by rw [hget]; exact hq⟩, ?_⟩
  have hbad' : (sccs.map (sccIsBad tgba)).getD i true = false := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, hbad]
  rw [hbad', hget, Std.HashSet.contains_iff_mem.mpr ht]
  rfl

/-- Every state reaches itself. -/
theorem self_mem_reachableFrom (succ : Nat → List Nat) (q : Nat) (candidates : List Nat) :
    (reachableFrom succ [q] candidates).contains q :=
  starts_subset_reachableFrom succ [q] candidates q (List.mem_singleton.mpr rfl)

/-- `reachableFrom` over `tgba`'s own states is transitive. -/
theorem tgba_reachableFrom_trans (tgba : TGBA α) (hwf : tgba.WellFormed) (p : Nat)
    (hp : tgba.states.contains p = true) (p' : Nat)
    (hp' : (reachableFrom (fun r => (tgba.succStates r).toList) [p] tgba.states.toList).contains p')
    (q : Nat) (hq : (reachableFrom (fun r => (tgba.succStates r).toList) [p'] tgba.states.toList).contains q) :
    (reachableFrom (fun r => (tgba.succStates r).toList) [p] tgba.states.toList).contains q := by
  apply reachableFrom_trans (fun r => (tgba.succStates r).toList)
    (fun x => tgba.states.contains x = true) ?_ [p] tgba.states.toList ?_ ?_ p' hp' q hq
  · intro s hs t ht
    obtain ⟨tr, htr, hteq⟩ := Array.mem_map.mp (by simpa [TGBA.succStates] using ht)
    rw [← hteq]
    exact hwf.succ_mem s tr hs htr
  · intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact hp
  · intro x hx
    exact Or.inr (Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hx))

/-- A mark is internal to `scc` iff some transition with both endpoints in `scc` carries it. -/
theorem mem_sccInternalMarks_iff (tgba : TGBA α) (scc : Std.HashSet Nat) (m : Nat) :
    (sccInternalMarks tgba scc).contains m ↔
      ∃ q, scc.contains q = true ∧ ∃ t ∈ tgba.getSuccessors q, scc.contains t.target = true ∧
        t.acceptMarks.contains m = true := by
  have hinner : ∀ (ts : List (TGBA.Transition α)) (acc : Std.HashSet Nat),
      (ts.foldl (fun acc t => if scc.contains t.target then acc.union t.acceptMarks else acc) acc).contains m ↔
        acc.contains m ∨ ∃ t ∈ ts, scc.contains t.target = true ∧ t.acceptMarks.contains m = true := by
    intro ts
    induction ts with
    | nil => simp
    | cons a rest ih =>
      intro acc
      rw [List.foldl_cons]
      by_cases hc : scc.contains a.target = true
      · rw [if_pos hc, ih (acc.union a.acceptMarks), Std.HashSet.union_eq, Std.HashSet.contains_union,
          Bool.or_eq_true]
        constructor
        · rintro ((h1 | h2) | ⟨t, ht, htc, htm⟩)
          · exact Or.inl h1
          · exact Or.inr ⟨a, List.mem_cons_self .., hc, h2⟩
          · exact Or.inr ⟨t, List.mem_cons_of_mem a ht, htc, htm⟩
        · rintro (h | ⟨t, ht, htc, htm⟩)
          · exact Or.inl (Or.inl h)
          · rcases List.mem_cons.mp ht with rfl | ht'
            · exact Or.inl (Or.inr htm)
            · exact Or.inr ⟨t, ht', htc, htm⟩
      · rw [if_neg hc, ih acc]
        constructor
        · rintro (h | ⟨t, ht, htc, htm⟩)
          · exact Or.inl h
          · exact Or.inr ⟨t, List.mem_cons_of_mem a ht, htc, htm⟩
        · rintro (h | ⟨t, ht, htc, htm⟩)
          · exact Or.inl h
          · rcases List.mem_cons.mp ht with rfl | ht'
            · exact absurd htc hc
            · exact Or.inr ⟨t, ht', htc, htm⟩
  have houter : ∀ (qs : List Nat) (acc : Std.HashSet Nat),
      (qs.foldl (fun acc q => (tgba.getSuccessors q).foldl
        (fun acc t => if scc.contains t.target then acc.union t.acceptMarks else acc) acc) acc).contains m ↔
        acc.contains m ∨ ∃ q ∈ qs, ∃ t ∈ tgba.getSuccessors q, scc.contains t.target = true ∧
          t.acceptMarks.contains m = true := by
    intro qs
    induction qs with
    | nil => simp
    | cons a rest ih =>
      intro acc
      rw [List.foldl_cons]
      rw [ih ((tgba.getSuccessors a).foldl
        (fun acc t => if scc.contains t.target then acc.union t.acceptMarks else acc) acc)]
      have hconv : ((tgba.getSuccessors a).foldl
          (fun acc t => if scc.contains t.target then acc.union t.acceptMarks else acc) acc).contains m ↔
          acc.contains m ∨ ∃ t ∈ tgba.getSuccessors a, scc.contains t.target = true ∧
            t.acceptMarks.contains m = true := by
        rw [← Array.foldl_toList, hinner (tgba.getSuccessors a).toList acc]
        constructor
        · rintro (h | ⟨t, ht, htc, htm⟩)
          · exact Or.inl h
          · exact Or.inr ⟨t, Array.mem_toList_iff.mp ht, htc, htm⟩
        · rintro (h | ⟨t, ht, htc, htm⟩)
          · exact Or.inl h
          · exact Or.inr ⟨t, Array.mem_toList_iff.mpr ht, htc, htm⟩
      rw [hconv]
      constructor
      · rintro ((h | h) | ⟨q, hq, ht⟩)
        · exact Or.inl h
        · exact Or.inr ⟨a, List.mem_cons_self .., h⟩
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, ht⟩
      · rintro (h | ⟨q, hq, ht⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hq with rfl | hq'
          · exact Or.inl (Or.inr ht)
          · exact Or.inr ⟨q, hq', ht⟩
  unfold sccInternalMarks
  rw [houter, Std.HashSet.contains_emptyWithCapacity]
  simp only [Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨q, hq, ht⟩
    exact ⟨q, Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hq), ht⟩
  · rintro ⟨q, hq, ht⟩
    exact ⟨q, Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hq), ht⟩

/-- `reachableFrom` over `tgba`'s own states is closed under successors. -/
theorem tgba_reach_step (tgba : TGBA α) (hwf : tgba.WellFormed) {x y z : Nat} (hx : tgba.states.contains x = true)
    (hy : (reachableFrom (fun r => (tgba.succStates r).toList) [x] tgba.states.toList).contains y)
    (hz : z ∈ tgba.succStates y) :
    (reachableFrom (fun r => (tgba.succStates r).toList) [x] tgba.states.toList).contains z :=
  reachableFrom_closed (fun r => (tgba.succStates r).toList) [x] tgba.states.toList
    (fun x => tgba.states.contains x = true)
    (fun s hs t ht => by
      obtain ⟨tr, htr, hteq⟩ := Array.mem_map.mp (by simpa [TGBA.succStates] using ht)
      rw [← hteq]; exact hwf.succ_mem s tr hs htr)
    (fun w hw => by rw [List.mem_singleton] at hw; subst hw; exact hx)
    (fun w hw => Or.inr (Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hw)))
    y hy z (Array.mem_toList_iff.mpr hz)

/-- `reachableFrom` read as a path: every state it reaches is the start or the end of a `PathTo`. -/
theorem pathTo_of_reach (tgba : TGBA α) {x y : Nat}
    (h : (reachableFrom (fun r => (tgba.succStates r).toList) [x] tgba.states.toList).contains y) :
    x = y ∨ PathTo tgba.succStates (fun _ => False) x y := by
  refine reachableFrom_subset (fun r => (tgba.succStates r).toList) (fun y => x = y ∨ PathTo tgba.succStates
    (fun _ => False) x y) ?_ [x] tgba.states.toList ?_ y h
  · rintro s (rfl | hp) t ht
    · exact Or.inr (.direct (Array.mem_toList_iff.mp ht))
    · exact Or.inr (hp.snoc (fun h => h) (Array.mem_toList_iff.mp ht))
  · intro w hw; rw [List.mem_singleton] at hw; exact Or.inl hw.symm

/-- A path from a state of `tgba` ends at a state `reachableFrom` reaches. -/
theorem reach_of_pathTo (tgba : TGBA α) (hwf : tgba.WellFormed) {b : Nat → Prop} {x y : Nat}
    (hx : tgba.states.contains x = true) (h : PathTo tgba.succStates b x y) :
    (reachableFrom (fun r => (tgba.succStates r).toList) [x] tgba.states.toList).contains y := by
  have key : ∀ w z, PathTo tgba.succStates b w z →
      (reachableFrom (fun r => (tgba.succStates r).toList) [x] tgba.states.toList).contains w →
      (reachableFrom (fun r => (tgba.succStates r).toList) [x] tgba.states.toList).contains z := by
    intro w z hp
    induction hp with
    | direct ht => exact fun hw => tgba_reach_step tgba hwf hx hw ht
    | through hmid _ _ ih => exact fun hw => ih (tgba_reach_step tgba hwf hx hw hmid)
  exact key x y h (self_mem_reachableFrom _ x _)

/-- The states mutually reachable with `x`, its SCC. -/
def trueSCC (tgba : TGBA α) (x : Nat) : Std.HashSet Nat :=
  Std.HashSet.ofList (tgba.states.toList.filter fun y =>
    (reachableFrom (fun r => (tgba.succStates r).toList) [x] tgba.states.toList).contains y &&
      (reachableFrom (fun r => (tgba.succStates r).toList) [y] tgba.states.toList).contains x)

theorem mem_trueSCC (tgba : TGBA α) {x y : Nat} :
    y ∈ trueSCC tgba x ↔ tgba.states.contains y = true ∧
      (reachableFrom (fun r => (tgba.succStates r).toList) [x] tgba.states.toList).contains y = true ∧
      (reachableFrom (fun r => (tgba.succStates r).toList) [y] tgba.states.toList).contains x = true := by
  unfold trueSCC
  rw [Std.HashSet.mem_ofList, List.contains_iff_mem, List.mem_filter, Std.HashSet.mem_toList,
    Std.HashSet.mem_iff_contains, Bool.and_eq_true]

/-- A path between two members of `x`'s SCC stays inside it. -/
private theorem pathTo_within_trueSCC (tgba : TGBA α) (hwf : tgba.WellFormed) {x : Nat}
    (hx : tgba.states.contains x = true) {s t : Nat} (h : PathTo tgba.succStates (fun _ => False) s t) :
    s ∈ trueSCC tgba x → t ∈ trueSCC tgba x → PathTo (sccSuccs tgba.succStates (trueSCC tgba x)) (fun _ => False) s t := by
  have hinS : ∀ {a b : Nat}, a ∈ trueSCC tgba x → b ∈ tgba.succStates a →
      (reachableFrom (fun r => (tgba.succStates r).toList) [b] tgba.states.toList).contains x = true →
      b ∈ trueSCC tgba x := by
    intro a b ha hb hbx
    obtain ⟨hastate, hxa, -⟩ := (mem_trueSCC tgba).mp ha
    have hxb := tgba_reach_step tgba hwf hx hxa hb
    have hbstate : tgba.states.contains b = true := by
      obtain ⟨tr, htr, hteq⟩ := Array.mem_map.mp (by simpa [TGBA.succStates] using hb)
      rw [← hteq]; exact hwf.succ_mem a tr hastate htr
    exact (mem_trueSCC tgba).mpr ⟨hbstate, hxb, hbx⟩
  induction h with
  | @direct a b hab =>
    intro _ hb
    exact .direct (Array.mem_filter.mpr ⟨hab, Std.HashSet.mem_iff_contains.mp hb⟩)
  | @through a mid b hmid _ hpath ih =>
    intro ha hb
    obtain ⟨hbstate, -, hbx⟩ := (mem_trueSCC tgba).mp hb
    have hmidstate : tgba.states.contains mid = true := by
      obtain ⟨tr, htr, hteq⟩ := Array.mem_map.mp (by simpa [TGBA.succStates] using hmid)
      rw [← hteq]; exact hwf.succ_mem a tr ((mem_trueSCC tgba).mp ha).1 htr
    have hmidb := reach_of_pathTo tgba hwf hmidstate hpath
    have hmidS : mid ∈ trueSCC tgba x :=
      hinS ha hmid (tgba_reachableFrom_trans tgba hwf mid hmidstate b hmidb x hbx)
    exact .through (Array.mem_filter.mpr ⟨hmid, Std.HashSet.mem_iff_contains.mp hmidS⟩) (fun h => h) (ih hmidS hb)

/-- `x`'s SCC is internally connected, every two members joined by a path inside it. -/
theorem trueSCC_internallyConnected (tgba : TGBA α) (hwf : tgba.WellFormed) {x : Nat}
    (hx : tgba.states.contains x = true) : InternallyConnected tgba.succStates (trueSCC tgba x) := by
  intro s hs t ht
  obtain ⟨hsstate, -, hsx⟩ := (mem_trueSCC tgba).mp hs
  obtain ⟨-, hxt, -⟩ := (mem_trueSCC tgba).mp ht
  have hst := tgba_reachableFrom_trans tgba hwf s hsstate x hsx t hxt
  rcases pathTo_of_reach tgba hst with rfl | hp
  · exact Or.inl rfl
  · exact Or.inr (pathTo_within_trueSCC tgba hwf hx hp hs ht)

/-- Every state reachable from `tgba`'s own states is one of them, so reachability is finite. -/
theorem tgba_finiteReach (tgba : TGBA α) (hwf : tgba.WellFormed) :
    FiniteReach tgba.states.toList tgba.succStates := by
  refine ⟨tgba.states.toList, fun s hs => ?_⟩
  simp only [Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]
  induction hs with
  | base hi => exact Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hi)
  | step _ ht ih =>
    obtain ⟨tr, htr, hteq⟩ := Array.mem_map.mp (by simpa [TGBA.succStates] using ht)
    rw [← hteq]; exact hwf.succ_mem _ tr ih htr

/-- Tarjan's enumeration of `tgba`'s SCCs is sound. -/
theorem tgbaSCCs_sound (tgba : TGBA α) (hwf : tgba.WellFormed) :
    SCCEnumerationSound tgba.states.toList tgba.succStates (tgbaSCCs tgba).toList := by
  unfold tgbaSCCs
  rw [List.toList_toArray]
  exact tarjanSCCs_sound tgba.succStates tgba.states.toList (tgba_finiteReach tgba hwf)

/-- An infinite path of `tgba` eventually stays within one SCC, from some `N` on every two positions reach each other
(`[SB00]` §6). -/
theorem eventually_mutually_reachable (tgba : TGBA α) (hwf : tgba.WellFormed) (q : Nat → Nat)
    (hqmem : ∀ n, tgba.states.contains (q n) = true) (hqsucc : ∀ n, q (n + 1) ∈ tgba.succStates (q n)) :
    ∃ N, ∀ n m, N ≤ n → N ≤ m →
      (reachableFrom (fun r => (tgba.succStates r).toList) [q n] tgba.states.toList).contains (q m) = true := by
  set F : Nat → Std.HashSet Nat := fun n => reachableFrom (fun r => (tgba.succStates r).toList) [q n]
    tgba.states.toList with hF
  have hself : ∀ n, (F n).contains (q n) = true := fun n =>
    self_mem_reachableFrom (fun r => (tgba.succStates r).toList) (q n) tgba.states.toList
  have hsub : ∀ n x, (F (n + 1)).contains x = true → (F n).contains x = true := fun n x hx =>
    tgba_reachableFrom_trans tgba hwf (q n) (hqmem n) (q (n + 1))
      (tgba_reach_step tgba hwf (hqmem n) (hself n) (hqsucc n)) x hx
  set f : Nat → Nat := fun n => (F n).toList.toFinSet.card with hfdef
  have hfanti : ∀ n, f (n + 1) ≤ f n := by
    intro n
    apply FinSet.card_le_card
    intro x hx
    rw [List.mem_toFinSet, Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains] at hx ⊢
    exact hsub n x hx
  obtain ⟨N, hNstable⟩ := antitone_nat_eventually_const f hfanti
  have hReq : ∀ n, N ≤ n → ∀ x, (F n).contains x = (F N).contains x := by
    intro n
    induction n with
    | zero => intro hn x; rw [Nat.le_zero.mp hn]
    | succ n ih =>
      intro hn x
      by_cases hcase : N ≤ n
      · have hcardeq : f (n + 1) = f n := by rw [hNstable (n + 1) (by omega), hNstable n hcase]
        have hsubfin : (F (n + 1)).toList.toFinSet ⊆ (F n).toList.toFinSet := by
          intro y hy
          rw [List.mem_toFinSet, Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains] at hy ⊢
          exact hsub n y hy
        have heqfin := FinSet.eq_of_subset_of_card_le hsubfin (Nat.le_of_eq hcardeq.symm)
        have hstep : (F (n + 1)).contains x = (F n).contains x := by
          rw [Bool.eq_iff_iff, ← Std.HashSet.mem_iff_contains, ← Std.HashSet.mem_iff_contains,
            ← Std.HashSet.mem_toList, ← Std.HashSet.mem_toList, ← List.mem_toFinSet, ← List.mem_toFinSet, heqfin]
        rw [hstep, ih hcase]
      · rw [show N = n + 1 by omega]
  exact ⟨N, fun n m hn hm => by
    show (F n).contains (q m) = true
    rw [hReq n hn, ← hReq m hm]
    exact hself m⟩

theorem eraseMarks_initialStates (tgba : TGBA α) (sccs : Array (Std.HashSet Nat)) :
    (eraseMarks tgba sccs).initialStates = tgba.initialStates := rfl

theorem eraseMarks_states (tgba : TGBA α) (sccs : Array (Std.HashSet Nat)) :
    (eraseMarks tgba sccs).states = tgba.states := rfl

/-- `eraseMarks`'s successors at any of `tgba`'s own states. -/
theorem eraseMarks_getSuccessors (tgba : TGBA α) (sccs : Array (Std.HashSet Nat)) (q : Nat)
    (hq : q ∈ tgba.states.toList) : (eraseMarks tgba sccs).getSuccessors q =
      (tgba.getSuccessors q).map fun t =>
        if keepMarks sccs (sccs.map (sccIsBad tgba)) (sccIndex sccs) q t.target then t
        else { t with acceptMarks := Std.HashSet.emptyWithCapacity 0 } := by
  unfold eraseMarks
  unfold TGBA.getSuccessors
  rw [getElem?_foldl_insert_of_mem _ q tgba.states.toList (states_toList_nodup tgba) hq]
  rfl

/-- Mark erasure keeps a TGBA well-formed. -/
theorem eraseMarks_wellFormed (tgba : TGBA α) (hwf : tgba.WellFormed) (sccs : Array (Std.HashSet Nat)) :
    (eraseMarks tgba sccs).WellFormed where
  initial_mem q hq := by
    rw [eraseMarks_states]
    exact hwf.initial_mem q hq
  succ_mem q t hq ht := by
    rw [eraseMarks_states] at hq ⊢
    rw [eraseMarks_getSuccessors tgba sccs q
      (Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hq))] at ht
    obtain ⟨t', ht'mem, ht'eq⟩ := Array.mem_map.mp ht
    rw [← ht'eq]
    split
    · exact hwf.succ_mem q t' hq ht'mem
    · exact hwf.succ_mem q t' hq ht'mem
  marks_range q t hq ht m hm := by
    rw [eraseMarks_states] at hq
    rw [eraseMarks_getSuccessors tgba sccs q
      (Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hq))] at ht
    obtain ⟨t', ht'mem, ht'eq⟩ := Array.mem_map.mp ht
    rw [← ht'eq] at hm
    split at hm
    · exact hwf.marks_range q t' hq ht'mem m hm
    · simp at hm

/-- Mark erasure keeps every transition's marks, at any state, below `numAcceptSets`. -/
theorem eraseMarks_marks_lt (tgba : TGBA α) (sccs : Array (Std.HashSet Nat))
    (hb : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets) :
    ∀ q t, t ∈ (eraseMarks tgba sccs).getSuccessors q → ∀ m ∈ t.acceptMarks,
      m < (eraseMarks tgba sccs).numAcceptSets := by
  intro q t ht m hm
  by_cases hq : q ∈ tgba.states.toList
  · rw [eraseMarks_getSuccessors tgba sccs q hq] at ht
    obtain ⟨t0, ht0, rfl⟩ := Array.mem_map.mp ht
    split at hm
    · exact hb q t0 ht0 m hm
    · simp at hm
  · have hempty : (eraseMarks tgba sccs).getSuccessors q = #[] := by
      unfold eraseMarks TGBA.getSuccessors
      rw [getElem?_foldl_insert_of_not_mem _ q tgba.states.toList _ hq]
      simp
    rw [hempty] at ht
    exact absurd ht (by simp)

/-- `[SB00]` §6: mark erasure over a sound SCC enumeration preserves the accepted language. -/
theorem eraseMarks_correct (tgba : TGBA α) (hwf : tgba.WellFormed) (sccs : Array (Std.HashSet Nat))
    (hsccs : SCCEnumerationSound tgba.states.toList tgba.succStates sccs.toList) (ξ : OmegaWord α) :
    tgba.toSpec.accepts ξ ↔ (eraseMarks tgba sccs).toSpec.accepts ξ := by
  constructor
  · rintro ⟨σ, hrun, hcompat, hacc⟩
    have hstateMem : ∀ n, tgba.states.contains (σ n).1 = true := by
      intro n
      induction n with
      | zero => exact hwf.initial_mem _ hrun.1
      | succ n ih =>
        have hlink : (σ n).2.target = (σ (n + 1)).1 := (hrun.2 n).2
        rw [← hlink]
        exact hwf.succ_mem _ _ ih (hrun.2 n).1
    have hqsucc : ∀ n, (σ (n + 1)).1 ∈ tgba.succStates (σ n).1 := fun n =>
      Array.mem_map.mpr ⟨(σ n).2, (hrun.2 n).1, (hrun.2 n).2⟩
    obtain ⟨N, hmut⟩ := eventually_mutually_reachable tgba hwf (fun n => (σ n).1) hstateMem hqsucc
    -- the run stays inside the SCC of its state at `N`, which some enumerated set contains
    have hinS : ∀ n, N ≤ n → (σ n).1 ∈ trueSCC tgba (σ N).1 := fun n hn =>
      (mem_trueSCC tgba).mpr ⟨hstateMem n, hmut N n (Nat.le_refl _) hn, hmut n N hn (Nat.le_refl _)⟩
    obtain ⟨C, hC, hSC⟩ := hsccs.2.2 (trueSCC tgba (σ N).1) ⟨(σ N).1, hinS N (Nat.le_refl _)⟩
      (trueSCC_internallyConnected tgba hwf (hstateMem N))
      (fun s hs => .base (Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr ((mem_trueSCC tgba).mp hs).1)))
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hC
    have hi' : i < sccs.size := by simpa using hi
    have hCi : sccs.toList[i] = sccs[i] := by simp
    rw [hCi] at hSC
    have hnotbad : sccIsBad tgba sccs[i] = false := by
      have hall : (List.range tgba.numAcceptSets).all (fun m => (sccInternalMarks tgba sccs[i]).contains m) = true := by
        rw [List.all_eq_true]
        intro m hmrange
        rw [List.mem_range] at hmrange
        obtain ⟨j, hj⟩ := hacc ⟨m, hmrange⟩ N
        have hlink : (σ (N + j)).2.target = (σ (N + j + 1)).1 := (hrun.2 (N + j)).2
        rw [mem_sccInternalMarks_iff]
        refine ⟨(σ (N + j)).1, Std.HashSet.mem_iff_contains.mp (hSC _ (hinS (N + j) (by omega))), (σ (N + j)).2,
          (hrun.2 (N + j)).1, ?_, hj⟩
        rw [hlink]
        exact Std.HashSet.mem_iff_contains.mp (hSC _ (hinS (N + j + 1) (by omega)))
      unfold sccIsBad
      rw [hall]
      rfl
    have hkeep : ∀ n, N ≤ n → keepMarks sccs (sccs.map (sccIsBad tgba)) (sccIndex sccs) (σ n).1 (σ n).2.target = true := by
      intro n hn
      have hlink : (σ n).2.target = (σ (n + 1)).1 := (hrun.2 n).2
      refine keepMarks_of tgba sccs hi' (hSC _ (hinS n hn)) hnotbad ?_
      rw [hlink]
      exact hSC _ (hinS (n + 1) (by omega))
    have hkept : ∀ n, N ≤ n →
        (if keepMarks sccs (sccs.map (sccIsBad tgba)) (sccIndex sccs) (σ n).1 (σ n).2.target then (σ n).2
          else { (σ n).2 with acceptMarks := Std.HashSet.emptyWithCapacity 0 }) = (σ n).2 := fun n hn => by
      rw [if_pos (hkeep n hn)]
    refine ⟨fun n => ⟨(σ n).1, if keepMarks sccs (sccs.map (sccIsBad tgba)) (sccIndex sccs) (σ n).1 (σ n).2.target
      then (σ n).2 else { (σ n).2 with acceptMarks := Std.HashSet.emptyWithCapacity 0 }⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · show (eraseMarks tgba sccs).initialStates.contains (σ 0).1
      rw [eraseMarks_initialStates]; exact hrun.1
    · intro n
      have hqn : (σ n).1 ∈ tgba.states.toList :=
        Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr (hstateMem n))
      have hlink : (σ n).2.target = (σ (n + 1)).1 := (hrun.2 n).2
      refine ⟨?_, ?_⟩
      · show (if keepMarks sccs (sccs.map (sccIsBad tgba)) (sccIndex sccs) (σ n).1 (σ n).2.target then (σ n).2
          else { (σ n).2 with acceptMarks := Std.HashSet.emptyWithCapacity 0 }) ∈
          (eraseMarks tgba sccs).getSuccessors (σ n).1
        rw [eraseMarks_getSuccessors tgba sccs _ hqn]
        exact Array.mem_map.mpr ⟨(σ n).2, (hrun.2 n).1, rfl⟩
      · show (if keepMarks sccs (sccs.map (sccIsBad tgba)) (sccIndex sccs) (σ n).1 (σ n).2.target then (σ n).2
          else { (σ n).2 with acceptMarks := Std.HashSet.emptyWithCapacity 0 }).target = (σ (n + 1)).1
        split <;> exact hlink
    · intro n
      have hc := hcompat n
      show (∀ a, (if keepMarks sccs (sccs.map (sccIsBad tgba)) (sccIndex sccs) (σ n).1 (σ n).2.target then (σ n).2
          else { (σ n).2 with acceptMarks := Std.HashSet.emptyWithCapacity 0 } :
          TGBA.Transition α).positiveProps.contains a → ξ n a) ∧
        ∀ a, (if keepMarks sccs (sccs.map (sccIsBad tgba)) (sccIndex sccs) (σ n).1 (σ n).2.target then (σ n).2
          else { (σ n).2 with acceptMarks := Std.HashSet.emptyWithCapacity 0 } :
          TGBA.Transition α).negativeProps.contains a → ¬ ξ n a
      split <;> exact hc
    · intro i n0
      obtain ⟨j, hj⟩ := hacc i (max n0 N)
      refine ⟨max n0 N + j - n0, ?_⟩
      have hn0j : n0 + (max n0 N + j - n0) = max n0 N + j := by omega
      rw [hn0j]
      show (if keepMarks sccs (sccs.map (sccIsBad tgba)) (sccIndex sccs) (σ (max n0 N + j)).1
          (σ (max n0 N + j)).2.target then (σ (max n0 N + j)).2
          else { (σ (max n0 N + j)).2 with acceptMarks := Std.HashSet.emptyWithCapacity 0 }).acceptMarks.contains
        i.val = true
      rw [hkept (max n0 N + j) (by omega)]
      exact hj
  · rintro ⟨σ, hrun, hcompat, hacc⟩
    have hwf' := eraseMarks_wellFormed tgba hwf sccs
    have hstateMem : ∀ n, (eraseMarks tgba sccs).states.contains (σ n).1 = true := by
      intro n
      induction n with
      | zero => exact hwf'.initial_mem _ hrun.1
      | succ n ih =>
        have hlink : (σ n).2.target = (σ (n + 1)).1 := (hrun.2 n).2
        rw [← hlink]
        exact hwf'.succ_mem _ _ ih (hrun.2 n).1
    have hpre : ∀ n, ∃ t ∈ tgba.getSuccessors (σ n).1, (σ n).2 =
        if keepMarks sccs (sccs.map (sccIsBad tgba)) (sccIndex sccs) (σ n).1 t.target then t
        else { t with acceptMarks := Std.HashSet.emptyWithCapacity 0 } := by
      intro n
      have hqn : (σ n).1 ∈ tgba.states.toList :=
        Std.HashSet.mem_toList.mpr (by rw [← eraseMarks_states tgba sccs]; exact hstateMem n)
      have hvalidn : (σ n).2 ∈ (eraseMarks tgba sccs).getSuccessors (σ n).1 := (hrun.2 n).1
      rw [eraseMarks_getSuccessors tgba sccs _ hqn] at hvalidn
      obtain ⟨t', ht'mem, ht'eq⟩ := Array.mem_map.mp hvalidn
      exact ⟨t', ht'mem, ht'eq.symm⟩
    obtain ⟨t, ht⟩ := Classical.axiomOfChoice hpre
    obtain ⟨htmem, ht⟩ := forall_and.mp ht
    refine ⟨fun n => ⟨(σ n).1, t n⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · show tgba.initialStates.contains (σ 0).1
      rw [← eraseMarks_initialStates tgba sccs]
      exact hrun.1
    · intro n
      have hlink : (σ n).2.target = (σ (n + 1)).1 := (hrun.2 n).2
      refine ⟨htmem n, ?_⟩
      show (t n).target = (σ (n + 1)).1
      rw [← hlink, ht n]
      split <;> rfl
    · intro n
      have hcn : (∀ a, (σ n).2.positiveProps.contains a → ξ n a) ∧
          ∀ a, (σ n).2.negativeProps.contains a → ¬ ξ n a := hcompat n
      show (∀ a, (t n).positiveProps.contains a → ξ n a) ∧ ∀ a, (t n).negativeProps.contains a → ¬ ξ n a
      rw [ht n] at hcn
      split at hcn <;> exact hcn
    · intro i n0
      obtain ⟨j, hj⟩ := hacc i n0
      refine ⟨j, ?_⟩
      show (t (n0 + j)).acceptMarks.contains i.val = true
      have hcm : (σ (n0 + j)).2.acceptMarks.contains i.val = true := hj
      rw [ht (n0 + j)] at hcm
      split at hcm
      · exact hcm
      · simp at hcm

end MarkErasureCorrect

/-! ## Implied-transition removal -/

/-- A transition's label as the single cube it already is. -/
def cubeOf (t : TGBA.Transition α) : Cube α := { pos := t.positiveProps, neg := t.negativeProps }

/-- Same target, marks and label. -/
def sameTrans (t1 t2 : TGBA.Transition α) : Bool :=
  t1.target == t2.target && hashSetEq t1.acceptMarks t2.acceptMarks &&
  hashSetEq t1.positiveProps t2.positiveProps && hashSetEq t1.negativeProps t2.negativeProps

/-- Fold exact duplicates into one, so implication is never checked against a transition's own copy. -/
@[expose] def dedupExactTrans (ts : Array (TGBA.Transition α)) : Array (TGBA.Transition α) :=
  ts.foldl (fun acc t => if acc.any (sameTrans · t) then acc else acc.push t) #[]

/-- Deduplicating never increases the weight. -/
theorem dedupExactTrans_weight_le (ts : Array (TGBA.Transition α)) :
    transWeight (dedupExactTrans ts) ≤ transWeight ts := by
  unfold dedupExactTrans transWeight
  rw [← Array.foldl_toList]
  have := sum_foldl_condPush_le (fun t : TGBA.Transition α => 1 + t.acceptMarks.size)
    (fun acc t => acc.any (sameTrans · t)) ts.toList #[]
  simpa using this

/-- Implied-transition removal on one array: drop a transition implied by another to the same target with marks no
fewer, `[GO01]` §6 rule 2. -/
@[expose] def dropImpliedWithin (ts : Array (TGBA.Transition α)) : Array (TGBA.Transition α) :=
  let ts := dedupExactTrans ts
  ts.filter fun t2 =>
    !ts.any fun t1 =>
      t1.target == t2.target && hashSetSubset t2.acceptMarks t1.acceptMarks && Cube.litImplies (cubeOf t2) (cubeOf t1) &&
      !sameTrans t1 t2

/-- `dropImpliedWithin` never increases the weight. -/
theorem dropImpliedWithin_weight_le (ts : Array (TGBA.Transition α)) :
    transWeight (dropImpliedWithin ts) ≤ transWeight ts :=
  Nat.le_trans (transWeight_filter_le _ _) (dedupExactTrans_weight_le ts)

/-- `ts` sorted by target and split into the runs sharing one. -/
def targetGroups (ts : Array (TGBA.Transition α)) : List (List (TGBA.Transition α)) :=
  (ts.toList.mergeSort fun t1 t2 => t1.target ≤ t2.target).splitBy fun t1 t2 => t1.target == t2.target

/-- Implied-transition removal: `dropImpliedWithin` on every run of transitions sharing a target. -/
def dropImpliedTrans (ts : Array (TGBA.Transition α)) : Array (TGBA.Transition α) :=
  ((targetGroups ts).flatMap fun g => (dropImpliedWithin g.toArray).toList).toArray

theorem mem_targetGroups {ts : Array (TGBA.Transition α)} {t : TGBA.Transition α} :
    t ∈ ts ↔ ∃ g ∈ targetGroups ts, t ∈ g := by
  rw [← List.mem_flatten, targetGroups, List.flatten_splitBy, List.mem_mergeSort, Array.mem_toList_iff]

theorem transWeight_targetGroups (ts : Array (TGBA.Transition α)) :
    ((targetGroups ts).map fun g => transWeight g.toArray).sum = transWeight ts := by
  unfold transWeight
  have h : ((targetGroups ts).map fun g => (g.toArray.toList.map fun t => 1 + t.acceptMarks.size).sum).sum =
      ((targetGroups ts).flatten.map fun t => 1 + t.acceptMarks.size).sum := by
    rw [List.map_flatten, List.sum_flatten, List.map_map]
    rfl
  rw [h, targetGroups, List.flatten_splitBy]
  exact ((List.mergeSort_perm _ _).map _).sum_nat

/-- Implied-transition removal never increases the weight. -/
theorem dropImpliedTrans_weight_le (ts : Array (TGBA.Transition α)) :
    transWeight (dropImpliedTrans ts) ≤ transWeight ts := by
  have h : transWeight (dropImpliedTrans ts) =
      ((targetGroups ts).map fun g => transWeight (dropImpliedWithin g.toArray)).sum := by
    unfold dropImpliedTrans transWeight
    rw [List.toList_toArray, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map, List.map_map]
    rfl
  rw [h, ← transWeight_targetGroups ts]
  exact List.sum_map_le_sum_map fun g _ => dropImpliedWithin_weight_le _

/-! ## Implied-transition removal correctness -/

section ImpliedRemovalCorrectness

-- `sameTrans` bridged to pointwise agreement.
theorem sameTrans_iff (t1 t2 : TGBA.Transition α) :
    sameTrans t1 t2 = true ↔ t1.target = t2.target ∧ hashSetEq t1.acceptMarks t2.acceptMarks = true ∧
      hashSetEq t1.positiveProps t2.positiveProps = true ∧ hashSetEq t1.negativeProps t2.negativeProps = true := by
  unfold sameTrans
  constructor
  · intro h; simp only [Bool.and_eq_true, beq_iff_eq] at h; grind
  · rintro ⟨h1, h2, h3, h4⟩; simp [h1, h2, h3, h4]

-- `t1` dominates `t2`, exactly `dropImpliedTrans`'s own per-pair check.
@[expose] def beatsPred (t1 t2 : TGBA.Transition α) : Bool :=
  t1.target == t2.target && hashSetSubset t2.acceptMarks t1.acceptMarks && Cube.litImplies (cubeOf t2) (cubeOf t1) &&
    !sameTrans t1 t2

theorem beatsPred_iff (t1 t2 : TGBA.Transition α) :
    beatsPred t1 t2 = true ↔ sameTrans t1 t2 = false ∧ t1.target = t2.target ∧
      hashSetSubset t2.acceptMarks t1.acceptMarks = true ∧ Cube.litImplies (cubeOf t2) (cubeOf t1) = true := by
  unfold beatsPred
  constructor
  · intro h; simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h; grind
  · rintro ⟨h1, h2, h3, h4⟩; simp [h1, h2, h3, h4]

theorem dropImpliedWithin_eq (ts : Array (TGBA.Transition α)) :
    dropImpliedWithin ts = (dedupExactTrans ts).filter fun t2 => !(dedupExactTrans ts).any (beatsPred · t2) := rfl

theorem mem_dropImpliedWithin_iff (ts : Array (TGBA.Transition α)) (t : TGBA.Transition α) :
    t ∈ dropImpliedWithin ts ↔ t ∈ dedupExactTrans ts ∧ ∀ t1 ∈ dedupExactTrans ts, beatsPred t1 t = false := by
  rw [dropImpliedWithin_eq, Array.mem_filter, Bool.not_eq_true']
  rw [Array.any_eq_false']
  constructor
  · rintro ⟨ht, hb⟩
    refine ⟨ht, fun t1 ht1 => ?_⟩
    match hbe : beatsPred t1 t with
    | false => rfl
    | true => exact absurd hbe (hb t1 ht1)
  · rintro ⟨ht, hb⟩; exact ⟨ht, fun t1 ht1 => by simp [hb t1 ht1]⟩

variable [LawfulBEq α] [LawfulHashable α]

-- `beatsPred` is transitive.
theorem beatsPred_trans {t1 t2 t3 : TGBA.Transition α} (h12 : beatsPred t1 t2 = true)
    (h23 : beatsPred t2 t3 = true) : beatsPred t1 t3 = true := by
  obtain ⟨hs12, ht12, hm12, hi12⟩ := (beatsPred_iff t1 t2).mp h12
  obtain ⟨-, ht23, hm23, hi23⟩ := (beatsPred_iff t2 t3).mp h23
  refine (beatsPred_iff t1 t3).mpr ⟨?_, ht12.trans ht23, hashSetSubset_trans hm23 hm12, Cube.litImplies_trans hi23 hi12⟩
  by_contra hst13
  obtain ⟨-, hmarks13, hpos13, hneg13⟩ := (sameTrans_iff t1 t3).mp (by simpa using hst13)
  have hsubR : ∀ {s1 s2 : Std.HashSet α}, hashSetEq s1 s2 = true → hashSetSubset s2 s1 = true := fun h =>
    (hashSetSubset_iff _ _).mpr fun a ha => ((hashSetEq_iff _ _).mp h a).mpr ha
  have hm1_2 : hashSetSubset t1.acceptMarks t2.acceptMarks = true :=
    hashSetSubset_trans ((hashSetSubset_iff _ _).mpr fun a ha => ((hashSetEq_iff _ _).mp hmarks13 a).mp ha) hm23
  unfold Cube.litImplies cubeOf at hi12 hi23
  simp only [Bool.and_eq_true] at hi12 hi23
  have hp : hashSetEq t1.positiveProps t2.positiveProps = true :=
    hashSetEq_of_subset_subset hi12.1 (hashSetSubset_trans hi23.1 (hsubR hpos13))
  have hn : hashSetEq t1.negativeProps t2.negativeProps = true :=
    hashSetEq_of_subset_subset hi12.2 (hashSetSubset_trans hi23.2 (hsubR hneg13))
  have hst12 : sameTrans t1 t2 = true :=
    (sameTrans_iff t1 t2).mpr ⟨ht12, hashSetEq_of_subset_subset hm1_2 hm12, hp, hn⟩
  exact absurd hst12 (by simp [hs12])

-- A filtered list's length is monotone under a pointwise implication between the two predicates.
theorem length_filter_le_of_impl {γ} {l : List γ} {P Q : γ → Bool} (h : ∀ x ∈ l, P x → Q x) :
    (l.filter P).length ≤ (l.filter Q).length := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have ihr := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.filter_cons]
    by_cases hPa : P a = true
    · have hQa : Q a = true := h a (List.mem_cons_self ..) hPa
      simp [hPa, hQa]; omega
    · by_cases hQa : Q a = true <;> simp [hPa, hQa] <;> omega

-- Strict version: a witnessed member on the RHS but not the LHS makes the filtered lengths strict.
theorem length_filter_lt_of_impl_of_mem_diff {γ} {l : List γ} {P Q : γ → Bool}
    (h : ∀ x ∈ l, P x → Q x) {t : γ} (ht : t ∈ l) (htQ : Q t = true) (htP : P t = false) :
    (l.filter P).length < (l.filter Q).length := by
  induction l with
  | nil => simp at ht
  | cons a rest ih =>
    have hmono := length_filter_le_of_impl (l := rest) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.mem_cons] at ht
    simp only [List.filter_cons]
    rcases ht with rfl | ht
    · rw [htP, htQ]; simpa using Nat.lt_succ_of_le hmono
    · by_cases hPa : P a = true
      · have hQa : Q a = true := h a (List.mem_cons_self ..) hPa
        have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) ht
        simp [hPa, hQa]; omega
      · by_cases hQa : Q a = true
        · have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) ht
          simp [hPa, hQa]; omega
        · simpa [hPa, hQa] using ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) ht

/-- Every transition of `ts0` is unbeaten or dominated by an unbeaten transition of `ts0`, `[GO01]` §6 rule 2. -/
theorem exists_dropImpliedTrans_dominator_aux (ts0 : Array (TGBA.Transition α)) (t2 : TGBA.Transition α)
    (ht2 : t2 ∈ ts0) :
    ∃ t1 ∈ ts0, (t1 = t2 ∨ (t1.target = t2.target ∧ hashSetSubset t2.acceptMarks t1.acceptMarks = true ∧
      Cube.litImplies (cubeOf t2) (cubeOf t1) = true)) ∧ ∀ t' ∈ ts0, beatsPred t' t1 = false := by
  have hself_notbeats : ∀ (t : TGBA.Transition α), beatsPred t t = false := by
    intro t
    have hst : sameTrans t t = true := (sameTrans_iff t t).mpr
      ⟨rfl, hashSetEq_refl t.acceptMarks, hashSetEq_refl t.positiveProps, hashSetEq_refl t.negativeProps⟩
    by_contra hb
    exact absurd hst (by simpa using ((beatsPred_iff t t).mp (by simpa using hb)).1)
  suffices h : ∀ n (t2 : TGBA.Transition α), (ts0.toList.filter (beatsPred · t2)).length ≤ n → t2 ∈ ts0 →
      ∃ t1 ∈ ts0, (t1 = t2 ∨ (t1.target = t2.target ∧ hashSetSubset t2.acceptMarks t1.acceptMarks = true ∧
        Cube.litImplies (cubeOf t2) (cubeOf t1) = true)) ∧ ∀ t' ∈ ts0, beatsPred t' t1 = false by
    exact h _ t2 (Nat.le_refl _) ht2
  intro n
  induction n with
  | zero =>
    intro t2 hn ht2
    refine ⟨t2, ht2, Or.inl rfl, fun t' ht' => ?_⟩
    by_contra hbeat
    have : t' ∈ ts0.toList.filter (beatsPred · t2) :=
      List.mem_filter.mpr ⟨Array.mem_toList_iff.mpr ht', by simpa using hbeat⟩
    have := List.length_pos_of_mem this
    omega
  | succ n ih =>
    intro t2 hn ht2
    by_cases hsurv : ∀ t' ∈ ts0, beatsPred t' t2 = false
    · exact ⟨t2, ht2, Or.inl rfl, hsurv⟩
    · simp only [Classical.not_forall] at hsurv
      obtain ⟨t1', ht1'mem, ht1'beats⟩ := hsurv
      have ht1'beats' : beatsPred t1' t2 = true := by simpa using ht1'beats
      have hsub : ∀ x ∈ ts0.toList, beatsPred x t1' = true → beatsPred x t2 = true :=
        fun _ _ hx => beatsPred_trans hx ht1'beats'
      have hlt : (ts0.toList.filter (beatsPred · t1')).length <
          (ts0.toList.filter (beatsPred · t2)).length :=
        length_filter_lt_of_impl_of_mem_diff hsub (Array.mem_toList_iff.mpr ht1'mem) ht1'beats'
          (hself_notbeats t1')
      obtain ⟨t1, ht1mem, hdom, hsurv1⟩ := ih t1' (by omega) ht1'mem
      refine ⟨t1, ht1mem, ?_, hsurv1⟩
      rcases hdom with rfl | ⟨httgt, hmsub, himp⟩
      · exact Or.inr ((beatsPred_iff t1 t2).mp ht1'beats').2
      · obtain ⟨_, ht1'tgt, ht1'marks, ht1'imp⟩ := (beatsPred_iff t1' t2).mp ht1'beats'
        exact Or.inr ⟨httgt.trans ht1'tgt, hashSetSubset_trans ht1'marks hmsub, Cube.litImplies_trans ht1'imp himp⟩

theorem exists_dropImpliedWithin_dominator (ts : Array (TGBA.Transition α)) (t2 : TGBA.Transition α)
    (ht2 : t2 ∈ dedupExactTrans ts) :
    ∃ t1 ∈ dropImpliedWithin ts, t1.target = t2.target ∧ hashSetSubset t2.acceptMarks t1.acceptMarks = true ∧
      Cube.litImplies (cubeOf t2) (cubeOf t1) = true := by
  obtain ⟨t1, ht1mem, hdom, hsurv⟩ := exists_dropImpliedTrans_dominator_aux (dedupExactTrans ts) t2 ht2
  refine ⟨t1, (mem_dropImpliedWithin_iff ts t1).mpr ⟨ht1mem, hsurv⟩, ?_⟩
  rcases hdom with rfl | hdom
  · exact ⟨rfl, (hashSetSubset_iff t1.acceptMarks t1.acceptMarks).mpr (fun _ h => h), Cube.litImplies_refl _⟩
  · exact hdom

end ImpliedRemovalCorrectness

/-- `dropImpliedTrans` over every state. -/
def dropImpliedAll (tgba : TGBA α) : TGBA α :=
  { tgba with
    successors := tgba.states.toList.foldl (fun m q => m.insert q (dropImpliedTrans (tgba.getSuccessors q)))
      (Std.HashMap.emptyWithCapacity tgba.states.size) }

/-- Implied-transition removal never increases the measure. -/
theorem measureTGBA_dropImpliedAll_le (tgba : TGBA α) : measureTGBA (dropImpliedAll tgba) ≤ measureTGBA tgba := by
  have hnd := states_toList_nodup tgba
  have hst : (dropImpliedAll tgba).states = tgba.states := rfl
  have hgs : ∀ q ∈ tgba.states.toList.toFinSet,
      transWeight ((dropImpliedAll tgba).getSuccessors q) ≤ transWeight (tgba.getSuccessors q) := by
    intro q hq
    rw [List.mem_toFinSet] at hq
    unfold dropImpliedAll
    unfold TGBA.getSuccessors
    rw [getElem?_foldl_insert_of_mem _ q tgba.states.toList hnd hq]
    exact dropImpliedTrans_weight_le (tgba.getSuccessors q)
  unfold measureTGBA
  rw [hst]
  exact Nat.add_le_add_left (FinSet.sum_le_sum hgs) _

section DropImpliedAllCorrect

-- A conditionally-pushing fold only ever keeps elements already in the accumulator or the source list.
theorem mem_foldl_condPush_of_mem {β} (p : Array β → β → Bool) :
    ∀ (l : List β) (acc0 : Array β) (x : β),
      x ∈ l.foldl (fun acc y => if p acc y then acc else acc.push y) acc0 → x ∈ acc0 ∨ x ∈ l := by
  intro l
  induction l with
  | nil => intro acc0 x hx; exact Or.inl hx
  | cons a rest ih =>
    intro acc0 x hx
    rw [List.foldl_cons] at hx
    by_cases h : p acc0 a
    · rw [if_pos h] at hx
      rcases ih acc0 x hx with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (List.mem_cons_of_mem _ h2)
    · rw [if_neg h] at hx
      rcases ih (acc0.push a) x hx with h1 | h2
      · rcases (Array.mem_push).mp h1 with h1 | rfl
        · exact Or.inl h1
        · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h2)

-- A conditionally-pushing fold only ever adds to the accumulator, never removes from it.
theorem mem_of_mem_foldl_condPush_acc0 {β} (p : Array β → β → Bool) :
    ∀ (l : List β) (acc0 : Array β) (x : β), x ∈ acc0 →
      x ∈ l.foldl (fun acc y => if p acc y then acc else acc.push y) acc0 := by
  intro l
  induction l with
  | nil => intro acc0 x hx; exact hx
  | cons a rest ih =>
    intro acc0 x hx
    rw [List.foldl_cons]
    by_cases h : p acc0 a
    · rw [if_pos h]; exact ih acc0 x hx
    · rw [if_neg h]; exact ih (acc0.push a) x (Array.mem_push.mpr (Or.inl hx))

theorem mem_dedupExactTrans_of_mem {ts : Array (TGBA.Transition α)} {t : TGBA.Transition α}
    (ht : t ∈ dedupExactTrans ts) : t ∈ ts := by
  unfold dedupExactTrans at ht
  rw [← Array.foldl_toList] at ht
  rcases mem_foldl_condPush_of_mem (fun acc y => acc.any (sameTrans · y)) ts.toList #[] t ht with h | h
  · simp at h
  · exact Array.mem_toList_iff.mp h

theorem mem_dropImpliedWithin_of_mem {ts : Array (TGBA.Transition α)} {t : TGBA.Transition α}
    (ht : t ∈ dropImpliedWithin ts) : t ∈ ts :=
  mem_dedupExactTrans_of_mem ((mem_dropImpliedWithin_iff ts t).mp ht).1

theorem mem_dropImpliedTrans_of_mem {ts : Array (TGBA.Transition α)} {t : TGBA.Transition α}
    (ht : t ∈ dropImpliedTrans ts) : t ∈ ts := by
  unfold dropImpliedTrans at ht
  rw [List.mem_toArray, List.mem_flatMap] at ht
  obtain ⟨g, hg, htg⟩ := ht
  exact mem_targetGroups.mpr ⟨g, hg, List.mem_toArray.mp (mem_dropImpliedWithin_of_mem (Array.mem_toList_iff.mp htg))⟩

/-- `dropImpliedAll` replaces every state's outgoing array by its `dropImpliedTrans`. -/
theorem dropImpliedAll_getSuccessors (tgba : TGBA α) {q : Nat} (hq : q ∈ tgba.states.toList) :
    (dropImpliedAll tgba).getSuccessors q = dropImpliedTrans (tgba.getSuccessors q) := by
  unfold TGBA.getSuccessors dropImpliedAll
  rw [getElem?_foldl_insert_of_mem _ q tgba.states.toList (states_toList_nodup tgba) hq]
  rfl

/-- Implied-transition removal keeps a TGBA well-formed. -/
theorem dropImpliedAll_wellFormed (tgba : TGBA α) (hwf : tgba.WellFormed) : (dropImpliedAll tgba).WellFormed := by
  have hmem : ∀ q, tgba.states.contains q = true → q ∈ tgba.states.toList :=
    fun q hq => Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hq)
  refine ⟨fun q hq => hwf.initial_mem q hq, fun q t hq ht => ?_, fun q t hq ht => ?_⟩
  · rw [dropImpliedAll_getSuccessors tgba (hmem q hq)] at ht
    exact hwf.succ_mem q t hq (mem_dropImpliedTrans_of_mem ht)
  · rw [dropImpliedAll_getSuccessors tgba (hmem q hq)] at ht
    exact hwf.marks_range q t hq (mem_dropImpliedTrans_of_mem ht)

/-- Implied-transition removal keeps every transition's marks, at any state, below `numAcceptSets`. -/
theorem dropImpliedAll_marks_lt (tgba : TGBA α)
    (hb : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets) :
    ∀ q t, t ∈ (dropImpliedAll tgba).getSuccessors q → ∀ m ∈ t.acceptMarks, m < (dropImpliedAll tgba).numAcceptSets := by
  intro q t ht m hm
  by_cases hq : q ∈ tgba.states.toList
  · rw [dropImpliedAll_getSuccessors tgba hq] at ht
    exact hb q t (mem_dropImpliedTrans_of_mem ht) m hm
  · have hempty : (dropImpliedAll tgba).getSuccessors q = #[] := by
      unfold dropImpliedAll TGBA.getSuccessors
      rw [getElem?_foldl_insert_of_not_mem _ q tgba.states.toList _ hq]
      simp
    rw [hempty] at ht
    exact absurd ht (by simp)

variable [LawfulBEq α] [LawfulHashable α]

-- Every transition of `ts` has a `sameTrans`-equivalent representative surviving `dedupExactTrans`.
theorem exists_rep_foldl_condPush {β} (same : β → β → Bool) (hrefl : ∀ x, same x x = true) :
    ∀ (l : List β) (acc0 : Array β) (x : β), x ∈ l →
      ∃ x' ∈ l.foldl (fun acc y => if acc.any (same · y) then acc else acc.push y) acc0, same x' x = true := by
  intro l
  induction l with
  | nil => intro acc0 x hx; simp at hx
  | cons a rest ih =>
    intro acc0 x hx
    rw [List.foldl_cons]
    rw [List.mem_cons] at hx
    by_cases h : acc0.any (same · a)
    · rw [if_pos h]
      rcases hx with rfl | hx
      · obtain ⟨x', hx'mem, hx'same⟩ := Array.any_eq_true'.mp h
        exact ⟨x', mem_of_mem_foldl_condPush_acc0 _ rest acc0 x' hx'mem, hx'same⟩
      · exact ih acc0 x hx
    · rw [if_neg h]
      rcases hx with rfl | hx
      · exact ⟨x, mem_of_mem_foldl_condPush_acc0 _ rest (acc0.push x) x (Array.mem_push.mpr (Or.inr rfl)),
          hrefl x⟩
      · exact ih (acc0.push a) x hx

theorem exists_dedupExactTrans_rep {ts : Array (TGBA.Transition α)} {t : TGBA.Transition α} (ht : t ∈ ts) :
    ∃ t' ∈ dedupExactTrans ts, sameTrans t' t = true := by
  unfold dedupExactTrans
  rw [← Array.foldl_toList]
  exact exists_rep_foldl_condPush sameTrans
    (fun x => (sameTrans_iff x x).mpr ⟨rfl, hashSetEq_refl _, hashSetEq_refl _, hashSetEq_refl _⟩)
    ts.toList #[] t (Array.mem_toList_iff.mpr ht)

-- `exists_dropImpliedWithin_dominator` generalised to an arbitrary (not necessarily deduplicated) member.
theorem exists_dropImpliedWithin_dominator' (ts : Array (TGBA.Transition α)) (t2 : TGBA.Transition α)
    (ht2 : t2 ∈ ts) :
    ∃ t1 ∈ dropImpliedWithin ts, t1.target = t2.target ∧ hashSetSubset t2.acceptMarks t1.acceptMarks = true ∧
      Cube.litImplies (cubeOf t2) (cubeOf t1) = true := by
  obtain ⟨t2', ht2'mem, ht2'same⟩ := exists_dedupExactTrans_rep ht2
  obtain ⟨ht2'tgt, ht2'marks, ht2'pos, ht2'neg⟩ := (sameTrans_iff t2' t2).mp ht2'same
  obtain ⟨t1, ht1mem, ht1tgt, ht1marks, ht1imp⟩ := exists_dropImpliedWithin_dominator ts t2' ht2'mem
  refine ⟨t1, ht1mem, ht1tgt.trans ht2'tgt, ?_, ?_⟩
  · exact (hashSetSubset_iff _ _).mpr fun a ha =>
      (hashSetSubset_iff _ _).mp ht1marks a (((hashSetEq_iff _ _).mp ht2'marks a).mpr ha)
  · refine Cube.litImplies_trans ?_ ht1imp
    unfold Cube.litImplies cubeOf
    simp only [Bool.and_eq_true]
    exact ⟨(hashSetSubset_iff _ _).mpr fun a ha => ((hashSetEq_iff _ _).mp ht2'pos a).mp ha,
      (hashSetSubset_iff _ _).mpr fun a ha => ((hashSetEq_iff _ _).mp ht2'neg a).mp ha⟩

/-- Every transition of `ts` has a dominator surviving `dropImpliedTrans`. -/
theorem exists_dropImpliedTrans_dominator' (ts : Array (TGBA.Transition α)) (t2 : TGBA.Transition α)
    (ht2 : t2 ∈ ts) :
    ∃ t1 ∈ dropImpliedTrans ts, t1.target = t2.target ∧ hashSetSubset t2.acceptMarks t1.acceptMarks = true ∧
      Cube.litImplies (cubeOf t2) (cubeOf t1) = true := by
  obtain ⟨g, hg, ht2g⟩ := mem_targetGroups.mp ht2
  obtain ⟨t1, ht1mem, hrest⟩ := exists_dropImpliedWithin_dominator' g.toArray t2 (List.mem_toArray.mpr ht2g)
  refine ⟨t1, ?_, hrest⟩
  unfold dropImpliedTrans
  rw [List.mem_toArray, List.mem_flatMap]
  exact ⟨g, hg, Array.mem_toList_iff.mpr ht1mem⟩

/-- `[GO01]` §6 rule 2: implied-transition removal preserves the accepted language. -/
theorem dropImpliedAll_correct (tgba : TGBA α) (hwf : tgba.WellFormed) (ξ : OmegaWord α) :
    tgba.toSpec.accepts ξ ↔ (dropImpliedAll tgba).toSpec.accepts ξ := by
  have hinit : (dropImpliedAll tgba).initialStates = tgba.initialStates := rfl
  have hsucc : ∀ q ∈ tgba.states.toList, (dropImpliedAll tgba).getSuccessors q =
      dropImpliedTrans (tgba.getSuccessors q) := fun _ hq => dropImpliedAll_getSuccessors tgba hq
  constructor
  · rintro ⟨σ, hrun, hcompat, hacc⟩
    have hstate_mem : ∀ n, tgba.states.contains (σ n).1 = true := by
      intro n
      induction n with
      | zero => exact hwf.initial_mem _ hrun.1
      | succ n ih =>
        have hlink : (σ n).2.target = (σ (n + 1)).1 := (hrun.2 n).2
        rw [← hlink]
        exact hwf.succ_mem _ _ ih (hrun.2 n).1
    obtain ⟨rep, hrep⟩ := Classical.axiomOfChoice fun n =>
      exists_dropImpliedTrans_dominator' (tgba.getSuccessors (σ n).1) (σ n).2 (hrun.2 n).1
    obtain ⟨hrepmem, hrep⟩ := forall_and.mp hrep
    obtain ⟨hreptgt, hrep⟩ := forall_and.mp hrep
    obtain ⟨hrepmarks, hrepimp⟩ := forall_and.mp hrep
    refine ⟨fun n => ⟨(σ n).1, rep n⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · show (dropImpliedAll tgba).initialStates.contains (σ 0).1
      rw [hinit]; exact hrun.1
    · intro n
      have hqmem : (σ n).1 ∈ tgba.states.toList :=
        Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr (hstate_mem n))
      refine ⟨?_, (hreptgt n).trans (hrun.2 n).2⟩
      show rep n ∈ (dropImpliedAll tgba).getSuccessors (σ n).1
      rw [hsucc _ hqmem]
      exact hrepmem n
    · intro n
      show (cubeOf (rep n)).sat (ξ n)
      exact Cube.sat_of_litImplies (hrepimp n) _ (hcompat n)
    · intro i N
      obtain ⟨j, hj⟩ := hacc i N
      refine ⟨j, ?_⟩
      show (rep (N + j)).acceptMarks.contains i.val = true
      exact (hashSetSubset_iff _ _).mp (hrepmarks (N + j)) i.val hj
  · rintro ⟨σ, hrun, hcompat, hacc⟩
    refine ⟨σ, ⟨?_, ?_⟩, hcompat, hacc⟩
    · show tgba.isInitial (σ 0).1
      have h0 : (dropImpliedAll tgba).initialStates.contains (σ 0).1 := hrun.1
      rwa [hinit] at h0
    · intro n
      have hvalidn : (σ n).2 ∈ (dropImpliedAll tgba).getSuccessors (σ n).1 := (hrun.2 n).1
      refine ⟨?_, (hrun.2 n).2⟩
      by_cases hq : (σ n).1 ∈ tgba.states.toList
      · rw [hsucc _ hq] at hvalidn
        exact mem_dropImpliedTrans_of_mem hvalidn
      · have hempty : (dropImpliedAll tgba).getSuccessors (σ n).1 = #[] := by
          unfold TGBA.getSuccessors dropImpliedAll
          rw [getElem?_foldl_insert_of_not_mem _ (σ n).1 tgba.states.toList
            (Std.HashMap.emptyWithCapacity tgba.states.size) hq]
          simp
        rw [hempty] at hvalidn
        exact absurd hvalidn (by simp)

end DropImpliedAllCorrect

/-! ## State merge -/


/-- Same target, marks and label. -/
def matchTrans (t1 t2 : TGBA.Transition α) : Bool :=
  t1.target == t2.target && hashSetEq t1.acceptMarks t2.acceptMarks &&
  hashSetEq t1.positiveProps t2.positiveProps && hashSetEq t1.negativeProps t2.negativeProps

/-- Same target and label, marks ignored. -/
def matchLabelTarget (t1 t2 : TGBA.Transition α) : Bool :=
  t1.target == t2.target && hashSetEq t1.positiveProps t2.positiveProps && hashSetEq t1.negativeProps t2.negativeProps

/-- Two states have the same outgoing transitions as sets, matched by target, marks and label in both directions. -/
def sameOutgoing (ts1 ts2 : Array (TGBA.Transition α)) : Bool :=
  ts1.size == ts2.size &&
  ts1.all (fun t1 => ts2.any (matchTrans t1 ·)) &&
  ts2.all (fun t2 => ts1.any (matchTrans · t2))

/-- Two states have the same outgoing transitions up to marks, as sets. -/
def sameLabelsTargets (ts1 ts2 : Array (TGBA.Transition α)) : Bool :=
  ts1.all (fun t1 => ts2.any (matchLabelTarget t1 ·)) && ts2.all (fun t2 => ts1.any (matchLabelTarget · t2))

/-- An order-independent hash of a set, the sum of its members' hashes. -/
def setSig {β : Type w} [BEq β] [Hashable β] (s : Std.HashSet β) : UInt64 := s.fold (fun acc a => acc + hash a) 0

/-- An order- and duplicate-independent hash of a state's outgoing (target, label) pairs, equal for any two states
`sameOutgoing` or `sameLabelsTargets` relates. -/
def outSig (ts : Array (TGBA.Transition α)) : UInt64 :=
  setSig (Std.HashSet.ofList (ts.toList.map fun t =>
    mixHash (hash t.target) (mixHash (setSig t.positiveProps) (setSig t.negativeProps))))

/-- No cycle passes through `q`: every enumerated set containing it is a singleton, and it has no self-loop. -/
def isTransient (tgba : TGBA α) (sccs : Array (Std.HashSet Nat)) (idx : Std.HashMap Nat (List Nat)) (q : Nat) : Bool :=
  !(tgba.succStates q).contains q &&
    (idx.getD q []).all fun i => decide ((sccs.getD i (Std.HashSet.emptyWithCapacity 0)).size ≤ 1)

/-- The order states are processed in: states on a cycle first, then transient ones, each by number. -/
def mergeKey (N : Nat) (transient : Nat → Bool) (q : Nat) : Nat := if transient q then N + q else q

/-- `q` may be merged into `r`: the same outgoing transitions, or the same up to marks when `q` lies on no cycle. -/
def mergeCond (tgba : TGBA α) (transient : Nat → Bool) (q r : Nat) : Bool :=
  sameOutgoing (tgba.getSuccessors q) (tgba.getSuccessors r) ||
    (transient q && sameLabelsTargets (tgba.getSuccessors q) (tgba.getSuccessors r))

/-- One step of the redirect fold: redirect `q` to the first of its candidates processed before it, not itself
redirected, and satisfying `cond`. -/
def redirectStep (key : Nat → Nat) (cands : Nat → List Nat) (cond : Nat → Nat → Bool) (acc : Std.HashMap Nat Nat)
    (q : Nat) : Std.HashMap Nat Nat :=
  match (cands q).find? fun r => key r < key q && !acc.contains r && cond q r with
  | some r => acc.insert q r
  | none => acc

/-- `tgba` with every state of `ids` replaced by its representative `redirect.getD q q`. -/
@[expose] def redirectTGBA (tgba : TGBA α) (ids : List Nat) (redirect : Std.HashMap Nat Nat) : TGBA α :=
  let kept := ids.filter fun q => !redirect.contains q
  { states := Std.HashSet.ofList kept
    initialStates := Std.HashSet.ofList (tgba.initialStates.toList.map fun q => redirect.getD q q)
    successors := kept.foldl (fun m q =>
      m.insert q ((tgba.getSuccessors q).map fun t => { t with target := redirect.getD t.target t.target }))
      (Std.HashMap.emptyWithCapacity kept.length)
    numAcceptSets := tgba.numAcceptSets }

/-- State merging: merge every state into an earlier state with the same outgoing transitions, or the same up to marks
when it lies on no cycle, `[GO01]` §6 with `[LTL2BA-1.3]`'s SCC relaxation. -/
def mergeEquivalentStates (tgba : TGBA α) : TGBA α :=
  let sccs := tgbaSCCs tgba
  let transientSet := Std.HashSet.ofList (tgba.states.toList.filter (isTransient tgba sccs (sccIndex sccs)))
  let transient (q : Nat) : Bool := transientSet.contains q
  let key := mergeKey (tgba.states.toList.foldl max 0 + 1) transient
  let ids := tgba.states.toList.mergeSort fun a b => key a ≤ key b
  let sigs := ids.foldl (fun (m : Std.HashMap Nat UInt64) q => m.insert q (outSig (tgba.getSuccessors q)))
    (Std.HashMap.emptyWithCapacity ids.length)
  let bySig := groupByKey (fun q => sigs.getD q 0) ids
  let redirect := ids.foldl (redirectStep key (fun q => bySig.getD (sigs.getD q 0) []) (mergeCond tgba transient))
    (Std.HashMap.emptyWithCapacity ids.length)
  if redirect.isEmpty then tgba else redirectTGBA tgba ids redirect

/-- The `FinSet` of a `Std.HashSet` built by `ofList` is the source list's `FinSet`. -/
theorem toList_toFinSet_ofList {β} [BEq β] [Hashable β] [LawfulBEq β] [LawfulHashable β] [DecidableEq β]
    (l : List β) : (Std.HashSet.ofList l).toList.toFinSet = l.toFinSet := by
  ext x
  simp only [List.mem_toFinSet]
  rw [Std.HashSet.mem_toList, Std.HashSet.mem_ofList, List.contains_iff_mem]

theorem redirectTGBA_states (tgba : TGBA α) (ids : List Nat) (redirect : Std.HashMap Nat Nat) :
    (redirectTGBA tgba ids redirect).states = Std.HashSet.ofList (ids.filter fun q => !redirect.contains q) := rfl

theorem redirectTGBA_getSuccessors (tgba : TGBA α) (ids : List Nat) (redirect : Std.HashMap Nat Nat)
    (hnd : ids.Nodup) (q : Nat) :
    (redirectTGBA tgba ids redirect).getSuccessors q = if q ∈ ids.filter (fun q => !redirect.contains q) then
      (tgba.getSuccessors q).map fun t => { t with target := redirect.getD t.target t.target } else #[] := by
  have hkeptnd : (ids.filter fun q => !redirect.contains q).Nodup := hnd.sublist List.filter_sublist
  unfold TGBA.getSuccessors
  show ((ids.filter fun q => !redirect.contains q).foldl (fun m q =>
      m.insert q ((tgba.getSuccessors q).map fun t => { t with target := redirect.getD t.target t.target }))
      (Std.HashMap.emptyWithCapacity _))[q]?.getD #[] = _
  split
  · rename_i hq
    rw [getElem?_foldl_insert_of_mem _ q _ hkeptnd hq]
    rfl
  · rename_i hq
    rw [getElem?_foldl_insert_of_not_mem _ q _ _ hq]
    simp

/-- A redirect never increases the measure. -/
theorem measureTGBA_redirectTGBA_le (tgba : TGBA α) (ids : List Nat) (redirect : Std.HashMap Nat Nat)
    (hperm : ids.Perm tgba.states.toList) : measureTGBA (redirectTGBA tgba ids redirect) ≤ measureTGBA tgba := by
  set kept := ids.filter fun q => !redirect.contains q with hkept
  have hnd : tgba.states.toList.Nodup := states_toList_nodup tgba
  have hidsnd : ids.Nodup := (List.Perm.nodup_iff hperm).mpr hnd
  have hkeptnd : kept.Nodup := hidsnd.sublist List.filter_sublist
  have hidsFinSet : ids.toFinSet = tgba.states.toList.toFinSet := by
    ext x; simp [List.mem_toFinSet, hperm.mem_iff]
  have hkeptSub : kept.toFinSet ⊆ tgba.states.toList.toFinSet := by
    rw [hkept, List.toFinSet_filter, ← hidsFinSet]
    exact FinSet.filter_subset _ _
  have hresultFinSet : (redirectTGBA tgba ids redirect).states.toList.toFinSet = kept.toFinSet := by
    rw [redirectTGBA_states]; exact toList_toFinSet_ofList kept
  have hgs : ∀ q ∈ kept.toFinSet,
      transWeight ((redirectTGBA tgba ids redirect).getSuccessors q) = transWeight (tgba.getSuccessors q) := by
    intro q hq
    rw [List.mem_toFinSet] at hq
    rw [redirectTGBA_getSuccessors tgba ids redirect hidsnd, if_pos hq]
    exact transWeight_map_marks_eq
      (f := fun t => { t with target := redirect.getD t.target t.target }) (fun _ => rfl) _
  unfold measureTGBA
  rw [hresultFinSet, FinSet.sum_congr rfl hgs, redirectTGBA_states]
  calc (Std.HashSet.ofList kept).size + ∑ q ∈ kept.toFinSet, transWeight (tgba.getSuccessors q)
      ≤ kept.length + ∑ q ∈ kept.toFinSet, transWeight (tgba.getSuccessors q) :=
        Nat.add_le_add_right Std.HashSet.size_ofList_le _
    _ = kept.toFinSet.card + ∑ q ∈ kept.toFinSet, transWeight (tgba.getSuccessors q) := by
        rw [List.toFinSet_card_of_nodup hkeptnd]
    _ ≤ tgba.states.toList.toFinSet.card + ∑ q ∈ tgba.states.toList.toFinSet, transWeight (tgba.getSuccessors q) :=
        Nat.add_le_add (FinSet.card_le_card hkeptSub) (FinSet.sum_le_sum_of_subset hkeptSub)
    _ = tgba.states.size + ∑ q ∈ tgba.states.toList.toFinSet, transWeight (tgba.getSuccessors q) := by
        rw [List.toFinSet_card_of_nodup hnd, Std.HashSet.length_toList]

/-- State merging never increases the measure. -/
theorem measureTGBA_mergeEquivalentStates_le (tgba : TGBA α) :
    measureTGBA (mergeEquivalentStates tgba) ≤ measureTGBA tgba := by
  have key : ∀ (ids : List Nat) (redirect : Std.HashMap Nat Nat), ids.Perm tgba.states.toList →
      measureTGBA (if redirect.isEmpty then tgba else redirectTGBA tgba ids redirect) ≤ measureTGBA tgba := by
    intro ids redirect hperm
    split
    · exact Nat.le_refl _
    · exact measureTGBA_redirectTGBA_le _ _ _ hperm
  exact key _ _ (List.mergeSort_perm _ _)

/-! ## State merge correctness -/

/-- `matchTrans` bridged to pointwise agreement. -/
theorem matchTrans_iff (t1 t2 : TGBA.Transition α) :
    matchTrans t1 t2 = true ↔ t1.target = t2.target ∧ hashSetEq t1.acceptMarks t2.acceptMarks = true ∧
      hashSetEq t1.positiveProps t2.positiveProps = true ∧ hashSetEq t1.negativeProps t2.negativeProps = true := by
  unfold matchTrans
  constructor
  · intro h; simp only [Bool.and_eq_true, beq_iff_eq] at h; grind
  · rintro ⟨h1, h2, h3, h4⟩; simp [h1, h2, h3, h4]

theorem matchLabelTarget_iff (t1 t2 : TGBA.Transition α) :
    matchLabelTarget t1 t2 = true ↔ t1.target = t2.target ∧
      hashSetEq t1.positiveProps t2.positiveProps = true ∧ hashSetEq t1.negativeProps t2.negativeProps = true := by
  unfold matchLabelTarget
  constructor
  · intro h; simp only [Bool.and_eq_true, beq_iff_eq] at h; grind
  · rintro ⟨h1, h2, h3⟩; simp [h1, h2, h3]

/-- `sameOutgoing` bridged to bidirectional pointwise coverage. -/
theorem sameOutgoing_iff (ts1 ts2 : Array (TGBA.Transition α)) :
    sameOutgoing ts1 ts2 = true ↔ ts1.size = ts2.size ∧
      (∀ t1 ∈ ts1, ∃ t2 ∈ ts2, matchTrans t1 t2 = true) ∧
      (∀ t2 ∈ ts2, ∃ t1 ∈ ts1, matchTrans t1 t2 = true) := by
  unfold sameOutgoing
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', Array.any_eq_true']
  grind

theorem sameLabelsTargets_iff (ts1 ts2 : Array (TGBA.Transition α)) :
    sameLabelsTargets ts1 ts2 = true ↔
      (∀ t1 ∈ ts1, ∃ t2 ∈ ts2, matchLabelTarget t1 t2 = true) ∧
      (∀ t2 ∈ ts2, ∃ t1 ∈ ts1, matchLabelTarget t1 t2 = true) := by
  unfold sameLabelsTargets
  simp only [Bool.and_eq_true, Array.all_eq_true', Array.any_eq_true']

/-- A `redirectStep` at `q` leaves every other key's membership unchanged. -/
theorem redirectStep_contains_of_ne (key : Nat → Nat) (cands : Nat → List Nat) (cond : Nat → Nat → Bool)
    (acc : Std.HashMap Nat Nat) (q x : Nat) (hne : q ≠ x) :
    (redirectStep key cands cond acc q).contains x = acc.contains x := by
  simp only [redirectStep]
  cases (cands q).find? fun r => key r < key q && !acc.contains r && cond q r with
  | none => rfl
  | some r => simp [Std.HashMap.contains_insert, beq_iff_eq, hne]

/-- Along a `redirectStep` fold over a suffix of the key-sorted `ids`, redirect targets stay strictly earlier in key
order, are never redirected themselves, lie in `ids` and satisfy `cond`, which rules out redirect chains. -/
theorem redirect_isRoot_of_suffix (ids : List Nat) (key : Nat → Nat) (cands : Nat → List Nat)
    (cond : Nat → Nat → Bool) (hinj : ∀ a ∈ ids, ∀ b ∈ ids, key a = key b → a = b)
    (hcands : ∀ q, ∀ r ∈ cands q, r ∈ ids) :
    ∀ (suf : List Nat), suf.Nodup → suf.Pairwise (fun a b => key a ≤ key b) → suf <:+ ids →
      ∀ (acc : Std.HashMap Nat Nat),
        (∀ x, acc.contains x → ∀ y ∈ suf, key x < key y) →
        (∀ x, acc.contains x → key (acc.getD x x) < key x) →
        (∀ x, acc.contains x → !acc.contains (acc.getD x x)) →
        (∀ x, acc.contains x → acc.getD x x ∈ ids) →
        (∀ x, acc.contains x → cond x (acc.getD x x) = true) →
        ∀ x, (suf.foldl (redirectStep key cands cond) acc).contains x →
          key ((suf.foldl (redirectStep key cands cond) acc).getD x x) < key x ∧
          !(suf.foldl (redirectStep key cands cond) acc).contains
            ((suf.foldl (redirectStep key cands cond) acc).getD x x) ∧
          (suf.foldl (redirectStep key cands cond) acc).getD x x ∈ ids ∧
          cond x ((suf.foldl (redirectStep key cands cond) acc).getD x x) = true := by
  intro suf
  induction suf with
  | nil => intro _ _ _ acc _ hJ2 hJ3 hJ4 hJ5 x hx; exact ⟨hJ2 x hx, hJ3 x hx, hJ4 x hx, hJ5 x hx⟩
  | cons q rest ih =>
    intro hnd hsorted hsuf acc hJ1 hJ2 hJ3 hJ4 hJ5
    rw [List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hsorted
    have hrestsuf : rest <:+ ids := (List.suffix_cons q rest).trans hsuf
    have hqids : q ∈ ids := hsuf.subset List.mem_cons_self
    have hqlt : ∀ y ∈ rest, key q < key y := by
      intro y hy
      have hle := hsorted.1 y hy
      have hne : key q ≠ key y := fun heq =>
        hnd.1 (by rw [hinj q hqids y (hrestsuf.subset hy) heq]; exact hy)
      omega
    have hneq : ∀ x, key x < key q → (q == x) = false := by
      intro x hx
      rcases hb : (q == x) with _ | _
      · rfl
      · exact absurd (congrArg key (beq_iff_eq.mp hb)).symm (Nat.ne_of_lt hx)
    rw [List.foldl_cons]
    rcases hf : (cands q).find? (fun s => key s < key q && !acc.contains s && cond q s) with _ | r
    · have hstep : redirectStep key cands cond acc q = acc := by unfold redirectStep; rw [hf]
      rw [hstep]
      exact ih hnd.2 hsorted.2 hrestsuf acc
        (fun x hx y hy => hJ1 x hx y (List.mem_cons_of_mem q hy)) hJ2 hJ3 hJ4 hJ5
    · have hstep : redirectStep key cands cond acc q = acc.insert q r := by unfold redirectStep; rw [hf]
      have hspec := List.find?_some hf
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hspec
      obtain ⟨⟨hrq, hrnc⟩, hrcond⟩ := hspec
      have hrmem : r ∈ ids := hcands q r (List.mem_of_find?_eq_some hf)
      rw [hstep]
      apply ih hnd.2 hsorted.2 hrestsuf (acc.insert q r)
      · intro x hx y hy
        rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
        rcases hx with hxq | hxacc
        · subst hxq; exact hqlt y hy
        · exact hJ1 x hxacc y (List.mem_cons_of_mem q hy)
      · intro x hx
        rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
        rcases hx with hxq | hxacc
        · subst hxq; rw [Std.HashMap.getD_insert_self]; exact hrq
        · simp [Std.HashMap.getD_insert, hneq x (hJ1 x hxacc q List.mem_cons_self)]
          exact hJ2 x hxacc
      · intro x hx
        rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
        rcases hx with hxq | hxacc
        · subst hxq
          rw [Std.HashMap.getD_insert_self, Std.HashMap.contains_insert, Bool.not_eq_true',
            Bool.or_eq_false_iff, hneq r hrq]
          exact ⟨rfl, hrnc⟩
        · have hxltq : key x < key q := hJ1 x hxacc q List.mem_cons_self
          simp only [Std.HashMap.getD_insert, hneq x hxltq, Bool.false_eq_true, if_false]
          rw [Std.HashMap.contains_insert, Bool.not_eq_true', Bool.or_eq_false_iff,
            hneq _ (Nat.lt_trans (hJ2 x hxacc) hxltq)]
          exact ⟨rfl, by simpa using hJ3 x hxacc⟩
      · intro x hx
        rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
        rcases hx with hxq | hxacc
        · subst hxq; rw [Std.HashMap.getD_insert_self]; exact hrmem
        · simp [Std.HashMap.getD_insert, hneq x (hJ1 x hxacc q List.mem_cons_self)]
          exact hJ4 x hxacc
      · intro x hx
        rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
        rcases hx with hxq | hxacc
        · subst hxq; rw [Std.HashMap.getD_insert_self]; exact hrcond
        · simp [Std.HashMap.getD_insert, hneq x (hJ1 x hxacc q List.mem_cons_self)]
          exact hJ5 x hxacc

theorem le_foldl_max (l : List Nat) (init : Nat) : init ≤ l.foldl max init ∧ ∀ x ∈ l, x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih (max init a)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 x hx

/-- `mergeKey` is injective below its offset. -/
theorem mergeKey_inj (N : Nat) (transient : Nat → Bool) {a b : Nat} (ha : a < N) (hb : b < N)
    (h : mergeKey N transient a = mergeKey N transient b) : a = b := by
  unfold mergeKey at h
  split at h <;> split at h <;> omega

/-- Two members of a hash set of size at most one are equal. -/
theorem eq_of_mem_of_size_le_one {s : Std.HashSet Nat} (h : s.size ≤ 1) {a b : Nat} (ha : a ∈ s) (hb : b ∈ s) :
    a = b := by
  have ha' := Std.HashSet.mem_toList.mpr ha
  have hb' := Std.HashSet.mem_toList.mpr hb
  rw [← Std.HashSet.length_toList] at h
  generalize s.toList = l at h ha' hb'
  match l with
  | [] => simp at ha'
  | [x] => rw [List.mem_singleton] at ha' hb'; rw [ha', hb']
  | _ :: _ :: _ => simp at h

/-- A transient state lies on no cycle: a path leaving it never returns. -/
theorem not_reach_of_isTransient (tgba : TGBA α) (hwf : tgba.WellFormed) {q p : Nat}
    (hq : tgba.states.contains q = true) (ht : isTransient tgba (tgbaSCCs tgba) (sccIndex (tgbaSCCs tgba)) q = true)
    (hp : p ∈ tgba.succStates q)
    (hpq : (reachableFrom (fun r => (tgba.succStates r).toList) [p] tgba.states.toList).contains q = true) : False := by
  unfold isTransient at ht
  rw [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at ht
  obtain ⟨hnoloop, hsing⟩ := ht
  have hpne : p ≠ q := by
    rintro rfl
    rw [Array.contains_iff_mem.mpr hp] at hnoloop
    exact Bool.noConfusion hnoloop
  have hpstate : tgba.states.contains p = true := by
    obtain ⟨tr, htr, hteq⟩ := Array.mem_map.mp (by simpa [TGBA.succStates] using hp)
    rw [← hteq]; exact hwf.succ_mem q tr hq htr
  have hself := self_mem_reachableFrom (fun r => (tgba.succStates r).toList) q tgba.states.toList
  have hpS : p ∈ trueSCC tgba q := (mem_trueSCC tgba).mpr ⟨hpstate, tgba_reach_step tgba hwf hq hself hp, hpq⟩
  have hqS : q ∈ trueSCC tgba q := (mem_trueSCC tgba).mpr ⟨hq, hself, hself⟩
  obtain ⟨C, hC, hsub⟩ := (tgbaSCCs_sound tgba hwf).2.2 (trueSCC tgba q) ⟨q, hqS⟩
    (trueSCC_internallyConnected tgba hwf hq)
    (fun s hs => Reachable.base (Std.HashSet.mem_toList.mpr
      (Std.HashSet.mem_iff_contains.mpr ((mem_trueSCC tgba).mp hs).1)))
  rw [Array.mem_toList_iff] at hC
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hC
  have hget : (tgbaSCCs tgba).getD i (Std.HashSet.emptyWithCapacity 0) = (tgbaSCCs tgba)[i] := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  have hidx : i ∈ (sccIndex (tgbaSCCs tgba)).getD q [] :=
    (mem_sccIndex _ q i).mpr ⟨hi, by rw [hget]; exact hsub q hqS⟩
  have hsize := of_decide_eq_true (hsing i hidx)
  rw [hget] at hsize
  exact hpne (eq_of_mem_of_size_le_one hsize (hsub p hpS) (hsub q hqS))

/-- An infinite path visits transient states only finitely often, each at most once. -/
theorem eventually_not_transient (tgba : TGBA α) (hwf : tgba.WellFormed) (s : Nat → Nat)
    (hmem : ∀ n, tgba.states.contains (s n) = true) (hsucc : ∀ n, s (n + 1) ∈ tgba.succStates (s n)) :
    ∃ M, ∀ n, M ≤ n → isTransient tgba (tgbaSCCs tgba) (sccIndex (tgbaSCCs tgba)) (s n) = false := by
  set T : Nat → Prop := fun n => isTransient tgba (tgbaSCCs tgba) (sccIndex (tgbaSCCs tgba)) (s n) = true with hT
  have hreach : ∀ n k, n + 1 ≤ k →
      (reachableFrom (fun r => (tgba.succStates r).toList) [s (n + 1)] tgba.states.toList).contains (s k) = true := by
    intro n k hk
    induction k, hk using Nat.le_induction with
    | base => exact self_mem_reachableFrom _ _ _
    | succ k _ ih => exact tgba_reach_step tgba hwf (hmem (n + 1)) ih (hsucc k)
  have hinj : ∀ n, T n → ∀ m, T m → s n = s m → n = m := by
    intro n hn m hm heq
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact not_reach_of_isTransient tgba hwf (hmem n) hn (hsucc n) (heq ▸ hreach n m hlt)
    · exact not_reach_of_isTransient tgba hwf (hmem m) hm (hsucc m) (heq ▸ hreach m n hlt)
  have himg : FinitePred fun b => ∃ n, T n ∧ s n = b := by
    refine FinitePred.subset (FinSet.finite tgba.states.toList.toFinSet) ?_
    rintro _ ⟨n, -, rfl⟩
    simp only [List.mem_toFinSet, Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]
    exact hmem n
  obtain ⟨M, hM⟩ := FinitePred.nat_iff.mp (FinitePred.of_finite_image himg hinj)
  refine ⟨M, fun n hn => ?_⟩
  by_contra h
  have : n < M := hM n (by simpa [hT] using h)
  omega

/-- A property holding infinitely often carries over to one it implies from some point on. -/
theorem infOften_of_eventually_imp {P Q : Nat → Prop} (M : Nat) (himp : ∀ n, M ≤ n → P n → Q n)
    (h : ∀ N, ∃ j, P (N + j)) : ∀ N, ∃ j, Q (N + j) := by
  intro N
  obtain ⟨j, hj⟩ := h (N + M)
  exact ⟨M + j, by rw [← Nat.add_assoc]; exact himp _ (by omega) hj⟩

section MergeEquivalentStatesCorrect
variable [LawfulBEq α] [LawfulHashable α]

/-- `sameOutgoing` is reflexive. -/
theorem sameOutgoing_refl (ts : Array (TGBA.Transition α)) : sameOutgoing ts ts = true := by
  rw [sameOutgoing_iff]
  refine ⟨rfl, fun t ht => ⟨t, ht, ?_⟩, fun t ht => ⟨t, ht, ?_⟩⟩ <;>
    exact (matchTrans_iff t t).mpr ⟨rfl, hashSetEq_refl _, hashSetEq_refl _, hashSetEq_refl _⟩

/-- Merging every state into a representative preserves the language, when the transitions of a state and of its
representative match both ways, with marks allowed to differ only at states every infinite path leaves for good. -/
theorem redirectTGBA_spec (tgba : TGBA α) (hwf : tgba.WellFormed) (ids : List Nat) (redirect : Std.HashMap Nat Nat)
    (transient : Nat → Bool) (hperm : ids.Perm tgba.states.toList)
    (hroot : ∀ q ∈ ids, (!redirect.contains (redirect.getD q q)) = true ∧ redirect.getD q q ∈ ids)
    (hfwd : ∀ q ∈ ids, ∀ t ∈ tgba.getSuccessors q, ∃ t' ∈ tgba.getSuccessors (redirect.getD q q),
      matchLabelTarget t t' = true ∧ (transient q = false → hashSetEq t.acceptMarks t'.acceptMarks = true))
    (hbwd : ∀ q ∈ ids, ∀ t' ∈ tgba.getSuccessors (redirect.getD q q), ∃ t ∈ tgba.getSuccessors q,
      matchLabelTarget t t' = true ∧ (transient q = false → hashSetEq t.acceptMarks t'.acceptMarks = true))
    (hfin : ∀ s : Nat → Nat, (∀ n, tgba.states.contains (s n) = true) → (∀ n, s (n + 1) ∈ tgba.succStates (s n)) →
      ∃ M, ∀ n, M ≤ n → transient (s n) = false) :
    (redirectTGBA tgba ids redirect).WellFormed ∧
      ((redirectTGBA tgba ids redirect).numAcceptSets = tgba.numAcceptSets ∧
        ∀ q t, t ∈ (redirectTGBA tgba ids redirect).getSuccessors q →
          ∃ q', ∃ t' ∈ tgba.getSuccessors q', t.acceptMarks = t'.acceptMarks) ∧
      ∀ ξ : OmegaWord α, tgba.toSpec.accepts ξ ↔ (redirectTGBA tgba ids redirect).toSpec.accepts ξ := by
  set kept := ids.filter fun q => !redirect.contains q with hkept
  set result := redirectTGBA tgba ids redirect with hresult
  have hnd : tgba.states.toList.Nodup := states_toList_nodup tgba
  have hidsnd : ids.Nodup := (List.Perm.nodup_iff hperm).mpr hnd
  have hidsstates : ∀ q, q ∈ ids ↔ tgba.states.contains q := by
    intro q; rw [hperm.mem_iff, Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]
  have hkeptMem : ∀ q ∈ ids, redirect.getD q q ∈ kept := fun q hq =>
    List.mem_filter.mpr ⟨(hroot q hq).2, (hroot q hq).1⟩
  have hsucc : ∀ q ∈ kept, result.getSuccessors q =
      (tgba.getSuccessors q).map fun t => { t with target := redirect.getD t.target t.target } := by
    intro q hq
    rw [hresult, redirectTGBA_getSuccessors tgba ids redirect hidsnd, if_pos hq]
  have hinitIff : ∀ q, result.initialStates.contains q ↔
      ∃ q0 ∈ tgba.initialStates.toList, redirect.getD q0 q0 = q := by
    intro q
    show (Std.HashSet.ofList (tgba.initialStates.toList.map fun q0 => redirect.getD q0 q0)).contains q = true ↔ _
    rw [Std.HashSet.contains_iff_mem, Std.HashSet.mem_ofList, List.contains_iff_mem, List.mem_map]
  have hkeptStates : ∀ q ∈ kept, tgba.states.contains q = true :=
    fun q hq => (hidsstates q).mp (List.filter_sublist.subset hq)
  have hresStates : ∀ q, result.states.contains q = true ↔ q ∈ kept := by
    intro q
    rw [hresult, redirectTGBA_states, Std.HashSet.contains_ofList, List.contains_iff_mem]
  have hsuccStates : ∀ q t, tgba.states.contains q = true → t ∈ tgba.getSuccessors q →
      t.target ∈ tgba.succStates q := fun q t _ ht => Array.mem_map.mpr ⟨t, ht, rfl⟩
  refine ⟨⟨fun q hq => ?_, fun q t hq ht => ?_, fun q t hq ht m hm => ?_⟩, ⟨rfl, fun q t ht => ?_⟩,
    fun ξ => ?_⟩
  · obtain ⟨q0, hq0mem, rfl⟩ := (hinitIff q).mp hq
    have hq0init : tgba.isInitial q0 = true :=
      Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hq0mem)
    exact (hresStates _).mpr (hkeptMem q0 ((hidsstates q0).mpr (hwf.initial_mem q0 hq0init)))
  · have hqk := (hresStates q).mp hq
    rw [hsucc q hqk] at ht
    obtain ⟨v, hvmem, rfl⟩ := Array.mem_map.mp ht
    exact (hresStates _).mpr
      (hkeptMem v.target ((hidsstates _).mpr (hwf.succ_mem q v (hkeptStates q hqk) hvmem)))
  · have hqk := (hresStates q).mp hq
    rw [hsucc q hqk] at ht
    obtain ⟨v, hvmem, rfl⟩ := Array.mem_map.mp ht
    exact hwf.marks_range q v (hkeptStates q hqk) hvmem m hm
  · by_cases hqk : q ∈ kept
    · rw [hsucc q hqk] at ht
      obtain ⟨v, hvmem, rfl⟩ := Array.mem_map.mp ht
      exact ⟨q, v, hvmem, rfl⟩
    · rw [hresult, redirectTGBA_getSuccessors tgba ids redirect hidsnd, if_neg hqk] at ht
      exact absurd ht (by simp)
  constructor
  · rintro ⟨σ, hrun, hcompat, hacc⟩
    have hstateMem : ∀ n, tgba.states.contains (σ n).1 = true := by
      intro n
      induction n with
      | zero => exact hwf.initial_mem _ hrun.1
      | succ n ih =>
        have hlink : (σ n).2.target = (σ (n + 1)).1 := (hrun.2 n).2
        rw [← hlink]
        exact hwf.succ_mem _ _ ih (hrun.2 n).1
    have hidmem : ∀ n, (σ n).1 ∈ ids := fun n => (hidsstates _).mpr (hstateMem n)
    obtain ⟨M, hM⟩ := hfin (fun n => (σ n).1) hstateMem fun n => by
      show (σ (n + 1)).1 ∈ tgba.succStates (σ n).1
      rw [← (show (σ n).2.target = (σ (n + 1)).1 from (hrun.2 n).2)]
      exact hsuccStates _ _ (hstateMem n) (hrun.2 n).1
    obtain ⟨t', ht'⟩ := Classical.axiomOfChoice fun n => hfwd (σ n).1 (hidmem n) (σ n).2 (hrun.2 n).1
    obtain ⟨ht'mem, ht'⟩ := forall_and.mp ht'
    obtain ⟨ht'match, ht'marks⟩ := forall_and.mp ht'
    refine ⟨fun n => ⟨redirect.getD (σ n).1 (σ n).1,
      { t' n with target := redirect.getD (t' n).target (t' n).target }⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · show result.initialStates.contains (redirect.getD (σ 0).1 (σ 0).1)
      rw [hinitIff]
      exact ⟨(σ 0).1, Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hrun.1), rfl⟩
    · intro n
      have hq'kept : redirect.getD (σ n).1 (σ n).1 ∈ kept := hkeptMem (σ n).1 (hidmem n)
      have hmatch := (matchLabelTarget_iff (σ n).2 (t' n)).mp (ht'match n)
      refine ⟨?_, ?_⟩
      · show { t' n with target := redirect.getD (t' n).target (t' n).target } ∈
          result.getSuccessors (redirect.getD (σ n).1 (σ n).1)
        rw [hsucc _ hq'kept]
        exact Array.mem_map.mpr ⟨t' n, ht'mem n, rfl⟩
      · show redirect.getD (t' n).target (t' n).target = redirect.getD (σ (n + 1)).1 (σ (n + 1)).1
        rw [show (t' n).target = (σ (n + 1)).1 from hmatch.1.symm.trans (hrun.2 n).2]
    · intro n
      obtain ⟨-, hposeq, hnegeq⟩ := (matchLabelTarget_iff (σ n).2 (t' n)).mp (ht'match n)
      obtain ⟨hpos, hneg⟩ := hcompat n
      refine ⟨?_, ?_⟩
      · exact fun a ha => hpos a (((hashSetEq_iff _ _).mp hposeq a).mpr ha)
      · exact fun a ha => hneg a (((hashSetEq_iff _ _).mp hnegeq a).mpr ha)
    · intro i N
      exact infOften_of_eventually_imp (P := fun n => (σ n).2.acceptMarks.contains i.val = true)
        (Q := fun n => (t' n).acceptMarks.contains i.val = true) M
        (fun n hn hP => ((hashSetEq_iff _ _).mp (ht'marks n (hM n hn)) i.val).mp hP) (hacc i) N
  · rintro ⟨σ', hrun', hcompat', hacc'⟩
    have hstateMem' : ∀ n, (σ' n).1 ∈ kept := by
      intro n
      induction n with
      | zero =>
        obtain ⟨q0, hq0mem, hq0eq⟩ := (hinitIff (σ' 0).1).mp hrun'.1
        rw [← hq0eq]
        exact hkeptMem q0 ((hidsstates q0).mpr
          (hwf.initial_mem q0 (Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hq0mem))))
      | succ n ih =>
        have hvalidn : (σ' n).2 ∈ result.getSuccessors (σ' n).1 := (hrun'.2 n).1
        rw [hsucc _ ih] at hvalidn
        obtain ⟨v, hvmem, hveq⟩ := Array.mem_map.mp hvalidn
        have hlink : (σ' n).2.target = (σ' (n + 1)).1 := (hrun'.2 n).2
        have hqinstates : tgba.states.contains (σ' n).1 = true :=
          (hidsstates _).mp (List.filter_sublist.subset ih)
        have hvtargetids : v.target ∈ ids := (hidsstates _).mpr (hwf.succ_mem _ _ hqinstates hvmem)
        have hveqtarget : redirect.getD v.target v.target = (σ' (n + 1)).1 := by
          rw [← hveq] at hlink; simpa using hlink
        rw [← hveqtarget]
        exact hkeptMem v.target hvtargetids
    have hex : ∀ n q, q ∈ ids → redirect.getD q q = (σ' n).1 →
        ∃ q', q' ∈ ids ∧ redirect.getD q' q' = (σ' (n + 1)).1 ∧
          ∃ t ∈ tgba.getSuccessors q, t.target = q' ∧
            (transient q = false → hashSetEq t.acceptMarks (σ' n).2.acceptMarks = true) ∧
            hashSetEq t.positiveProps (σ' n).2.positiveProps = true ∧
            hashSetEq t.negativeProps (σ' n).2.negativeProps = true := by
      intro n q hqids hqeq
      have hvalidn : (σ' n).2 ∈ result.getSuccessors (σ' n).1 := (hrun'.2 n).1
      rw [hsucc _ (hstateMem' n)] at hvalidn
      obtain ⟨v, hvmem, hveq⟩ := Array.mem_map.mp hvalidn
      rw [← hqeq] at hvmem
      obtain ⟨t, htmem, htmatch, htmarks⟩ := hbwd q hqids v hvmem
      have hmatch := (matchLabelTarget_iff t v).mp htmatch
      have hqinstates : tgba.states.contains q = true := (hidsstates q).mp hqids
      have hmarks : (σ' n).2.acceptMarks = v.acceptMarks := by rw [← hveq]
      have hpos : (σ' n).2.positiveProps = v.positiveProps := by rw [← hveq]
      have hneg : (σ' n).2.negativeProps = v.negativeProps := by rw [← hveq]
      refine ⟨t.target, (hidsstates _).mpr (hwf.succ_mem q t hqinstates htmem), ?_, t, htmem, rfl,
        fun hq => by rw [hmarks]; exact htmarks hq, ?_, ?_⟩
      · rw [hmatch.1]
        have hlink : (σ' n).2.target = (σ' (n + 1)).1 := (hrun'.2 n).2
        rw [← hveq] at hlink
        simpa using hlink
      · rw [hpos]; exact hmatch.2.1
      · rw [hneg]; exact hmatch.2.2
    obtain ⟨q0, hq0init, hq0ids, hq0eq⟩ :
        ∃ q0, tgba.isInitial q0 = true ∧ q0 ∈ ids ∧ redirect.getD q0 q0 = (σ' 0).1 := by
      obtain ⟨q0, hq0mem, hq0eq⟩ := (hinitIff (σ' 0).1).mp hrun'.1
      have hq0init : tgba.isInitial q0 = true := Std.HashSet.mem_iff_contains.mp
        (Std.HashSet.mem_toList.mp hq0mem)
      exact ⟨q0, hq0init, (hidsstates q0).mpr (hwf.initial_mem q0 hq0init), hq0eq⟩
    let stepper : ∀ n, {q // q ∈ ids ∧ redirect.getD q q = (σ' n).1} →
        {q // q ∈ ids ∧ redirect.getD q q = (σ' (n + 1)).1} := fun n qq =>
      ⟨(hex n qq.1 qq.2.1 qq.2.2).choose, (hex n qq.1 qq.2.1 qq.2.2).choose_spec.1,
        (hex n qq.1 qq.2.1 qq.2.2).choose_spec.2.1⟩
    let qSeq : ∀ n, {q // q ∈ ids ∧ redirect.getD q q = (σ' n).1} :=
      fun n => Nat.rec ⟨q0, hq0ids, hq0eq⟩ stepper n
    let t : ∀ n, TGBA.Transition α :=
      fun n => (hex n (qSeq n).1 (qSeq n).2.1 (qSeq n).2.2).choose_spec.2.2.choose
    have ht : ∀ n, t n ∈ tgba.getSuccessors (qSeq n).1 :=
      fun n => (hex n (qSeq n).1 (qSeq n).2.1 (qSeq n).2.2).choose_spec.2.2.choose_spec.1
    have httarget : ∀ n, (t n).target = (qSeq (n + 1)).1 :=
      fun n => (hex n (qSeq n).1 (qSeq n).2.1 (qSeq n).2.2).choose_spec.2.2.choose_spec.2.1
    have htmarks : ∀ n, transient (qSeq n).1 = false → hashSetEq (t n).acceptMarks (σ' n).2.acceptMarks = true :=
      fun n => (hex n (qSeq n).1 (qSeq n).2.1 (qSeq n).2.2).choose_spec.2.2.choose_spec.2.2.1
    have htpos : ∀ n, hashSetEq (t n).positiveProps (σ' n).2.positiveProps = true :=
      fun n => (hex n (qSeq n).1 (qSeq n).2.1 (qSeq n).2.2).choose_spec.2.2.choose_spec.2.2.2.1
    have htneg : ∀ n, hashSetEq (t n).negativeProps (σ' n).2.negativeProps = true :=
      fun n => (hex n (qSeq n).1 (qSeq n).2.1 (qSeq n).2.2).choose_spec.2.2.choose_spec.2.2.2.2
    have hqstates : ∀ n, tgba.states.contains (qSeq n).1 = true := fun n => (hidsstates _).mp (qSeq n).2.1
    obtain ⟨M, hM⟩ := hfin (fun n => (qSeq n).1) hqstates fun n => by
      show (qSeq (n + 1)).1 ∈ tgba.succStates (qSeq n).1
      rw [← httarget n]
      exact hsuccStates _ _ (hqstates n) (ht n)
    refine ⟨fun n => ⟨(qSeq n).1, t n⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · show tgba.initialStates.contains (qSeq 0).1 = true
      exact hq0init
    · intro n
      exact ⟨ht n, httarget n⟩
    · intro n
      refine ⟨?_, ?_⟩
      · intro a ha; exact (hcompat' n).1 a (((hashSetEq_iff _ _).mp (htpos n) a).mp ha)
      · intro a ha; exact (hcompat' n).2 a (((hashSetEq_iff _ _).mp (htneg n) a).mp ha)
    · intro i N
      exact infOften_of_eventually_imp (P := fun n => (σ' n).2.acceptMarks.contains i.val = true)
        (Q := fun n => (t n).acceptMarks.contains i.val = true) M
        (fun n hn hP => ((hashSetEq_iff _ _).mp (htmarks n (hM n hn)) i.val).mpr hP) (hacc' i) N

private theorem mergeEquivalentStates_spec (tgba : TGBA α) (hwf : tgba.WellFormed) :
    (mergeEquivalentStates tgba).WellFormed ∧
      ((mergeEquivalentStates tgba).numAcceptSets = tgba.numAcceptSets ∧
        ∀ q t, t ∈ (mergeEquivalentStates tgba).getSuccessors q →
          ∃ q', ∃ t' ∈ tgba.getSuccessors q', t.acceptMarks = t'.acceptMarks) ∧
      ∀ ξ : OmegaWord α, tgba.toSpec.accepts ξ ↔ (mergeEquivalentStates tgba).toSpec.accepts ξ := by
  set transient := fun q => (Std.HashSet.ofList (tgba.states.toList.filter
    (isTransient tgba (tgbaSCCs tgba) (sccIndex (tgbaSCCs tgba))))).contains q with htransient
  set N := tgba.states.toList.foldl max 0 + 1 with hN
  set key := mergeKey N transient with hkey
  set ids := tgba.states.toList.mergeSort (fun a b => key a ≤ key b) with hids
  set sigs := ids.foldl (fun (m : Std.HashMap Nat UInt64) q => m.insert q (outSig (tgba.getSuccessors q)))
    (Std.HashMap.emptyWithCapacity ids.length) with hsigs
  set bySig := groupByKey (fun q => sigs.getD q 0) ids with hbySig
  set redirect := ids.foldl (redirectStep key (fun q => bySig.getD (sigs.getD q 0) []) (mergeCond tgba transient))
    (Std.HashMap.emptyWithCapacity ids.length) with hredirect
  have hdef : mergeEquivalentStates tgba = if redirect.isEmpty then tgba else redirectTGBA tgba ids redirect := rfl
  by_cases hemp : redirect.isEmpty = true
  · rw [hdef, if_pos hemp]
    exact ⟨hwf, ⟨rfl, fun q t ht => ⟨q, t, ht, rfl⟩⟩, fun _ => Iff.rfl⟩
  rw [hdef, if_neg hemp]
  have hperm : ids.Perm tgba.states.toList := List.mergeSort_perm _ _
  have hnd : tgba.states.toList.Nodup := states_toList_nodup tgba
  have hidsnd : ids.Nodup := (List.Perm.nodup_iff hperm).mpr hnd
  have hidsBoolSorted : ids.Pairwise (fun a b => decide (key a ≤ key b) = true) :=
    List.pairwise_mergeSort (by intro a b c hab hbc; simp_all only [decide_eq_true_eq]; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) tgba.states.toList
  have hidssorted : ids.Pairwise (fun a b => key a ≤ key b) := hidsBoolSorted.imp fun h => by simpa using h
  have hidsstates : ∀ q, q ∈ ids ↔ tgba.states.contains q := by
    intro q; rw [hperm.mem_iff, Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]
  have hltN : ∀ q ∈ ids, q < N := fun q hq =>
    Nat.lt_succ_of_le ((le_foldl_max _ 0).2 q (hperm.mem_iff.mp hq))
  have hinj : ∀ a ∈ ids, ∀ b ∈ ids, key a = key b → a = b := fun a ha b hb h =>
    mergeKey_inj N transient (hltN a ha) (hltN b hb) h
  have hrootAux := redirect_isRoot_of_suffix ids key (fun q => bySig.getD (sigs.getD q 0) [])
    (mergeCond tgba transient) hinj (fun q r hr => ((mem_groupByKey _ ids _ r).mp hr).1)
    ids hidsnd hidssorted (List.suffix_refl ids) (Std.HashMap.emptyWithCapacity ids.length)
    (by simp) (by simp) (by simp) (by simp) (by simp)
  have hroot : ∀ q ∈ ids, (!redirect.contains (redirect.getD q q)) = true ∧ redirect.getD q q ∈ ids := by
    intro q hq
    by_cases hc : redirect.contains q = true
    · exact ⟨(hrootAux q hc).2.1, (hrootAux q hc).2.2.1⟩
    · rw [Bool.not_eq_true] at hc
      rw [Std.HashMap.getD_eq_fallback_of_contains_eq_false hc]
      exact ⟨by rw [hc]; rfl, hq⟩
  -- every state's transitions and its representative's match, exactly or, at a transient state, up to marks
  have hcond : ∀ q ∈ ids, sameOutgoing (tgba.getSuccessors q) (tgba.getSuccessors (redirect.getD q q)) = true ∨
      (transient q = true ∧
        sameLabelsTargets (tgba.getSuccessors q) (tgba.getSuccessors (redirect.getD q q)) = true) := by
    intro q hq
    by_cases hc : redirect.contains q = true
    · have h : mergeCond tgba transient q (redirect.getD q q) = true := (hrootAux q hc).2.2.2
      simpa only [mergeCond, Bool.or_eq_true, Bool.and_eq_true] using h
    · rw [Bool.not_eq_true] at hc
      rw [Std.HashMap.getD_eq_fallback_of_contains_eq_false hc]
      exact Or.inl (sameOutgoing_refl _)
  have hlt_of_match : ∀ t1 t2 : TGBA.Transition α, matchTrans t1 t2 = true → matchLabelTarget t1 t2 = true := by
    intro t1 t2 h
    obtain ⟨h1, -, h3, h4⟩ := (matchTrans_iff t1 t2).mp h
    exact (matchLabelTarget_iff t1 t2).mpr ⟨h1, h3, h4⟩
  refine redirectTGBA_spec tgba hwf ids redirect transient hperm hroot ?_ ?_ ?_
  · intro q hq t ht
    rcases hcond q hq with hso | ⟨htr, hslt⟩
    · obtain ⟨t', ht', hm⟩ := ((sameOutgoing_iff _ _).mp hso).2.1 t ht
      exact ⟨t', ht', hlt_of_match t t' hm, fun _ => ((matchTrans_iff t t').mp hm).2.1⟩
    · obtain ⟨t', ht', hm⟩ := ((sameLabelsTargets_iff _ _).mp hslt).1 t ht
      exact ⟨t', ht', hm, fun h => absurd htr (by rw [h]; decide)⟩
  · intro q hq t' ht'
    rcases hcond q hq with hso | ⟨htr, hslt⟩
    · obtain ⟨t, ht, hm⟩ := ((sameOutgoing_iff _ _).mp hso).2.2 t' ht'
      exact ⟨t, ht, hlt_of_match t t' hm, fun _ => ((matchTrans_iff t t').mp hm).2.1⟩
    · obtain ⟨t, ht, hm⟩ := ((sameLabelsTargets_iff _ _).mp hslt).2 t' ht'
      exact ⟨t, ht, hm, fun h => absurd htr (by rw [h]; decide)⟩
  · intro s hmem hsucc
    obtain ⟨M, hM⟩ := eventually_not_transient tgba hwf s hmem hsucc
    refine ⟨M, fun n hn => ?_⟩
    rw [htransient, Bool.eq_false_iff]
    intro h
    simp only [Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_filter] at h
    rw [hM n hn] at h
    exact Bool.noConfusion h.2

/-- State merging keeps a TGBA well-formed. -/
theorem mergeEquivalentStates_wellFormed (tgba : TGBA α) (hwf : tgba.WellFormed) :
    (mergeEquivalentStates tgba).WellFormed :=
  (mergeEquivalentStates_spec tgba hwf).1

/-- State merging keeps every transition's marks, at any state, below `numAcceptSets`. -/
theorem mergeEquivalentStates_marks_lt (tgba : TGBA α) (hwf : tgba.WellFormed)
    (hb : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets) :
    ∀ q t, t ∈ (mergeEquivalentStates tgba).getSuccessors q →
      ∀ m ∈ t.acceptMarks, m < (mergeEquivalentStates tgba).numAcceptSets := by
  intro q t ht m hm
  obtain ⟨hnum, hsub⟩ := (mergeEquivalentStates_spec tgba hwf).2.1
  obtain ⟨q', t', ht', heq⟩ := hsub q t ht
  rw [hnum]
  exact hb q' t' ht' m (heq ▸ hm)

/-- `[GO01]` §6 with `[LTL2BA-1.3]`'s SCC relaxation: state merging preserves the accepted language. -/
theorem mergeEquivalentStates_correct (tgba : TGBA α) (hwf : tgba.WellFormed) (ξ : OmegaWord α) :
    tgba.toSpec.accepts ξ ↔ (mergeEquivalentStates tgba).toSpec.accepts ξ :=
  (mergeEquivalentStates_spec tgba hwf).2.2 ξ

end MergeEquivalentStatesCorrect


/-! ## Dead and unreachable states -/

/-- Drop every state without transitions, which lies on no infinite run, and every transition into it, then every state
left unreachable from the initial states. -/
def pruneDeadAndUnreachable (tgba : TGBA α) : TGBA α :=
  let alive (q : Nat) : Bool := (tgba.getSuccessors q).size > 0
  let live := tgba.states.toList.filter alive
  let trimmed : TGBA α :=
    { states := Std.HashSet.ofList live
      initialStates := Std.HashSet.ofList (tgba.initialStates.toList.filter alive)
      successors := live.foldl (fun m q =>
        m.insert q ((tgba.getSuccessors q).filter fun t => alive t.target))
        (Std.HashMap.emptyWithCapacity live.length)
      numAcceptSets := tgba.numAcceptSets }
  let reach := reachableFrom (fun q => (trimmed.succStates q).toList) trimmed.initialStates.toList live
  let reached := trimmed.states.toList.filter reach.contains
  { trimmed with
    states := Std.HashSet.ofList reached
    successors := reached.foldl (fun m q => m.insert q (trimmed.getSuccessors q))
      (Std.HashMap.emptyWithCapacity reached.length) }

/-- Pruning dead and unreachable states never increases the measure. -/
theorem measureTGBA_pruneDeadAndUnreachable_le (tgba : TGBA α) :
    measureTGBA (pruneDeadAndUnreachable tgba) ≤ measureTGBA tgba := by
  set alive := fun (q : Nat) => (tgba.getSuccessors q).size > 0 with halive
  set live := tgba.states.toList.filter alive with hlive
  set trimmed : TGBA α :=
    { states := Std.HashSet.ofList live
      initialStates := Std.HashSet.ofList (tgba.initialStates.toList.filter alive)
      successors := live.foldl (fun m q =>
        m.insert q ((tgba.getSuccessors q).filter fun t => alive t.target))
        (Std.HashMap.emptyWithCapacity live.length)
      numAcceptSets := tgba.numAcceptSets } with htrimmed
  set reach := reachableFrom (fun q => (trimmed.succStates q).toList) trimmed.initialStates.toList live with hreach
  set reached := trimmed.states.toList.filter reach.contains with hreached
  set result : TGBA α :=
    { trimmed with
      states := Std.HashSet.ofList reached
      successors := reached.foldl (fun m q => m.insert q (trimmed.getSuccessors q))
        (Std.HashMap.emptyWithCapacity reached.length) } with hresult
  have heq : pruneDeadAndUnreachable tgba = result := rfl
  rw [heq]
  have hnd : tgba.states.toList.Nodup := states_toList_nodup tgba
  have hlivend : live.Nodup := hnd.sublist List.filter_sublist
  have hliveSub : live.toFinSet ⊆ tgba.states.toList.toFinSet := by
    rw [hlive, List.toFinSet_filter]; exact FinSet.filter_subset _ _
  have htrimmedStates : trimmed.states = Std.HashSet.ofList live := by rw [htrimmed]
  have htrimmedFinSet : trimmed.states.toList.toFinSet = live.toFinSet := by
    rw [htrimmedStates]; exact toList_toFinSet_ofList live
  have htrimmednd : trimmed.states.toList.Nodup := states_toList_nodup trimmed
  have hreachedSub : reached.toFinSet ⊆ live.toFinSet := by
    rw [hreached, List.toFinSet_filter, htrimmedFinSet]; exact FinSet.filter_subset _ _
  have hreachednd : reached.Nodup := htrimmednd.sublist List.filter_sublist
  have hgsLive : ∀ q ∈ live.toFinSet,
      transWeight (trimmed.getSuccessors q) ≤ transWeight (tgba.getSuccessors q) := by
    intro q hq
    rw [List.mem_toFinSet] at hq
    rw [htrimmed]
    unfold TGBA.getSuccessors
    rw [getElem?_foldl_insert_of_mem _ q live hlivend hq]
    exact transWeight_filter_le (fun t => alive t.target) (tgba.successors[q]?.getD #[])
  have hresultStates : result.states = Std.HashSet.ofList reached := by rw [hresult]
  have hresultFinSet : result.states.toList.toFinSet = reached.toFinSet := by
    rw [hresultStates]; exact toList_toFinSet_ofList reached
  have hgsReached : ∀ q ∈ reached.toFinSet,
      transWeight (result.getSuccessors q) = transWeight (trimmed.getSuccessors q) := by
    intro q hq
    rw [List.mem_toFinSet] at hq
    rw [hresult]
    unfold TGBA.getSuccessors
    rw [getElem?_foldl_insert_of_mem _ q reached hreachednd hq]
    simp
  unfold measureTGBA
  rw [hresultStates, hresultFinSet, FinSet.sum_congr rfl hgsReached]
  calc (Std.HashSet.ofList reached).size + ∑ q ∈ reached.toFinSet, transWeight (trimmed.getSuccessors q)
      ≤ reached.length + ∑ q ∈ reached.toFinSet, transWeight (trimmed.getSuccessors q) :=
        Nat.add_le_add_right Std.HashSet.size_ofList_le _
    _ = reached.toFinSet.card + ∑ q ∈ reached.toFinSet, transWeight (trimmed.getSuccessors q) := by
        rw [List.toFinSet_card_of_nodup hreachednd]
    _ ≤ live.toFinSet.card + ∑ q ∈ live.toFinSet, transWeight (trimmed.getSuccessors q) :=
        Nat.add_le_add (FinSet.card_le_card hreachedSub) (FinSet.sum_le_sum_of_subset hreachedSub)
    _ = live.length + ∑ q ∈ live.toFinSet, transWeight (trimmed.getSuccessors q) := by
        rw [List.toFinSet_card_of_nodup hlivend]
    _ ≤ live.length + ∑ q ∈ live.toFinSet, transWeight (tgba.getSuccessors q) :=
        Nat.add_le_add_left (FinSet.sum_le_sum hgsLive) _
    _ = live.toFinSet.card + ∑ q ∈ live.toFinSet, transWeight (tgba.getSuccessors q) := by
        rw [List.toFinSet_card_of_nodup hlivend]
    _ ≤ tgba.states.toList.toFinSet.card + ∑ q ∈ tgba.states.toList.toFinSet, transWeight (tgba.getSuccessors q) :=
        Nat.add_le_add (FinSet.card_le_card hliveSub) (FinSet.sum_le_sum_of_subset hliveSub)
    _ = tgba.states.size + ∑ q ∈ tgba.states.toList.toFinSet, transWeight (tgba.getSuccessors q) := by
        rw [List.toFinSet_card_of_nodup hnd, Std.HashSet.length_toList]

/-! ## The fixpoint loop -/

/-- Implied-transition removal, state merging and pruning, the part of a round after mark erasure. -/
def reduceRound (tgba : TGBA α) : TGBA α :=
  pruneDeadAndUnreachable (mergeEquivalentStates (dropImpliedAll tgba))

theorem measureTGBA_reduceRound_le (tgba : TGBA α) : measureTGBA (reduceRound tgba) ≤ measureTGBA tgba :=
  (Nat.le_trans (measureTGBA_pruneDeadAndUnreachable_le _))
    (Nat.le_trans (measureTGBA_mergeEquivalentStates_le _) (measureTGBA_dropImpliedAll_le _))

/-- Mark erasure then `reduceRound`, repeated until `reduceRound` changes nothing. Mark erasure is idempotent on an
unchanged graph and `reduceRound` does not depend on the order of transitions, so a further round would change nothing. -/
@[expose] def simplifyTGBA (tgba : TGBA α) : TGBA α :=
  let erased := eraseMarks tgba (tgbaSCCs tgba)
  let next := reduceRound erased
  if _h : measureTGBA next = measureTGBA erased then next else simplifyTGBA next
termination_by measureTGBA tgba
decreasing_by
  exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_ne (measureTGBA_reduceRound_le _) _h) (measureTGBA_eraseMarks_le _ _)


/-- Run compatibility reads only the edges, so it agrees for any two `TGBA`s on the same run. -/
theorem TGBA.toSpec_runCompatible_indep (T1 T2 : TGBA α) (σ : Lentil.exec (TGBA.Edge α)) (ξ : OmegaWord α) :
    T1.toSpec.runCompatible σ ξ ↔ T2.toSpec.runCompatible σ ξ := Iff.rfl

/-- Acceptance of a run agrees for any two `TGBA`s with the same `numAcceptSets`. -/
theorem TGBA.toSpec_isAcceptingRun_indep (T1 T2 : TGBA α) (hk : T1.numAcceptSets = T2.numAcceptSets)
    (σ : Lentil.exec (TGBA.Edge α)) : T1.toSpec.isAcceptingRun σ ↔ T2.toSpec.isAcceptingRun σ := by
  unfold TGBA.toSpec TOASpec.isAcceptingRun
  rw [hk]

private theorem pruneDeadAndUnreachable_spec (tgba : TGBA α) (hwf : tgba.WellFormed) :
    (pruneDeadAndUnreachable tgba).WellFormed ∧
      (∀ q t, t ∈ (pruneDeadAndUnreachable tgba).getSuccessors q → t ∈ tgba.getSuccessors q) ∧
      ∀ ξ : OmegaWord α, tgba.toSpec.accepts ξ ↔ (pruneDeadAndUnreachable tgba).toSpec.accepts ξ := by
  set alive : Nat → Bool := fun q => (tgba.getSuccessors q).size > 0 with halive
  set live := tgba.states.toList.filter alive with hlive
  set trimmed : TGBA α :=
    { states := Std.HashSet.ofList live
      initialStates := Std.HashSet.ofList (tgba.initialStates.toList.filter alive)
      successors := live.foldl (fun m q =>
        m.insert q ((tgba.getSuccessors q).filter fun t => alive t.target))
        (Std.HashMap.emptyWithCapacity live.length)
      numAcceptSets := tgba.numAcceptSets } with htrimmed
  set reach := reachableFrom (fun q => (trimmed.succStates q).toList) trimmed.initialStates.toList live
    with hreach
  set reached := trimmed.states.toList.filter reach.contains with hreached
  set result : TGBA α :=
    { trimmed with
      states := Std.HashSet.ofList reached
      successors := reached.foldl (fun m q => m.insert q (trimmed.getSuccessors q))
        (Std.HashMap.emptyWithCapacity reached.length) } with hresult
  have heq : pruneDeadAndUnreachable tgba = result := rfl
  rw [heq]
  have hnd : tgba.states.toList.Nodup := states_toList_nodup tgba
  have hlivend : live.Nodup := hnd.sublist List.filter_sublist
  have hreachednd : reached.Nodup := (states_toList_nodup trimmed).sublist List.filter_sublist
  have hlive_iff : ∀ q, q ∈ live ↔ tgba.states.contains q ∧ alive q := by
    intro q
    rw [hlive, List.mem_filter, ← Std.HashSet.mem_iff_contains, Std.HashSet.mem_toList]
  have htrimmedSucc : ∀ q ∈ live, trimmed.getSuccessors q =
      (tgba.getSuccessors q).filter fun t => alive t.target := by
    intro q hq
    have heq2 : trimmed.getSuccessors q = _ := rfl
    rw [heq2]; unfold TGBA.getSuccessors
    rw [getElem?_foldl_insert_of_mem _ q live hlivend hq]
    rfl
  have htrimmedInit_iff : ∀ q, trimmed.initialStates.contains q ↔
      tgba.initialStates.contains q ∧ alive q := by
    intro q
    have heq2 : trimmed.initialStates = Std.HashSet.ofList (tgba.initialStates.toList.filter alive) := rfl
    rw [heq2]
    simp only [Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_filter,
      Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains]
  have htrimmedStates_iff : ∀ q, trimmed.states.contains q ↔ q ∈ live := by
    intro q
    have heq2 : trimmed.states = Std.HashSet.ofList live := rfl
    rw [heq2, Std.HashSet.contains_ofList, List.contains_iff_mem]
  have htrimmedSuccStates_iff : ∀ q, q ∈ live → ∀ q', q' ∈ trimmed.succStates q ↔
      ∃ t ∈ tgba.getSuccessors q, t.target = q' ∧ alive q' := by
    intro q hq q'
    have heq2 : trimmed.succStates q = (trimmed.getSuccessors q).map (·.target) := rfl
    rw [heq2, htrimmedSucc q hq, Array.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [Array.mem_filter] at ht
      exact ⟨t, ht.1, rfl, ht.2⟩
    · rintro ⟨t, ht, heqt, halivet⟩
      exact ⟨t, Array.mem_filter.mpr ⟨ht, by rw [heqt]; exact halivet⟩, heqt⟩
  have hU : ∀ q, q ∈ live → tgba.states.contains q := fun q hq => (hlive_iff q).mp hq |>.1
  have hclosed : ∀ p, p ∈ live → ∀ q' ∈ (trimmed.succStates p).toList, q' ∈ live := by
    intro p hp q' hq'
    rw [Array.mem_toList_iff] at hq'
    obtain ⟨t, ht, heqt, halivet⟩ := (htrimmedSuccStates_iff p hp q').mp hq'
    refine (hlive_iff q').mpr ⟨?_, halivet⟩
    exact heqt ▸ hwf.succ_mem p t (hU p hp) ht
  have hstarts : ∀ x ∈ trimmed.initialStates.toList, x ∈ live := by
    intro x hx
    rw [Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains, htrimmedInit_iff] at hx
    exact (hlive_iff x).mpr ⟨hwf.initial_mem x hx.1, hx.2⟩
  have hcov : ∀ x, x ∈ live → x ∈ trimmed.initialStates.toList ∨ x ∈ live := fun _ hx => Or.inr hx
  have hreach_closed := reachableFrom_closed (fun q => (trimmed.succStates q).toList)
    trimmed.initialStates.toList live (fun q => q ∈ live) hclosed hstarts hcov
  have hreach_starts : ∀ x ∈ trimmed.initialStates.toList, reach.contains x :=
    fun x hx => starts_subset_reachableFrom (fun q => (trimmed.succStates q).toList)
      trimmed.initialStates.toList live x hx
  have hreached_iff : ∀ q, q ∈ reached ↔ q ∈ live ∧ reach.contains q := by
    intro q
    rw [hreached, List.mem_filter, Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains,
      htrimmedStates_iff]
  have hresultSucc : ∀ q ∈ reached, result.getSuccessors q = trimmed.getSuccessors q := by
    intro q hq
    have heq2 : result.getSuccessors q = _ := rfl
    rw [heq2]; unfold TGBA.getSuccessors
    rw [getElem?_foldl_insert_of_mem _ q reached hreachednd hq]
    rfl
  have hresultInit : result.initialStates = trimmed.initialStates := rfl
  have hresult_sub_tgba : ∀ q t, t ∈ result.getSuccessors q → t ∈ tgba.getSuccessors q := by
    intro q t ht
    by_cases hq : q ∈ reached
    · rw [hresultSucc q hq] at ht
      have hqlive : q ∈ live := (hreached_iff q).mp hq |>.1
      rw [htrimmedSucc q hqlive] at ht
      exact (Array.mem_filter.mp ht).1
    · have heq2 : result.getSuccessors q = #[] := by
        have heq3 : result.getSuccessors q = _ := rfl
        rw [heq3]; unfold TGBA.getSuccessors
        rw [getElem?_foldl_insert_of_not_mem _ q reached (Std.HashMap.emptyWithCapacity reached.length) hq]
        simp
      rw [heq2] at ht
      exact absurd ht (by simp)
  have hresStates : ∀ q, result.states.contains q = true ↔ q ∈ reached := by
    intro q
    show (Std.HashSet.ofList reached).contains q = true ↔ _
    rw [Std.HashSet.contains_ofList, List.contains_iff_mem]
  refine ⟨⟨fun q hq => ?_, fun q t hq ht => ?_, fun q t hq ht m hm => ?_⟩, hresult_sub_tgba, fun ξ => ?_⟩
  · have hinit' : trimmed.initialStates.contains q = true := hq
    obtain ⟨hinit0, halive0⟩ := (htrimmedInit_iff q).mp hinit'
    exact (hresStates q).mpr ((hreached_iff q).mpr ⟨(hlive_iff q).mpr ⟨hwf.initial_mem q hinit0, halive0⟩,
      hreach_starts q (Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hinit'))⟩)
  · have hqr := (hreached_iff q).mp ((hresStates q).mp hq)
    have ht' : t ∈ (tgba.getSuccessors q).filter fun t => alive t.target := by
      rw [← htrimmedSucc q hqr.1, ← hresultSucc q ((hresStates q).mp hq)]
      exact ht
    obtain ⟨httgba, halivet⟩ := Array.mem_filter.mp ht'
    have hsuccMem : t.target ∈ (trimmed.succStates q).toList := by
      rw [Array.mem_toList_iff, htrimmedSuccStates_iff _ hqr.1]
      exact ⟨t, httgba, rfl, halivet⟩
    exact (hresStates _).mpr ((hreached_iff _).mpr
      ⟨(hlive_iff _).mpr ⟨hwf.succ_mem q t (hU q hqr.1) httgba, halivet⟩, hreach_closed _ hqr.2 _ hsuccMem⟩)
  · have hqr := (hreached_iff q).mp ((hresStates q).mp hq)
    exact hwf.marks_range q t (hU q hqr.1) (hresult_sub_tgba q t ht) m hm
  constructor
  · rintro ⟨σ, hrun, hcompat, hacc⟩
    have hlive_visit : ∀ n, (σ n).1 ∈ live ∧ reach.contains (σ n).1 := by
      intro n
      induction n with
      | zero =>
          have hinit0 : tgba.initialStates.contains (σ 0).1 := hrun.1
          have hvalid0 : (σ 0).2 ∈ tgba.getSuccessors (σ 0).1 := (hrun.2 0).1
          have halive0 : alive (σ 0).1 := decide_eq_true_iff.mpr (Array.size_pos_of_mem hvalid0)
          have hlive0 : (σ 0).1 ∈ live := (hlive_iff _).mpr ⟨hwf.initial_mem _ hinit0, halive0⟩
          have htrimmedInit0 : trimmed.initialStates.contains (σ 0).1 :=
            (htrimmedInit_iff _).mpr ⟨hinit0, halive0⟩
          have hmemtoList : (σ 0).1 ∈ trimmed.initialStates.toList :=
            Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr htrimmedInit0)
          exact ⟨hlive0, hreach_starts _ hmemtoList⟩
      | succ n ih =>
          have hvalidn : (σ n).2 ∈ tgba.getSuccessors (σ n).1 := (hrun.2 n).1
          have hlinkn : (σ n).2.target = (σ (n + 1)).1 := (hrun.2 n).2
          have hvalidn1 : (σ (n + 1)).2 ∈ tgba.getSuccessors (σ (n + 1)).1 := (hrun.2 (n + 1)).1
          have halive1 : alive (σ (n + 1)).1 := decide_eq_true_iff.mpr (Array.size_pos_of_mem hvalidn1)
          have hlive1 : (σ (n + 1)).1 ∈ live :=
            (hlive_iff _).mpr ⟨hlinkn ▸ hwf.succ_mem _ _ (hU _ ih.1) hvalidn, halive1⟩
          have hsuccMem : (σ (n + 1)).1 ∈ (trimmed.succStates (σ n).1).toList := by
            rw [Array.mem_toList_iff, htrimmedSuccStates_iff _ ih.1]
            exact ⟨(σ n).2, hvalidn, hlinkn, halive1⟩
          exact ⟨hlive1, hreach_closed _ ih.2 _ hsuccMem⟩
    have hvisit_reached : ∀ n, (σ n).1 ∈ reached := fun n =>
      (hreached_iff _).mpr (hlive_visit n)
    refine ⟨σ, ⟨?_, ?_⟩, (TGBA.toSpec_runCompatible_indep tgba result σ ξ).mp hcompat,
      (TGBA.toSpec_isAcceptingRun_indep tgba result rfl σ).mp hacc⟩
    · show result.isInitial (σ 0).1
      show result.initialStates.contains (σ 0).1
      rw [hresultInit]
      have hinit0 : tgba.initialStates.contains (σ 0).1 := hrun.1
      have hvalid0 : (σ 0).2 ∈ tgba.getSuccessors (σ 0).1 := (hrun.2 0).1
      have halive0 : alive (σ 0).1 := decide_eq_true_iff.mpr (Array.size_pos_of_mem hvalid0)
      exact (htrimmedInit_iff _).mpr ⟨hinit0, halive0⟩
    · intro n
      have hvalidn : (σ n).2 ∈ tgba.getSuccessors (σ n).1 := (hrun.2 n).1
      have hlinkn : (σ n).2.target = (σ (n + 1)).1 := (hrun.2 n).2
      refine ⟨?_, hlinkn⟩
      show (σ n).2 ∈ result.getSuccessors (σ n).1
      rw [hresultSucc _ (hvisit_reached n), htrimmedSucc _ (hlive_visit n).1]
      refine Array.mem_filter.mpr ⟨hvalidn, ?_⟩
      rw [hlinkn]
      exact (hlive_iff _).mp (hlive_visit (n + 1)).1 |>.2
  · rintro ⟨σ, hrun, hcompat, hacc⟩
    refine ⟨σ, ⟨?_, ?_⟩, (TGBA.toSpec_runCompatible_indep result tgba σ ξ).mp hcompat,
      (TGBA.toSpec_isAcceptingRun_indep result tgba rfl σ).mp hacc⟩
    · show tgba.isInitial (σ 0).1
      have hresultInit0 : result.initialStates.contains (σ 0).1 := hrun.1
      rw [hresultInit] at hresultInit0
      exact (htrimmedInit_iff _).mp hresultInit0 |>.1
    · intro n
      have hvalidn : (σ n).2 ∈ result.getSuccessors (σ n).1 := (hrun.2 n).1
      exact ⟨hresult_sub_tgba _ _ hvalidn, (hrun.2 n).2⟩

/-- Pruning dead and unreachable states keeps a TGBA well-formed. -/
theorem pruneDeadAndUnreachable_wellFormed (tgba : TGBA α) (hwf : tgba.WellFormed) :
    (pruneDeadAndUnreachable tgba).WellFormed :=
  (pruneDeadAndUnreachable_spec tgba hwf).1

/-- Pruning dead and unreachable states keeps every transition's marks, at any state, below `numAcceptSets`. -/
theorem pruneDeadAndUnreachable_marks_lt (tgba : TGBA α) (hwf : tgba.WellFormed)
    (hb : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets) :
    ∀ q t, t ∈ (pruneDeadAndUnreachable tgba).getSuccessors q →
      ∀ m ∈ t.acceptMarks, m < (pruneDeadAndUnreachable tgba).numAcceptSets :=
  fun q t ht => hb q t ((pruneDeadAndUnreachable_spec tgba hwf).2.1 q t ht)

/-- Pruning dead and unreachable states preserves the accepted language. -/
theorem pruneDeadAndUnreachable_correct (tgba : TGBA α) (hwf : tgba.WellFormed) (ξ : OmegaWord α) :
    tgba.toSpec.accepts ξ ↔ (pruneDeadAndUnreachable tgba).toSpec.accepts ξ :=
  (pruneDeadAndUnreachable_spec tgba hwf).2.2 ξ

/-! ## Correctness of the simplification loop -/

section LoopCorrect

variable [LawfulBEq α] [LawfulHashable α]

theorem reduceRound_wellFormed (tgba : TGBA α) (hwf : tgba.WellFormed) : (reduceRound tgba).WellFormed :=
  pruneDeadAndUnreachable_wellFormed _ (mergeEquivalentStates_wellFormed _ (dropImpliedAll_wellFormed _ hwf))

theorem reduceRound_marks_lt (tgba : TGBA α) (hwf : tgba.WellFormed)
    (hb : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets) :
    ∀ q t, t ∈ (reduceRound tgba).getSuccessors q → ∀ m ∈ t.acceptMarks, m < (reduceRound tgba).numAcceptSets := by
  have h2 := dropImpliedAll_wellFormed _ hwf
  exact pruneDeadAndUnreachable_marks_lt _ (mergeEquivalentStates_wellFormed _ h2)
    (mergeEquivalentStates_marks_lt _ h2 (dropImpliedAll_marks_lt _ hb))

theorem reduceRound_correct (tgba : TGBA α) (hwf : tgba.WellFormed) (ξ : OmegaWord α) :
    tgba.toSpec.accepts ξ ↔ (reduceRound tgba).toSpec.accepts ξ := by
  have h2 := dropImpliedAll_wellFormed _ hwf
  exact (dropImpliedAll_correct _ hwf ξ).trans ((mergeEquivalentStates_correct _ h2 ξ).trans
    (pruneDeadAndUnreachable_correct _ (mergeEquivalentStates_wellFormed _ h2) ξ))

/-- The simplification loop keeps a TGBA well-formed and preserves its accepted language. -/
theorem simplifyTGBA_spec (tgba : TGBA α) (hwf : tgba.WellFormed) :
    (simplifyTGBA tgba).WellFormed ∧
      ((∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets) →
        ∀ q t, t ∈ (simplifyTGBA tgba).getSuccessors q → ∀ m ∈ t.acceptMarks, m < (simplifyTGBA tgba).numAcceptSets) ∧
      ∀ ξ : OmegaWord α, tgba.toSpec.accepts ξ ↔ (simplifyTGBA tgba).toSpec.accepts ξ := by
  suffices H : ∀ n (tgba : TGBA α), measureTGBA tgba = n → tgba.WellFormed →
      (simplifyTGBA tgba).WellFormed ∧
        ((∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets) →
          ∀ q t, t ∈ (simplifyTGBA tgba).getSuccessors q → ∀ m ∈ t.acceptMarks,
            m < (simplifyTGBA tgba).numAcceptSets) ∧
        ∀ ξ : OmegaWord α, tgba.toSpec.accepts ξ ↔ (simplifyTGBA tgba).toSpec.accepts ξ from H _ tgba rfl hwf
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro tgba hm hwf
    have h1 := eraseMarks_wellFormed tgba hwf (tgbaSCCs tgba)
    have hcorr1 := eraseMarks_correct tgba hwf _ (tgbaSCCs_sound tgba hwf)
    have hnext := reduceRound_wellFormed _ h1
    by_cases hc : measureTGBA (reduceRound (eraseMarks tgba (tgbaSCCs tgba))) =
        measureTGBA (eraseMarks tgba (tgbaSCCs tgba))
    · have heq : simplifyTGBA tgba = reduceRound (eraseMarks tgba (tgbaSCCs tgba)) := by
        rw [simplifyTGBA]; exact dif_pos hc
      rw [heq]
      exact ⟨hnext, fun hb => reduceRound_marks_lt _ h1 (eraseMarks_marks_lt tgba _ hb),
        fun ξ => (hcorr1 ξ).trans (reduceRound_correct _ h1 ξ)⟩
    · have heq : simplifyTGBA tgba = simplifyTGBA (reduceRound (eraseMarks tgba (tgbaSCCs tgba))) := by
        rw [simplifyTGBA]; exact dif_neg hc
      rw [heq]
      have hlt : measureTGBA (reduceRound (eraseMarks tgba (tgbaSCCs tgba))) < n :=
        hm ▸ Nat.lt_of_lt_of_le (Nat.lt_of_le_of_ne (measureTGBA_reduceRound_le _) hc) (measureTGBA_eraseMarks_le _ _)
      obtain ⟨hwf', hmk, hcorr⟩ := ih _ hlt _ rfl hnext
      exact ⟨hwf', fun hb => hmk (reduceRound_marks_lt _ h1 (eraseMarks_marks_lt tgba _ hb)),
        fun ξ => (hcorr1 ξ).trans ((reduceRound_correct _ h1 ξ).trans (hcorr ξ))⟩

/-- The simplification loop keeps a TGBA well-formed. -/
theorem simplifyTGBA_wellFormed (tgba : TGBA α) (hwf : tgba.WellFormed) : (simplifyTGBA tgba).WellFormed :=
  (simplifyTGBA_spec tgba hwf).1

/-- The simplification loop keeps every transition's marks, at any state, below `numAcceptSets`. -/
theorem simplifyTGBA_marks_lt (tgba : TGBA α) (hwf : tgba.WellFormed)
    (hb : ∀ q t, t ∈ tgba.getSuccessors q → ∀ m ∈ t.acceptMarks, m < tgba.numAcceptSets) :
    ∀ q t, t ∈ (simplifyTGBA tgba).getSuccessors q → ∀ m ∈ t.acceptMarks, m < (simplifyTGBA tgba).numAcceptSets :=
  (simplifyTGBA_spec tgba hwf).2.1 hb

/-- The simplification loop preserves the accepted language. -/
theorem simplifyTGBA_correct (tgba : TGBA α) (hwf : tgba.WellFormed) (ξ : OmegaWord α) :
    tgba.toSpec.accepts ξ ↔ (simplifyTGBA tgba).toSpec.accepts ξ :=
  (simplifyTGBA_spec tgba hwf).2.2 ξ

end LoopCorrect

end LTLLib
