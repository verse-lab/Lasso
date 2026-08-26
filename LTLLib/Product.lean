/-
  Product construction between an external system (Kripke structure) and a
  Büchi Automaton `BA.lean`, built on-the-fly as a plain successor function.

  Product state order is `SysState × BAState`.

  Sections:
  - Product construction
  - System run / system language
  - Product run decomposition + acceptance transfer
  - Lasso witness
-/
import LTLLib.NestedDFS.NestedDFSTermination
import LTLLib.AbstractSpec.Acceptance
import LTLLib.AbstractSpec.EmptinessCheck
import LTLLib.AbstractSpec.Lasso
import Mathlib.Data.Finite.Prod

namespace LTLLib

namespace Product

/-! ## Product construction -/

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]

def initialStates (ba : BA α) (sysInit : List SysState) :
    List (SysState × BAState) :=
  sysInit.flatMap fun s => ba.initialStates.toList.map fun q => (s, q)

/-- Wraps a successor function so a terminal state gets a self-loop instead, giving every state
a total transition relation, as required by Büchi semantics over infinite words. -/
def totalizeSucc {State : Type u} (succs : State → Array State) : State → Array State :=
  fun s =>
    let ss := succs s
    if ss.isEmpty then #[s] else ss

theorem reachable_totalizeSucc_imp {State : Type u} (initialStates : List State)
    (succs : State → Array State) :
    ∀ {s : State}, Reachable initialStates (totalizeSucc succs) s →
      Reachable initialStates succs s := by
  intro s hs
  induction hs with
  | base hi => exact .base hi
  | step _ hmem ih =>
    rename_i s t
    dsimp only [totalizeSucc] at hmem
    split at hmem
    · exact (Array.mem_singleton.mp hmem) ▸ ih
    · exact .step ih hmem

theorem finiteReach_totalizeSucc {State : Type u} (initialStates : List State)
    (succs : State → Array State) (fr : FiniteReach initialStates succs) :
    FiniteReach initialStates (totalizeSucc succs) :=
  fr.subset (fun _ hs => reachable_totalizeSucc_imp initialStates succs hs)

/-- Successors of a product state, computed on the fly (never materialized as an edge set).
Compatibility is checked at the source state `(s, q)`, if it fails, `(s, q)` has no outgoing edges. -/
def getSuccessors (ba : BA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) :
    (SysState × BAState) → Array (SysState × BAState) :=
  fun (s, q) =>
    if ba.compatible q (sysLabel s) then
      (totalizeSucc sysSucc s).flatMap fun s' => (ba.getSuccessors q).map fun q' => (s', q')
    else #[]

def isAccepting (ba : BA α) : (SysState × BAState) → Bool :=
  fun (_, q) => ba.isAccepting q

/-- Every `Reachable` product state's halves are themselves reachable in their own component graphs. -/
private theorem reachable_imp (ba : BA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    ∀ {p : SysState × BAState},
      Reachable (initialStates ba sysInit) (getSuccessors ba sysSucc sysLabel) p →
      Reachable sysInit (totalizeSucc sysSucc) p.1 ∧
        Reachable ba.initialStates.toList ba.getSuccessors p.2 := by
  intro p h
  induction h with
  | base hi =>
    simp only [initialStates, List.mem_flatMap, List.mem_map] at hi
    obtain ⟨s, hs_mem, q, hq_mem, heq⟩ := hi
    subst heq
    exact ⟨.base hs_mem, .base hq_mem⟩
  | step hprev hmem ih =>
    rename_i prev cur
    obtain ⟨s, q⟩ := prev
    obtain ⟨s', q'⟩ := cur
    obtain ⟨ih1, ih2⟩ := ih
    unfold getSuccessors at hmem
    cases hcompat : ba.compatible q (sysLabel s) with
    | false => simp [hcompat] at hmem
    | true =>
      simp only [hcompat, if_true, Array.mem_flatMap, Array.mem_map] at hmem
      obtain ⟨s'', hs''_mem, q'', hq''_mem, heq⟩ := hmem
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
      exact ⟨.step ih1 hs''_mem, .step ih2 hq''_mem⟩

/-- The product's reachable states are contained in `reachable(sys) × reachable(ba)`.
The model checking caller supplies their own system's `FiniteReach` witness -/
def finiteReach (ba : BA α) (hbawf : ba.WellFormed)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState) (sysFR : FiniteReach sysInit sysSucc) :
    FiniteReach (initialStates ba sysInit) (getSuccessors ba sysSucc sysLabel) :=
  ((finiteReach_totalizeSucc sysInit sysSucc sysFR).prod (ba.finiteReach hbawf)).subset
    (fun _ hp => reachable_imp ba sysSucc sysLabel sysInit hp)

end Product

/-! ## System run / system language -/


def Sys.toSpec {α : Type u} {SysState : Type v} [BEq α] [Hashable α]
    (sysSucc : SysState → Array SysState) (sysInit : List SysState)
    (sysLabel : SysState → Std.HashSet α) : OASpec SysState α 0 where
  trans s t := t ∈ Product.totalizeSucc sysSucc s
  initial s := s ∈ sysInit
  labelCompat s v := ∀ a, v a ↔ a ∈ sysLabel s
  acceptSet := Fin.elim0

/-! ## Product run decomposition + acceptance transfer  -/

namespace Product

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]


def toSpec (ba : BA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    OASpec (SysState × BAState) α 1 where
  trans p p' := p' ∈ getSuccessors ba sysSucc sysLabel p
  initial p := p ∈ initialStates ba sysInit
  labelCompat p v := ∀ a, v a ↔ a ∈ sysLabel p.1
  acceptSet _ p := isAccepting ba p

private theorem getSuccessors_mem_iff (ba : BA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) {p p' : SysState × BAState} :
    p' ∈ getSuccessors ba sysSucc sysLabel p ↔
      ba.compatible p.2 (sysLabel p.1) = true ∧
      p'.1 ∈ totalizeSucc sysSucc p.1 ∧ p'.2 ∈ ba.getSuccessors p.2 := by
  obtain ⟨s, q⟩ := p
  obtain ⟨s', q'⟩ := p'
  unfold getSuccessors
  constructor
  · intro hmem
    cases hcompat : ba.compatible q (sysLabel s) with
    | false => simp [hcompat] at hmem
    | true =>
      simp only [hcompat, if_true, Array.mem_flatMap, Array.mem_map] at hmem
      obtain ⟨s'', hs''_mem, q'', hq''_mem, heq⟩ := hmem
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
      -- `cases hcompat : ...` already substituted `ba.compatible q (sysLabel s)`
      -- with `true` in the goal (but not in `hcompat`'s own stated type), so
      -- the first conjunct's goal is literally `true = true` here.
      exact ⟨rfl, hs''_mem, hq''_mem⟩
  · rintro ⟨hcompat, hs'_mem, hq'_mem⟩
    simp only [hcompat, if_true, Array.mem_flatMap, Array.mem_map]
    exact ⟨s', hs'_mem, q', hq'_mem, rfl⟩

/-- A product run decomposes into a BA run and a `Sys.toSpec` run that stay `compatible` at every step. -/
theorem run_decompose (ba : BA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {r : Nat → SysState × BAState} (hrun : (toSpec ba sysSucc sysLabel sysInit).isRun r) :
    (ba.toSpec).isRun (Prod.snd ∘ r) ∧
    (Sys.toSpec sysSucc sysInit sysLabel).isRun (Prod.fst ∘ r) ∧
    ∀ n, ba.compatible (r n).2 (sysLabel (r n).1) = true := by
  obtain ⟨hinit, htrans⟩ := hrun
  simp only [toSpec, initialStates, List.mem_flatMap, List.mem_map] at hinit
  obtain ⟨s, hs_mem, q, hq_mem, heq⟩ := hinit
  refine ⟨⟨?_, fun n => ((getSuccessors_mem_iff ba sysSucc sysLabel).mp (htrans n)).2.2⟩,
    ⟨?_, fun n => ((getSuccessors_mem_iff ba sysSucc sysLabel).mp (htrans n)).2.1⟩,
    fun n => ((getSuccessors_mem_iff ba sysSucc sysLabel).mp (htrans n)).1⟩
  · show ba.initialStates.contains (r 0).2 = true
    rw [← heq]
    exact Std.HashSet.mem_iff_contains.mp (Std.HashSet.mem_toList.mp hq_mem)
  · show (r 0).1 ∈ sysInit
    rw [← heq]
    exact hs_mem

/-- A BA run and a `Sys.toSpec` run that agree at every step under `ba.compatible` combine into a genuine product run. -/
theorem run_combine (ba : BA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {σ : Nat → BAState} {τ : Nat → SysState}
    (hba : (ba.toSpec).isRun σ) (hsys : (Sys.toSpec sysSucc sysInit sysLabel).isRun τ)
    (hcompat : ∀ n, ba.compatible (σ n) (sysLabel (τ n)) = true) :
    (toSpec ba sysSucc sysLabel sysInit).isRun (fun n => (τ n, σ n)) := by
  obtain ⟨hba_init, hba_trans⟩ := hba
  obtain ⟨hsys_init, hsys_trans⟩ := hsys
  refine ⟨?_, fun n => (getSuccessors_mem_iff ba sysSucc sysLabel).mpr
    ⟨hcompat n, hsys_trans n, hba_trans n⟩⟩
  show (τ 0, σ 0) ∈ initialStates ba sysInit
  simp only [initialStates, List.mem_flatMap, List.mem_map]
  exact ⟨τ 0, hsys_init, σ 0,
    Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hba_init), rfl⟩

theorem acc_iff (ba : BA α) (p : SysState × BAState) :
    isAccepting ba p = ba.isAccepting p.2 := by
  obtain ⟨_, _⟩ := p
  rfl

private theorem compatible_iff_labelCompat [LawfulBEq α] (ba : BA α) (s : BAState)
    (valuation : Std.HashSet α) :
    ba.compatible s valuation = true ↔ ba.toSpec.labelCompat s (fun a => a ∈ valuation) := by
  unfold BA.compatible BA.getLabeling BA.toSpec
  cases hlab : ba.labeling[s.gbaState]? with
  | none =>
    simp only [hlab, Option.getD_none, Bool.and_eq_true, Bool.not_eq_true',
      Std.HashSet.all_eq_true_iff_forall_mem, Std.HashSet.any_eq_false_iff_forall_mem]
    simp [Std.HashSet.not_mem_emptyWithCapacity]
  | some pn =>
    obtain ⟨pos, neg⟩ := pn
    simp only [hlab, Option.getD_some, Bool.and_eq_true, Bool.not_eq_true',
      Std.HashSet.all_eq_true_iff_forall_mem, Std.HashSet.any_eq_false_iff_forall_mem,
      Std.HashSet.mem_iff_contains, Bool.not_eq_true]

/-- An accepting product run decomposes into a `Sys.toSpec` run and a BA-language membership
witness for the system's real labeling. -/
theorem gsp_correct1 [LawfulBEq α] (ba : BA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {r : Nat → SysState × BAState}
    (hacc : (toSpec ba sysSucc sysLabel sysInit).isRun r ∧
            (toSpec ba sysSucc sysLabel sysInit).isAcceptingRun r) :
    (Sys.toSpec sysSucc sysInit sysLabel).isRun (Prod.fst ∘ r) ∧
    (ba.toSpec).accepts (fun n a => a ∈ sysLabel (r n).1) := by
  obtain ⟨hrun, hacc⟩ := hacc
  obtain ⟨hσrun, hτrun, hcompat⟩ := run_decompose ba sysSucc sysLabel sysInit hrun
  refine ⟨hτrun, Prod.snd ∘ r, hσrun,
    fun n => (compatible_iff_labelCompat ba (r n).2 (sysLabel (r n).1)).mp (hcompat n),
    fun i n => ?_⟩
  obtain ⟨j, hj⟩ := hacc i n
  exact ⟨j, by simpa [acc_iff] using hj⟩

/-- A genuine system run whose real labeling lies in the BA's language lifts to an accepting
product run projecting back down to it. -/
theorem gsp_correct2 [LawfulBEq α] (ba : BA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState)
    {τ : Nat → SysState}
    (hsys : (Sys.toSpec sysSucc sysInit sysLabel).isRun τ)
    (hlang : (ba.toSpec).accepts (fun n a => a ∈ sysLabel (τ n))) :
    ∃ r : Nat → SysState × BAState, τ = Prod.fst ∘ r ∧
      (toSpec ba sysSucc sysLabel sysInit).isRun r ∧
      (toSpec ba sysSucc sysLabel sysInit).isAcceptingRun r := by
  obtain ⟨σ, hσrun, hσcompat, hσacc⟩ := hlang
  refine ⟨fun n => (τ n, σ n), rfl,
    run_combine ba sysSucc sysLabel sysInit hσrun hsys
      (fun n => (compatible_iff_labelCompat ba (σ n) (sysLabel (τ n))).mpr (hσcompat n)),
    fun i n => ?_⟩
  obtain ⟨j, hj⟩ := hσacc i n
  exact ⟨j, by simpa [acc_iff] using hj⟩

end Product

/-! ## Lasso witness -/

/-- The `Product.toSpec` specialization of `toValidLassoOf`. -/
def AcceptingCycle.toValidLassoProduct {α : Type u} {SysState : Type v} [BEq α] [Hashable α]
    {ba : BA α} {sysSucc : SysState → Array SysState}
    {sysLabel : SysState → Std.HashSet α} {sysInit : List SysState}
    (ac : AcceptingCycle (Product.initialStates ba sysInit)
      (Product.getSuccessors ba sysSucc sysLabel) (Product.isAccepting ba)) :
    ValidLasso (Product.toSpec ba sysSucc sysLabel sysInit) ac.stem ac.cycle :=
  ac.toValidLassoOf Iff.rfl Iff.rfl Iff.rfl

end LTLLib
