/-
  Product construction between an external system and a `BA`, built
  on-the-fly (as a plain successor function, never a materialized graph).

  See `ProductModelChecker.md` at the repo root for the full design
  rationale and the CAVA source this is ported from.

  The external interface is deliberately three bare arguments — no bundled
  `System` record — matching both CAVA's `sa_rec` (`g_V0`/`g_E`/`sa_L`,
  `CAVA_Automata/Automata.thy`) and this repo's own `nestedDFS`/`nestedDFSWF`
  (`NestedDFS/NestedDFSRef.lean`, `NestedDFS/NestedDFSTermination.lean`), which already take a bare
  `initialStates`/`successors : State → Array State` pair with no
  automaton-specific record:
  - `sysInit : List SysState` — corresponds to CAVA's `g_V0`.
  - `sysSucc : SysState → Array SysState` — corresponds to CAVA's `g_E`
    (given as a successor function via `E_of_succ` in the executable
    refinement `CAVA_Impl.thy`'s `cava_inter_impl_loc`, not a relation).
  - `sysLabel : SysState → Std.HashSet α` — corresponds to CAVA's `sa_L`.

  Product state order is `SysState × BAState` (Lean-natural `(input,
  automaton)` order); CAVA's own `(q,s)` pairs are `(automaton, system)`.
-/
import LTLLib.NestedDFS.NestedDFSTermination
import Mathlib.Data.Finite.Prod

namespace LTLLib

namespace Product

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]
  [BEq SysState] [Hashable SysState]

/-- Corresponds to CAVA's `g_V0 = igba.V0 × sa.V0`
(`igba_sys_prod_precond.prod`, `Automata.thy`) — the *unfiltered* full
product, no compatibility pre-filter. An incompatible initial pair simply
has no successors once `getSuccessors`'s gate is evaluated below, and is
harmless dead weight for the DFS; CAVA doesn't filter it out either. -/
def initialStates (ba : BA α) (sysInit : List SysState) :
    List (SysState × BAState) :=
  sysInit.flatMap fun s => ba.initialStates.toList.map fun q => (s, q)

/-- Corresponds to CAVA's on-the-fly `g_E` in `cava_inter_impl_loc`
(`CAVA_Impl.thy`):
```
g_E = E_of_succ (λ(q,s).
  if igba.L q (sa.L s) then (succs of s) × (succs of q) else {})
```
computed as a plain function of the current product state, never
materialized as an explicit edge set — this is what makes the whole
construction on-the-fly.

The `compatible` gate is evaluated on the *source* state `(s, q)`, i.e. it
asks "is q's label consistent with the system state we're currently at",
not "is q' consistent with s'". Getting this backwards (checking the
successor pair instead) was an actual mistake made once while designing
this, corrected by re-reading `Automata.thy` directly — the gate decides
whether `(s, q)` has *any* outgoing edges at all; it says nothing about the
successor pair once produced. -/
def getSuccessors (ba : BA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) :
    (SysState × BAState) → Array (SysState × BAState) :=
  fun (s, q) =>
    if ba.compatible q (sysLabel s) then
      (sysSucc s).flatMap fun s' => (ba.getSuccessors q).map fun q' => (s', q')
    else #[]

/-- Corresponds to CAVA's `igbg_acc = λ(q,s). if s∈sa.V then igba.acc q else
{}` (`Automata.thy`) — minus the `s ∈ sa.V` guard. That guard is a
well-formedness technicality for an *explicit* state set (`sa.V`); it's
meaningless for an open-world successor function, for the same reason
`nestedDFS`/`nestedDFSWF` never assume a `states` set for their generic
`State` parameter either. -/
def isAccepting (ba : BA α) : (SysState × BAState) → Bool :=
  fun (_, q) => ba.isAccepting q

/-- Every `Reachable` product state's halves are themselves reachable in
their own component graphs — the key lemma `finiteReach` below needs.
Mechanical retargeting of the same `hcompat`/`Array.mem_flatMap`/
`Array.mem_map` case split `finiteReach.closed` always needed (back when
`FiniteReach` carried a `Std.HashSet` witness); the combinatorial content is
unchanged, only the conclusion (`Reachable.step` instead of a `HashSet.
contains` fact) differs. -/
private theorem reachable_imp (ba : BA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    ∀ {p : SysState × BAState},
      Reachable (initialStates ba sysInit) (getSuccessors ba sysSucc sysLabel) p →
      Reachable sysInit sysSucc p.1 ∧ Reachable ba.initialStates.toList ba.getSuccessors p.2 := by
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

/-- Corresponds to CAVA's `prod_finite_reachable` (`Automata.thy`,
`igba_sys_prod_precond`): the product's reachable states are contained in
`reachable(sys) × reachable(ba)`. The caller supplies their own system's
`FiniteReach` witness (their system being finitely-reachable is *their*
proof obligation, exactly as CAVA's `inter_spec` takes
`finite (sa.E⇧* `` sa.V0)` as a precondition rather than deriving it), and
this combines it with `BA.finiteReach` (`NestedDFS/NestedDFSTermination.lean`).
A pure existence proof — no cross-product `Std.HashSet` materialization
(`hashSetProd`, deleted) of any kind, cheap regardless of how large `sysFR`'s
own witness would have needed to be under the old design. -/
def finiteReach (ba : BA α) (hbawf : ba.WellFormed)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState) (sysFR : FiniteReach sysInit sysSucc) :
    FiniteReach (initialStates ba sysInit) (getSuccessors ba sysSucc sysLabel) :=
  (sysFR.prod (ba.finiteReach hbawf)).subset
    (fun p hp => reachable_imp ba sysSucc sysLabel sysInit hp)

end Product

end LTLLib
