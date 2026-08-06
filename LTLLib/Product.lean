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

/-- Cartesian product of two `HashSet`s, used to build a `FiniteReach`
witness for the product below. Specialized to `SysState`/`BAState` (rather
than kept fully generic) to avoid introducing fresh universe variables that
could be confused with the `α`/`SysState` ones already in scope here. -/
private def hashSetProd (A : Std.HashSet SysState) (B : Std.HashSet BAState) :
    Std.HashSet (SysState × BAState) :=
  Std.HashSet.ofList (A.toList.flatMap fun a => B.toList.map fun b => (a, b))

/-- Membership in `hashSetProd`: `(a, b)` is in the product iff `a`/`b` are
each in their own half. The lemma `hashSetProd` itself was missing before
`finiteReach.closed` could be proven (see that def's docstring). -/
private theorem hashSetProd_mem [LawfulBEq SysState] [LawfulHashable SysState]
    (A : Std.HashSet SysState) (B : Std.HashSet BAState) (a : SysState) (b : BAState) :
    (a, b) ∈ hashSetProd A B ↔ a ∈ A ∧ b ∈ B := by
  simp [hashSetProd, Std.HashSet.mem_ofList, List.mem_flatMap, List.mem_map, Prod.mk.injEq,
    Std.HashSet.mem_toList]

/-- Corresponds to CAVA's `prod_finite_reachable` (`Automata.thy`,
`igba_sys_prod_precond`): the product's reachable states are contained in
`reachable(sys) × reachable(ba)`. The caller supplies their own system's
`FiniteReach` witness (their system being finitely-reachable is *their*
proof obligation, exactly as CAVA's `inter_spec` takes
`finite (sa.E⇧* `` sa.V0)` as a precondition rather than deriving it), and
this combines it with `BA.finiteReach` (`NestedDFS/NestedDFSTermination.lean`).

`[LawfulBEq SysState] [LawfulHashable SysState]` (beyond the file's own
`variable` block) are needed only here, for `hashSetProd_mem`'s
`Std.HashSet.mem_ofList`/`mem_toList` lemmas to hold of the product
`Std.HashSet (SysState × BAState)` — `BAState` already has both instances
(`BA.lean`). -/
def finiteReach [LawfulBEq SysState] [LawfulHashable SysState] (ba : BA α) (hbawf : ba.WellFormed)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysSucc) :
    FiniteReach (getSuccessors ba sysSucc sysLabel) where
  univ := hashSetProd sysFR.univ (ba.finiteReach hbawf).univ
  closed := by
    rintro ⟨s, q⟩ hsq ⟨s', q'⟩ hst
    obtain ⟨hs_mem, hq_mem⟩ := (hashSetProd_mem ..).mp (Std.HashSet.mem_iff_contains.mpr hsq)
    unfold getSuccessors at hst
    cases hcompat : ba.compatible q (sysLabel s) with
    | false => simp [hcompat] at hst
    | true =>
      simp only [hcompat, if_true, Array.mem_flatMap, Array.mem_map] at hst
      obtain ⟨s'', hs''_mem, q'', hq''_mem, heq⟩ := hst
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
      have hs'_mem : s'' ∈ sysFR.univ :=
        Std.HashSet.mem_iff_contains.mpr
          (sysFR.closed s (Std.HashSet.mem_iff_contains.mp hs_mem) s'' hs''_mem)
      have hq'_mem : q'' ∈ (ba.finiteReach hbawf).univ :=
        Std.HashSet.mem_iff_contains.mpr
          ((ba.finiteReach hbawf).closed q (Std.HashSet.mem_iff_contains.mp hq_mem) q'' hq''_mem)
      exact Std.HashSet.mem_iff_contains.mp ((hashSetProd_mem ..).mpr ⟨hs'_mem, hq'_mem⟩)

end Product

end LTLLib
