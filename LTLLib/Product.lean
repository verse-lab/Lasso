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
import LTLLib.Acceptance
import Mathlib.Data.Finite.Prod

namespace LTLLib

namespace Product

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]

/-- Corresponds to CAVA's `g_V0 = igba.V0 × sa.V0`
(`igba_sys_prod_precond.prod`, `Automata.thy`) — the *unfiltered* full
product, no compatibility pre-filter. An incompatible initial pair simply
has no successors once `getSuccessors`'s gate is evaluated below, and is
harmless dead weight for the DFS; CAVA doesn't filter it out either. -/
def initialStates (ba : BA α) (sysInit : List SysState) :
    List (SysState × BAState) :=
  sysInit.flatMap fun s => ba.initialStates.toList.map fun q => (s, q)

/-- Wraps a successor function so that a state with no outgoing edges gets a
self-loop instead — every state under `totalizeSucc succs` has at least one
successor.

LTL/Büchi-automaton semantics are defined over *infinite* words: a run that
simply stops is not something any standard Kripke structure admits. Left
untouched, a genuinely terminal client state becomes a dead end in the
product graph too, so nested DFS can never close a cycle through it —
`modelCheck` would silently miss a real counterexample whose violation only
manifests by the system stalling forever there (e.g. `□◇p` failing because
the system gets stuck somewhere `p` never holds again). The standard
model-checking convention (matching how NuSMV/SPIN treat deadlock states)
reads a terminal state as "the system stays here forever"; this wrapper
makes that reading literal by inserting the missing self-loop, so every
finite prefix into the client's system extends to a genuine infinite run.

This is not just an analogy to NuSMV/SPIN — it's CAVA's own construction:
`CAVA_Automata/Stuttering_Extension.thy`'s `stutter_extend_edges V E ≡ E ∪
{(v,v) | v. v ∈ V ∧ v ∉ Domain E}` is this function verbatim, with proofs
that it preserves reachability (`stutter_extend_edges_rtrancl`) and
bisimulation (`stutter_extend`). CAVA never wires it into `inter_spec`/
`abs_model_check` themselves, though — it's consumed by the SM/BoolProgs/
Promela concrete-system-encoding layer, a client applying it by hand before
ever building its `sa_rec`, not the abstract product-construction pipeline
this file ports. So CAVA's own theorems already confirm the construction is
sound *when a client does it*; here it's applied automatically, inside
`getSuccessors` below, and `reachable_totalizeSucc_imp`/
`finiteReach_totalizeSucc` (plus `Sys.toSpec` being stated over
`totalizeSucc sysSucc` rather than raw `sysSucc`) carry that same soundness
through every caller instead of leaving it an obligation someone could
forget. See `README.md`'s "Terminal states, and a deliberate divergence
from CAVA" for the full writeup. -/
def totalizeSucc {State : Type u} (succs : State → Array State) : State → Array State :=
  fun s =>
    let ss := succs s
    if ss.isEmpty then #[s] else ss

/-- The states reachable under `totalizeSucc succs` are exactly the states
reachable under `succs` — the wrapper only ever adds a self-loop on a
state that is *already* reachable, it never makes a new state reachable.
Only this direction (totalized-reachable → original-reachable) is needed:
`finiteReach` below uses it to transport the caller's `sysFR` witness across
the wrapper without asking the caller to re-prove anything about
`totalizeSucc sysSucc`. -/
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

/-- Transport a `FiniteReach` witness for the client's raw `sysSucc` across
the `totalizeSucc` wrapper: totalizing never grows the reachable set (see
`reachable_totalizeSucc_imp`), so the same finiteness proof applies to
`totalizeSucc sysSucc` unchanged. -/
theorem finiteReach_totalizeSucc {State : Type u} (initialStates : List State)
    (succs : State → Array State) (fr : FiniteReach initialStates succs) :
    FiniteReach initialStates (totalizeSucc succs) :=
  fr.subset (fun _ hs => reachable_totalizeSucc_imp initialStates succs hs)

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
successor pair once produced.

Uses `totalizeSucc sysSucc`, not the caller's raw `sysSucc`, as the actual
source of system-side edges — see `totalizeSucc`'s docstring for why a
terminal client state must be read as a self-loop for LTL/Büchi purposes. -/
def getSuccessors (ba : BA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) :
    (SysState × BAState) → Array (SysState × BAState) :=
  fun (s, q) =>
    if ba.compatible q (sysLabel s) then
      (totalizeSucc sysSucc s).flatMap fun s' => (ba.getSuccessors q).map fun q' => (s', q')
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
contains` fact) differs.

System-side conclusion is stated over `totalizeSucc sysSucc`, matching what
`getSuccessors` actually steps through — see `totalizeSucc`'s docstring. -/
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

/-- Corresponds to CAVA's `prod_finite_reachable` (`Automata.thy`,
`igba_sys_prod_precond`): the product's reachable states are contained in
`reachable(sys) × reachable(ba)`. The caller supplies their own system's
`FiniteReach` witness for their raw `sysSucc` (their system being
finitely-reachable is *their* proof obligation, exactly as CAVA's
`inter_spec` takes `finite (sa.E⇧* `` sa.V0)` as a precondition rather than
deriving it), and this combines it with `BA.finiteReach`
(`NestedDFS/NestedDFSTermination.lean`) — transporting `sysFR` across
`totalizeSucc` first (`finiteReach_totalizeSucc`) since that's the successor
function `getSuccessors` actually steps through. A pure existence proof — no
cross-product `Std.HashSet` materialization (`hashSetProd`, deleted) of any
kind, cheap regardless of how large `sysFR`'s own witness would have needed
to be under the old design. -/
def finiteReach (ba : BA α) (hbawf : ba.WellFormed)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysInit : List SysState) (sysFR : FiniteReach sysInit sysSucc) :
    FiniteReach (initialStates ba sysInit) (getSuccessors ba sysSucc sysLabel) :=
  ((finiteReach_totalizeSucc sysInit sysSucc sysFR).prod (ba.finiteReach hbawf)).subset
    (fun p hp => reachable_imp ba sysSucc sysLabel sysInit hp)

end Product

/-! ## System run / system language

Item 1 of `ModelCheckCorrectnessPlan.md` — CAVA's `sa.is_run`/`sa.accept`/
`sa.lang` (`CAVA_Automata/Digraph.thy`'s `graph_defs.is_run`,
`CAVA_Automata/Automata.thy`'s `sa` locale). Reused via `OASpec` at `k = 0`
rather than a hand-written duplicate — see the plan doc §2.2 for why this is
the CAVA-faithful reading (`sa`/`igba` already share one `is_run` via
`graph_defs` in the Isabelle source; `OASpec` is the same shared structure
here) and not a simplification invented for this port. -/

/-- Corresponds to CAVA's `sa_rec`/`sa` locale (`Automata.thy`) via the
`graph_defs`-shared `is_run` (`Digraph.thy`) — see
`ModelCheckCorrectnessPlan.md` §2 for the full correspondence and why
`k = 0` (a plain Kripke structure has no Büchi-style acceptance condition,
so `OASpec.isAcceptingRun` at `k = 0` is vacuous over every run, collapsing
`OASpec.accepts` down to exactly `∃r. is_run r ∧ w = L∘r`).

Deliberately stated over `Product.totalizeSucc sysSucc`, not the caller's
raw `sysSucc` — see `README.md`'s "Terminal states, and a deliberate
divergence from CAVA": CAVA's own `sa.is_run` has no deadlock handling at
all (a state with no outgoing edge simply can never appear at a non-final
run position), so it implicitly relies on the client's `g_E` already being
total; this port can't assume that of its own caller, hence `totalizeSucc`.

`labelCompat` is exact membership-agreement (`↔`, not the one-directional
containment `BA.toSpec`/`GBA.toSpec` use for their `pos`/`neg` checks):
`sa_L` is a genuine deterministic function on Kripke-structure states, not a
many-valuations-compatible relation like the automaton side's tableau
states — see `canonicalLabel`'s docstring (`Acceptance.lean`) for the same
sa_L-vs-automaton-labeling contrast, there because `canonicalLabel` exists
specifically to work around the lack of a system-side function like this
one existing yet; now that it does, `runCompatible` with this `labelCompat`
recovers CAVA's `w = L∘r` directly, with no `canonicalLabel`-style synthesis
needed. -/
def Sys.toSpec {α : Type u} {SysState : Type v} [BEq α] [Hashable α]
    (sysSucc : SysState → Array SysState) (sysInit : List SysState)
    (sysLabel : SysState → Std.HashSet α) : OASpec SysState α 0 where
  trans s t := t ∈ Product.totalizeSucc sysSucc s
  initial s := s ∈ sysInit
  labelCompat s v := ∀ a, v a ↔ a ∈ sysLabel s
  acceptSet := Fin.elim0

/-! ## Product run decomposition + acceptance transfer

Item 2 of `ModelCheckCorrectnessPlan.md` — CAVA's `prod_run`/`prod_acc`/
`gsp_correct1`/`gsp_correct2` (`CAVA_Automata/Automata.thy`'s
`igba_sys_prod_precond` locale), ported directly against `Product`'s own
successor/initial/accepting functions rather than an abstract `prod` value.
`gsp_correct1`/`gsp_correct2` themselves are step 3 of the plan, not this
one — this section only covers `toSpec`/`run_decompose`/`run_combine`/
`acc_iff`. -/

namespace Product

variable {α : Type u} {SysState : Type v} [BEq α] [Hashable α]

/-- Corresponds to instantiating `igba_sys_prod_precond.prod` as an
`OASpec`-shaped run/acceptance carrier — the Lean analogue of the `prod`
locale value itself, not just its `g_E`/`g_V0` fields `getSuccessors`/
`initialStates` already expose. -/
def toSpec (ba : BA α) (sysSucc : SysState → Array SysState)
    (sysLabel : SysState → Std.HashSet α) (sysInit : List SysState) :
    OASpec (SysState × BAState) α 1 where
  trans p p' := p' ∈ getSuccessors ba sysSucc sysLabel p
  initial p := p ∈ initialStates ba sysInit
  labelCompat p v := ∀ a, v a ↔ a ∈ sysLabel p.1
  acceptSet _ p := isAccepting ba p

/-- One-step membership shape of `getSuccessors`, generalizing the case
split `reachable_imp`'s step case already does into a standalone iff —
shared by `run_decompose`/`run_combine` below, each of which only needs one
direction. -/
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

/-- Corresponds to `prod_run`'s "→" direction: a product run decomposes
into a BA run and a `Sys.toSpec` run that stay `compatible` at every step. -/
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

/-- Corresponds to `prod_run`'s "←" direction (the "combine" half CAVA
folds into the same iff, split out here for Lean ergonomics — see
`ModelCheckCorrectnessPlan.md` §3.1 note 2): a BA run and a `Sys.toSpec`
run that agree at every step under `ba.compatible` combine into a genuine
product run. -/
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

/-- Corresponds to `prod_acc` — no `range (snd∘r) ⊆ sa.V`-style side
hypothesis needed: `isAccepting` already dropped CAVA's analogous `s ∈ sa.V`
guard (see `isAccepting`'s own docstring above), so this direction is
unconditional and definitional. -/
theorem acc_iff (ba : BA α) (p : SysState × BAState) :
    isAccepting ba p = ba.isAccepting p.2 := by
  obtain ⟨_, _⟩ := p
  rfl

/-- Bridges `BA.compatible`'s Bool computation (the runtime edge-gate
`getSuccessors` actually evaluates) to `BA.toSpec.labelCompat`'s Prop-level
match (what `ba.toSpec.accepts`/`runCompatible` need) — needed to move
between `run_decompose`'s compatibility output and `gsp_correct1`/
`gsp_correct2`'s `ba.toSpec.accepts` statements below. Not otherwise needed
anywhere in the codebase before this: every existing `labelCompat` proof
(`DegeneralBridge.lean`, `Pipeline.lean`) goes through `canonicalLabel_compat`
instead, built from the automaton's own synthesized labeling rather than an
externally supplied `Std.HashSet` like `sysLabel`. -/
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

/-- Corresponds to `gsp_correct1`: an accepting product run decomposes into
a `Sys.toSpec` run and a genuine BA-language membership witness for the
system's *real* labeling along that run (`sysLabel`, not `canonicalLabel` —
`run_decompose`'s compatibility clause already supplies exactly the fact
needed, no synthesis required). Soundness direction, used directly by
`modelCheck_nonEmpty_sat` (`ModelCheckCorrectnessPlan.md` §3.4). -/
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

/-- Corresponds to `gsp_correct2`: a genuine system run whose real labeling
lies in the BA's language combines (via `run_combine`) into an accepting
product run projecting back down to it. Completeness direction, used
directly by `modelCheck_empty_unsat` (`ModelCheckCorrectnessPlan.md` §3.4). -/
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

end LTLLib
