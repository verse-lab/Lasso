/-
  End-to-end model checking: system × LTL formula φ → does the system
  satisfy φ?

  See `ProductModelChecker.md` at the repo root for the full design
  rationale and the CAVA source this is ported from.

  Corresponds to CAVA's `abs_model_check` (`CAVA_Abstract.thy`) — the piece
  `fullPipeline` (`Pipeline.lean`) deliberately left out (see that file's own
  docstring: "minus the `inter_spec`/system-intersection stage"). Standard
  automata-theoretic model checking: negate `φ`, build a `BA` for `¬φ`,
  product it against the caller's system (`Product.lean`), and check the
  product for emptiness — `sys ⊨ φ` iff the product is empty.

  Kept in its own file, separate from `Product.lean`, since `Product.lean`
  is the reusable on-the-fly graph-construction layer while this file is the
  specific "chain it all together for LTL model checking" wiring, matching
  how `Pipeline.lean` is kept separate from `NestedDFS/NestedDFSRef.lean`/`BA.lean`.
-/
import LTLLib.LTLtoGBA.GraphComplete
import LTLLib.DegeneralBridge
import LTLLib.LTLtoGBA.ExpandTermination
import LTLLib.Product
import LTLLib.OutputVerifyBA

namespace LTLLib

variable {α : Type u} {S : Type w} [FSet (NNF α) S]
  {SysState : Type v} [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
  [LawfulHashable SysState]
  [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] [DecidableEq α]

/-- Does `sys` (given by `sysInit`/`sysSucc`/`sysLabel`) satisfy `φ`?

Corresponds to CAVA's
```isabelle
abs_model_check _ _ _ _ sys φ ≡ do {
  gba ← ltl_to_gba_spec (Not_ltlc φ);
  (Gprod, map_state) ← inter_spec sys gba;
  find_ce_spec Gprod }
```
collapsed into one total function exactly as `fullPipeline` already does for
the system-free case: `createGraph`'s `none` branch is defensive dead code
(`createGraph_term` guarantees success for every formula), matching the
"junk value on unreachable input" pattern `fullPipeline` also uses.

`φ` is the *surface* `Formula α` (`LTL/Syntax.lean`), not `NNF α` — matching
`Not_ltlc φ` above, which wraps the *surface* formula in negation before any
NNF conversion runs. `fullPipeline` (`Pipeline.lean`) takes `NNF α` because it
never negates anything (it checks `φ`'s own satisfiability directly); this
function does need a negation, so it takes the type CAVA negates at, and
folds "negate, then normalize" into the single call `φ.toNNF false`
(`LTL/Syntax.lean`'s `pos`-flag convention: `toNNF pos (.not ψ) = toNNF
(!pos) ψ`, so `(Formula.not φ).toNNF true` and `φ.toNNF false` compute the
exact same NNF). Getting this backwards — taking `NNF α` and calling
`.neg` on an already-normalized formula — was the first draft of this
function; it happened to still be logically sound but did the negation at
the wrong layer relative to CAVA, redoing normalization work `toNNF false`
already does in one pass.

The caller supplies `sysFR : FiniteReach sysInit sysSucc` — proof that their
own system is finitely reachable — exactly as CAVA's `inter_spec` takes
`finite (sa.E⇧* `` sa.V0)` as a precondition rather than deriving it
(`Product.lean`'s `Product.finiteReach` docstring). This is now a bare
existence certificate (`FiniteReach` is a `Prop`, no `Std.HashSet` witness
of any kind) — a caller with e.g. a bounded-counter system state supplies a
cheap structural finiteness proof instead of enumerating/hashing every
reachable state.

The emptiness check itself is parameterized by `checker : EmptinessChecker`
(`EmptinessCheck.lean` — the algorithm-agnostic contract; `nestedDFSChecker`,
its one existing refinement, lives in `NestedDFS/NestedDFSTermination.lean` since
that part *is* nested-DFS-specific), defaulting to `nestedDFSChecker`. This
mirrors how CAVA's `abs_model_check`
is defined against the abstract `find_ce_spec` rather than any concrete
algorithm, with nested DFS proven as one *refinement* of that spec among
possibly several: swapping in a future SCC-based checker means proving a
new `EmptinessChecker` instance, not touching this function or any proof
built on top of it.

`EmptinessResult.empty` means `sys ⊨ φ`; `EmptinessResult.nonEmpty stem loop`
means the product found a run of `sys` violating `φ`, witnessed by
`(system state, ¬φ-automaton state)` pairs along `stem`/`loop`. -/
def modelCheck (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc)
    (checker : EmptinessChecker (SysState × BAState) := nestedDFSChecker) :
    EmptinessResult (SysState × BAState) :=
  let negNNF := φ.toNNF false
  match hcg : createGraph (S := S) negNNF with
  | some st =>
    let ba := (constructGBA negNNF st).degeneralize
    let hbawf := degeneralize_wellFormed_any (constructGBA negNNF st)
      (constructGBA_wellFormed hcg)
    checker.check (Product.getSuccessors ba sysSucc sysLabel)
      (Product.initialStates ba sysInit)
      (Product.finiteReach ba hbawf sysSucc sysLabel sysInit sysFR) (Product.isAccepting ba)
  | none => .empty 0

omit [LawfulHashable SysState] [LawfulBEq α] [LawfulHashable α] [DecidableEq α] in
/-- Unfolding lemma: `modelCheck` at a known `createGraph` result. Same
role as `Pipeline.lean`'s `fullPipeline_eq` — lets the two correctness
theorems below `rw` past the `createGraph`/`degeneralize` scaffolding
without re-deriving `createGraph_term`'s totality argument inline. -/
theorem modelCheck_eq (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc)
    (checker : EmptinessChecker (SysState × BAState))
    {st : ExpandState α S} (hcg : createGraph (φ.toNNF false) = some st) :
    modelCheck (S := S) φ sysInit sysSucc sysLabel sysFR checker =
      let ba := (constructGBA (φ.toNNF false) st).degeneralize
      let hbawf := degeneralize_wellFormed_any (constructGBA (φ.toNNF false) st)
        (constructGBA_wellFormed hcg)
      checker.check (Product.getSuccessors ba sysSucc sysLabel)
        (Product.initialStates ba sysInit)
        (Product.finiteReach ba hbawf sysSucc sysLabel sysInit sysFR)
        (Product.isAccepting ba) := by
  unfold modelCheck
  dsimp only
  split
  next st' hcg' =>
    obtain rfl : st' = st := Option.some.inj (hcg'.symm.trans hcg)
    rfl
  next hcg' => exact absurd (hcg'.symm.trans hcg) (by simp)

omit [LawfulHashable SysState] in
/-- Corresponds to CAVA's `abs_model_check_correct`'s `None` case
(`sa.lang sys ⊆ language_ltlc φ`): if `modelCheck` finds no counterexample,
every real run of the caller's system (through `Sys.toSpec` — see
`README.md`'s "Terminal states, and a deliberate divergence from CAVA" for
why that's `totalizeSucc sysSucc`, not raw `sysSucc`) satisfies `φ`, under
its own real labeling. `checker` is left universally quantified over any
`EmptinessChecker`, not fixed to `nestedDFSChecker` — matching
`ProductModelChecker.md`'s "keeping the correctness proof algorithm-agnostic"
design note, and CAVA's own `abs_model_check_correct` being proven once
against the abstract `find_ce_spec` contract rather than any concrete
algorithm. -/
theorem modelCheck_empty_unsat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc)
    (checker : EmptinessChecker (SysState × BAState)) {n : Nat}
    (h : modelCheck (S := S) φ sysInit sysSucc sysLabel sysFR checker = .empty n) :
    ∀ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ →
      Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  intro τ hτ
  by_contra hviolate
  obtain ⟨st, hcg, _⟩ := createGraph_term (S := S) (φ.toNNF false)
  rw [modelCheck_eq φ sysInit sysSucc sysLabel sysFR checker hcg] at h
  set gba := constructGBA (φ.toNNF false) st with hgba
  set ba := gba.degeneralize with hba
  have hwf := constructGBA_wellFormed hcg
  have hbawf := degeneralize_wellFormed_any gba hwf
  have hgba_acc : gba.toSpec.accepts (fun i a => a ∈ sysLabel (τ i)) :=
    (constructGBA_correct_weak hcg _).mpr ((Formula.toNNF_correct_neg _ φ).mp hviolate)
  have hba_acc : ba.toSpec.accepts (fun i a => a ∈ sysLabel (τ i)) :=
    (degeneralize_accepts_any gba hwf _).mpr hgba_acc
  obtain ⟨r, _, hrrun, hracc⟩ := Product.gsp_correct2 ba sysSucc sysLabel sysInit hτ hba_acc
  have hcyc : ∃ _ac : AcceptingCycle (Product.initialStates ba sysInit)
      (Product.getSuccessors ba sysSucc sysLabel) (Product.isAccepting ba), True :=
    exists_acceptingCycle_of_run (Product.finiteReach ba hbawf sysSucc sysLabel sysInit sysFR)
      hrrun.1 hrrun.2
      (fun N => by
        obtain ⟨j, hj⟩ := hracc ⟨0, Nat.one_pos⟩ N
        exact ⟨N + j, by omega, hj⟩)
  exact checker.empty_no_cycle h hcyc

omit [LawfulHashable SysState] in
/-- Corresponds to CAVA's `abs_model_check_correct`'s `Some (Some r)` case
(`graph_defs.is_run sys r ∧ sa_L sys ∘ r ∉ language_ltlc φ`): if `modelCheck`
finds a counterexample, there's a genuine, concrete infinite run of the
system violating `φ` under its own real labeling — not just an abstract
existence claim, the witness is literally built from the returned
`stem`/`loop` via `AcceptingCycle.toValidLassoProduct` (`OutputVerifyBA.lean`).
No `canonicalLabel`/`BA.WellFormed` reasoning needed here at all, unlike
`Pipeline.lean`'s `fullPipeline_nonEmpty_sat` — `Product.gsp_correct1`
already surfaces the caller's *real* `sysLabel` compatibility directly, see
`ModelCheckCorrectnessPlan.md` §3.4's callout. -/
theorem modelCheck_nonEmpty_sat (φ : Formula α) (sysInit : List SysState)
    (sysSucc : SysState → Array SysState) (sysLabel : SysState → Std.HashSet α)
    (sysFR : FiniteReach sysInit sysSucc)
    (checker : EmptinessChecker (SysState × BAState))
    {stem loop : List (SysState × BAState)}
    (h : modelCheck (S := S) φ sysInit sysSucc sysLabel sysFR checker = .nonEmpty stem loop) :
    ∃ τ : Nat → SysState, (Sys.toSpec sysSucc sysInit sysLabel).isRun τ ∧
      ¬ Formula.directSatisfies (fun i a => a ∈ sysLabel (τ i)) φ := by
  obtain ⟨st, hcg, _⟩ := createGraph_term (S := S) (φ.toNNF false)
  rw [modelCheck_eq φ sysInit sysSucc sysLabel sysFR checker hcg] at h
  set gba := constructGBA (φ.toNNF false) st with hgba
  set ba := gba.degeneralize with hba
  have hwf := constructGBA_wellFormed hcg
  have hbawf := degeneralize_wellFormed_any gba hwf
  obtain ⟨ac, _, _⟩ := checker.nonEmpty_valid h
  have hrrun := ac.toValidLassoProduct.run_isRun
  have hracc := ac.toValidLassoProduct.run_isAccepting
  obtain ⟨hτrun, hlang⟩ := Product.gsp_correct1 ba sysSucc sysLabel sysInit ⟨hrrun, hracc⟩
  refine ⟨Prod.fst ∘ ac.toValidLassoProduct.run, hτrun, fun hsat => ?_⟩
  obtain ⟨σ, hσrun, hσcompat, hσacc⟩ := hlang
  have hgba_acc : gba.toSpec.accepts (fun n a => a ∈ sysLabel (ac.toValidLassoProduct.run n).1) :=
    (degeneralize_accepts_any gba hwf _).mp ⟨σ, hσrun, hσcompat, hσacc⟩
  exact (Formula.toNNF_correct_neg _ φ).mpr ((constructGBA_correct_weak hcg _).mp hgba_acc) hsat

end LTLLib
