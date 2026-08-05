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
  how `Pipeline.lean` is kept separate from `NestedDFS.lean`/`BA.lean`.
-/
import LTLLib.LTLtoGBA.GraphComplete
import LTLLib.DegeneralBridge
import LTLLib.LTLtoGBA.ExpandTermination
import LTLLib.Product

namespace LTLLib

variable {α : Type u} {S : Type w} [FSet (NNF α) S]
  {SysState : Type v} [BEq SysState] [Hashable SysState] [LawfulBEq SysState]
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

The caller supplies `sysFR : FiniteReach sysSucc` — proof that their own
system is finitely reachable — exactly as CAVA's `inter_spec` takes
`finite (sa.E⇧* `` sa.V0)` as a precondition rather than deriving it
(`Product.lean`'s `Product.finiteReach` docstring).

The emptiness check itself is parameterized by `checker : EmptinessChecker`
(`EmptinessCheck.lean` — the algorithm-agnostic contract; `nestedDFSChecker`,
its one existing refinement, lives in `NestedDFSTermination.lean` since
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
    (sysFR : FiniteReach sysSucc)
    (checker : EmptinessChecker (SysState × BAState) := nestedDFSChecker) :
    EmptinessResult (SysState × BAState) :=
  let negNNF := φ.toNNF false
  match hcg : createGraph (S := S) negNNF with
  | some st =>
    let ba := (constructGBA negNNF st).degeneralize
    let hbawf := degeneralize_wellFormed_any (constructGBA negNNF st)
      (constructGBA_wellFormed hcg)
    checker.check (Product.getSuccessors ba sysSucc sysLabel)
      (Product.finiteReach ba hbawf sysSucc sysLabel sysFR) (Product.isAccepting ba)
      (Product.initialStates ba sysInit)
  | none => .empty 0

end LTLLib
