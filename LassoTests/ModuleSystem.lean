module

/-
  Checks what the root module exports: that a client can reduce the public syntax and semantic API, that the
  exported tactic works without importing its implementation, that explicitly meta-imported algorithms stay
  executable, and that the private fuel bridge does not leak.
-/
import Lasso
import Lean.Elab.BuiltinEvalCommand
meta import Lasso

open Lasso

-- A client of the root module can reduce the public syntax and semantic API.
example (φ : NNF Nat) : φ.always = .release .ff φ := rfl

example (ξ : OmegaWord Nat) : NNF.satisfies ξ .tt := True.intro

-- The exported tactic works in a downstream module without importing its implementation.
example (n : Nat) : n + 1 = n + 1 := by
  set k := n + 1 with hk
  rfl

-- Ordinary algorithms remain executable when explicitly imported at meta phase.
#eval show IO Unit from do
  unless (NNF.tt : NNF Nat).subformulasDedup == [NNF.tt] do
    throw (IO.userError "subformula enumeration changed")

-- Check the actual exported environment, including definition-body boundaries.
run_meta do
  let env ← Lean.getEnv
  -- The fixpoint bodies are also needed when exporting partial_correctness metadata.
  for name in #[`Lasso.NNF.always, `Lasso.NNF.satisfies,
      `Lasso.exploreState, `Lasso.pruneLoopP] do
    unless (env.find? name).any (·.hasValue) do
      throwError "expected an exposed definition: {name}"
  for name in #[`Lasso.NNF.subformulasDedup, `Lasso.TGBA.edgeWitness] do
    unless (env.find? name).isSome do
      throwError "missing public declaration: {name}"
    if (env.find? name).any (·.hasValue) then
      throwError "unexpected exposed implementation: {name}"
  if (env.find? `Lasso.innerDFS_fuel_eq_innerDFSWF).isSome then
    throwError "the private fuel bridge leaked through the root module"
