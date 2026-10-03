module

import LTLLib
import Lean.Elab.BuiltinEvalCommand
meta import LTLLib

open LTLLib

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
  for name in #[`LTLLib.NNF.always, `LTLLib.NNF.satisfies] do
    unless (env.find? name).any (·.hasValue) do
      throwError "expected an exposed definition: {name}"
  for name in #[`LTLLib.NNF.subformulasDedup, `LTLLib.TGBA.edgeWitness] do
    unless (env.find? name).isSome do
      throwError "missing public declaration: {name}"
    if (env.find? name).any (·.hasValue) then
      throwError "unexpected exposed implementation: {name}"
  if (env.find? `LTLLib.innerDFS_fuel_eq_innerDFSWF).isSome then
    throwError "the private fuel bridge leaked through the root module"
