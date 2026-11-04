module

/-
  The `#guard_axioms` command, which fails the build when a declaration depends on an axiom outside a given
  list. `PipelineTheorems.lean` pins the top-level results down with it.
-/
public meta import Lean

public meta section

open Lean Elab Command

/-- Assert that each declaration depends only on axioms from the given list. -/
elab "#guard_axioms " decls:ident,+ " ⊆ " "[" allowed:ident,* "]" : command => liftTermElabM do
  let allowed ← allowed.getElems.mapM fun ax => realizeGlobalConstNoOverloadWithInfo ax
  for decl in decls.getElems do
    let name ← realizeGlobalConstNoOverloadWithInfo decl
    let axioms ← collectAxioms name
    let unexpected := axioms.filter (!allowed.contains ·)
    unless unexpected.isEmpty do
      throwErrorAt decl "unexpected axioms in {name}: {unexpected}"
