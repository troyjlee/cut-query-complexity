import QuantumQueryComplexity.Test.AxiomSupport

/-! # Test-only axiom audit with one environment scan

The defining-module criterion and allowed axioms are the same as in the
sibling audit helper. Declarations are grouped in one pass, and each call
to `Lean.collectAxioms` supplies both the rejection check and the report.
Missing/empty modules, absent or out-of-scope pins, and forbidden transitive
axioms all fail. This module is not imported by the production library.
-/

namespace CutQueryComplexityChecks.AxiomAudit
open Lean Elab Command
open QuantumQueryComplexity.AxiomAudit (allowedAxioms)

def auditDecl (n : Name) : CoreM (Array Name) := do
  unless (← getEnv).contains n do
    throwError "axiom audit: the declaration `{n}` does not exist."
  let axs ← collectAxioms n
  let bad := axs.filter fun a => !allowedAxioms.contains a
  unless bad.isEmpty do
    throwError "axiom audit: `{n}` depends on the forbidden axiom(s) {bad.toList}."
  return axs

def auditModules (mods : List Name) (pinNames : List Name) : CoreM Unit := do
  let env ← getEnv
  let mut groups : NameMap (Array Name) := {}
  for m in mods do
    unless env.header.moduleNames.contains m do
      throwError "axiom audit: the module `{m}` is not in the environment."
    if groups.contains m then
      throwError "axiom audit: the module `{m}` is listed more than once."
    groups := groups.insert m #[]
  for p in pinNames do
    unless env.contains p do
      throwError "axiom audit: the pinned declaration `{p}` does not exist."
    let some idx := env.getModuleIdxFor? p
      | throwError "axiom audit: the pinned declaration `{p}` has no defining module."
    let pm := env.header.moduleNames[idx.toNat]!
    unless mods.contains pm do
      throwError "axiom audit: the pinned declaration `{p}` lives in `{pm}`, which is not audited."
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if let some ns := groups.find? m then
        groups := groups.insert m (ns.push n)
  let mut total := 0
  let mut seen : Array Name := #[]
  for m in mods do
    let decls := (groups.find? m).getD #[]
    if decls.isEmpty then
      throwError "axiom audit: the module `{m}` contributes no declaration; a checker that checks nothing must fail."
    for n in decls do
      let axs ← auditDecl n
      for a in axs do
        unless seen.contains a do seen := seen.push a
    total := total + decls.size
    logInfo m!"axiom audit: {m}: {decls.size} declarations checked"
  logInfo m!"axiom audit: {total} declarations in {mods.length} modules, {pinNames.length} pins; axioms encountered: {seen.toList}"

syntax (name := auditModulesCmd)
  "#audit_cut_axioms " "[" ident,* "]" " pins " "[" ident,* "]" : command

@[command_elab auditModulesCmd] def elabAuditModules : CommandElab := fun stx => do
  match stx with
  | `(#audit_cut_axioms [$ms,*] pins [$ps,*]) =>
      liftCoreM (auditModules (ms.getElems.toList.map (·.getId)) (ps.getElems.toList.map (·.getId)))
  | _ => throwUnsupportedSyntax

syntax (name := auditDeclCmd) "#audit_cut_decl " ident : command

@[command_elab auditDeclCmd] def elabAuditDecl : CommandElab := fun stx => do
  match stx with
  | `(#audit_cut_decl $n) => liftCoreM (discard <| auditDecl n.getId)
  | _ => throwUnsupportedSyntax

end CutQueryComplexityChecks.AxiomAudit
