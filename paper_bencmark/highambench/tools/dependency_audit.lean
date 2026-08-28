/-
HighamBench target dependency audit.

This program dynamically imports a compiled submission module, walks constants
used by the target theorem's type and proof, follows task-local helper bodies,
and emits a small tab-separated report.  It deliberately reports ownership by
compiled Lean module rather than matching names in source text.

The hidden validator writes candidate source-module names to
`.highambench-validator-local-modules` before invoking this program. This lets
the audit treat axioms in imported candidate helper modules exactly like axioms
in the main submission module.

Usage:
  lake env lean --run dependency_audit.lean Submission.Module target.name
  lake env lean --run dependency_audit.lean Submission.Module --pairs-file PAIRS EXPECTED_MODULE LOCAL_MODULES
-/

import Lean

open Lean

namespace HighamBenchDependencyAudit

private def defaultLocalModulesFile : System.FilePath :=
  ".highambench-validator-local-modules"

private def loadLocalModules (localModulesFile : System.FilePath) : IO NameSet := do
  let contents ←
    try
      IO.FS.readFile localModulesFile
    catch _ =>
      pure ""
  return contents.splitOn "\n" |>.foldl (init := {}) fun names line =>
    if line.isEmpty then names else names.insert line.toName

private structure AuditPlan where
  pairs : Array (Name × Name) := #[]
  renames : Array (Name × Name) := #[]

private def loadAuditPairs
    (pairsFile : System.FilePath) : IO AuditPlan := do
  let contents ← IO.FS.readFile pairsFile
  let mut plan : AuditPlan := {}
  for line in contents.splitOn "\n" do
    if !line.isEmpty then
      match line.splitOn "\t" with
      | [kind, candidate, expected] =>
          if candidate.isEmpty || expected.isEmpty then
            throw <| IO.userError "empty declaration in audit-pairs file"
          let pair := (candidate.toName, expected.toName)
          if kind == "proof" then
            plan := { plan with pairs := plan.pairs.push pair }
          else if kind == "map" then
            plan := { plan with renames := plan.renames.push pair }
          else
            throw <| IO.userError "unknown audit-pairs row kind"
      | _ => throw <| IO.userError "malformed audit-pairs file"
  if plan.pairs.isEmpty || plan.renames.isEmpty then
    throw <| IO.userError "audit-pairs file needs proof and map rows"
  return plan

private def bodyConstants : ConstantInfo → NameSet
  | .defnInfo value => value.value.getUsedConstantsAsSet
  | .thmInfo value => value.value.getUsedConstantsAsSet
  | .opaqueInfo value => value.value.getUsedConstantsAsSet
  | .recInfo value => value.rules.foldl (init := {}) fun names rule =>
      names ++ rule.rhs.getUsedConstantsAsSet
  | _ => {}

private def allConstants (info : ConstantInfo) : NameSet :=
  info.type.getUsedConstantsAsSet ++ bodyConstants info

private def ownerModule? (env : Environment) (name : Name) : Option Name := do
  let moduleIdx ← env.getModuleIdxFor? name
  return env.header.moduleNames[moduleIdx]!

private def isNumStabilityModule (moduleName : Name) : Bool :=
  let text := moduleName.toString
  text == "NumStability" || text.startsWith "NumStability."

private structure Finding where
  name : Name
  moduleName : Name
  distance : Nat

private def findingLess (left right : Finding) : Bool :=
  left.distance < right.distance ||
    (left.distance == right.distance && left.name.toString < right.name.toString)

private def sanitize (value : String) : String :=
  value.replace "\t" " " |>.replace "\r" " " |>.replace "\n" " "

private def writeFields (fields : Array String) : IO Unit :=
  IO.println <| String.intercalate "\t" (fields.toList.map sanitize)

private def mappedName?
    (renames : List (Name × Name)) (name : Name) : Option Name :=
  match renames with
  | [] => none
  | (candidate, expected) :: rest =>
      if name == expected then
        some candidate
      else
        let text := name.toString
        let expectedPrefix := expected.toString ++ "."
        if text.startsWith expectedPrefix then
          some <| (candidate.toString ++ "." ++ text.drop expectedPrefix.length).toName
        else
          mappedName? rest name

private partial def renameConstants
    (renames : List (Name × Name)) : Expr → Expr
  | .bvar index => .bvar index
  | .fvar id => .fvar id
  | .mvar id => .mvar id
  | .sort level => .sort level
  | .const name levels => .const ((mappedName? renames name).getD name) levels
  | .app fn argument =>
      .app (renameConstants renames fn) (renameConstants renames argument)
  | .lam name type body info =>
      .lam name (renameConstants renames type) (renameConstants renames body) info
  | .forallE name type body info =>
      .forallE name (renameConstants renames type) (renameConstants renames body) info
  | .letE name type value body nondep =>
      .letE name (renameConstants renames type) (renameConstants renames value)
        (renameConstants renames body) nondep
  | .lit literal => .lit literal
  | .mdata data expression => .mdata data (renameConstants renames expression)
  | .proj typeName index value =>
      .proj ((mappedName? renames typeName).getD typeName) index
        (renameConstants renames value)

private unsafe def declarationTypesDefEq
    (env : Environment) (left right : ConstantInfo)
    (renames : Array (Name × Name) := #[]) : IO Bool := do
  let context : Core.Context := {
    fileName := "<HighamBench semantic statement check>"
    fileMap := default
  }
  let state : Core.State := { env := env }
  Prod.fst <$> Core.CoreM.toIO (ctx := context) (s := state) do
    Meta.MetaM.run' do
      Meta.isDefEq left.type (renameConstants renames.toList right.type)

private unsafe def auditInEnvironment
    (env : Environment) (moduleName targetName : Name)
    (expected? : Option (Name × Name)) (localModulesBase : NameSet)
    (renames : Array (Name × Name) := #[]) : IO UInt32 := do
  let some targetInfo := env.find? targetName
    | IO.eprintln s!"unknown target declaration: {targetName}"; return 3
  writeFields #["format", "2"]
  if let some (_, expectedName) := expected? then
    let some expectedInfo := env.find? expectedName
      | IO.eprintln s!"unknown expected declaration: {expectedName}"; return 3
    let equal ← declarationTypesDefEq env targetInfo expectedInfo renames
    writeFields #[
      "typeeq",
      targetName.toString,
      expectedName.toString,
      if equal then "true" else "false"
    ]
    if !equal then
      return 5
  let targetOwner := (ownerModule? env targetName).getD moduleName
  let localModules := localModulesBase.insert moduleName
  writeFields #["target", targetName.toString, targetOwner.toString]
  let sortedLocalModules := localModules.toArray.qsort fun left right =>
    left.toString < right.toString
  for localModule in sortedLocalModules do
    writeFields #["localmodule", localModule.toString]

  let mut queue : Array (Name × Nat) := #[(targetName, 0)]
  let mut cursor := 0
  let mut seen : NameSet := {}
  let mut library : Array Finding := #[]
  let mut forbidden : Array (Name × String) := #[]
  while cursor < queue.size do
    let ⟨name, distance⟩ := queue[cursor]!
    cursor := cursor + 1
    if !seen.contains name then
      seen := seen.insert name
      if let some info := env.find? name then
        if name != targetName then
          if name.toString.contains "sorryAx" then
            forbidden := forbidden.push (name, "sorry placeholder")
          if let some owner := ownerModule? env name then
            if isNumStabilityModule owner then
              library := library.push {
                name := name
                moduleName := owner
                distance := distance
              }
            if localModules.contains owner then
              match info with
              | .axiomInfo _ =>
                  forbidden := forbidden.push (name, "task-local axiom")
              | _ => pure ()
        let dependencies :=
          (allConstants info).toArray.qsort fun left right =>
            left.toString < right.toString
        for dependency in dependencies do
          if !seen.contains dependency then
            queue := queue.push (dependency, distance + 1)

  let sortedLibrary := library.qsort findingLess
  let sortedForbidden := forbidden.qsort fun left right =>
    left.1.toString < right.1.toString
  for finding in sortedLibrary do
    writeFields #[
      "library",
      finding.name.toString,
      finding.moduleName.toString,
      toString finding.distance
    ]
  for finding in sortedForbidden do
    writeFields #["forbidden", finding.1.toString, finding.2]
  writeFields #["visited", toString seen.size]
  writeFields #["summary", toString sortedLibrary.size, toString sortedForbidden.size]
  return if sortedForbidden.isEmpty then 0 else 4

private unsafe def audit
    (moduleName targetName : Name)
    (expected? : Option (Name × Name) := none)
    (localModulesFile : System.FilePath := defaultLocalModulesFile)
    (renames : Array (Name × Name) := #[]) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let imports := match expected? with
    | none => #[{ module := moduleName }]
    | some (expectedModule, _) =>
        #[{ module := moduleName }, { module := expectedModule }]
  let localModules ← loadLocalModules localModulesFile
  withImportModules imports {} fun env =>
    auditInEnvironment env moduleName targetName expected? localModules renames

unsafe def run (args : List String) : IO UInt32 := do
  match args with
  | [moduleText, targetText] => audit moduleText.toName targetText.toName
  | [moduleText, targetText, expectedModuleText, expectedTargetText] =>
      audit moduleText.toName targetText.toName <|
        some (expectedModuleText.toName, expectedTargetText.toName)
  | [moduleText, "--pairs-file", pairsFile, expectedModuleText, localModulesFile] =>
      let plan ← loadAuditPairs pairsFile
      initSearchPath (← findSysroot)
      let moduleName := moduleText.toName
      let expectedModule := expectedModuleText.toName
      let localModules ← loadLocalModules localModulesFile
      withImportModules #[{ module := moduleName }, { module := expectedModule }] {} fun env => do
        let mut result : UInt32 := 0
        for ⟨targetName, expectedName⟩ in plan.pairs do
          let code ← auditInEnvironment env moduleName targetName
            (some (expectedModule, expectedName)) localModules plan.renames
          if result == 0 && code != 0 then
            result := code
        return result
  | [moduleText, targetText, expectedModuleText, expectedTargetText, localModulesFile] =>
      audit moduleText.toName targetText.toName
        (some (expectedModuleText.toName, expectedTargetText.toName))
        localModulesFile
  | _ =>
      IO.eprintln
        "usage: lean --run dependency_audit.lean MODULE TARGET [EXPECTED_MODULE EXPECTED_TARGET] | MODULE --pairs-file PAIRS EXPECTED_MODULE LOCAL_MODULES"
      return 2

end HighamBenchDependencyAudit

unsafe def main (args : List String) : IO UInt32 :=
  HighamBenchDependencyAudit.run args
