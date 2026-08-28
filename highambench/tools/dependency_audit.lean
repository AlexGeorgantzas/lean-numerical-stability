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

private unsafe def declarationTypesDefEq
    (env : Environment) (left right : ConstantInfo) : IO Bool := do
  let context : Core.Context := {
    fileName := "<HighamBench semantic statement check>"
    fileMap := default
  }
  let state : Core.State := { env := env }
  Prod.fst <$> Core.CoreM.toIO (ctx := context) (s := state) do
    Meta.MetaM.run' do
      Meta.isDefEq left.type right.type

private unsafe def audit
    (moduleName targetName : Name)
    (expected? : Option (Name × Name) := none)
    (localModulesFile : System.FilePath := defaultLocalModulesFile) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let imports := match expected? with
    | none => #[{ module := moduleName }]
    | some (expectedModule, _) =>
        #[{ module := moduleName }, { module := expectedModule }]
  withImportModules imports {} fun env => do
    let some targetInfo := env.find? targetName
      | IO.eprintln s!"unknown target declaration: {targetName}"; return 3
    writeFields #["format", "2"]
    if let some (_, expectedName) := expected? then
      let some expectedInfo := env.find? expectedName
        | IO.eprintln s!"unknown expected declaration: {expectedName}"; return 3
      let equal ← declarationTypesDefEq env targetInfo expectedInfo
      writeFields #[
        "typeeq",
        targetName.toString,
        expectedName.toString,
        if equal then "true" else "false"
      ]
      if !equal then
        return 5
    let targetOwner := (ownerModule? env targetName).getD moduleName
    let localModules := (← loadLocalModules localModulesFile).insert moduleName
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

unsafe def run (args : List String) : IO UInt32 := do
  match args with
  | [moduleText, targetText] => audit moduleText.toName targetText.toName
  | [moduleText, targetText, expectedModuleText, expectedTargetText] =>
      audit moduleText.toName targetText.toName <|
        some (expectedModuleText.toName, expectedTargetText.toName)
  | [moduleText, targetText, expectedModuleText, expectedTargetText, localModulesFile] =>
      audit moduleText.toName targetText.toName
        (some (expectedModuleText.toName, expectedTargetText.toName))
        localModulesFile
  | _ =>
      IO.eprintln
        "usage: lean --run dependency_audit.lean MODULE TARGET [EXPECTED_MODULE EXPECTED_TARGET]"
      return 2

end HighamBenchDependencyAudit

unsafe def main (args : List String) : IO UInt32 :=
  HighamBenchDependencyAudit.run args
