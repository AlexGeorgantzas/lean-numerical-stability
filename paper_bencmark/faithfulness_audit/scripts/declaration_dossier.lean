/-
Emit the semantic dependency closure of a HighamBench target declaration.

The target proof is deliberately excluded. The audit concerns what the target
states, so traversal starts from the theorem type and follows the types and
bodies of declarations owned by the supplied benchmark modules. Declarations
at the external Lean/mathlib boundary are printed but not recursively unfolded.

Usage:
  lake env lean --run declaration_dossier.lean \
    TARGET_MODULE TARGET_DECLARATION LOCAL_MODULES_FILE
-/

import Lean

open Lean

namespace HighamBenchFaithfulnessDossier

private structure Dependency where
  name : Name
  owner : Name
  distance : Nat
  role : String
  kind : String
  typeReadable : String
  typeExplicit : String
  bodyReadable : String

private structure Edge where
  parent : Name
  child : Name
  origin : String

private def escape (value : String) : String :=
  value.replace "\\" "\\\\"
    |>.replace "\t" "\\t"
    |>.replace "\r" "\\r"
    |>.replace "\n" "\\n"

private def writeFields (fields : Array String) : IO Unit :=
  IO.println <| String.intercalate "\t" (fields.toList.map escape)

private def loadNames (path : System.FilePath) : IO NameSet := do
  let contents ← IO.FS.readFile path
  return contents.splitOn "\n" |>.foldl (init := {}) fun names line =>
    let line := line.trimAscii.toString
    if line.isEmpty then names else names.insert line.toName

private def ownerModule? (env : Environment) (name : Name) : Option Name := do
  let moduleIdx ← env.getModuleIdxFor? name
  return env.header.moduleNames[moduleIdx]!

private def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo info => if info.hints.isAbbrev then "abbrev" else "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def body? : ConstantInfo → Option Expr
  | .defnInfo info => some info.value
  | .opaqueInfo info => some info.value
  | _ => none

private def bodyConstants : ConstantInfo → NameSet
  | .defnInfo info => info.value.getUsedConstantsAsSet
  | .opaqueInfo info => info.value.getUsedConstantsAsSet
  | .recInfo info => info.rules.foldl (init := {}) fun names rule =>
      names ++ rule.rhs.getUsedConstantsAsSet
  | _ => {}

private def structuralConstants : ConstantInfo → Array Name
  | .inductInfo info => info.ctors.toArray
  | _ => #[]

private unsafe def ppExprIn
    (env : Environment) (expression : Expr) (explicit : Bool) : IO String := do
  let context : Core.Context := {
    fileName := "<HighamBench faithfulness declaration dossier>"
    fileMap := default
  }
  let state : Core.State := { env := env }
  Prod.fst <$> Core.CoreM.toIO (ctx := context) (s := state) do
    let render : CoreM String := Meta.MetaM.run' do
      return (← Meta.ppExpr expression).pretty
    if explicit then
      withOptions (fun options => options.setBool `pp.all true) render
    else
      withOptions (fun options =>
        options.setBool `pp.universes false
          |>.setBool `pp.explicit false
          |>.setBool `pp.coercions true) render

private def dependencyLess (left right : Dependency) : Bool :=
  let leftRank := if left.role == "local" then 0 else 1
  let rightRank := if right.role == "local" then 0 else 1
  leftRank < rightRank ||
    (leftRank == rightRank &&
      (left.distance < right.distance ||
        (left.distance == right.distance &&
          left.name.toString < right.name.toString)))

private def edgeLess (left right : Edge) : Bool :=
  left.parent.toString < right.parent.toString ||
    (left.parent == right.parent &&
      (left.child.toString < right.child.toString ||
        (left.child == right.child && left.origin < right.origin)))

private unsafe def emit
    (targetModule targetName : Name) (localModulesFile : System.FilePath) : IO UInt32 := do
  initSearchPath (← findSysroot)
  withImportModules #[{ module := targetModule }] {} fun env => do
    let some targetInfo := env.find? targetName
      | IO.eprintln s!"unknown target declaration: {targetName}"; return 3
    let localModules := (← loadNames localModulesFile).insert targetModule

    writeFields #["format", "1"]
    writeFields #["target", targetName.toString]
    writeFields #["target-readable", ← ppExprIn env targetInfo.type false]
    writeFields #["target-explicit", ← ppExprIn env targetInfo.type true]

    let sortedModules := env.header.moduleNames.qsort fun left right =>
      left.toString < right.toString
    for moduleName in sortedModules do
      writeFields #["environment-module", moduleName.toString]

    let initial := targetInfo.type.getUsedConstantsAsSet.toArray.qsort fun left right =>
      left.toString < right.toString
    let mut queue : Array (Name × Nat) := initial.map fun name => (name, 1)
    let mut cursor := 0
    let mut seen : NameSet := {}
    let mut dependencies : Array Dependency := #[]
    let mut edges : Array Edge := initial.map fun name => {
      parent := targetName
      child := name
      origin := "type"
    }

    while cursor < queue.size do
      let ⟨name, distance⟩ := queue[cursor]!
      cursor := cursor + 1
      if !seen.contains name then
        seen := seen.insert name
        if let some info := env.find? name then
          let owner := (ownerModule? env name).getD `_builtin
          let isLocal := localModules.contains owner
          let role := if isLocal then "local" else "external-frontier"
          let bodyReadable ← match body? info with
            | some body => ppExprIn env body false
            | none => pure ""
          dependencies := dependencies.push {
            name
            owner
            distance
            role
            kind := constantKind info
            typeReadable := ← ppExprIn env info.type false
            typeExplicit := ← ppExprIn env info.type true
            bodyReadable
          }
          if isLocal then
            let typeNames := info.type.getUsedConstantsAsSet.toArray.qsort fun left right =>
              left.toString < right.toString
            let bodyNames := bodyConstants info |>.toArray.qsort fun left right =>
              left.toString < right.toString
            let structureNames := structuralConstants info |>.qsort fun left right =>
              left.toString < right.toString
            for child in typeNames do
              edges := edges.push { parent := name, child, origin := "type" }
              if !seen.contains child then
                queue := queue.push (child, distance + 1)
            for child in bodyNames do
              edges := edges.push { parent := name, child, origin := "body" }
              if !seen.contains child then
                queue := queue.push (child, distance + 1)
            for child in structureNames do
              edges := edges.push { parent := name, child, origin := "constructor" }
              if !seen.contains child then
                queue := queue.push (child, distance + 1)

    for dependency in dependencies.qsort dependencyLess do
      writeFields #[
        "dependency",
        dependency.role,
        dependency.name.toString,
        dependency.owner.toString,
        toString dependency.distance,
        dependency.kind,
        dependency.typeReadable,
        dependency.typeExplicit,
        dependency.bodyReadable
      ]
    for edge in edges.qsort edgeLess do
      writeFields #[
        "edge",
        edge.parent.toString,
        edge.child.toString,
        edge.origin
      ]
    writeFields #["summary", toString dependencies.size, toString edges.size]
    return 0

unsafe def run (args : List String) : IO UInt32 := do
  match args with
  | [targetModule, targetName, localModulesFile] =>
      emit targetModule.toName targetName.toName localModulesFile
  | _ =>
      IO.eprintln
        "usage: lean --run declaration_dossier.lean TARGET_MODULE TARGET_DECLARATION LOCAL_MODULES_FILE"
      return 2

end HighamBenchFaithfulnessDossier

unsafe def main (args : List String) : IO UInt32 :=
  HighamBenchFaithfulnessDossier.run args
