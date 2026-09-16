/-
Emit the semantic dependency closure of a generated formalization target.

Traversal starts from the target theorem's type, never its proof.  Types and
bodies of declarations owned by the target module or a configured recursive
module prefix are followed transitively.  Other Lean/Mathlib declarations form
an external frontier: their type and one-level body are emitted, but traversal
stops there.

The TSV output is an internal control artifact.  The Python preparation tool
must pseudonymize it before supplying any content to an audit role.

Usage:
  lean --run declaration_dossier.lean \
    TARGET_MODULE TARGET_DECLARATION RECURSIVE_PREFIXES_FILE
-/

import Lean

open Lean

namespace HighamBenchFormalizationDossier

private structure Dependency where
  name : Name
  owner : Name
  distance : Nat
  role : String
  kind : String
  typeReadable : String
  typeExplicit : String
  bodyReadable : String
  bodyExplicit : String

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

private def loadPrefixes (path : System.FilePath) : IO (Array String) := do
  let contents ← IO.FS.readFile path
  return contents.splitOn "\n" |>.foldl (init := #[]) fun prefixes line =>
    let line := line.trimAscii.toString
    if line.isEmpty then prefixes else prefixes.push line

private def ownerModule? (env : Environment) (name : Name) : Option Name := do
  let moduleIdx ← env.getModuleIdxFor? name
  return env.header.moduleNames[moduleIdx]!

private def moduleMatchesPrefix (moduleName : Name) (prefixValue : String) : Bool :=
  let rendered := moduleName.toString
  rendered == prefixValue || rendered.startsWith (prefixValue ++ ".")

private def recursivelyOwned
    (targetModule owner : Name) (prefixes : Array String) : Bool :=
  owner == targetModule || prefixes.any (moduleMatchesPrefix owner)

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
    fileName := "<HighamBench generated declaration dossier>"
    fileMap := default
  }
  let state : Core.State := { env := env }
  Prod.fst <$> Core.CoreM.toIO (ctx := context) (s := state) do
    let render : CoreM String := Meta.MetaM.run' do
      return (← Meta.ppExpr expression).pretty
    if explicit then
      withOptions (fun options =>
        options.setBool `pp.all true
          |>.setBool `pp.fullNames true
          |>.setBool `pp.privateNames true) render
    else
      withOptions (fun options =>
        options.setBool `pp.universes false
          |>.setBool `pp.explicit false
          |>.setBool `pp.coercions true
          |>.setBool `pp.fullNames true
          |>.setBool `pp.privateNames true) render

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
    (targetModule targetName : Name) (prefixesFile : System.FilePath) : IO UInt32 := do
  initSearchPath (← findSysroot)
  withImportModules #[{ module := targetModule }] {} fun env => do
    let some targetInfo := env.find? targetName
      | IO.eprintln s!"unknown target declaration: {targetName}"; return 3
    let prefixes ← loadPrefixes prefixesFile

    writeFields #["format", "2"]
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
          let isLocal := recursivelyOwned targetModule owner prefixes
          let role := if isLocal then "local" else "external-frontier"
          let bodyReadable ← match body? info with
            | some body => ppExprIn env body false
            | none => pure ""
          let bodyExplicit ← match body? info with
            | some body => ppExprIn env body true
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
            bodyExplicit
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
        dependency.bodyReadable,
        dependency.bodyExplicit
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
  | [targetModule, targetName, prefixesFile] =>
      emit targetModule.toName targetName.toName prefixesFile
  | _ =>
      IO.eprintln
        "usage: lean --run declaration_dossier.lean TARGET_MODULE TARGET_DECLARATION RECURSIVE_PREFIXES_FILE"
      return 2

end HighamBenchFormalizationDossier

unsafe def main (args : List String) : IO UInt32 :=
  HighamBenchFormalizationDossier.run args
