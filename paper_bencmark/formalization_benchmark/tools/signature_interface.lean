/-
Emit the one-hop NumStability constants used by the elaborated types of a
frozen list of packet declarations.  Declaration bodies are never inspected.

Input TSV rows contain:
  OWNER_MODULE<TAB>DECLARATION_NAME

Usage:
  lean --run signature_interface.lean INPUT_TSV
-/

import Lean

open Lean

namespace HighamBenchSignatureInterface

private def escape (value : String) : String :=
  value.replace "\\" "\\\\"
    |>.replace "\t" "\\t"
    |>.replace "\r" "\\r"
    |>.replace "\n" "\\n"

private def writeFields (fields : Array String) : IO Unit :=
  IO.println <| String.intercalate "\t" (fields.toList.map escape)

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

private unsafe def ppSignatureIn (env : Environment) (name : Name) : IO String := do
  let context : Core.Context := {
    fileName := "<HighamBench signature interface>"
    fileMap := default
  }
  let state : Core.State := { env := env }
  Prod.fst <$> Core.CoreM.toIO (ctx := context) (s := state) do
    withOptions (fun options =>
      options.setBool `pp.all false
        |>.setBool `pp.notation true
        |>.setBool `pp.fieldNotation true
        |>.setBool `pp.universes false
        |>.setBool `pp.explicit false
        |>.setBool `pp.coercions true
        |>.setBool `pp.fullNames false
        |>.setBool `pp.privateNames true) <| Meta.MetaM.run' do
      return (← PrettyPrinter.ppSignature name).fmt.pretty

private def loadSeeds (path : System.FilePath) : IO (Array (Name × Name)) := do
  let contents ← IO.FS.readFile path
  let mut seeds : Array (Name × Name) := #[]
  for rawLine in contents.splitOn "\n" do
    let line := rawLine.trimAscii.toString
    if !line.isEmpty then
      match line.splitOn "\t" with
      | [moduleName, declarationName] =>
          seeds := seeds.push (moduleName.toName, declarationName.toName)
      | _ => throw <| IO.userError "malformed signature-interface seed row"
  return seeds

private unsafe def emit (inputFile : System.FilePath) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let seeds ← loadSeeds inputFile
  if seeds.isEmpty then
    IO.eprintln "signature-interface seed list is empty"
    return 3

  let mut seenModules : NameSet := {}
  let mut imports : Array Import := #[]
  for ⟨moduleName, _⟩ in seeds do
    if !seenModules.contains moduleName then
      seenModules := seenModules.insert moduleName
      imports := imports.push { module := moduleName }
  imports := imports.qsort fun left right =>
    left.module.toString < right.module.toString

  withImportModules imports {} fun env => do
    writeFields #["format", "1"]
    let mut directCount := 0
    let sortedSeeds := seeds.qsort fun left right =>
      left.2.toString < right.2.toString
    for seed in sortedSeeds do
      let expectedModule := seed.1
      let seedName := seed.2
      let some seedInfo := env.find? seedName
        | IO.eprintln s!"unknown packet declaration: {seedName}"; return 4
      let some actualModule := ownerModule? env seedName
        | IO.eprintln s!"packet declaration has no owner module: {seedName}"; return 5
      if actualModule != expectedModule then
        IO.eprintln s!"packet declaration owner mismatch: {seedName}"
        return 6
      writeFields #[
        "seed",
        seedName.toString,
        actualModule.toString,
        constantKind seedInfo,
        ← ppSignatureIn env seedName
      ]
      let used := seedInfo.type.getUsedConstantsAsSet.toArray.qsort fun left right =>
        left.toString < right.toString
      for dependencyName in used do
        let rendered := dependencyName.toString
        if rendered == "NumStability" || rendered.startsWith "NumStability." then
          let some dependencyInfo := env.find? dependencyName
            | IO.eprintln s!"unknown type dependency: {dependencyName}"; return 7
          let some dependencyModule := ownerModule? env dependencyName
            | IO.eprintln s!"type dependency has no owner module: {dependencyName}"
              return 8
          writeFields #[
            "direct",
            seedName.toString,
            dependencyName.toString,
            dependencyModule.toString,
            constantKind dependencyInfo
          ]
          directCount := directCount + 1
    writeFields #["summary", toString seeds.size, toString directCount]
    return 0

unsafe def run (args : List String) : IO UInt32 := do
  match args with
  | [inputFile] => emit inputFile
  | _ =>
      IO.eprintln "usage: lean --run signature_interface.lean INPUT_TSV"
      return 2

end HighamBenchSignatureInterface

unsafe def main (args : List String) : IO UInt32 :=
  HighamBenchSignatureInterface.run args
