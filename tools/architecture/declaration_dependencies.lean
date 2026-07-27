/-
# NumStability declaration dependency extractor

This program loads the compiled `NumStability` environment and emits a tab-separated stream.
It deliberately keeps dependencies occurring in declaration signatures separate from dependencies
occurring in values/proofs.  The Python baseline generator consumes this stream and computes the
architecture metrics.

The format-2 declaration graph treats Lean-reserved declarations as regenerable implementation
details.  Synthetic `_simp_*` declarations are omitted too, while references to them are attributed
to their parent declaration.  This keeps graph ownership stable when Lean regenerates auxiliaries in
a different importing module.

Run it through `tools/architecture/generate_baseline.py`; the TSV format is an implementation
detail and is not intended to be checked in.
-/

import Lean

open Lean

namespace NumStabilityArchitecture

private def isProjectModule (moduleName : Name) : Bool :=
  let text := moduleName.toString
  text == "NumStability" || text.startsWith "NumStability."

private def isSyntheticSimpAuxiliary (name : Name) : Bool :=
  name.isStr && name.getString!.startsWith "_simp_"

private def shouldIncludeDeclaration (env : Environment) (name : Name) : Bool :=
  !isReservedName env name && !isSyntheticSimpAuxiliary name

private def normalizeDependencyName? (env : Environment) (name : Name) : Option Name := do
  guard <| !isReservedName env name
  return if isSyntheticSimpAuxiliary name then name.getPrefix else name

private def normalizeDependencyTargets (env : Environment) (targets : NameSet) : NameSet :=
  targets.toArray.foldl (init := {}) fun normalized target =>
    match normalizeDependencyName? env target with
    | some target => normalized.insert target
    | none => normalized

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def declarationVisibility (name : Name) : String :=
  if isPrivateName name then
    "private"
  else if name.isInternalDetail then
    "internal"
  else
    "public"

private def bodyConstants : ConstantInfo → NameSet
  | .defnInfo value => value.value.getUsedConstantsAsSet
  | .thmInfo value => value.value.getUsedConstantsAsSet
  | .opaqueInfo value => value.value.getUsedConstantsAsSet
  | .recInfo value => value.rules.foldl (init := {}) fun names rule =>
      names ++ rule.rhs.getUsedConstantsAsSet
  | _ => {}

private structure ProjectDeclaration where
  name : Name
  moduleName : Name
  info : ConstantInfo

private def sanitizeField (value : String) : String :=
  value.replace "\t" " " |>.replace "\r" " " |>.replace "\n" " "

private def writeFields (handle : IO.FS.Handle) (fields : Array String) : IO Unit :=
  handle.putStrLn <| String.intercalate "\t" (fields.toList.map sanitizeField)

private def collectProjectDeclarations (env : Environment) : Array ProjectDeclaration := Id.run do
  let mut result := #[]
  -- Iterating `env.constants` walks every declaration imported from Mathlib.  `moduleData` already
  -- partitions the same constants by owning module, so selecting project modules first is much
  -- faster and avoids realizing unrelated constants.
  for h : moduleIdx in *...env.header.moduleData.size do
    let moduleName := env.header.moduleNames[moduleIdx]!
    if isProjectModule moduleName then
      let data := env.header.moduleData[moduleIdx]
      for name in data.constNames, info in data.constants do
        -- Module data may repeat a declaration re-exported through a legacy module.  The
        -- environment's ownership index identifies the unique originating module.
        if shouldIncludeDeclaration env name && env.getModuleIdxFor? name == some moduleIdx then
          result := result.push { name, moduleName, info }
  return result.qsort fun left right => left.name.toString < right.name.toString

private def writeEdges
    (handle : IO.FS.Handle)
    (env : Environment)
    (projectNames : NameSet)
    (edgeKind : String)
    (source : ProjectDeclaration)
    (targets : NameSet) : IO Unit := do
  for target in (normalizeDependencyTargets env targets).toArray.qsort (·.toString < ·.toString) do
    if projectNames.contains target then
      writeFields handle #[
        "edge",
        edgeKind,
        source.name.toString,
        target.toString
      ]

private unsafe def extract (outputPath : System.FilePath) : IO Unit := do
  initSearchPath (← findSysroot)
  withImportModules #[{ module := `NumStability }] {} fun env => do
    let declarations := collectProjectDeclarations env
    let projectNames : NameSet := declarations.foldl (init := {}) fun names declaration =>
      names.insert declaration.name
    IO.FS.withFile outputPath IO.FS.Mode.write fun handle => do
      writeFields handle #["format", "2"]
      for declaration in declarations do
        writeFields handle #[
          "declaration",
          declaration.name.toString,
          declaration.moduleName.toString,
          declarationKind declaration.info,
          declarationVisibility declaration.name
        ]
      for declaration in declarations do
        writeEdges handle env projectNames "signature" declaration
          declaration.info.type.getUsedConstantsAsSet
        writeEdges handle env projectNames "body" declaration
          (bodyConstants declaration.info)

private def ensureSelfTest (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw <| IO.userError s!"declaration dependency extractor self-test failed: {message}"

private unsafe def selfTest : IO Unit := do
  initSearchPath (← findSysroot)
  withImportModules #[{ module := `Lean }] {} fun env => do
    let parent := `NumStabilityArchitecture.selfTestParent
    let syntheticOne := Name.str parent "_simp_1_1"
    let syntheticTwo := Name.str parent "_simp_1_8"
    let reserved := Name.str ``List.map "eq_1"

    ensureSelfTest (isSyntheticSimpAuxiliary syntheticOne)
      "a `_simp_*` suffix was not recognized"
    ensureSelfTest (!isSyntheticSimpAuxiliary (Name.str parent "simp_1_1"))
      "a non-synthetic suffix was classified as `_simp_*`"
    ensureSelfTest (isReservedName env reserved)
      "Lean did not recognize a standard equational theorem name as reserved"
    ensureSelfTest (!shouldIncludeDeclaration env reserved)
      "a Lean-reserved declaration was retained"
    ensureSelfTest (!shouldIncludeDeclaration env syntheticOne)
      "a synthetic `_simp_*` declaration was retained"
    ensureSelfTest (shouldIncludeDeclaration env parent)
      "an ordinary declaration was omitted"
    ensureSelfTest (normalizeDependencyName? env reserved == none)
      "a reserved dependency target was retained"
    ensureSelfTest (normalizeDependencyName? env syntheticOne == some parent)
      "a synthetic dependency target was not normalized to its parent"
    ensureSelfTest (normalizeDependencyName? env parent == some parent)
      "an ordinary dependency target was changed"

    let targets : NameSet :=
      ((({} : NameSet).insert parent).insert syntheticOne).insert syntheticTwo |>.insert reserved
    let normalized := normalizeDependencyTargets env targets
    ensureSelfTest (normalized.toArray.size == 1 && normalized.contains parent)
      "normalized dependency targets were not deduplicated"

  IO.println "declaration dependency extractor self-test passed"

unsafe def run (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] =>
      selfTest
      return 0
  | [outputPath] =>
      extract outputPath
      return 0
  | _ =>
      IO.eprintln "usage: lake env lean --run tools/architecture/declaration_dependencies.lean OUTPUT.tsv"
      IO.eprintln "       lake env lean --run tools/architecture/declaration_dependencies.lean --self-test"
      return 2

end NumStabilityArchitecture

unsafe def main (args : List String) : IO UInt32 :=
  NumStabilityArchitecture.run args
