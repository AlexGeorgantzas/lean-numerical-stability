/-
# NumStability declaration dependency extractor

This program loads the compiled `NumStability` environment and emits a tab-separated stream.
It deliberately keeps dependencies occurring in declaration signatures separate from dependencies
occurring in values/proofs.  The Python baseline generator consumes this stream and computes the
architecture metrics.

The format-2 declaration graph treats Lean-reserved declarations and compiler-generated internal
details as regenerable implementation details.  For private declarations, the private module prefix
is removed before rejecting components that Lean's frontend cannot assign to authored declarations
(leading `_` or numeric components), together with compiler `match_<ordinal>` components and their
descendants.  Authored private helpers and source-facing names such as `eq_11_15` are still retained.
Generated declarations are contracted out of the graph: a dependency path through one or more such
declarations becomes a direct dependency on every authored project declaration reachable through
that path.  In particular, Lean may cache and reuse `_proof_*` declarations under an unrelated
parent, so attributing those names to their textual prefix would invent semantic edges, while simply
dropping them would lose real dependencies from their bodies.  This keeps graph ownership stable
when Lean regenerates auxiliaries in a different importing module without weakening the semantic
dependency record.

Run it through `tools/architecture/generate_baseline.py`; the TSV format is an implementation
detail and is not intended to be checked in.
-/

import Lean

open Lean

namespace NumStabilityArchitecture

private def isProjectModule (moduleName : Name) : Bool :=
  let text := moduleName.toString
  text == "NumStability" || text.startsWith "NumStability."

private def isGeneratedMatchComponent (part : String) : Bool :=
  part.startsWith "match_" && (Name.mkSimple part).isInternalDetail

private def hasCompilerGeneratedComponent : Name → Bool
  | .anonymous => false
  | .num _ _ => true
  | .str parent part =>
      part.startsWith "_" || isGeneratedMatchComponent part ||
        hasCompilerGeneratedComponent parent

private def isCompilerGeneratedDetail (name : Name) : Bool :=
  hasCompilerGeneratedComponent (privateToUserName name)

private def shouldIncludeDeclaration (env : Environment) (name : Name) : Bool :=
  !isReservedName env name && !isCompilerGeneratedDetail name

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

private def allConstants (info : ConstantInfo) : NameSet :=
  info.type.getUsedConstantsAsSet ++ bodyConstants info

/--
Replace dependency paths through omitted project implementation details with
their reachable authored project declarations.  Non-project dependencies are
intentionally terminal because this extractor records only the project graph.
-/
private def contractDependencyTargets
    (env : Environment)
    (authoredProjectNames allProjectNames targets : NameSet) : NameSet := Id.run do
  let mut result : NameSet := {}
  let mut visited : NameSet := {}
  let mut pending := targets.toArray
  while !pending.isEmpty do
    let target := pending.back!
    pending := pending.pop
    if !visited.contains target then
      visited := visited.insert target
      if authoredProjectNames.contains target then
        result := result.insert target
      else if allProjectNames.contains target then
        if let some info := env.find? target then
          pending := pending ++ (allConstants info).toArray
  return result

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
        if env.getModuleIdxFor? name == some moduleIdx then
          result := result.push { name, moduleName, info }
  return result.qsort fun left right => left.name.toString < right.name.toString

private def writeEdges
    (handle : IO.FS.Handle)
    (env : Environment)
    (authoredProjectNames allProjectNames : NameSet)
    (edgeKind : String)
    (source : ProjectDeclaration)
    (targets : NameSet) : IO Unit := do
  for target in
      (contractDependencyTargets env authoredProjectNames allProjectNames targets).toArray.qsort
        (·.toString < ·.toString) do
    writeFields handle #[
      "edge",
      edgeKind,
      source.name.toString,
      target.toString
    ]

private unsafe def extract (outputPath : System.FilePath) : IO Unit := do
  initSearchPath (← findSysroot)
  withImportModules #[{ module := `NumStability }] {} fun env => do
    let allDeclarations := collectProjectDeclarations env
    let declarations := allDeclarations.filter fun declaration =>
      shouldIncludeDeclaration env declaration.name
    let allProjectNames : NameSet := allDeclarations.foldl (init := {}) fun names declaration =>
      names.insert declaration.name
    let authoredProjectNames : NameSet := declarations.foldl (init := {}) fun names declaration =>
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
        writeEdges handle env authoredProjectNames allProjectNames "signature" declaration
          declaration.info.type.getUsedConstantsAsSet
        writeEdges handle env authoredProjectNames allProjectNames "body" declaration
          (bodyConstants declaration.info)

private def ensureSelfTest (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw <| IO.userError s!"declaration dependency extractor self-test failed: {message}"

private unsafe def selfTest : IO Unit := do
  initSearchPath (← findSysroot)
  withImportModules #[{ module := `Lean }] {} fun env => do
    let parent := `NumStabilityArchitecture.selfTestParent
    let syntheticOne := Name.str parent "_simp_1_1"
    let generatedProof := Name.str parent "_proof_1_2"
    let generatedMatch := Name.str parent "match_1_3"
    let generatedMatchDescendant := Name.str generatedMatch "splitter"
    let authoredEquation := Name.str parent "eq_11_15"
    let authoredPrivate := mkPrivateNameCore `NumStabilityArchitecture.SelfTest parent
    let generatedPrivate :=
      mkPrivateNameCore `NumStabilityArchitecture.SelfTest generatedMatch
    let reserved := Name.str ``List.map "eq_1"

    ensureSelfTest (isCompilerGeneratedDetail syntheticOne)
      "an internal `_simp_*` declaration was not recognized"
    ensureSelfTest (!isCompilerGeneratedDetail (Name.str parent "simp_1_1"))
      "a user-spellable suffix was classified as an internal detail"
    ensureSelfTest (isCompilerGeneratedDetail generatedProof)
      "an internal `_proof_*` declaration was not recognized"
    ensureSelfTest (isCompilerGeneratedDetail generatedMatch)
      "an internal `match_*` declaration was not recognized"
    ensureSelfTest (isCompilerGeneratedDetail generatedMatchDescendant)
      "a descendant of an internal `match_*` declaration was not recognized"
    ensureSelfTest (!isCompilerGeneratedDetail authoredEquation)
      "an authored source-equation declaration was classified as generated"
    ensureSelfTest (!isCompilerGeneratedDetail authoredPrivate)
      "an authored private declaration was classified as an internal detail"
    ensureSelfTest (isCompilerGeneratedDetail generatedPrivate)
      "a generated private declaration was not recognized after prefix removal"
    ensureSelfTest (isReservedName env reserved)
      "Lean did not recognize a standard equational theorem name as reserved"
    ensureSelfTest (!shouldIncludeDeclaration env reserved)
      "a Lean-reserved declaration was retained"
    ensureSelfTest (!shouldIncludeDeclaration env syntheticOne)
      "a synthetic `_simp_*` declaration was retained"
    ensureSelfTest (!shouldIncludeDeclaration env generatedProof)
      "an internal `_proof_*` declaration was retained"
    ensureSelfTest (!shouldIncludeDeclaration env generatedPrivate)
      "a generated private declaration was retained"
    ensureSelfTest (shouldIncludeDeclaration env authoredPrivate)
      "an authored private declaration was omitted"
    ensureSelfTest (shouldIncludeDeclaration env parent)
      "an ordinary declaration was omitted"

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
