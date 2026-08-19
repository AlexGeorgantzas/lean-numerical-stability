import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.BlockResidual.LeftResidualBounds

/-!
# LeftResidualBounds private normalization

Constructs the 3 approved post-delivery private name(s) for this
destination and requires each present in the environment AND its
pre-delivery name absent.
-/

private def appendNameParts (baseName : Lean.Name) (parts : List String) : Lean.Name :=
  parts.foldl (fun name part => .str name part) baseName

private def mangledPrivateName (moduleName declarationName : String)
    (ordinal : Nat) : Lean.Name :=
  let modulePrefix := appendNameParts .anonymous ("_private" :: moduleName.splitOn ".")
  appendNameParts (.num modulePrefix ordinal) (declarationName.splitOn ".")

private def approvedPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.BlockResidual.LeftResidualBounds" "NumStability.Ch14Ext.ch14ext_castAdd_eq_iff" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.BlockResidual.LeftResidualBounds" "NumStability.Ch14Ext.ch14ext_castAdd_ne_natAdd" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.BlockResidual.LeftResidualBounds" "NumStability.Ch14Ext.ch14ext_natAdd_eq_iff" 0
]

private def retiredPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Algorithms.Ch14Method2C" "NumStability.Ch14Ext.ch14ext_castAdd_eq_iff" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14Method2C" "NumStability.Ch14Ext.ch14ext_castAdd_ne_natAdd" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14Method2C" "NumStability.Ch14Ext.ch14ext_natAdd_eq_iff" 0
]

run_cmd do
  let environment ← Lean.getEnv
  for name in approvedPrivateNames do
    unless Lean.Environment.contains environment name do
      throwError "R08 LeftResidualBounds private normalization: missing approved name {name}"
  for name in retiredPrivateNames do
    if Lean.Environment.contains environment name then
      throwError "R08 LeftResidualBounds private normalization: retired name {name} still present"
