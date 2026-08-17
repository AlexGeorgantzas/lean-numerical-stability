import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ComposedCoefficientFamilies.RemainderAsymptotics

/-!
# RemainderAsymptotics private normalization

Constructs the 2 approved post-delivery private name(s) for this
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
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ComposedCoefficientFamilies.RemainderAsymptotics" "NumStability.Ch14Ext.composed_gammaQuadraticCoefficient_isBigO_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ComposedCoefficientFamilies.RemainderAsymptotics" "NumStability.Ch14Ext.composed_gammaUnitCoefficient_isBigO_one" 0
]

private def retiredPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Algorithms.Ch14AsymptoticFamilies" "NumStability.Ch14Ext.composed_gammaQuadraticCoefficient_isBigO_one" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14AsymptoticFamilies" "NumStability.Ch14Ext.composed_gammaUnitCoefficient_isBigO_one" 0
]

run_cmd do
  let environment ← Lean.getEnv
  for name in approvedPrivateNames do
    unless Lean.Environment.contains environment name do
      throwError "R08 RemainderAsymptotics private normalization: missing approved name {name}"
  for name in retiredPrivateNames do
    if Lean.Environment.contains environment name then
      throwError "R08 RemainderAsymptotics private normalization: retired name {name} still present"
