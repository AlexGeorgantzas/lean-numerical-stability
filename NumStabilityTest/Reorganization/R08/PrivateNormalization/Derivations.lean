import NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.TwoBlockFirstOrder.Derivations

/-!
# Derivations private normalization

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
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.TwoBlockFirstOrder.Derivations" "NumStability.Ch14Ext.higham14_problem14_2_castAdd_ne_natAdd" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.TwoBlockFirstOrder.Derivations" "NumStability.Ch14Ext.higham14_problem14_2_natAdd_ne_castAdd" 0
]

private def retiredPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Algorithms.Ch14Problem142" "NumStability.Ch14Ext.higham14_problem14_2_castAdd_ne_natAdd" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14Problem142" "NumStability.Ch14Ext.higham14_problem14_2_natAdd_ne_castAdd" 0
]

run_cmd do
  let environment ← Lean.getEnv
  for name in approvedPrivateNames do
    unless Lean.Environment.contains environment name do
      throwError "R08 Derivations private normalization: missing approved name {name}"
  for name in retiredPrivateNames do
    if Lean.Environment.contains environment name then
      throwError "R08 Derivations private normalization: retired name {name} still present"
