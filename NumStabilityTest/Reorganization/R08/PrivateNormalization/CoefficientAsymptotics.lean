import NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics

/-!
# CoefficientAsymptotics private normalization

Constructs the 14 approved post-delivery private name(s) for this
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
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics" "NumStability.Ch14Ext.ch14ext_gammaQuadraticCoefficient_family_isBigO_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics" "NumStability.Ch14Ext.ch14ext_gammaUnitCoefficient_family_isBigO_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics" "NumStability.Ch14Ext.ch14ext_gjeForwardQ1_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics" "NumStability.Ch14Ext.ch14ext_gjeForwardQ2_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics" "NumStability.Ch14Ext.ch14ext_gjeForwardRaw_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics" "NumStability.Ch14Ext.ch14ext_gjeForwardT1_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics" "NumStability.Ch14Ext.ch14ext_gjeForwardT2_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics" "NumStability.Ch14Ext.ch14ext_gjeForwardUinvCorrection_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics" "NumStability.Ch14Ext.ch14ext_gjeResidualS22_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics" "NumStability.Ch14Ext.ch14ext_gjeResidualS23_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics" "NumStability.Ch14Ext.ch14ext_gjeResidualS2_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics" "NumStability.Ch14Ext.ch14ext_one_add_gamma_family_isBigO_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics" "NumStability.Ch14Ext.ch14ext_one_add_gamma_pow_family_isBigO_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics" "NumStability.Ch14Ext.ch14ext_one_add_gamma_pow_sub_one_family_isBigO_unit" 0
]

private def retiredPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Algorithms.Ch14GJEAsymptoticFamilies" "NumStability.Ch14Ext.ch14ext_gammaQuadraticCoefficient_family_isBigO_one" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEAsymptoticFamilies" "NumStability.Ch14Ext.ch14ext_gammaUnitCoefficient_family_isBigO_one" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEAsymptoticFamilies" "NumStability.Ch14Ext.ch14ext_gjeForwardQ1_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEAsymptoticFamilies" "NumStability.Ch14Ext.ch14ext_gjeForwardQ2_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEAsymptoticFamilies" "NumStability.Ch14Ext.ch14ext_gjeForwardRaw_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEAsymptoticFamilies" "NumStability.Ch14Ext.ch14ext_gjeForwardT1_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEAsymptoticFamilies" "NumStability.Ch14Ext.ch14ext_gjeForwardT2_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEAsymptoticFamilies" "NumStability.Ch14Ext.ch14ext_gjeForwardUinvCorrection_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEAsymptoticFamilies" "NumStability.Ch14Ext.ch14ext_gjeResidualS22_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEAsymptoticFamilies" "NumStability.Ch14Ext.ch14ext_gjeResidualS23_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEAsymptoticFamilies" "NumStability.Ch14Ext.ch14ext_gjeResidualS2_family_isBigOOne" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEAsymptoticFamilies" "NumStability.Ch14Ext.ch14ext_one_add_gamma_family_isBigO_one" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEAsymptoticFamilies" "NumStability.Ch14Ext.ch14ext_one_add_gamma_pow_family_isBigO_one" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEAsymptoticFamilies" "NumStability.Ch14Ext.ch14ext_one_add_gamma_pow_sub_one_family_isBigO_unit" 0
]

run_cmd do
  let environment ← Lean.getEnv
  for name in approvedPrivateNames do
    unless Lean.Environment.contains environment name do
      throwError "R08 CoefficientAsymptotics private normalization: missing approved name {name}"
  for name in retiredPrivateNames do
    if Lean.Environment.contains environment name then
      throwError "R08 CoefficientAsymptotics private normalization: retired name {name} still present"
