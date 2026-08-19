import NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices

/-!
# StressAndPeiMatrices private normalization

Constructs the 9 approved post-delivery private name(s) for this
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
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_det_stressUpper_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_peiMatrix_eq_smul_one_add_rankOne" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_prod_fin_nat_sub_eq_factorial" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_prod_nat_sub_eq_factorial" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_prod_rowNorm2_stressUpper_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_rowNorm2_sq_stressUpper_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_rowNorm2_stressUpper_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_stressUpper_one_upper" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_sum_tail_one" 0
]

private def retiredPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_det_stressUpper_one" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_peiMatrix_eq_smul_one_add_rankOne" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_prod_fin_nat_sub_eq_factorial" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_prod_nat_sub_eq_factorial" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_prod_rowNorm2_stressUpper_one" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_rowNorm2_sq_stressUpper_one" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_rowNorm2_stressUpper_one" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_stressUpper_one_upper" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_sum_tail_one" 0
]

run_cmd do
  let environment ← Lean.getEnv
  for name in approvedPrivateNames do
    unless Lean.Environment.contains environment name do
      throwError "R08 StressAndPeiMatrices private normalization: missing approved name {name}"
  for name in retiredPrivateNames do
    if Lean.Environment.contains environment name then
      throwError "R08 StressAndPeiMatrices private normalization: retired name {name} still present"
