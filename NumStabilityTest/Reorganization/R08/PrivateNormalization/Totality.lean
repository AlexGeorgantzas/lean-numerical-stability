import NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.TwoBlockFirstOrder.Derivations
import NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices
import NumStability.Source.Higham.Chapter14.Problem15.SingularValueGuards.DeterminantSignAndRelativeBounds
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ComposedCoefficientFamilies.RemainderAsymptotics
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ScaledPerturbationEndpoints.ForwardError
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1B.BlockResidual.WholeMatrixBounds
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.BlockResidual.LeftResidualBounds
import NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics
import NumStability.Source.Higham.Chapter14.Theorem05.PrintedEnvelopes.CorrectionBounds

/-!
# R08 approved private normalization (exhaustive)

Constructs all 48 approved post-delivery private names and requires
each present in the environment AND its pre-delivery name absent. This is the
totality assertion over the reviewed R08 private-normalization map.
-/

private def appendNameParts (baseName : Lean.Name) (parts : List String) : Lean.Name :=
  parts.foldl (fun name part => .str name part) baseName

private def mangledPrivateName (moduleName declarationName : String)
    (ordinal : Nat) : Lean.Name :=
  let modulePrefix := appendNameParts .anonymous ("_private" :: moduleName.splitOn ".")
  appendNameParts (.num modulePrefix ordinal) (declarationName.splitOn ".")

private def approvedPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ComposedCoefficientFamilies.RemainderAsymptotics" "NumStability.Ch14Ext.composed_gammaQuadraticCoefficient_isBigO_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ComposedCoefficientFamilies.RemainderAsymptotics" "NumStability.Ch14Ext.composed_gammaUnitCoefficient_isBigO_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ScaledPerturbationEndpoints.ForwardError" "NumStability.Ch14Ext.ch14ext_double_sum_add_scaled" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ScaledPerturbationEndpoints.ForwardError" "NumStability.Ch14Ext.ch14ext_matMulVec_matrix_add_scaled" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ScaledPerturbationEndpoints.ForwardError" "NumStability.Ch14Ext.ch14ext_matMulVec_triple_matrix_add_scaled" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ScaledPerturbationEndpoints.ForwardError" "NumStability.Ch14Ext.ch14ext_matMulVec_vector_add_scaled" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ScaledPerturbationEndpoints.ForwardError" "NumStability.Ch14Ext.ch14ext_sq_mul_isBigO_of_continuousAt" 0,
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
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics" "NumStability.Ch14Ext.ch14ext_one_add_gamma_pow_sub_one_family_isBigO_unit" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.PrintedEnvelopes.CorrectionBounds" "NumStability.Ch14Ext.ch14ext_gjeInvCumProd_unit_upper" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.PrintedEnvelopes.CorrectionBounds" "NumStability.Ch14Ext.ch14ext_gjeInvStageMatrix_diag_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.PrintedEnvelopes.CorrectionBounds" "NumStability.Ch14Ext.ch14ext_gjeInvStageMatrix_upper_triangular" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.PrintedEnvelopes.CorrectionBounds" "NumStability.Ch14Ext.ch14ext_gje_Pabs_le" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.PrintedEnvelopes.CorrectionBounds" "NumStability.Ch14Ext.ch14ext_gje_Q_abs_le" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.PrintedEnvelopes.CorrectionBounds" "NumStability.Ch14Ext.ch14ext_matMul_diag_one_of_unit_upper" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Theorem05.PrintedEnvelopes.CorrectionBounds" "NumStability.Ch14Ext.ch14ext_matMul_upper_triangular" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1B.BlockResidual.WholeMatrixBounds" "NumStability.Ch14Ext.ch14ext_m1b_castAdd_eq_iff" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1B.BlockResidual.WholeMatrixBounds" "NumStability.Ch14Ext.ch14ext_m1b_castAdd_ne_natAdd" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1B.BlockResidual.WholeMatrixBounds" "NumStability.Ch14Ext.ch14ext_m1b_natAdd_eq_iff" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.BlockResidual.LeftResidualBounds" "NumStability.Ch14Ext.ch14ext_castAdd_eq_iff" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.BlockResidual.LeftResidualBounds" "NumStability.Ch14Ext.ch14ext_castAdd_ne_natAdd" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.BlockResidual.LeftResidualBounds" "NumStability.Ch14Ext.ch14ext_natAdd_eq_iff" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.TwoBlockFirstOrder.Derivations" "NumStability.Ch14Ext.higham14_problem14_2_castAdd_ne_natAdd" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.TwoBlockFirstOrder.Derivations" "NumStability.Ch14Ext.higham14_problem14_2_natAdd_ne_castAdd" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_det_stressUpper_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_peiMatrix_eq_smul_one_add_rankOne" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_prod_fin_nat_sub_eq_factorial" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_prod_nat_sub_eq_factorial" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_prod_rowNorm2_stressUpper_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_rowNorm2_sq_stressUpper_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_rowNorm2_stressUpper_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_stressUpper_one_upper" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices" "NumStability.higham14_problem14_12_sum_tail_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem15.SingularValueGuards.DeterminantSignAndRelativeBounds" "NumStability.Ch14Ext.ch14ext_complexMatrixEuclideanLin_add" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem15.SingularValueGuards.DeterminantSignAndRelativeBounds" "NumStability.Ch14Ext.ch14ext_det_add_ne_zero_of_opNorm2_lt_last_singularValue" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem15.SingularValueGuards.DeterminantSignAndRelativeBounds" "NumStability.Ch14Ext.ch14ext_opNorm2_smul" 0
]

private def retiredPrivateNames : List Lean.Name := [
  mangledPrivateName "NumStability.Algorithms.Ch14AsymptoticFamilies" "NumStability.Ch14Ext.composed_gammaQuadraticCoefficient_isBigO_one" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14AsymptoticFamilies" "NumStability.Ch14Ext.composed_gammaUnitCoefficient_isBigO_one" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14ForwardErrorEndpoint" "NumStability.Ch14Ext.ch14ext_double_sum_add_scaled" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14ForwardErrorEndpoint" "NumStability.Ch14Ext.ch14ext_matMulVec_matrix_add_scaled" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14ForwardErrorEndpoint" "NumStability.Ch14Ext.ch14ext_matMulVec_triple_matrix_add_scaled" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14ForwardErrorEndpoint" "NumStability.Ch14Ext.ch14ext_matMulVec_vector_add_scaled" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14ForwardErrorEndpoint" "NumStability.Ch14Ext.ch14ext_sq_mul_isBigO_of_continuousAt" 0,
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
  mangledPrivateName "NumStability.Algorithms.Ch14GJEAsymptoticFamilies" "NumStability.Ch14Ext.ch14ext_one_add_gamma_pow_sub_one_family_isBigO_unit" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure" "NumStability.Ch14Ext.ch14ext_gjeInvCumProd_unit_upper" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure" "NumStability.Ch14Ext.ch14ext_gjeInvStageMatrix_diag_one" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure" "NumStability.Ch14Ext.ch14ext_gjeInvStageMatrix_upper_triangular" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure" "NumStability.Ch14Ext.ch14ext_gje_Pabs_le" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure" "NumStability.Ch14Ext.ch14ext_gje_Q_abs_le" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure" "NumStability.Ch14Ext.ch14ext_matMul_diag_one_of_unit_upper" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure" "NumStability.Ch14Ext.ch14ext_matMul_upper_triangular" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14Method1BWhole" "NumStability.Ch14Ext.ch14ext_m1b_castAdd_eq_iff" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14Method1BWhole" "NumStability.Ch14Ext.ch14ext_m1b_castAdd_ne_natAdd" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14Method1BWhole" "NumStability.Ch14Ext.ch14ext_m1b_natAdd_eq_iff" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14Method2C" "NumStability.Ch14Ext.ch14ext_castAdd_eq_iff" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14Method2C" "NumStability.Ch14Ext.ch14ext_castAdd_ne_natAdd" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14Method2C" "NumStability.Ch14Ext.ch14ext_natAdd_eq_iff" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14Problem142" "NumStability.Ch14Ext.higham14_problem14_2_castAdd_ne_natAdd" 0,
  mangledPrivateName "NumStability.Algorithms.Ch14Problem142" "NumStability.Ch14Ext.higham14_problem14_2_natAdd_ne_castAdd" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_det_stressUpper_one" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_peiMatrix_eq_smul_one_add_rankOne" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_prod_fin_nat_sub_eq_factorial" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_prod_nat_sub_eq_factorial" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_prod_rowNorm2_stressUpper_one" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_rowNorm2_sq_stressUpper_one" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_rowNorm2_stressUpper_one" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_stressUpper_one_upper" 0,
  mangledPrivateName "NumStability.Algorithms.MatrixInversion" "NumStability.higham14_problem14_12_sum_tail_one" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem15" "NumStability.Ch14Ext.ch14ext_complexMatrixEuclideanLin_add" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem15" "NumStability.Ch14Ext.ch14ext_det_add_ne_zero_of_opNorm2_lt_last_singularValue" 0,
  mangledPrivateName "NumStability.Source.Higham.Chapter14.Problem15" "NumStability.Ch14Ext.ch14ext_opNorm2_smul" 0
]

run_cmd do
  let environment ← Lean.getEnv
  for name in approvedPrivateNames do
    unless Lean.Environment.contains environment name do
      throwError "R08 private normalization: missing approved name {name}"
  for name in retiredPrivateNames do
    if Lean.Environment.contains environment name then
      throwError "R08 private normalization: retired name {name} still present"
