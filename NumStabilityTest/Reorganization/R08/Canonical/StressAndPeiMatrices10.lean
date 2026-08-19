import NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices

/-!
# StressAndPeiMatrices canonical-only test

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.MatrixInversion`
during wave R08 and must resolve from this destination alone.
-/
#check @NumStability.higham14_problem14_12_hadamardConditionNumber_peiMatrix
#check @NumStability.higham14_problem14_12_hadamardConditionNumber_peiMatrix_abs
#check @NumStability.higham14_problem14_12_hadamardConditionNumber_stressUpper_one_eq_sqrt_factorial
#check @NumStability.higham14_problem14_12_peiMatrix_det
