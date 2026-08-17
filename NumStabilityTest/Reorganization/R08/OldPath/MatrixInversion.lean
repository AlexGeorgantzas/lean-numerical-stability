import NumStability.Algorithms.MatrixInversion

/-!
# MatrixInversion old-path-only test

Imports only the historical path. Every declaration checked below is part of
the residual C0004 surface that wave R08 relocated to
`NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices`,
so this compiles only if the compatibility module still re-exports it
under its original name.
-/
#check @NumStability.higham14_problem14_12_hadamardConditionNumber_peiMatrix
#check @NumStability.higham14_problem14_12_hadamardConditionNumber_peiMatrix_abs
#check @NumStability.higham14_problem14_12_hadamardConditionNumber_stressUpper_one_eq_sqrt_factorial
#check @NumStability.higham14_problem14_12_peiMatrix_det
