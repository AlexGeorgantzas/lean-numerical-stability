import NumStability.Analysis.TestMatrices.Pascal.Exact

/-!
# Exact canonical-only test (R_PASCAL, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28Exact`
during wave W09 and must resolve from R_PASCAL alone.
-/
#check @NumStability.pascalMatrix_quadratic_pos
#check @NumStability.pascalMatrix_quadratic_eq_sum_sq
#check @NumStability.pascalMatrix_isSymPosDef_explicit
