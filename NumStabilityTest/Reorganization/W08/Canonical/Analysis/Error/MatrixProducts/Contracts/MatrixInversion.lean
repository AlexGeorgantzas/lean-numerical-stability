import NumStability.Analysis.Error.MatrixProducts.Contracts.MatrixInversion

/-!
# MatrixInversion canonical-only test (D07, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.MatrixInversion`
during wave W08 and must resolve from D07 alone.
-/
#check @NumStability.MatProdError
#check @NumStability.higham14_unit_roundoff_add_gamma_le_gamma_succ
#check @NumStability.higham14_infNorm_le_of_componentwise_matmul_bound
