import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedScalar

/-!
# GinibreSignedScalar canonical-only test (S_GIN_SIGNED, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28GinibreSignedScalar`
during wave W09 and must resolve from S_GIN_SIGNED alone.
-/
#check @NumStability.ginibreCharacteristicProductKernel
#check @NumStability.tendsto_pow_mul_exp_mul_sub_sq_pow
#check @NumStability.tendsto_pow_mul_exp_neg_sq_div_two
