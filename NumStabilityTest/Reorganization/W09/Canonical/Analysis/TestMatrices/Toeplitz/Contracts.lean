import NumStability.Analysis.TestMatrices.Toeplitz.Contracts

/-!
# Contracts canonical-only test (R_TOEPLITZ, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28Contracts`
during wave W09 and must resolve from R_TOEPLITZ alone.
-/
#check @NumStability.toeplitzSineVector
#check @NumStability.symmetricToeplitzEigenvalue
#check @NumStability.tridiagonalToeplitz_mulVec_apply
