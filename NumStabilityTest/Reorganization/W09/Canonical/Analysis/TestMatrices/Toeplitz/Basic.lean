import NumStability.Analysis.TestMatrices.Toeplitz.Basic

/-!
# Basic canonical-only test (R_TOEPLITZ, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28`
during wave W09 and must resolve from R_TOEPLITZ alone.
-/
#check @NumStability.tridiagonalToeplitz
#check @NumStability.tridiagonalToeplitz_diag
#check @NumStability.tridiagonalToeplitz_transpose
