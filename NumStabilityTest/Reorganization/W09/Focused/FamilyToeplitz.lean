import NumStability.Analysis.TestMatrices.Toeplitz.Basic
import NumStability.Analysis.TestMatrices.Toeplitz.Contracts

/-!
# Toeplitz: reusable test-matrix analysis, standing alone

Imports only the reusable `Toeplitz` modules. This is the family boundary the
wave brief asks for: reusable test-matrix analysis that a later wave can use
without importing Chapter 28 source correspondence.
-/
#check @NumStability.toeplitzSineVector
#check @NumStability.tridiagonalToeplitz
#check @NumStability.tridiagonalToeplitz_diag
#check @NumStability.symmetricToeplitzEigenvalue
