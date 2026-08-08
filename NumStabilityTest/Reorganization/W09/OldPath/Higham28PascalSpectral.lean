import NumStability.Algorithms.TestMatrices.Higham28PascalSpectral

/-!
# Higham28PascalSpectral old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W09, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.pascalInverseMatrix
#check @NumStability.opNorm2_transpose_eq
#check @NumStability.opNorm2_matrix_mul_le
