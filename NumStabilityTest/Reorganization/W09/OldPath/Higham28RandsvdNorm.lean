import NumStability.Algorithms.TestMatrices.Higham28RandsvdNorm

/-!
# Higham28RandsvdNorm old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W09, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.randsvdInverseMatrix
#check @NumStability.randsvdMatrix_isInverse
#check @NumStability.oneLargeSingularValues_pos
