import NumStability.Algorithms.TestMatrices.Higham28Contracts

/-!
# R09 old_only test

isolated historical import preserves the exact supported declaration surface
-/

#check @NumStability.companionMatrix_sub_scalar_rank_ge
#check @NumStability.companion_hasLeftCyclicVector
#check @NumStability.companion_transpose_krylov_eq_reverseBasis
#check @NumStability.companion_transpose_krylov_linearIndependent
#check @NumStability.higham9_sineMatrix_isOrthogonal
#check @NumStability.symmetricToeplitz_orthogonal_diagonalization
#check @NumStability.symmetricToeplitz_scaled_sine_eigenpair
#check @NumStability.symmetricToeplitz_sine_eigenpair
#check @NumStability.toeplitzSineVector_ne_zero
