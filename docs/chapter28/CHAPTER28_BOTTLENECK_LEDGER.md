# Chapter 28 Bottleneck Ledger

The selected-scope gate is **FAIL solely at 28-P3**. This ledger distinguishes
that one remaining proof bottleneck from terminal source imprecision and from
source sentences that required a proved correction.

## Hilbert and Cauchy subgroup

| Source conclusion | Production evidence | Exact remaining foundation | Status |
|---|---|---|---|
| Hilbert SPD and total positivity | `hilbertMatrix_isSymPosDef_explicit`, `hilbertMatrix_isStrictlyTotallyPositive` | none | PASS |
| (28.1)-(28.4) | `factorInverseGram_eq_hilbertInverseFormula`, `hilbert_inverse_formula`, `hilbert_inverse_formula_left`, `hilbert_det_formula`, `hilbertMatrix_eq_choleskyGram`, `hilbertCholeskyFactor_mul_inverse`, `hilbertCholeskyFactorInverse_mul` | none | PASS |
| `det(H_n) ~ 2^{-2n²}` in leading-exponential sense | `log_hilbert_det_eq_sum`, `hilbertDetLeadingLogRate_proved` | none for the faithful leading-log interpretation | PASS |
| `‖H̃_n‖₂ = π + O(1/log n)` | `opNorm2_shiftedHilbert_le_pi`, `pi_sub_sixteen_div_log_succ_le_opNorm2_shiftedHilbert`, `shiftedHilbert_norm_asymptotic` | none | PASS |
| `κ₂(H_n) ~ exp(3.5n)` | exact Hilbert definitions | the printed `3.5` is rounded and does not determine a ratio-accurate proposition | DEFER-MISSING-PRECISE-STATEMENT |
| Cauchy determinant/inverse/LU/entry sum/total positivity | `cauchyMatrix_det_eq_formula`, `cauchyMatrix_mul_cauchyInverseFormula`, `cauchyInverseFormula_mul_cauchyMatrix`, `cauchyLower_mul_cauchyUpper`, `sum_cauchyInverseFormula`, `cauchy_ordered_minor_det_formula`, `cauchyMatrix_isStrictlyTotallyPositive` | none | PASS |

The Cauchy proofs use pivot/Schur induction, Lagrange interpolation/residues,
and finite product telescoping. No determinant, inverse, LU, sum, or minor
identity is supplied as a premise.

## Random-matrix probability subgroup

| Source conclusion | Production evidence | Exact remaining foundation | Status |
|---|---|---|---|
| 28-P3 real-Ginibre expected real-eigenvalue limit | `measurable_realEigenvalueCount`, `integrable_realEigenvalueCount`, `lintegral_ginibreIncidence_regular_eq_rootCount`, `lintegral_ginibreIncidence_gaussian_eq_rootCount`, and `lintegral_ginibreIncidence_gaussian_eq_expected` close the actual expectation reduction. `realGinibreExpectedCountClosedForm_limit` proves the analytic closed-form limit; dimensions one and two are identified exactly. The projective, determinant-moment, characteristic-product, and Sylvester modules add unconditional scalar/structural reductions. | A premise-free theorem `RealGinibreFiniteExpectationFormula` for every positive dimension, or an equivalent premise-free `RealGinibreExpectedCountLimit`. `realGinibreExpectedCountLimit_of_finiteExpectationFormula` remains conditional on the missing finite formula. Concretely, the exact all-positive-dimension determinant/absolute-characteristic-moment integral still has to be evaluated or shown to obey the recurrence matching the closed form. | **PARTIAL/OPEN** |
| Uniform iid `[0,1]` matrix has a positive Perron root a.s. | `uniformUnitIntervalMatrixMeasure_strictlyPositive`, `hasPositiveDominantEigenvalue_of_strictlyPositive`, `uniformPositivePerronAlmostSure` | none | PASS |

Root-count measurability and the finite-to-one coarea step are no longer
bottlenecks; both now have unconditional production theorems.

## Stewart and randsvd subgroup

| Source conclusion | Production evidence | Exact remaining foundation | Status |
|---|---|---|---|
| Theorem 28.1: Stewart output is Haar | `stewartOrthogonalGroupLaw_eq_normalizedOrthogonalHaar`, `stewartTheorem28_1HaarConclusion` | none | PASS |
| Prescribed randsvd spectrum | `randsvdMatrix_transpose_mul_self`, `randsvdMatrix_rightGram_column_eigenpair`, `randsvdMatrix_rightSingularVectors_orthonormal` | none, under explicit orthogonality hypotheses | PASS |
| Schedule parameter `alpha = kappa_2(A)` | `kappa2_randsvdMatrix_eq_of_attained_bounds`, `randsvd_oneLarge_kappa2_eq_alpha`, `randsvd_oneSmall_kappa2_eq_alpha`, `randsvd_geometric_kappa2_eq_alpha`, `randsvd_arithmetic_kappa2_eq_alpha` | none, under explicit positivity/order/nonzero hypotheses | PASS |
| Single-Householder diagonal-plus-rank-2 warning | `singleHouseholder_randsvd_eq_diagonal_add_rankTwo`, `singleHouseholder_randsvd_correction_rank_le_two` | none | PASS |
| Symmetric adaptation `Q Λ Qᵀ` | `symmetricRandsvdMatrix`, `symmetricRandsvdMatrix_transpose`, `symmetricRandsvdMatrix_column_eigenpair` | none | PASS |
| Printed operation-count comparison | construction definitions | no exact operation graph or flop convention is printed | DEFER-MISSING-PRECISE-STATEMENT |

## Pascal and moment subgroup

| Source conclusion | Production evidence | Exact remaining foundation | Status |
|---|---|---|---|
| Hilbert/Pascal moment representations and positivity | `intervalMomentMatrix_quadraticForm`, `intervalMomentMatrix_quadraticForm_re_nonneg`, `intervalMomentMatrix_quadraticForm_re_pos`, `hilbertMatrix_eq_intervalMomentMatrix`, `pascalMoment_integral`, `pascalMatrix_eq_intervalMomentMatrix`, `pascal_circleAverage`, `pascal_circleMoment_normalized`, `pascal_circleMoment` | none | PASS |
| Pascal reciprocal characteristic polynomial | `pascal_charpoly_reciprocal`, `pascal_charpoly_palindromic_of_even` | none for the correct signed/parity theorem; the sign-free all-order source statement is false for odd order | PASS / SOURCE-DISCREPANCY |
| Optimal singularizing perturbation | `pascalOptimalSingularizingPerturbation_mulVec`, `pascalOptimalPerturbation_has_nonzero_kernel`, `opNorm2_pascalOptimalSingularizingPerturbation`, `pascalOptimalPerturbation_is_operator2_minimal` | none | PASS |
| Pascal condition and perturbation asymptotics | `pascalConditionTwo_eq_opNorm2_sq`, `pascalConditionTwo_exponential_sandwich`, `pascalConditionTwo_log_rate`, `pascalOptimalPerturbation_log_rate`, `pascalCentralBinomial_sq_isEquivalent`, `pascalFactorialRatio_isEquivalent` | none for the faithful log rates and Stirling endpoints; the first printed ratio-one `~` conflicts with the source's own bound | PASS / SOURCE-DISCREPANCY |
| Pascal total positivity, strict spectrum, sign changes | `pascalMatrix_isStrictlyTotallyPositive`, `pascalSortedEigenvalue_strictAnti`, `pascalSortedEigenvector_hasExactlySignChanges` | none | PASS |
| Pascal algebraic core, final-entry perturbation, cube root | `pascalMatrix_eq_lower_mul_transpose`, `pascalMatrix_det`, `signedPascal_mul_self`, `pascalMatrix_mul_signedGram`, `signedGram_mul_pascalMatrix`, `pascalInverseFormula_apply_of_le`, `signedPascal_conj_pascalMatrix`, `pascal_reciprocal_eigenpair`, `pascal_sub_last_entry_has_nonzero_kernel`, `pascalIdentityCubeRootCandidate_cube` | none | PASS |

## Toeplitz and companion subgroup

| Source conclusion | Production evidence | Exact remaining foundation | Status |
|---|---|---|---|
| General `T_n(c,d,e)` spectrum | `generalToeplitz_sine_eigenpair`, `generalToeplitz_complex_sine_eigenpair_of_super_ne_zero`, `generalToeplitz_unrestricted_complex_eigenpair`, `tridiagonalToeplitz_p522_unrestricted_eigenvalue`, `complexTridiagonalToeplitz_p522_unrestricted_charpoly`, `tridiagonalToeplitz_p522_unrestricted_charpoly`, `tridiagonalToeplitz_p522_unrestricted_roots_charpoly` | none, including degenerate product-zero cases | PASS |
| Inverse and condition asymptotic of `T_n(-1,2,-1)` | `tridiagonalToeplitz_mul_secondDifferenceInverse`, `secondDifferenceInverse_mul_tridiagonalToeplitz`, `opNorm2_secondDifference_eq`, `opNorm2_secondDifferenceInverse_eq`, `secondDifferenceConditionTwo_eq_closedForm`, `secondDifferenceClosedForm_isEquivalent_invHalfAngleSq`, `invSecondDifferenceHalfAngleSq_isEquivalent_model`, `secondDifferenceConditionAsymptotic_proved` | none | PASS |
| LU-diagonal/cyclic-reduction convergence prose | exact finite Toeplitz definitions | no fixed-diagonal indexing, topology/rate, or precise cyclic-reduction endpoint is printed | DEFER-MISSING-PRECISE-STATEMENT |
| Companion characteristic polynomial and `compan(poly(A))` | `companionMatrix_charpoly`, `companionOfMatrix`, `companionOfMatrix_charpoly` | none | PASS |
| Companion nonderogatory property under similarity | `companionMatrix_sub_scalar_rank_ge`, `Matrix.IsSimilar.rank_sub_scalar_eq`, `isSimilar_companion_rank_sub_scalar_ge` | none | PASS |
| Companion singular values | `companion_conjTranspose_mul_self_charpoly`, `companionSquaredSingularValues_multiset_eq`, `companionSquaredSingularValues_count_one`, `companionSingularValues_multiset_eq`, `companionSingularValues_eq_one_or_eq_exceptional` | none | PASS |
| Companion normality | `companion_orderTwo_isStarNormal_iff`, `companion_orderAtLeastThree_isStarNormal_iff` | none for the repaired order-sensitive classifications; the printed complex iff is false | PASS / SOURCE-DISCREPANCY |

## Gate conclusion

All selected non-Ginibre rows above are terminal. The only selected proof
bottleneck is the premise-free all-positive-dimension real-Ginibre expectation/limit
endpoint in 28-P3.
