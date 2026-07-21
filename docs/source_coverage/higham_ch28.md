# Higham Chapter 28 Source Coverage Ledger

Source: Higham, 2nd ed., Chapter 28, printed pp. 511-526. Mode: core.

| Source group | Terminal status | Lean evidence / dependency |
|---|---|---|
| Hilbert definition and symmetry | PASS | `hilbertMatrix`, `hilbertMatrix_transpose` |
| Hilbert SPD | PASS | `hilbertMatrix_isSymPosDef_explicit` from the compiled `RᵀR` quadratic sum of squares |
| Hilbert total positivity | PASS | `hilbertMatrix_isStrictlyTotallyPositive` specializes the proved ordered Cauchy-minor determinant formula |
| Hilbert GE/Cholesky componentwise-stability prose | DEFER-MISSING-PRECISE-STATEMENT | source prints no coefficient, denominator convention, arithmetic model, or quantified error bound |
| Table 28.1 MATLAB generator catalogue | EXCLUDED | software/literature table, explicitly accounted for |
| Equation (28.1) | PASS | `factorInverseGram_eq_hilbertInverseFormula`, `hilbert_inverse_formula`, `hilbert_inverse_formula_left` |
| Exact part of (28.2) | PASS | `hilbert_det_formula` for every order |
| Literal ratio reading of (28.2) | SOURCE-DISCREPANCY / CORRECTED | `higham28_not_HilbertDetAsymptotic` proves the recorded ratio-`IsEquivalent` surface false: the normalized ratio is at least `4^n` and tends to `+∞`. `hilbertDetLeadingLogRate_proved` retains the valid leading-log correction. |
| Equations (28.3)-(28.4) | PASS | `hilbertMatrix_eq_choleskyGram`, `hilbertCholeskyFactor_mul_inverse`, `hilbertCholeskyFactorInverse_mul` |
| Hilbert/Pascal moment-matrix representations | PASS | `intervalMomentMatrix_quadraticForm`, `intervalMomentMatrix_quadraticForm_re_pos`, `hilbertMatrix_eq_intervalMomentMatrix`, `pascalMoment_integral`, `pascalMatrix_eq_intervalMomentMatrix`, `pascal_circleAverage`, `pascal_circleMoment_normalized`, and `pascal_circleMoment` close the positive-weight and two source instances |
| Hilbert determinant leading asymptotic | PASS | `hilbertDetLeadingLogRate_proved : HilbertDetLeadingLogRate` proves `log(det(H_n))/n² -> -2 log 2`, the faithful leading-exponential interpretation of (28.2) |
| Hilbert condition/shifted-norm prose | PASS | `hilbertConditionTwo_log_rate` proves the source-faithful exact statement `log(κ₂(H_n))/n → 4 log(1+√2)` (approximately `3.5255`) by a finite central-Delannoy sandwich; `shiftedHilbert_norm_asymptotic` proves `‖H̃_n‖₂ = π + O(1/log n)`. The recorded literal ratio surface `HilbertConditionAsymptotic` remains intentionally unasserted because `3.5` is rounded. |
| Cauchy formulas | PASS | `cauchyMatrix_det_eq_formula`, `cauchyMatrix_mul_cauchyInverseFormula`, `cauchyInverseFormula_mul_cauchyMatrix`, `cauchyLower_mul_cauchyUpper`, `sum_cauchyInverseFormula`, `cauchy_ordered_minor_det_formula`, `cauchyMatrix_isStrictlyTotallyPositive` |
| Equations (28.5)-(28.11) | DEFER-MISSING-PRECISE-STATEMENT | source `approx` leaves convergence/error semantics unspecified |
| Randsvd definition and schedules | PASS | `randsvdMatrix`, four schedules, paired Stewart producer, exact right-Gram identity, and the proved Haar law for each Stewart factor |
| Gaussian QR Haar generator on p. 517 | **PASS** | `Higham28GaussianQRHaar.lean` constructs the iid `N(0,σ²)` column-product law, proves almost-sure nonsingularity, exact positive-diagonal MGS QR, measurable left-equivariant `Q`, and `gaussianQRQLawOfScale_eq_normalizedOrthogonalHaar` for every nonzero scale `σ` (equivalently every nondegenerate variance `σ²`). |
| Randsvd prescribed singular values and `alpha = kappa_2(A)` | PASS | `randsvdMatrix_rightGram_column_eigenpair`, `randsvdMatrix_rightSingularVectors_orthonormal`, `kappa2_randsvdMatrix_eq_of_attained_bounds`, `randsvd_oneLarge_kappa2_eq_alpha`, `randsvd_oneSmall_kappa2_eq_alpha`, `randsvd_geometric_kappa2_eq_alpha`, and `randsvd_arithmetic_kappa2_eq_alpha` close the row under explicit positivity/order hypotheses |
| Randsvd single-Householder rank-2 warning | PASS | `singleHouseholder_randsvd_eq_diagonal_add_rankTwo` and `singleHouseholder_randsvd_correction_rank_le_two` give the exact rectangular factorization and rank bound |
| Symmetric randsvd adaptation | PASS | `symmetricRandsvdMatrix`, `symmetricRandsvdMatrix_transpose`, and `symmetricRandsvdMatrix_column_eigenpair` give the symmetric construction and prescribed eigenbasis |
| Randsvd cost discussion | DEFER-MISSING-PRECISE-STATEMENT | no concrete operation graph, flop convention, or selected asymptotic-cost proposition is printed |
| Theorem 28.1 | PASS | normalized product-Gaussian inputs, exact Householder reduction, source-ordered `P_i`, `D`, `Q`, samplewise orthogonality, the dimension-step recursion, Gaussian rotation, Haar-fiber uniqueness, and `stewartOrthogonalGroupLaw_eq_normalizedOrthogonalHaar` are compiled |
| Real-Ginibre expected-count limit (28-P3) | **PASS** (2026-07-17) | Prior infrastructure (measurability, coarea/incidence chain, closed-form sequence limit, dims 1–2) is now completed by `ch28gf_kernelTransfer` → `ch28gf_realGinibreFiniteExpectationFormula` (premise-free) → `ch28gf_realGinibreExpectedCountLimit` (premise-free `E_n/√n → √(2/π)`), all axiom-clean, in `Higham28GinibreFiniteFormula.lean`. |
| Real-Ginibre proportion corollary | **PASS** | `ch28gf_realGinibreExpectedProportionLimit` derives the next printed sentence `E_n/n → 0`; the serialized focused target build passed (3,288 jobs), and the final axiom harness reports only `propext`, `Classical.choice`, and `Quot.sound`. |
| Uniform positive random matrix | PASS | `uniformUnitIntervalMatrixMeasure_strictlyPositive` proves boundary-null strict positivity, `hasPositiveDominantEigenvalue_of_strictlyPositive` supplies the deterministic Perron bridge, and `uniformPositivePerronAlmostSure` proves the concrete full-measure intersection event |
| Pascal algebraic core | PASS | `pascalMatrix_eq_lower_mul_transpose`, `pascalMatrix_det`, `signedPascal_mul_self`, `pascalMatrix_mul_signedGram`, `signedGram_mul_pascalMatrix`, `pascalInverseFormula_apply_of_le`, `signedPascal_conj_pascalMatrix`, `pascal_reciprocal_eigenpair` |
| Pascal characteristic-polynomial reciprocity | PASS / SOURCE-DISCREPANCY | `pascal_charpoly_reciprocal` proves the correct signed reversal `charpoly(P_n)=C((-1)^n)*charpoly(P_n).reverse`; `pascal_charpoly_palindromic_of_even` proves literal palindromicity for even order. The sign-free all-order source sentence is false at odd order. |
| Pascal final-entry perturbation and rotated cube root | PASS | `pascal_sub_last_entry_has_nonzero_kernel` gives an explicit all-orders kernel; `pascalIdentityCubeRootCandidate_cube` proves the source-correct identity `T³=I` from an actual alternating-binomial convolution |
| Pascal condition asymptotic | PASS / SOURCE-DISCREPANCY | `pascalConditionTwo_eq_opNorm2_sq`, `pascalConditionTwo_exponential_sandwich`, and `pascalConditionTwo_log_rate` prove the faithful rate `log 16`; `pascalCentralBinomial_sq_isEquivalent` proves the Stirling model. The printed first ratio-one `~` is inconsistent with the page's own norm bound. |
| General reciprocal-spectrum SPD construction on p. 520 | **PASS / SOURCE-DISCREPANCY** | `Higham28ReciprocalSPD.lean` proves `X²=I`, determinant one, SPD, and reciprocal nonzero eigenpairs. For lower `Z`, `higham28ReciprocalInvolution_lower_and_diag` derives lower `X` with diagonal `d`; `higham28ReciprocalSPD_row_sign_factorization` and `higham28ReciprocalSPD_lower_reverseCholeskyFactor` prove the corrected row scaling `R=DX` has diagonal `+1` and `RᵀR=A`, while `higham28ReciprocalSPD_transpose_column_sign_factorization` proves the equivalent transpose-column identity for `XᵀD`. The printed column scaling `XD` is false, as the compiled nonsingular lower-triangular witness `higham28ColumnScalingCounter_right_scaling_fails` shows; the correction is terminal. |
| Pascal optimal perturbation | PASS | `pascalOptimalSingularizingPerturbation_mulVec`, `pascalOptimalPerturbation_has_nonzero_kernel`, `opNorm2_pascalOptimalSingularizingPerturbation`, and `pascalOptimalPerturbation_is_operator2_minimal` prove singularity, norm, and optimality; `pascalOptimalPerturbation_log_rate` and `pascalFactorialRatio_isEquivalent` close the exponential/Stirling scale |
| Pascal total positivity, strict spectrum, and sign-change theorem | PASS | `pascalMatrix_isStrictlyTotallyPositive`, `pascalSortedEigenvalue_strictAnti`, and `pascalSortedEigenvector_hasExactlySignChanges` close the all-orders p. 520 row |
| Tridiagonal Toeplitz inverse | PASS | `tridiagonalToeplitz_mul_secondDifferenceInverse`, `secondDifferenceInverse_mul_tridiagonalToeplitz` |
| Toeplitz spectrum/condition asymptotic | PASS | `generalToeplitz_unrestricted_complex_eigenpair`, `tridiagonalToeplitz_p522_unrestricted_eigenvalue`, `complexTridiagonalToeplitz_p522_unrestricted_charpoly`, `tridiagonalToeplitz_p522_unrestricted_charpoly`, `tridiagonalToeplitz_p522_unrestricted_roots_charpoly`, `secondDifferenceConditionTwo_eq_closedForm`, and `secondDifferenceConditionAsymptotic_proved` cover the general spectrum, degenerate cases, exact norm quotient, and asymptotic |
| Toeplitz LU/cyclic-reduction convergence prose | DEFER-MISSING-PRECISE-STATEMENT | no fixed-diagonal indexing, convergence topology/rate, limiting factor, or exact cyclic-reduction proposition is printed |
| Companion eigenvector | PASS | `companionMatrix_mulVec_companionEigenvector` |
| Companion characteristic/nonderogatory/SVD properties | PASS | `companionMatrix_charpoly`, `companionOfMatrix_charpoly`, `isSimilar_companion_rank_sub_scalar_ge`, `companionSquaredSingularValues_multiset_eq`, and `companionSingularValues_multiset_eq` close the characteristic, similarity, eigenvalue-preservation, and singular-value conclusions |
| Companion normality classification | PASS / SOURCE-DISCREPANCY | `companion_orderTwo_isStarNormal_iff` and `companion_orderAtLeastThree_isStarNormal_iff` prove the correct order-sensitive classification. The printed `a_0=1`, all-higher-zero iff is false over `ℂ`, at order two, and at order one. |
| Problems 28.1-28.2 | EXCLUDED | optional research rows not selected |

Aggregate selected-scope status: **PASS** under the fresh strict precise-prose
audit. Row 28-P3's headline limit is closed by
`NumStability/Algorithms/TestMatrices/Higham28GinibreFiniteFormula.lean`, which
proves the premise-free `ch28gf_realGinibreFiniteExpectationFormula`
(`∀ n, 0 < n → expectedRealEigenvalueCount n = realGinibreExpectedCountClosedForm n`)
and hence the premise-free `ch28gf_realGinibreExpectedCountLimit` (`E_n/√n → √(2/π)`),
by supplying the missing measure-theoretic kernel-transfer link
(`ch28gf_kernelTransfer`) that completes the incidence chain and feeding the
formerly-conditional bridge `realGinibreExpectedCountLimit_of_finiteExpectationFormula`.
Both headline theorems take no hypotheses and are axiom-clean
(`[propext, Classical.choice, Quot.sound]`, full transitive closure). The new
`Higham28HilbertCondition.lean` closes the former Hilbert-rate gap with
`hilbertConditionTwo_log_rate`. `Higham28GaussianQRHaar.lean` closes the final
Gaussian-QR producer with a computed positive-diagonal QR map and the
all-nondegenerate-variance Haar push-forward theorem
`gaussianQRQLawOfScale_eq_normalizedOrthogonalHaar`. See
`docs/chapter28/CHAPTER28_NOT_PROVED_LEDGER.md`.

Verification targets are `Higham28`, `Higham28Exact`, `Higham28Stewart`,
`Higham28StewartHaar`, `Higham28StewartRecursion`, `Higham28StewartRawFiber`,
`Higham28Probability`, `Higham28Asymptotics`, `Higham28Ginibre`,
`Higham28GinibreRoots`, `Higham28GinibreIntegral`,
`Higham28GinibreDeterminantIntegral`, `Higham28GinibreGaussianBridge`,
`Higham28GinibreMeasure`, `Higham28GinibreIncidence`, `Higham28Pascal`,
`Higham28PascalSpectral`, `Higham28PascalCondition`,
`Higham28PascalTotalPositivity`, `Higham28PascalOscillationExact`,
`Higham28Moments`, `Higham28ToeplitzGeneral`, `Higham28ToeplitzSpectrum`,
`Higham28ToeplitzCondition`, `Higham28Companion`,
`Higham28CompanionSpectral`, `Higham28HilbertAsymptotic`,
`Higham28HilbertCondition`, `Higham28GaussianQRHaar`,
`Higham28ShiftedHilbert`, and `Higham28Contracts`, plus the Algorithms umbrella.
Forbidden-token hygiene and representative axiom audits are required at handoff.
