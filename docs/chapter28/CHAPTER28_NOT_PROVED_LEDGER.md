# Chapter 28 Not-Proved Ledger

The Chapter 28 selected-scope gate is now **PASS** (previously FAIL): row
28-P3 — the last open row — is now CLOSED. `Higham28GinibreFiniteFormula.lean`
proves the premise-free, axiom-clean `ch28gf_realGinibreFiniteExpectationFormula`
(`∀ n, 0 < n → expectedRealEigenvalueCount n = realGinibreExpectedCountClosedForm n`)
and hence the premise-free `ch28gf_realGinibreExpectedCountLimit`
(`E_n/√n → √(2/π)`). Every selected non-Ginibre mathematical row is PASS or
has a terminal source-imprecision/source-discrepancy disposition. Theorem
28.1, the uniform/Perron row, and all selected Hilbert, Cauchy, randsvd,
Pascal, Toeplitz, and companion endpoints are terminal.

## Formerly-open selected row 28-P3 (now CLOSED)

| ID | Printed conclusion | Genuine compiled progress | Endpoint (now supplied) | Status |
|---|---|---|---|---|
| 28-P3 | For a real `n × n` Ginibre matrix, `E_n / sqrt(n) -> sqrt(2/pi)` | `measurable_realEigenvalueCount` and `integrable_realEigenvalueCount` close the actual count's measurability and integrability. `lintegral_ginibreIncidence_regular_eq_rootCount`, `lintegral_ginibreIncidence_gaussian_eq_rootCount`, and `lintegral_ginibreIncidence_gaussian_eq_expected` close the multiplicity/coarea/incidence-to-expectation chain. `realGinibreExpectedCountClosedForm_limit` proves the closed-form sequence's limit; `expectedRealEigenvalueCount_eq_closedForm_one` and `expectedRealEigenvalueCount_eq_closedForm_two` prove dimensions one and two. The determinant/projective/characteristic-product modules supply further unconditional reductions. | NOW SUPPLIED: `ch28gf_realGinibreFiniteExpectationFormula` proves the premise-free all-positive-dimension `∀ n, 0 < n → expectedRealEigenvalueCount n = realGinibreExpectedCountClosedForm n`, and `ch28gf_realGinibreExpectedCountLimit` proves the premise-free `E_n/√n → √(2/π)` (both axiom-clean, `Higham28GinibreFiniteFormula.lean`), completing the incidence chain via the new kernel-transfer link `ch28gf_kernelTransfer` and feeding the formerly-conditional bridge `realGinibreExpectedCountLimit_of_finiteExpectationFormula`. | **CLOSED** (previously OPEN) |

There is no remaining gap. The former bottleneck — the all-positive-dimension
scalar evaluation of the exact expectation/determinant integral (equivalently,
the all-positive-dimension absolute-characteristic-moment evaluation or
recurrence needed to identify it with the proved EKS closed form) — is now
discharged by `ch28gf_kernelTransfer`, which supplies the missing
measure-theoretic kernel-transfer link that completes the incidence chain
feeding `ch28gf_realGinibreFiniteExpectationFormula`.

## Closed selected rows formerly listed here

| ID / source group | Terminal evidence | Status |
|---|---|---|
| 28.2 Hilbert determinant asymptotic | `hilbert_det_formula`, `log_hilbert_det_eq_sum`, `hilbertDetLeadingLogRate_proved` | PASS on the faithful leading-log interpretation |
| 28-A1 shifted Hilbert norm | `opNorm2_shiftedHilbert_le_pi`, `pi_sub_sixteen_div_log_succ_le_opNorm2_shiftedHilbert`, `shiftedHilbert_norm_asymptotic` | PASS |
| 28-P1 / 28-P2 Hilbert and Cauchy total positivity/formulas | `hilbertMatrix_isStrictlyTotallyPositive`, `cauchyMatrix_det_eq_formula`, `cauchyMatrix_mul_cauchyInverseFormula`, `cauchyInverseFormula_mul_cauchyMatrix`, `cauchyLower_mul_cauchyUpper`, `sum_cauchyInverseFormula`, `cauchyMatrix_isStrictlyTotallyPositive` | PASS |
| 28-P3a uniform/Perron | `uniformUnitIntervalMatrixMeasure_strictlyPositive`, `hasPositiveDominantEigenvalue_of_strictlyPositive`, `uniformPositivePerronAlmostSure` | PASS |
| 28.1T Stewart Haar conclusion | `stewartOrthogonalGroupLaw_eq_normalizedOrthogonalHaar`, `stewartTheorem28_1HaarConclusion` | PASS |
| 28-P3c prescribed randsvd spectrum and condition schedules | `randsvdMatrix_rightGram_column_eigenpair`, `randsvdMatrix_rightSingularVectors_orthonormal`, `kappa2_randsvdMatrix_eq_of_attained_bounds`, `randsvd_oneLarge_kappa2_eq_alpha`, `randsvd_oneSmall_kappa2_eq_alpha`, `randsvd_geometric_kappa2_eq_alpha`, `randsvd_arithmetic_kappa2_eq_alpha` | PASS |
| 28-P3d single-Householder warning | `singleHouseholder_randsvd_eq_diagonal_add_rankTwo`, `singleHouseholder_randsvd_correction_rank_le_two` | PASS |
| 28-P3e symmetric randsvd | `symmetricRandsvdMatrix`, `symmetricRandsvdMatrix_transpose`, `symmetricRandsvdMatrix_column_eigenpair` | PASS |
| 28-P4m Hilbert/Pascal moment representations | `intervalMomentMatrix_quadraticForm`, `intervalMomentMatrix_quadraticForm_re_nonneg`, `intervalMomentMatrix_quadraticForm_re_pos`, `hilbertMatrix_eq_intervalMomentMatrix`, `pascalMoment_integral`, `pascalMatrix_eq_intervalMomentMatrix`, `pascal_circleAverage`, `pascal_circleMoment_normalized`, `pascal_circleMoment` | PASS |
| 28-P4c Pascal characteristic polynomial | `pascal_charpoly_reciprocal`, `pascal_charpoly_palindromic_of_even` | PASS for the parity-corrected theorem; terminal SOURCE-DISCREPANCY for the sign-free all-order source sentence |
| 28-P4a Pascal optimal perturbation | `pascalOptimalSingularizingPerturbation_mulVec`, `pascalOptimalPerturbation_has_nonzero_kernel`, `opNorm2_pascalOptimalSingularizingPerturbation`, `pascalOptimalPerturbation_is_operator2_minimal` | PASS |
| 28-P4b Pascal total positivity/oscillation | `pascalMatrix_isStrictlyTotallyPositive`, `pascalSortedEigenvalue_strictAnti`, `pascalSortedEigenvector_hasExactlySignChanges` | PASS |
| 28-A2 Pascal asymptotics | `pascalConditionTwo_eq_opNorm2_sq`, `pascalConditionTwo_exponential_sandwich`, `pascalConditionTwo_log_rate`, `pascalOptimalPerturbation_log_rate`, `pascalCentralBinomial_sq_isEquivalent`, `pascalFactorialRatio_isEquivalent` | PASS for the source-faithful log rates and Stirling endpoints; terminal SOURCE-DISCREPANCY for the first printed ratio-one `~` |
| 28-P5 Toeplitz spectrum/inverse/condition asymptotic | `generalToeplitz_unrestricted_complex_eigenpair`, `tridiagonalToeplitz_p522_unrestricted_eigenvalue`, `complexTridiagonalToeplitz_p522_unrestricted_charpoly`, `tridiagonalToeplitz_p522_unrestricted_charpoly`, `tridiagonalToeplitz_p522_unrestricted_roots_charpoly`, `opNorm2_secondDifference_eq`, `opNorm2_secondDifferenceInverse_eq`, `secondDifferenceConditionTwo_eq_closedForm`, `secondDifferenceConditionAsymptotic_proved` | PASS |
| 28-P6 companion characteristic/nonderogatory/singular values | `companionMatrix_charpoly`, `isSimilar_companion_rank_sub_scalar_ge`, `companionSquaredSingularValues_multiset_eq`, `companionSquaredSingularValues_count_one`, `companionSingularValues_multiset_eq`, `companionSingularValues_eq_one_or_eq_exceptional` | PASS |
| 28-P6a `compan(poly(A))` | `companionOfMatrix`, `companionOfMatrix_charpoly` | PASS |
| 28-P6b companion normality | `companion_orderTwo_isStarNormal_iff`, `companion_orderAtLeastThree_isStarNormal_iff` | PASS for the repaired order-sensitive classification; terminal SOURCE-DISCREPANCY for the printed iff |

## Terminal non-proof dispositions

- The rounded `kappa_2(H_n) ~ exp(3.5n)` clause is
  `DEFER-MISSING-PRECISE-STATEMENT`; the precise shifted-Hilbert clause in
  the same row is PASS.
- Equations (28.5)-(28.11) are `DEFER-MISSING-PRECISE-STATEMENT`: `approx`
  is printed without a convergence mode, error term, or event.
- The pp. 512-513 GE/Cholesky componentwise-stability prose, p. 517
  qualitative Perron-root separation, p. 518 randsvd cost discussion, and
  p. 522 LU-diagonal/cyclic-reduction prose are terminally deferred because
  the source does not determine a unique quantitative theorem.
- Table 28.1 is an excluded software catalogue. Problems 28.1-28.2 are
  optional and not selected.
