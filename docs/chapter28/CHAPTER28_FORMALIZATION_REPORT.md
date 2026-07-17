# Higham Chapter 28 Formalization Report

## Source and scope

- Edition: 2nd ed., SIAM, 2002.
- Chapter: 28, "A Gallery of Test Matrices", printed pp. 511-526.
- Source file: `References/1.9780898718027.ch28.pdf`.
- Mode / split: core / Split 4.
- Selected-scope gate: **FAIL solely because 28-P3 remains PARTIAL/OPEN**.
  Every selected non-Ginibre mathematical row is PASS or has a terminal
  source-imprecision/source-discrepancy disposition.

## Compiled coverage

| Source group | Principal production declarations | Honest status |
|---|---|---|
| Hilbert definitions, SPD, inverse, Cholesky, determinant, total positivity | `hilbertMatrix`, `hilbertMatrix_isSymPosDef_explicit`, `factorInverseGram_eq_hilbertInverseFormula`, `hilbert_inverse_formula`, `hilbert_inverse_formula_left`, `hilbertMatrix_eq_choleskyGram`, `hilbertCholeskyFactor_mul_inverse`, `hilbertCholeskyFactorInverse_mul`, `hilbert_det_formula`, `hilbertMatrix_isStrictlyTotallyPositive` | PASS |
| Hilbert determinant and shifted-norm asymptotics | `log_hilbert_det_eq_sum`, `hilbertDetLeadingLogRate_proved`, `opNorm2_shiftedHilbert_le_pi`, `pi_sub_sixteen_div_log_succ_le_opNorm2_shiftedHilbert`, `shiftedHilbert_norm_asymptotic` | PASS for the faithful leading-log determinant statement and the precise `π + O(1/log n)` norm statement; rounded condition-number `3.5` clause is terminally deferred |
| Cauchy formulas | `cauchyMatrix_det_eq_formula`, `cauchyMatrix_mul_cauchyInverseFormula`, `cauchyInverseFormula_mul_cauchyMatrix`, `cauchyLower_mul_cauchyUpper`, `sum_cauchyInverseFormula`, `cauchy_ordered_minor_det_formula`, `cauchyMatrix_isStrictlyTotallyPositive` | PASS for determinant, inverse, Cho LU, inverse-entry sum, ordered minors, and total positivity |
| Theorem 28.1 | `stewartOrthogonalGroupLaw_eq_normalizedOrthogonalHaar`, `stewartTheorem28_1HaarConclusion` | PASS: the concrete Gaussian Householder producer has normalized Haar law in every dimension |
| Randsvd spectrum and schedules | `randsvdMatrix_rightGram_column_eigenpair`, `randsvdMatrix_rightSingularVectors_orthonormal`, `kappa2_randsvdMatrix_eq_of_attained_bounds`, `randsvd_oneLarge_kappa2_eq_alpha`, `randsvd_oneSmall_kappa2_eq_alpha`, `randsvd_geometric_kappa2_eq_alpha`, `randsvd_arithmetic_kappa2_eq_alpha` | PASS under explicit orthogonality, ordering, positivity, and nonzero hypotheses |
| Randsvd structural warnings/adaptation | `singleHouseholder_randsvd_eq_diagonal_add_rankTwo`, `singleHouseholder_randsvd_correction_rank_le_two`, `symmetricRandsvdMatrix`, `symmetricRandsvdMatrix_transpose`, `symmetricRandsvdMatrix_column_eigenpair` | PASS |
| Hilbert/Pascal moment representations | `intervalMomentMatrix_quadraticForm`, `intervalMomentMatrix_quadraticForm_re_nonneg`, `intervalMomentMatrix_quadraticForm_re_pos`, `hilbertMatrix_eq_intervalMomentMatrix`, `pascalMoment_integral`, `pascalMatrix_eq_intervalMomentMatrix`, `pascal_circleAverage`, `pascal_circleMoment_normalized`, `pascal_circleMoment` | PASS |
| Pascal algebraic/oscillation core | `pascalMatrix_eq_lower_mul_transpose`, `pascalMatrix_det`, `signedPascal_mul_self`, `pascalMatrix_mul_signedGram`, `signedGram_mul_pascalMatrix`, `pascalInverseFormula_apply_of_le`, `signedPascal_conj_pascalMatrix`, `pascal_reciprocal_eigenpair`, `pascal_sub_last_entry_has_nonzero_kernel`, `pascalIdentityCubeRootCandidate_cube`, `pascalMatrix_isStrictlyTotallyPositive`, `pascalSortedEigenvalue_strictAnti`, `pascalSortedEigenvector_hasExactlySignChanges` | PASS |
| Pascal characteristic polynomial | `pascal_charpoly_reciprocal`, `pascal_charpoly_palindromic_of_even` | PASS for the correct signed/parity theorem; SOURCE-DISCREPANCY for the false sign-free all-order sentence |
| Pascal optimal perturbation/asymptotics | `pascalOptimalSingularizingPerturbation_mulVec`, `pascalOptimalPerturbation_has_nonzero_kernel`, `opNorm2_pascalOptimalSingularizingPerturbation`, `pascalOptimalPerturbation_is_operator2_minimal`, `pascalConditionTwo_log_rate`, `pascalOptimalPerturbation_log_rate`, `pascalCentralBinomial_sq_isEquivalent`, `pascalFactorialRatio_isEquivalent` | PASS for exact optimality, log rates, and Stirling endpoints; SOURCE-DISCREPANCY for the first printed ratio-one condition-number `~` |
| Toeplitz | `generalToeplitz_unrestricted_complex_eigenpair`, `tridiagonalToeplitz_p522_unrestricted_eigenvalue`, `complexTridiagonalToeplitz_p522_unrestricted_charpoly`, `tridiagonalToeplitz_p522_unrestricted_charpoly`, `tridiagonalToeplitz_p522_unrestricted_roots_charpoly`, `tridiagonalToeplitz_mul_secondDifferenceInverse`, `secondDifferenceInverse_mul_tridiagonalToeplitz`, `opNorm2_secondDifference_eq`, `opNorm2_secondDifferenceInverse_eq`, `secondDifferenceConditionTwo_eq_closedForm`, `secondDifferenceConditionAsymptotic_proved` | PASS for the general spectrum, degenerate cases, inverse, exact condition quotient, and asymptotic; LU/cyclic prose terminally deferred |
| Companion | `companionMatrix_mulVec_companionEigenvector`, `companion_transpose_krylov_eq_reverseBasis`, `companionMatrix_sub_scalar_rank_ge`, `companionMatrix_charpoly`, `companionOfMatrix_charpoly`, `isSimilar_companion_rank_sub_scalar_ge`, `companion_conjTranspose_mul_self`, `companionSquaredSingularValues_multiset_eq`, `companionSingularValues_multiset_eq`, `companion_orderTwo_isStarNormal_iff`, `companion_orderAtLeastThree_isStarNormal_iff` | PASS for eigenvector, characteristic/eigenvalue preservation, similarity nonderogatoriness, singular values, and repaired normality; SOURCE-DISCREPANCY for the printed normality iff |
| Probability rows other than 28-P3 | `uniformPositivePerronAlmostSure` and the Stewart Haar theorems | PASS |
| 28-P3 real-Ginibre limit | `measurable_realEigenvalueCount`, `integrable_realEigenvalueCount`, `lintegral_ginibreIncidence_regular_eq_rootCount`, `lintegral_ginibreIncidence_gaussian_eq_rootCount`, `lintegral_ginibreIncidence_gaussian_eq_expected`, `realGinibreExpectedCountClosedForm_limit`, plus exact dimensions one and two | **PARTIAL/OPEN**: no premise-free all-positive-dimension expectation/limit theorem |

## The remaining selected gap

The actual real-eigenvalue count is measurable and integrable, the
finite-to-one multiplicity/coarea identity is compiled, and the specialized
Gaussian incidence integral is proved equal to
`expectedRealEigenvalueCount (n + 1)`. The analytic EKS closed form and its
`sqrt(2/pi)` normalized limit are also compiled.

What is still absent is an unconditional all-positive-dimension theorem

`RealGinibreFiniteExpectationFormula`

identifying `expectedRealEigenvalueCount n` with
`realGinibreExpectedCountClosedForm n` for every positive `n`, or an equivalent direct
proof of `RealGinibreExpectedCountLimit`. The existing theorem
`realGinibreExpectedCountLimit_of_finiteExpectationFormula` requires the
finite-formula proposition as a premise. The remaining analytic bottleneck is
therefore the all-positive-dimension evaluation/recurrence of the exact determinant or
absolute-characteristic-moment integral, not measurability or coarea.

The supporting Ginibre development now includes exact density and
Lebesgue-law bridges, incidence and projective charts, multiplicity and area
identities, scalar projective integrals, characteristic-product expectations,
Sylvester determinant identities, closed-form recurrences, and the exact
dimension-one and dimension-two expectations. None of those weaker results
is reported as closing 28-P3.

## Source corrections and terminal deferrals

- The p. 519 Pascal characteristic polynomial is not palindromic in every
  order. `pascal_charpoly_reciprocal` proves
  `charpoly(P_n) = C((-1)^n) * charpoly(P_n).reverse`, and
  `pascal_charpoly_palindromic_of_even` gives literal palindromicity for even
  `n`.
- The first Pascal condition-number `~` cannot be strict ratio equivalence in
  view of the page's own norm bound. `pascalConditionTwo_log_rate` and
  `pascalOptimalPerturbation_log_rate` prove the faithful exponential rates.
- The printed companion normality iff is false over `ℂ`, at order two, and at
  order one. `companion_orderTwo_isStarNormal_iff` and
  `companion_orderAtLeastThree_isStarNormal_iff` prove the repaired
  order-sensitive classifications.
- The rounded Hilbert condition shorthand `exp(3.5n)` is
  `DEFER-MISSING-PRECISE-STATEMENT`; it does not make the selected gate fail.
- Equations (28.5)-(28.11), the qualitative stability/Perron-separation/cost
  prose, and the Toeplitz LU/cyclic-reduction prose are terminally deferred
  because the source does not determine a unique formal endpoint. Table 28.1
  and Problems 28.1-28.2 retain their explicit excluded/optional statuses.

## Hidden-hypothesis audit

- Cauchy determinant, inverse, LU, entry-sum, and ordered-minor conclusions
  are derived from source-domain hypotheses, not assumed identities.
- The concrete Stewart producer is discharged by
  `stewartOrthogonalGroupLaw_eq_normalizedOrthogonalHaar`; the older ambient
  packaging predicate and dimension-zero Dirac example are not counted as
  Theorem 28.1 closure.
- Randsvd condition-number results state the required positivity, ordering,
  nonzero, and attained-bound hypotheses explicitly.
- Pascal, Toeplitz, and companion rows use the corrected production theorems
  above; source-false statements are not silently asserted.
- Ginibre measurability, coarea, and incidence-to-expectation theorems are
  unconditional. The only general limit theorem remains explicitly
  conditional on `RealGinibreFiniteExpectationFormula`, so 28-P3 stays OPEN.

## Documentation

- Inventory: `docs/chapter28/CHAPTER28_SOURCE_INVENTORY.md`
- Terminal/open register: `docs/chapter28/CHAPTER28_NOT_PROVED_LEDGER.md`
- Proof-source ledger: `docs/chapter28/CHAPTER28_PROOF_SOURCE_LEDGER.md`
- Bottleneck ledger: `docs/chapter28/CHAPTER28_BOTTLENECK_LEDGER.md`
- Source-coverage summary: `docs/source_coverage/higham_ch28.md`
