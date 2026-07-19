# Higham Chapter 28 Formalization Report

## Source and scope

- Edition: 2nd ed., SIAM, 2002.
- Chapter: 28, "A Gallery of Test Matrices", printed pp. 511-526.
- Source file: `References/1.9780898718027.ch28.pdf`.
- Mode / split: core / Split 4.
- Selected-scope gate: **FAIL** under the fresh strict precise-prose audit.
  Row 28-P3's headline limit is CLOSED (premise-free, axiom-clean
  `ch28gf_realGinibreFiniteExpectationFormula` and
  `ch28gf_realGinibreExpectedCountLimit`, `Higham28GinibreFiniteFormula.lean`).
  The open selected rows are the Hilbert condition log rate and Gaussian-QR
  Haar producer. The general reciprocal-spectrum SPD construction is closed;
  its final column-scaling sentence is closed by a corrected theorem and a
  terminal SOURCE-DISCREPANCY witness.

## Compiled coverage

| Source group | Principal production declarations | Honest status |
|---|---|---|
| Hilbert definitions, SPD, inverse, Cholesky, determinant, total positivity | `hilbertMatrix`, `hilbertMatrix_isSymPosDef_explicit`, `factorInverseGram_eq_hilbertInverseFormula`, `hilbert_inverse_formula`, `hilbert_inverse_formula_left`, `hilbertMatrix_eq_choleskyGram`, `hilbertCholeskyFactor_mul_inverse`, `hilbertCholeskyFactorInverse_mul`, `hilbert_det_formula`, `hilbertMatrix_isStrictlyTotallyPositive` | PASS |
| Hilbert determinant and shifted-norm asymptotics | `log_hilbert_det_eq_sum`, `hilbertDetLeadingLogRate_proved`, `opNorm2_shiftedHilbert_le_pi`, `pi_sub_sixteen_div_log_succ_le_opNorm2_shiftedHilbert`, `shiftedHilbert_norm_asymptotic` | PASS for the determinant leading-log and shifted-norm statements; **OPEN** for the central condition growth claim, which requires the corrected exact log rate `4 log(1+√2)` rather than literal ratio equivalence to rounded `exp(3.5n)` |
| Cauchy formulas | `cauchyMatrix_det_eq_formula`, `cauchyMatrix_mul_cauchyInverseFormula`, `cauchyInverseFormula_mul_cauchyMatrix`, `cauchyLower_mul_cauchyUpper`, `sum_cauchyInverseFormula`, `cauchy_ordered_minor_det_formula`, `cauchyMatrix_isStrictlyTotallyPositive` | PASS for determinant, inverse, Cho LU, inverse-entry sum, ordered minors, and total positivity |
| Theorem 28.1 | `stewartOrthogonalGroupLaw_eq_normalizedOrthogonalHaar`, `stewartTheorem28_1HaarConclusion` | PASS: the concrete Gaussian Householder producer has normalized Haar law in every dimension |
| Randsvd spectrum and schedules | `randsvdMatrix_rightGram_column_eigenpair`, `randsvdMatrix_rightSingularVectors_orthonormal`, `kappa2_randsvdMatrix_eq_of_attained_bounds`, `randsvd_oneLarge_kappa2_eq_alpha`, `randsvd_oneSmall_kappa2_eq_alpha`, `randsvd_geometric_kappa2_eq_alpha`, `randsvd_arithmetic_kappa2_eq_alpha` | PASS under explicit orthogonality, ordering, positivity, and nonzero hypotheses |
| Randsvd structural warnings/adaptation | `singleHouseholder_randsvd_eq_diagonal_add_rankTwo`, `singleHouseholder_randsvd_correction_rank_le_two`, `symmetricRandsvdMatrix`, `symmetricRandsvdMatrix_transpose`, `symmetricRandsvdMatrix_column_eigenpair` | PASS |
| Hilbert/Pascal moment representations | `intervalMomentMatrix_quadraticForm`, `intervalMomentMatrix_quadraticForm_re_nonneg`, `intervalMomentMatrix_quadraticForm_re_pos`, `hilbertMatrix_eq_intervalMomentMatrix`, `pascalMoment_integral`, `pascalMatrix_eq_intervalMomentMatrix`, `pascal_circleAverage`, `pascal_circleMoment_normalized`, `pascal_circleMoment` | PASS |
| Pascal algebraic/oscillation core | `pascalMatrix_eq_lower_mul_transpose`, `pascalMatrix_det`, `signedPascal_mul_self`, `pascalMatrix_mul_signedGram`, `signedGram_mul_pascalMatrix`, `pascalInverseFormula_apply_of_le`, `signedPascal_conj_pascalMatrix`, `pascal_reciprocal_eigenpair`, `pascal_sub_last_entry_has_nonzero_kernel`, `pascalIdentityCubeRootCandidate_cube`, `pascalMatrix_isStrictlyTotallyPositive`, `pascalSortedEigenvalue_strictAnti`, `pascalSortedEigenvector_hasExactlySignChanges` | PASS |
| General reciprocal-spectrum SPD construction | `higham28ReciprocalInvolution_sq`, `higham28ReciprocalSPD_det_one`, `higham28ReciprocalSPD_isSymPosDef_explicit`, `higham28ReciprocalSPD_reciprocal_eigenpair`, `higham28ReciprocalInvolution_lower_and_diag`, `higham28ReciprocalSPD_row_sign_factorization`, `higham28ReciprocalSPD_transpose_column_sign_factorization`, `higham28ReciprocalSPD_lower_reverseCholeskyFactor`, `higham28ColumnScalingCounter_right_scaling_fails` | PASS for the core `X=ZDZ⁻¹`, `A=XᵀX` family and corrected factor identities; SOURCE-DISCREPANCY for literal column scaling `XD` and the conventional Cholesky orientation |
| Pascal characteristic polynomial | `pascal_charpoly_reciprocal`, `pascal_charpoly_palindromic_of_even` | PASS for the correct signed/parity theorem; SOURCE-DISCREPANCY for the false sign-free all-order sentence |
| Pascal optimal perturbation/asymptotics | `pascalOptimalSingularizingPerturbation_mulVec`, `pascalOptimalPerturbation_has_nonzero_kernel`, `opNorm2_pascalOptimalSingularizingPerturbation`, `pascalOptimalPerturbation_is_operator2_minimal`, `pascalConditionTwo_log_rate`, `pascalOptimalPerturbation_log_rate`, `pascalCentralBinomial_sq_isEquivalent`, `pascalFactorialRatio_isEquivalent` | PASS for exact optimality, log rates, and Stirling endpoints; SOURCE-DISCREPANCY for the first printed ratio-one condition-number `~` |
| Toeplitz | `generalToeplitz_unrestricted_complex_eigenpair`, `tridiagonalToeplitz_p522_unrestricted_eigenvalue`, `complexTridiagonalToeplitz_p522_unrestricted_charpoly`, `tridiagonalToeplitz_p522_unrestricted_charpoly`, `tridiagonalToeplitz_p522_unrestricted_roots_charpoly`, `tridiagonalToeplitz_mul_secondDifferenceInverse`, `secondDifferenceInverse_mul_tridiagonalToeplitz`, `opNorm2_secondDifference_eq`, `opNorm2_secondDifferenceInverse_eq`, `secondDifferenceConditionTwo_eq_closedForm`, `secondDifferenceConditionAsymptotic_proved` | PASS for the general spectrum, degenerate cases, inverse, exact condition quotient, and asymptotic; LU/cyclic prose terminally deferred |
| Companion | `companionMatrix_mulVec_companionEigenvector`, `companion_transpose_krylov_eq_reverseBasis`, `companionMatrix_sub_scalar_rank_ge`, `companionMatrix_charpoly`, `companionOfMatrix_charpoly`, `isSimilar_companion_rank_sub_scalar_ge`, `companion_conjTranspose_mul_self`, `companionSquaredSingularValues_multiset_eq`, `companionSingularValues_multiset_eq`, `companion_orderTwo_isStarNormal_iff`, `companion_orderAtLeastThree_isStarNormal_iff` | PASS for eigenvector, characteristic/eigenvalue preservation, similarity nonderogatoriness, singular values, and repaired normality; SOURCE-DISCREPANCY for the printed normality iff |
| Probability rows other than 28-P3 | `uniformPositivePerronAlmostSure` and the Stewart Haar theorems | PASS for these producers; **OPEN** for the distinct normalized-Gaussian-QR Haar claim |
| 28-P3 real-Ginibre limit and proportion | `ch28gf_realGinibreFiniteExpectationFormula`, `ch28gf_realGinibreExpectedCountLimit`, `ch28gf_realGinibreExpectedProportionLimit`, `ch28gf_kernelTransfer` | **PASS**: premise-free finite formula, `E_n/√n → √(2/π)`, and `E_n/n → 0`; serialized focused target passed (3,288 jobs), and the final axiom harness reports only standard axioms |

## The former selected gap (now closed)

The actual real-eigenvalue count is measurable and integrable, the
finite-to-one multiplicity/coarea identity is compiled, and the specialized
Gaussian incidence integral is proved equal to
`expectedRealEigenvalueCount (n + 1)`. The analytic EKS closed form and its
`sqrt(2/pi)` normalized limit are also compiled.

This gap is now CLOSED. The unconditional all-positive-dimension theorem

`ch28gf_realGinibreFiniteExpectationFormula`

identifies `expectedRealEigenvalueCount n` with
`realGinibreExpectedCountClosedForm n` for every positive `n` (premise-free,
axiom-clean), and `ch28gf_realGinibreExpectedCountLimit` proves the premise-free
`E_n/√n → √(2/π)` directly. These feed the formerly-conditional
`realGinibreExpectedCountLimit_of_finiteExpectationFormula` (which took the
finite-formula proposition as a premise). The former analytic bottleneck — the
all-positive-dimension evaluation/recurrence of the exact determinant or
absolute-characteristic-moment integral — is discharged by the new
measure-theoretic kernel-transfer link `ch28gf_kernelTransfer`.

The supporting Ginibre development includes exact density and
Lebesgue-law bridges, incidence and projective charts, multiplicity and area
identities, scalar projective integrals, characteristic-product expectations,
Sylvester determinant identities, closed-form recurrences, and the exact
dimension-one and dimension-two expectations. No one of those weaker results
closed 28-P3 alone; the closure is achieved by
`ch28gf_realGinibreFiniteExpectationFormula` (via `ch28gf_kernelTransfer`),
building on them.

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
- The rounded Hilbert condition shorthand `exp(3.5n)` is an **open precise
  claim**, not a terminal deferral. The decimal prevents literal ratio
  equivalence but the sentence explicitly asserts exponential growth; closure
  requires a corrected exact log-rate theorem.
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
  unconditional. The finite-expectation formula and limit are now proved
  premise-free (`ch28gf_realGinibreFiniteExpectationFormula`,
  `ch28gf_realGinibreExpectedCountLimit`), discharging the general limit bridge
  `realGinibreExpectedCountLimit_of_finiteExpectationFormula`, so 28-P3 is now
  CLOSED (previously OPEN).
- Theorem 28.1 does not discharge the separate Gaussian-QR Haar statement;
  the algorithms are different. The formerly missing general `Z,D,X,A`
  construction is independently produced in `Higham28ReciprocalSPD.lean`.
  That module also audits the final p. 520 factor sentence: for lower `Z`, `X`
  is lower with diagonal `d`, but the Gram-preserving normalization is the row
  scaling `DX`, not the printed column scaling `XD`. Equivalently, `XᵀD` is
  a valid column scaling after transposition. A compiled two-by-two member of
  the source family disproves the literal `XD` reading.

## Documentation

- Inventory: `docs/chapter28/CHAPTER28_SOURCE_INVENTORY.md`
- Terminal/open register: `docs/chapter28/CHAPTER28_NOT_PROVED_LEDGER.md`
- Proof-source ledger: `docs/chapter28/CHAPTER28_PROOF_SOURCE_LEDGER.md`
- Bottleneck ledger: `docs/chapter28/CHAPTER28_BOTTLENECK_LEDGER.md`
- Source-coverage summary: `docs/source_coverage/higham_ch28.md`
