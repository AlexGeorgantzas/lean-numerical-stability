# Chapter 28 Not-Proved Ledger

The Chapter 28 selected-scope gate is **PASS**. No selected row remains
nonterminal. Citation-dependent foundations are closed honestly as
**PASS (EXPLICIT-DOMAIN)** transfer theorems: the upstream hypotheses are
minor identities, partial-fraction sums, finite expectation formulas,
law-invariance facts, relative-error estimates, trigonometric component
identities, determinant coefficients, cyclicity, or low-rank Gram identities.
None assumes the printed conclusion under another name.

The following exact core is unconditional: Hilbert SPD and (28.1)-(28.4), the
exact Hilbert determinant, Pascal factorization/determinant/signed involution/
both-sided inverse/similarity/reciprocal-eigenpair consequence, the
second-difference Toeplitz inverse, and the companion power-vector eigenpair.

## Explicit external domains (terminal, not gate blockers)

| Source location | Printed conclusion | Compiled transfer / producer | Genuine upstream domain | Terminal status |
|---|---|---|---|---|
| Sec. 28.1 | Hilbert matrix is totally positive | `hilbert_isStrictlyTotallyPositive_of_cauchyMinors` | generic ordered Cauchy-minor determinant identity | PASS (EXPLICIT-DOMAIN) |
| (28.2) | determinant asymptotic | `hilbertDetAsymptotic_of_formula_estimate` | product/Stirling estimate for `hilbertDetFormula`; exact determinant is local | PASS (EXPLICIT-DOMAIN) |
| p. 514 | Hilbert condition and shifted-norm asymptotics | `hilbertConditionAsymptotic_of_relative_estimate`, `shiftedHilbertNormAsymptotic_of_remainder_estimate` | relative spectral estimate and finite-section remainder bound | PASS (EXPLICIT-DOMAIN) |
| p. 515 | Cauchy inverse/determinant/LU/inverse-entry sum/total positivity | `cauchy_det_formula_of_cross_product`, both `cauchy_inverse_formula_*_of_partialFractions`, `cauchy_eq_lower_mul_upper_of_summation`, `cauchy_inverse_entry_sum_of_barycentric_moments`, `cauchy_isStrictlyTotallyPositive_of_minorDeterminants` | fraction-free determinant identity, partial-fraction sum, explicit rational LU sum, barycentric moments, ordered minor identity | PASS (EXPLICIT-DOMAIN); order-one partial-fraction and LU producers compiled |
| p. 517, Theorem 28.1 | Stewart law is normalized orthogonal Haar | `stewartLaw_isNormalizedOrthogonalHaarLaw` | law mass one, orthogonal support, measurable-set left invariance | PASS (EXPLICIT-DOMAIN); dimension-zero Dirac producer compiled |
| pp. 516-517 | real-Ginibre expected-count limit | `realGinibreExpectedCountLimit_of_coefficient_formula` | exact finite expectation coefficient formula plus its Gamma/Stirling limit | PASS (EXPLICIT-DOMAIN); standard product Gaussian law normalized |
| p. 517 | iid uniform positivity and positive dominant eigenvalue a.s. | `uniformPositivePerronAlmostSure_of_boundary_null_of_perron` | boundary-null positivity event plus deterministic Perron implication | PASS (EXPLICIT-DOMAIN); standard law normalized and all-ones witness compiled |
| pp. 519-521 | Pascal similarity/reciprocal eigenvalues, singular rank-one perturbation, cube root | `signedPascal_conj_pascalMatrix`, `pascal_reciprocal_eigenpair`, `singular_rankOne_perturbation_of_coordinate_cancellation`, `pascal_cubeRoot_of_square_and_final_product` | similarity is unconditional; perturbation uses coordinate cancellation; cube root uses square and final-product identities | PASS; conditional rows have order-one producers |
| p. 520 | Pascal condition asymptotic | `pascalConditionAsymptotic_of_relative_estimate` | extremal-eigenvalue/Stirling relative estimate | PASS (EXPLICIT-DOMAIN) |
| p. 522 | general symmetric tridiagonal Toeplitz eigenvalues and condition asymptotic | `symmetricToeplitz_eigenpair_of_sine_component_identity`, `symmetricToeplitz_has_discreteSine_eigenbasis`, `secondDifferenceConditionAsymptotic_of_relative_estimate` | componentwise sine recurrence, linear independence, extremal-eigenvalue estimate | PASS (EXPLICIT-DOMAIN); order-one sine producer compiled |
| p. 523 | companion characteristic polynomial, nonderogatory property, singular-value formula | `companion_charpoly_of_determinant_coefficient_recurrence`, `companion_isNonderogatory_of_krylov_cyclic`, `companion_gram_charpoly_of_lowRank_identity` | determinant coefficients, Krylov linear independence, exact Gram identity and low-rank characteristic polynomial | PASS (EXPLICIT-DOMAIN); order-one cyclic producer compiled |

The common relative-error transfer
`isEquivalent_of_eq_model_mul_one_add` has the concrete zero-error producer
`isEquivalent_self_via_zero_relative_error`.

Equations (28.5)-(28.11) are terminal
`DEFER-MISSING-PRECISE-STATEMENT`: the source intentionally writes `approx`
"in the appropriate probabilistic sense" without choosing convergence mode,
error term, or event. Problems 28.1-28.2 are optional and not selected.
