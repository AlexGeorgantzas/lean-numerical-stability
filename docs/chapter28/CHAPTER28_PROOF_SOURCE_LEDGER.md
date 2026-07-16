# Chapter 28 Proof-Source Ledger

The chapter supplies citations rather than full proofs for several hard
properties. No citation is introduced as a Lean axiom. Each such row has an
explicit-domain theorem whose hypotheses name the genuine upstream result.

| Selected claim | Source/citation named by chapter | Genuine upstream domain | Local theorem | Status |
|---|---|---|---|---|
| (28.1) Hilbert inverse | Choi [233, 1983]; Knuth [743, 1997] | factorial telescoping | `factorInverseGram_eq_hilbertInverseFormula`, `hilbert_inverse_formula`, left inverse | VERIFIED |
| (28.2) exact determinant | Hilbert [626, 1894]; Cauchy [207, 1841] | Cholesky diagonal product | `hilbert_det_formula` | VERIFIED |
| (28.2) determinant asymptotic | printed standard asymptotic | product/Stirling estimate for exact `hilbertDetFormula` | `hilbertDetAsymptotic_of_formula_estimate` | PASS (EXPLICIT-DOMAIN) |
| Hilbert condition/shifted norm | Wilf [1202, 1970] and chapter citations | relative spectral estimate; finite-section remainder `O(1/log n)` | `hilbertConditionAsymptotic_of_relative_estimate`, `shiftedHilbertNormAsymptotic_of_remainder_estimate` | PASS (EXPLICIT-DOMAIN) |
| (28.3)-(28.4) | Choi [233, 1983]; Todd [1141, 1954] | factorial and alternating-binomial telescoping | `hilbertMatrix_eq_choleskyGram`, factor/inverse products | VERIFIED |
| Hilbert total positivity | Cauchy [207, 1841] | determinant of every ordered Cauchy minor | `hilbert_isStrictlyTotallyPositive_of_cauchyMinors` | PASS (EXPLICIT-DOMAIN) |
| Cauchy formulas | Cauchy [207, 1841]; Cho [232, 1968] | fraction-free determinant, partial fractions, explicit LU sum, barycentric moments, ordered minor determinants | `cauchy_det_formula_of_cross_product`, `cauchy_inverse_formula_of_partialFractions`, `cauchy_eq_lower_mul_upper_of_summation`, entry-sum and positivity transfers | PASS (EXPLICIT-DOMAIN); order-one producers |
| Theorem 28.1 | Stewart [1070, 1980]; Anderson [113, 1979] | normalized push-forward law, orthogonal support, measurable-set left invariance | `higham28_theorem28_1_product_orthogonal`, `stewartLaw_isNormalizedOrthogonalHaarLaw` | PASS (EXPLICIT-DOMAIN); dimension-zero Dirac producer |
| Real-Ginibre expected count | chapter citations | exact finite expectation coefficient formula and Gamma/Stirling limit | `realGinibreExpectedCountLimit_of_coefficient_formula` | PASS (EXPLICIT-DOMAIN); normalized Gaussian product law |
| Uniform positive random matrix | Perron-Frobenius inference | boundary-null strict positivity and deterministic Perron implication | `uniformPositivePerronAlmostSure_of_boundary_null_of_perron` | PASS (EXPLICIT-DOMAIN); normalized law and all-ones witness |
| Pascal algebra/spectral consequences | Cohen [258, 1975], Turnbull [1167, 1929], Karlin [712, 1968] | binomial convolution; coordinate cancellation; two intermediate cube-root products; relative asymptotic estimate | exact factor/inverse/similarity/eigenpair theorems plus perturbation/cube-root/asymptotic transfers | VERIFIED / PASS (EXPLICIT-DOMAIN) |
| Toeplitz spectrum/condition | references [1004], [1005], [1143] | componentwise sine recurrence, linear independence, extremal relative estimate | `symmetricToeplitz_has_discreteSine_eigenbasis`, `secondDifferenceConditionAsymptotic_of_relative_estimate` | PASS (EXPLICIT-DOMAIN); order-one sine producer |
| Companion eigenvector | direct text | monic root equation | `companionMatrix_mulVec_companionEigenvector` | VERIFIED |
| Companion remaining properties | Kenney-Laub [725, 1988] | determinant coefficients, Krylov linear independence, exact Gram and low-rank characteristic polynomial | `companion_charpoly_of_determinant_coefficient_recurrence`, `companion_isNonderogatory_of_krylov_cyclic`, `companion_gram_charpoly_of_lowRank_identity` | PASS (EXPLICIT-DOMAIN); order-one cyclic producer |
