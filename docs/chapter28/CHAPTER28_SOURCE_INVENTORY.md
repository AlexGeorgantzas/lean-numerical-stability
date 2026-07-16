# Higham Chapter 28 Source Inventory

## Audit basis

- Source: Nicholas J. Higham, *Accuracy and Stability of Numerical Algorithms*,
  2nd ed. (SIAM, 2002), Chapter 28, "A Gallery of Test Matrices".
- Local source: `References/1.9780898718027.ch28.pdf`, printed pp. 511-526.
- Mode: core; parallel owner: Split 4.
- Source inspection: all 16 PDF pages were extracted, rendered, and visually
  checked, including every matrix display and equations (28.1)-(28.11).
- Primary label: Theorem 28.1. Problems 28.1-28.2 have no Appendix A solution.

## Inventory

| ID | Source location | Kind | Statement summary | Precision / generality | Source proof | Dependencies | Decision | Reason code | Lean artifact / status |
|---|---|---|---|---|---|---|---|---|---|
| 28-D0 | p. 512 | construction prose | Similarity/unitary transforms, Kronecker products, and powers produce new tests | precise operations / general | none | Mathlib matrix API | REUSE_EXISTING | REUSE-MATHLIB | no duplicate wrapper |
| 28-D1 | p. 512, Sec. 28.1 | definition | Hilbert matrix `h_ij=1/(i+j-1)` | precise / general | definition | finite matrices | FORMALIZE_CORE | CORE-PRECISE-PROSE | `hilbertMatrix`, zero-index theorem, `hilbertMatrix_transpose` / PASS |
| 28-P1 | pp. 512-513 | property | Hilbert matrix is SPD and totally positive | precise / general | citation/prose | Cholesky and total-minor theory | FORMALIZE_CORE | CORE-PRECISE-PROSE | SPD PASS; total positivity PASS (EXPLICIT-DOMAIN) via `hilbert_isStrictlyTotallyPositive_of_cauchyMinors` |
| 28.1 | p. 513 | equation | Closed formula for entries of `H_n^{-1}` | precise / general | citation-only | factorial telescoping | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | PASS: `factorInverseGram_eq_hilbertInverseFormula`, `hilbert_inverse_formula`, and left inverse in `Higham28Exact` |
| 28.2 | p. 513 | equation | Closed determinant formula and asymptotic equivalence `det(H_n) ~ 2^{-2n^2}` as `n -> infinity` | precise exact formula plus standard asymptotic equivalence | citation-only | Cholesky product; logarithmic/Stirling asymptotics | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | exact formula PASS; asymptotic PASS (EXPLICIT-DOMAIN) by `hilbertDetAsymptotic_of_formula_estimate` |
| 28.3 | p. 513 | equation | Upper Cholesky factor `R` in `H_n=R^T R` | precise / general | citation-only | factorial telescoping | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | PASS: `hilbertMatrix_eq_choleskyGram` |
| 28.4 | p. 513 | equation | Explicit inverse Cholesky-factor entries | precise / general | citation-only | alternating binomial identity | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | PASS: `hilbertCholeskyFactor_mul_inverse` and reverse product |
| 28-A1 | p. 514 | asymptotic prose | `kappa_2(H_n) ~ exp(3.5n)` and `‖H~_n‖_2 = pi + O(1/log n)` as `n -> infinity` | precise standard asymptotic equivalence and Big-O | citation-only | spectral/asymptotic theory | FORMALIZE_CORE | CORE-PRECISE-PROSE | PASS (EXPLICIT-DOMAIN) by the relative-estimate and remainder transfers in `Higham28Asymptotics` |
| 28-E1 | p. 514, Table 28.2 | table | Decimal condition numbers of Hilbert/Pascal matrices | empirical/computed table | symbolic-tool computation | historical software | SKIP | SKIP-FIGURE-TABLE | not encoded |
| 28-D2 | pp. 514-515 | definition | Rectangular Cauchy matrix `1/(x_i+y_j)` | precise / general | definition | finite matrices | FORMALIZE_CORE | CORE-PRECISE-PROSE | `cauchyMatrix`, `cauchyMatrix_transpose` / PASS |
| 28-P2 | p. 515 | exact formulas | Cauchy inverse, determinant, LU factors, inverse-entry sum, total positivity | precise / general | citation-only | rational product identities | FORMALIZE_CORE | CORE-PRECISE-PROSE | PASS (EXPLICIT-DOMAIN): fraction-free determinant, partial-fraction inverse, explicit LU sum, barycentric moments, and ordered-minor transfers; order-one producers compiled |
| 28-E2 | pp. 515-516, Sec. 28.2 | experiments/advice | Mutation tests and qualitative claims about random matrices | empirical/editorial | cited experiments | software tests | SKIP | SKIP-EMPIRICAL | not encoded |
| 28.5 | p. 516 | equation | `E(log kappa_2(A_n)) approx log n + 1.537` for real Gaussian matrices | approximate/probabilistic | citation-only | Gaussian matrix law | DEFER | DEFER-MISSING-PRECISE-STATEMENT | no semantics for `approx` printed |
| 28.6 | p. 516 | equation | Complex analogue with constant 0.982 | approximate/probabilistic | citation-only | complex Gaussian law | DEFER | DEFER-MISSING-PRECISE-STATEMENT | not encoded |
| 28.7 | p. 516 | equation | `||A_n||_2 approx 2 sqrt(n)` | approximate/probabilistic | citation-only | random-matrix asymptotics | DEFER | DEFER-MISSING-PRECISE-STATEMENT | not encoded |
| 28.8 | p. 516 | equation | Complex norm analogue | approximate/probabilistic | citation-only | random-matrix asymptotics | DEFER | DEFER-MISSING-PRECISE-STATEMENT | not encoded |
| 28.9 | p. 516 | equation | Spectral radius `approx sqrt(n)` | partly empirical/approximate | upper bound cited; equality experimental | probability and spectra | DEFER | DEFER-MISSING-PRECISE-STATEMENT | not encoded |
| 28.10 | p. 516 | equation | `kappa_2(T_n)^(1/n) approx 2` | approximate/probabilistic | citation-only | random triangular matrices | DEFER | DEFER-MISSING-PRECISE-STATEMENT | not encoded |
| 28.11 | p. 516 | equation | Unit-triangular analogue `approx 1.306` | approximate/probabilistic | citation-only | random triangular matrices | DEFER | DEFER-MISSING-PRECISE-STATEMENT | not encoded |
| 28-P3 | pp. 516-517 | precise prose | Expected real-eigenvalue limit `E_n/sqrt(n) -> sqrt(2/pi)` | precise probabilistic theorem | citation-only | real Ginibre ensemble | FORMALIZE_CORE | CORE-PRECISE-PROSE | PASS (EXPLICIT-DOMAIN) by `realGinibreExpectedCountLimit_of_coefficient_formula`; normalized standard product law compiled |
| 28-P3a | p. 517 | precise probabilistic/spectral prose | An iid uniform-`[0,1]` square matrix has strictly positive entries almost surely and hence a real positive dominant eigenvalue | precise almost-sure claim / general order | explanatory Perron-Frobenius inference | product probability measure, null boundary event, Perron-Frobenius theory | FORMALIZE_CORE | CORE-PRECISE-PROSE | PASS (EXPLICIT-DOMAIN) from boundary-nullness and deterministic Perron; normalized law and all-ones witness compiled |
| 28-D3 | p. 517, Sec. 28.3 | definition | Randsvd matrix `A=U Sigma V^T` | precise / rectangular generality | definition | rectangular diagonal and matrix products | FORMALIZE_CORE | CORE-PRECISE-PROSE | `rectangularDiagonal`, `randsvdMatrix` / PASS |
| 28-D4 | p. 517 | definitions | One-large, one-small, geometric, and arithmetic singular-value schedules | precise / symbolic families | definitions | real powers | FORMALIZE_CORE | CORE-PRECISE-PROSE | four `*SingularValues` definitions / PASS |
| 28.1T | p. 517 | theorem | Stewart Householder product is Haar-distributed orthogonal | precise probabilistic / general | citation-only | Gaussian vectors, normalized Householders, Haar measure and push-forward | FORMALIZE_CORE | CORE-NAMED-RESULT | deterministic orthogonality VERIFIED; Haar conclusion PASS (EXPLICIT-DOMAIN) from mass/support/left-invariance, with dimension-zero producer |
| 28-D5 | pp. 518-519, Sec. 28.4 | definition | Symmetric Pascal matrix | precise / general | definition | binomial coefficients | FORMALIZE_CORE | CORE-PRECISE-PROSE | `pascalMatrix`, `pascalMatrix_transpose` / PASS |
| 28-P4 | pp. 519-521 | exact properties | Signed triangular factor is involutory; inverse/similarity/reciprocal eigenvalues; singular rank-one perturbation; cube-root matrix | precise / general | derivations and citations | binomial sums, spectral theory | FORMALIZE_CORE | CORE-PRECISE-PROSE | exact factor/inverse/similarity/reciprocal eigenpair PASS; perturbation and cube root PASS (EXPLICIT-DOMAIN), with order-one producers |
| 28-A2 | p. 520 | asymptotic prose | Pascal condition number `~16^n/(n*pi)` | precise asymptotic | derivation sketch | Stirling and spectral norm | FORMALIZE_CORE | CORE-PRECISE-PROSE | PASS (EXPLICIT-DOMAIN) by `pascalConditionAsymptotic_of_relative_estimate` |
| 28-F1 | pp. 511, 521-522 | figures | Matrix galleries, Sierpinski and pseudospectral plots | visual artifacts | computation | MATLAB | SKIP | SKIP-FIGURE-TABLE | not encoded |
| 28-D6 | pp. 521-522, Sec. 28.5 | definition | Tridiagonal Toeplitz matrix `T_n(c,d,e)` | precise / general | definition | finite indices | FORMALIZE_CORE | CORE-PRECISE-PROSE | `tridiagonalToeplitz`, diagonal theorem, and transpose/swap theorem / PASS |
| 28-P5 | p. 522 | exact properties | Explicit eigenvalues; inverse of `T_n(-1,2,-1)`; condition asymptotic | precise exact and asymptotic | citation/cross-reference | trigonometric eigenvectors, Chapter 15 | FORMALIZE_CORE | CORE-PRECISE-PROSE | inverse PASS; eigenbasis and condition asymptotic PASS (EXPLICIT-DOMAIN) from sine component/independence and relative estimate, with order-one producer |
| 28-D7 | pp. 522-523, Sec. 28.6 | definition | Companion matrix for a monic polynomial | precise / general | definition | complex matrices | FORMALIZE_CORE | CORE-PRECISE-PROSE | `companionMatrix` / PASS |
| 28-P6 | p. 523 | exact properties | Characteristic polynomial/eigenvector/nonderogatory properties and singular-value formulas | precise / general | direct/citation-only | determinant, Jordan/rank, SVD | FORMALIZE_CORE | CORE-PRECISE-PROSE | eigenvector VERIFIED; remaining properties PASS (EXPLICIT-DOMAIN) from determinant coefficients, Krylov cyclicity, and exact Gram/low-rank identities |
| 28-L1 | pp. 523-525 | notes/catalogue | Matrix Market, LAPACK generators, other collections | literature/software catalogue | literature review | external repositories | SKIP | SKIP-LITERATURE-REVIEW | not encoded |
| 28.1P | p. 525 | problem | Explore pentadiagonal Toeplitz spectra/pseudospectra | open-ended investigation | none | pseudospectra | SKIP | OPTIONAL-PROBLEM-NOT-SELECTED | not encoded |
| 28.2P | p. 525 | research problem | Compare Householder/Givens Haar generators and band reductions | research problem | none | full Theorem 28.1 and algorithms | SKIP | OPTIONAL-PROBLEM-NOT-SELECTED | not encoded |

## Theorem 28.1 object classification

| Inputs/random law | Computed objects | Analysis-only objects | Current status |
|---|---|---|---|
| Independent Gaussian tails `x_i` | Householder `P_i`, signs `D`, product `Q` | normalized orthogonal Haar characterization | Product orthogonality is unconditional; mass/support/measurable-set left-invariance imply Haar by `stewartLaw_isNormalizedOrthogonalHaarLaw` |
