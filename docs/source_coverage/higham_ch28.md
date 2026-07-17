# Higham Chapter 28 Source Coverage Ledger

Source: Higham, 2nd ed., Chapter 28, printed pp. 511-526. Mode: core.

| Source group | Terminal status | Lean evidence / dependency |
|---|---|---|
| Hilbert definition and symmetry | VERIFIED | `hilbertMatrix`, `hilbertMatrix_transpose` |
| Hilbert SPD | VERIFIED | `hilbertMatrix_isSymPosDef_explicit` from the compiled `RᵀR` quadratic sum of squares |
| Hilbert total positivity | OPEN | positive Cauchy determinant-product side is proved; equality with every ordered minor determinant is missing |
| Hilbert GE/Cholesky componentwise-stability prose | DEFER-MISSING-PRECISE-STATEMENT | source prints no coefficient, denominator convention, arithmetic model, or quantified error bound |
| Table 28.1 MATLAB generator catalogue | EXCLUDED | software/literature table, explicitly accounted for |
| Equation (28.1) | VERIFIED | printed entry formula equals the inverse-factor Gram; `hilbert_inverse_formula` and left inverse |
| Exact part of (28.2) | VERIFIED | `hilbert_det_formula` for every order |
| Equations (28.3)-(28.4) | VERIFIED | `hilbertMatrix_eq_choleskyGram` and both factor-inverse products |
| Hilbert/Pascal moment-matrix contour representations | PARTIAL / OPEN | `hilbertMatrix_isSymPosDef_explicit` and `pascalMatrix_isSymPosDef_explicit` close the finite SPD endpoints algebraically, but the general positive-weight integral and the stated contour/change-of-variable instantiations are absent |
| Hilbert determinant/condition/shifted-norm asymptotics | OPEN / DEFER | exact target propositions remain, but assumption-only transfers were removed. The determinant shorthand needs a log-scale formulation/proof, `3.5` is rounded, and the shifted finite-section norm remainder is unproved. |
| Cauchy formulas | PARTIAL / OPEN | exact candidates, `CauchyAdmissible`, nonzero factors/entries, source-shaped triangular L/U, ordered-minor formula positivity, and first-pivot Schur identity are proved; determinant, inverse, LU, inverse-entry sum, and total positivity remain open |
| Equations (28.5)-(28.11) | DEFER-MISSING-PRECISE-STATEMENT | source `approx` leaves convergence/error semantics unspecified |
| Randsvd definition and schedules | VERIFIED definitions/algebra | `randsvdMatrix`, four schedules, paired Stewart producer, and exact right-Gram identity; the factor Haar laws depend on open Theorem 28.1 |
| Randsvd prescribed singular values and `alpha = kappa_2(A)` | PARTIAL / OPEN | the exact right-Gram identity is local, but singular-value-multiset invariance and the extremal-value condition-number theorem, with honest ordering/nonzero domains, are absent |
| Randsvd single-Householder rank-2 warning | OPEN | generic Householder and randsvd definitions exist; the two-factor outer-product expansion and rectangular rank bound are absent |
| Symmetric randsvd adaptation | OPEN | orthogonal/diagonal infrastructure exists, but `A = Q Lambda Q^T`, symmetry, and prescribed-eigenvalue preservation have not been formalized |
| Randsvd cost discussion | DEFER-MISSING-PRECISE-STATEMENT | no concrete operation graph, flop convention, or selected asymptotic-cost proposition is printed |
| Theorem 28.1 | PARTIAL / OPEN | normalized product-Gaussian inputs, exact Householder reduction, source-ordered `P_i`, `D`, `Q`, samplewise orthogonality, measurable orthogonal-group output, and normalized push-forward are compiled; the genuine Gaussian left-invariance/Haar proof remains open |
| Real-Ginibre expected-count limit | PARTIAL / OPEN | normalized standard product law and multiplicity-correct `realEigenvalueCount` are compiled; measurability/integrability of the count, the finite expectation formula, and the desired Gamma/Stirling limit remain unproved transfer premises |
| Uniform positive random matrix | PARTIAL / OPEN | normalized product law and deterministic/all-ones witnesses are compiled; boundary-null strict positivity and the full-measure Perron event remain assumed premises |
| Pascal algebraic core | VERIFIED | explicit SPD quadratic form, `P=LLᵀ`, determinant one, signed factor involution, `P⁻¹=SᵀS` both sides, Cohen's lower-triangular inverse-entry formula, similarity, and reciprocal eigenpairs |
| Pascal characteristic-polynomial palindromicity | OPEN | reciprocal matrix/eigenpair facts are local, but no coefficient-palindromicity or `pi_n(lambda)=lambda^n pi_n(1/lambda)` theorem is proved |
| Pascal final-entry perturbation and rotated cube root | VERIFIED | `pascal_sub_last_entry_has_nonzero_kernel` gives an explicit all-orders kernel; `pascalIdentityCubeRootCandidate_cube` proves the source-correct identity `T³=I` from an actual alternating-binomial convolution |
| Pascal condition asymptotic | PARTIAL / SOURCE DISCREPANCY | `pascalCentralBinomial_sq_isEquivalent` proves `binom(2n,n)² ~ 16^n/(nπ)` unconditionally. The same page's bound `p_nn ≤ ‖P‖₂ ≤ 2p_nn` forces normalized limsup at most `1/4`, so the printed first `~` cannot mean strict ratio-one equivalence; a constant-factor or log-rate theorem remains open. |
| Pascal optimal perturbation, total positivity, and sign-change theorem | OPEN | the easy singular perturbation, SPD, inverse, reciprocal eigenpairs, and factorial-ratio Stirling endpoint are local; optimality/norm linkage, all-minor positivity, and the oscillation bridge are missing |
| Tridiagonal Toeplitz inverse | VERIFIED | integer Green recurrence and both inverse products for `Tₙ(-1,2,-1)` |
| Toeplitz spectrum/condition asymptotic | PARTIAL / OPEN | direct sine recurrence, nonzero vectors, normalized DST orthogonality, and exact diagonalization verify the symmetric family `T_n(c,d,c)`; the printed general square-root spectrum and the operator-norm/cosine-asymptotic bridge remain open |
| Toeplitz LU/cyclic-reduction convergence prose | DEFER-MISSING-PRECISE-STATEMENT | no fixed-diagonal indexing, convergence topology/rate, limiting factor, or exact cyclic-reduction proposition is printed |
| Companion eigenvector | VERIFIED | `companionMatrix_mulVec_companionEigenvector` |
| Companion characteristic/nonderogatory/SVD properties | PARTIAL / OPEN / SOURCE DISCREPANCY | target-polynomial coefficients, an explicit all-order transpose Krylov basis, a unit-determinant shift minor proving the companion `rank(C-λI) ≥ n-1`, and exact `CᴴC` are proved; determinant equality, `compan(poly(A))` eigenvalue preservation, the statement for every matrix similar to a companion, and the `2≤n` Gram-spectrum/SVD formulas remain open. The printed complex normality iff with `a_0=1` is false; a repaired `n≥2`, `|a_0|=1` theorem is open. |
| Problems 28.1-28.2 | EXCLUDED | optional research rows not selected |

Aggregate selected-scope status: **FAIL** because the Hilbert/Pascal
asymptotic and total-positivity endpoints, the selected p.515 Cauchy row,
the random-matrix probability producers, Theorem 28.1 Haar conclusion, the
prescribed-spectrum, rank-2, and symmetric randsvd endpoints, and the remaining p. 522-523
Toeplitz/companion endpoints remain open. See
`docs/chapter28/CHAPTER28_NOT_PROVED_LEDGER.md`.

Verification targets are `Higham28`, `Higham28Exact`, `Higham28Stewart`,
`Higham28Probability`, `Higham28Asymptotics`, `Higham28Pascal`, and
`Higham28Contracts`, plus the Algorithms umbrella.
Forbidden-token hygiene and representative axiom audits are required at handoff.
