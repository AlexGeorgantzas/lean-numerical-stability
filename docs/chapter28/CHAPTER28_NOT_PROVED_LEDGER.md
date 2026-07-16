# Chapter 28 Not-Proved Ledger

The Chapter 28 selected-scope gate is **FAIL** because the selected p. 515
Cauchy formulas, their Hilbert total-positivity consequence, and the selected
p. 516-517 random-matrix probability producers and normalized-Haar conclusion
of Theorem 28.1 remain nonterminal, as do
the unresolved Hilbert/Pascal moment, palindromicity, asymptotic, and
total-positivity rows and the remaining p. 522-523 Toeplitz/companion
endpoints. For Stewart, the earlier
transfer lemma only repackaged assumed
mass/support/left-invariance and the dimension-zero Dirac example did not
instantiate the printed positive-dimensional Gaussian producer.

The unconditional exact core still includes Hilbert SPD and (28.1)--(28.4),
the exact Hilbert determinant, Pascal SPD/factorization/determinant/signed
involution/both-sided inverse/similarity/reciprocal-eigenpair consequence, the
printed Cohen inverse entries, the all-orders final-entry singular
perturbation, the rotated Pascal cube root of the identity, the unconditional
central-binomial Stirling endpoint, the second-difference Toeplitz inverse,
the full normalized discrete-sine
diagonalization of `T_n(c,d,c)`, the companion power-vector eigenpair, an
all-order transpose Krylov basis, the printed companion rank/nonderogatory
bound, and the exact companion Gram matrix.

## Open selected rows

| Source location | Printed conclusion | Genuine local progress | Missing foundation | Status |
|---|---|---|---|---|
| Sec. 28.1 | Hilbert matrix is totally positive | Hilbert SPD and positive Cauchy determinant-product side | determinant formula for every ordered Cauchy minor | OPEN |
| (28.2) | `det(H_n) ~ 2^{-2n²}` | exact determinant formula for every order | formulate and prove the intended leading-exponential/log-scale theorem; the literal ratio-equivalence reading is too strong | OPEN |
| p. 514 | `κ₂(H_n) ~ exp(3.5n)` and shifted-Hilbert norm `π + O(1/log n)` | exact matrix/inverse definitions and filter-based target propositions | replace rounded `3.5` by a precise rate statement; prove the shifted finite-section norm remainder | DEFER/OPEN |
| p. 515 | Cauchy determinant | exact product candidate, admissible nonzero numerator/denominator, first-pivot Schur identity | general determinant induction | OPEN |
| p. 515 | Cauchy inverse | exact paired-product entries and all denominator/nonzero proofs | genuine partial-fraction/residue proof yielding both matrix products | OPEN |
| p. 515 | Cho LU factors | exact source-shaped L/U entries, unit diagonal and triangularity, first-pivot Schur identity | finite Schur-complement induction/product telescoping | OPEN |
| p. 515 | sum of all inverse entries | exact inverse candidate only | inverse proof plus genuine row-sum/moment derivation | OPEN |
| p. 515 | Cauchy total positivity | positive determinant formula for every strictly ordered subfamily | equality of each minor determinant with that formula | OPEN |
| pp. 516-517 | real-Ginibre expected real-eigenvalue limit | normalized Gaussian product law; `realEigenvalueCount` now counts real characteristic roots with algebraic multiplicity | first prove strong measurability/integrability of the root-count integrand, then prove the finite expectation formula and Gamma/Stirling limit rather than assume them in a transfer | OPEN |
| p. 517 | iid uniform matrix is strictly positive a.s. and has a positive Perron root a.s. | normalized product law and deterministic/all-ones witnesses | boundary-null proof for strict positivity and a genuine full-measure deterministic Perron bridge | OPEN |
| p. 517, Theorem 28.1 | `Q = D P₁⋯P_{n-1}` from independent standard Gaussian tails is Haar-distributed on the orthogonal group | exact normalized product-Gaussian input law; exact local Householder reduction to `r_ii e₁`; source-indexed `P_i`, `D`, and sample-path `Q`; unconditional orthogonality; measurable orthogonal-group output; exact push-forward law and unconditional mass-one theorem | Gaussian null-set handling and a genuine induction/rotational-invariance proof that this exact normalized push-forward is left invariant, hence Haar | OPEN |
| pp. 517-518 | randsvd has the prescribed singular values and schedule parameter `alpha=kappa_2(A)` | `randsvdMatrix_transpose_mul_self` and the paired Stewart Gram identity are exact | singular-value-multiset invariance under both orthogonal factors, nonnegative/order/nonzero domains, and the extremal-value condition-number theorem | PARTIAL/OPEN |
| p. 518 | single-Householder factors give diagonal plus a rank-2 correction | generic Householder and randsvd definitions exist | instantiate both factors, expand into two outer-product corrections, and prove the rectangular rank bound | OPEN |
| p. 518 | symmetric adaptation `A=Q Lambda Q^T` has prescribed eigenvalues | orthogonal-matrix and diagonal infrastructure exists | define the symmetric construction and prove symmetry plus eigenvalue-multiset preservation; Haar distribution remains conditional on Theorem 28.1 | OPEN |
| pp. 518-519 | general moment-matrix representation and the stated Hilbert/Pascal contour/weight realizations | `hilbertMatrix_isSymPosDef_explicit` and `pascalMatrix_isSymPosDef_explicit` close both finite SPD claims algebraically | formalize the contour integral, positive-weight quadratic-form argument, and the two source contour/change-of-variable instantiations | PARTIAL/OPEN |
| p. 519 | Pascal characteristic polynomial is palindromic and `pi_n(lambda)=lambda^n pi_n(1/lambda)` | matrix similarity to the inverse and reciprocal eigenpair transfer | characteristic-polynomial equality under similarity/inversion, coefficient palindromicity, and the polynomial functional identity with its nonzero-`lambda` domain handled honestly | OPEN |
| p. 520 | `κ₂(P_n) ~ binom(2n,n)² ~ 16^n/(nπ)` | `pascalCentralBinomial_sq_isEquivalent` proves the second equivalence unconditionally | replace the literal first equivalence by a faithful constant-factor or log-rate theorem: the same page's norm bound implies a normalized limsup at most `1/4`, so ratio-to-one is not a valid target | PARTIAL/SOURCE DISCREPANCY |
| p. 520 | optimal singularizing perturbation and its `4^{-n} sqrt(nπ)` order | `pascal_sub_last_entry_has_nonzero_kernel` proves the printed easy final-entry perturbation for every nonempty order; `pascalFactorialRatio_isEquivalent` proves the factorial-ratio Stirling endpoint | symmetric spectral/norm proof of optimality and the link from the smallest eigenvalue to that factorial-ratio order | OPEN |
| p. 520 | Pascal total positivity and exact eigenvector sign changes | factorization, SPD, determinant, inverse, and reciprocal eigenpairs are local | Pascal-minor positivity plus the oscillation theorem connecting ordered eigenvectors to sign changes | OPEN |
| p. 522 | general tridiagonal Toeplitz eigenvalues and second-difference condition asymptotic | exact Green inverse; direct sine eigenpairs, nonzero eigenvectors, normalized sine orthogonality, and complete diagonalization for `T_n(c,d,c)`; exact closed-form condition quotient target | diagonal similarity and square-root-branch treatment for general `T_n(c,d,e)`; operator-norm/extremal-spectrum bridge; cosine asymptotic | PARTIAL/OPEN |
| p. 523 | companion characteristic polynomial, `compan(poly(A))` eigenvalue preservation, similarity-to-companion nonderogatory consequence, normality iff, and singular-value formula | exact eigenvector; exact target-polynomial coefficients; explicit all-order transpose Krylov basis; unit-determinant shift minor proving the companion bound `rank(C-λI) ≥ n-1`; exact entrywise formula for `CᴴC` | determinant recurrence; eigenvalue-multiset transport; similarity invariance; a corrected `n≥2`, `|a_0|=1` normality theorem (the printed complex `a_0=1` iff is false, and `n=1` is exceptional); and the `2≤n` Gram characteristic-polynomial/SVD bridge | PARTIAL/OPEN / SOURCE DISCREPANCY |

Equations (28.5)-(28.11) are terminal
`DEFER-MISSING-PRECISE-STATEMENT`: the source intentionally writes `approx`
"in the appropriate probabilistic sense" without choosing convergence mode,
error term, or event. The pp. 512-513 GE/Cholesky componentwise-stability
prose, p. 517 qualitative Perron-root separation observation, p. 518 randsvd
cost discussion, and p. 522 LU-diagonal/cyclic-reduction convergence prose are
also terminal deferred: no unique quantitative probability/cost statement is
printed, the GE prose gives no coefficient or arithmetic model, and the
Toeplitz prose supplies no fixed-diagonal indexing, topology/rate, or exact
cyclic-reduction statement.
Table 28.1 is an explicitly excluded software catalogue. Problems 28.1-28.2
are optional and not selected.
