# Chapter 28 Bottleneck Ledger

## Cauchy subgroup

Source: Higham, 2nd ed., p. 515 of
`References/1.9780898718027.ch28.pdf`.

The source prints five general conclusions for
`C_ij = 1 / (x_i + y_j)`: its inverse entries, determinant, Cho LU
factors, the sum of all inverse entries, and total positivity for strictly
increasing positive nodes. None is closed by assuming an equivalent rational
or minor identity.

| Source conclusion | Genuine Lean progress | Exact remaining foundation | Status |
|---|---|---|---|
| Determinant product | `cauchyDetFormula`, numerator/denominator split, `CauchyAdmissible`, nonzero-factor and formula-positivity theorems | finite Cauchy determinant induction identifying the matrix determinant with the printed product | OPEN |
| Inverse entries | paired-product `cauchyInverseEntry`, exact numerator/denominator split, and nonzero proofs on `CauchyAdmissible` | genuine residue/partial-fraction derivation of `C * B = I`; the left product then follows in finite dimension | OPEN |
| Cho LU factors | exact source-shaped strict-lower/unit-diagonal `L`, upper `U`, triangularity, and `cauchy_firstPivot_schur_entry` | iterate the Schur-complement identity through every pivot and identify the resulting finite products | OPEN |
| Sum of inverse entries | exact inverse candidate is available | first prove the inverse, then derive the all-entries sum by an actual row-sum or barycentric argument | OPEN |
| Cauchy total positivity | `cauchyMinorDetFormula_pos` proves the printed product is positive for every strictly ordered row/column subfamily | determinant formula for every selected square minor | OPEN |
| Hilbert total positivity | Hilbert SPD and exact Hilbert formulas remain proved | specialize the missing ordered Cauchy-minor determinant theorem | OPEN |

## Removed false closure surface

The following theorem-premise patterns and their order-one witnesses were
removed:

- fraction-free determinant equality as a premise;
- `CauchyInversePartialFractionIdentity`;
- `CauchyLUSummationIdentity`;
- assumed barycentric row sums and moment equality;
- assumed determinant formulas for every ordered minor.

These are useful descriptions of what a future proof must establish, but they
are not evidence that the source conclusions have been proved.

## Hilbert and Pascal subgroup

Source: Higham, 2nd ed., printed pp. 512-514 and 518-521.  The re-audit
removed the four assumption-only asymptotic transfers and the order-one
Pascal witnesses.  In their place, `Higham28Pascal.lean` proves the actual
all-orders cube-root-of-identity statement, the Contracts module proves the
all-orders final-entry singular perturbation, and `Higham28Asymptotics.lean`
proves the unconditional central-binomial Stirling endpoint.

| Source conclusion / dependency | Genuine Lean progress | Exact remaining foundation | Status |
|---|---|---|---|
| `det(H_n) ~ 2^{-2n²}` | exact determinant formula for every order | state and prove the intended leading-exponential/log-scale asymptotic; literal ratio equivalence is not the printed estimate's mathematically faithful reading | OPEN |
| `κ₂(H_n) ~ exp(3.5n)` | exact Hilbert matrix and inverse, with a filter target recorded | the printed `3.5` is rounded; choose a precise exponential-rate theorem and prove it from extremal Hilbert spectral asymptotics | DEFER/OPEN |
| `‖H̃_n‖₂ = π + O(1/log n)` | exact shifted family and Big-O target | finite-section operator-norm estimate | OPEN |
| Hilbert/Pascal moment-matrix contour representations | `hilbertMatrix_isSymPosDef_explicit` and `pascalMatrix_isSymPosDef_explicit` close both finite SPD endpoints algebraically | contour-integral formalization, general positive-weight quadratic-form theorem, and the stated Hilbert/Pascal contour/change-of-variable instantiations | PARTIAL/OPEN |
| `κ₂(P_n) ~ binom(2n,n)² ~ 16^n/(nπ)` | `pascalCentralBinomial_sq_isEquivalent` proves the second equivalence directly from Mathlib Stirling | formulate/prove a constant-factor or log-rate result; the same page's `p_nn ≤ ‖P‖₂ ≤ 2p_nn` bound rules out literal ratio-one equivalence (normalized limsup is at most `1/4`) | PARTIAL/SOURCE DISCREPANCY |
| Pascal characteristic-polynomial palindromicity | similarity to the inverse and reciprocal eigenpair transfer | characteristic-polynomial inversion/similarity theorem, coefficient reversal, and the source functional identity | OPEN |
| Subtract one from the final Pascal diagonal entry | explicit inverse-column kernel in `pascal_sub_last_entry_has_nonzero_kernel` | none | VERIFIED |
| Rotated signed-Pascal cube root | polynomial alternating-binomial convolution, exact square, and `pascalIdentityCubeRootCandidate_cube` | none; target corrected to the source's `T³=I` | VERIFIED |
| Optimal singularizing perturbation and its asymptotic size | easy final-entry perturbation and `pascalFactorialRatio_isEquivalent` are verified | symmetric spectral/norm optimality plus the link from the smallest eigenvalue to the factorial-ratio order | OPEN |
| Pascal total positivity and eigenvector sign changes | SPD, determinant, inverse, reciprocal eigenpairs, and Cohen entries | every Pascal minor positive, then the cited oscillation theorem | OPEN |

## Random-matrix probability subgroup

| Source conclusion / dependency | Genuine Lean progress | Exact remaining foundation | Status |
|---|---|---|---|
| Real-Ginibre expected real-eigenvalue limit | normalized product-Gaussian law; repaired `realEigenvalueCount` counts characteristic roots with algebraic multiplicity | strong measurability/integrability of the count, the finite expectation formula, and its Gamma/Stirling limit, with the latter two currently supplied as premises to the transfer | OPEN |
| Uniform iid `[0,1]` matrix is strictly positive and has a positive Perron root almost surely | normalized product law and deterministic/all-ones witnesses | boundary-null strict-positivity proof and the full-measure Perron implication for the concrete event | OPEN |

## Stewart randsvd subgroup

Source: Higham, 2nd ed., printed pp. 517-518 (PDF pages 7-8) of
`References/1.9780898718027.ch28.pdf`.  Printed pp. 519-520 belong to the
following Pascal section.

The exact source path is now represented in
`Higham28Stewart.lean`: independent Gaussian tails with dimensions
`n,n-1,...,1`; embedded Householders `P₁,...,P_{n-1}`; the printed sign
diagonal `D`; the product `Q`; an exact value in Mathlib's orthogonal group;
and the normalized push-forward law of that concrete measurable producer.

| Source conclusion / dependency | Genuine Lean progress | Exact remaining foundation | Status |
|---|---|---|---|
| Independent standard-normal tail vectors | `stewartGaussianInputMeasure`; `stewartGaussianInputMeasure_univ`; probability-measure instance | none for normalization | VERIFIED |
| `P_i = diag(I_{i-1}, Pbar_i)` reduces `x_i` to `r_ii e₁`, and `Q = D P₁⋯P_{n-1}` is orthogonal | exact local reduction `stewartLocalHouseholder_reduces`; source-indexed embedded vectors and reflectors; inactive-prefix identity; sign diagonal; source-ordered list; `stewartOrthogonalMatrix_orthogonal` | none for local reduction or samplewise orthogonality | VERIFIED |
| Exact orthogonal-group random output | compositional measurability lemmas through sign, square root, finite sums/products, embedded reflectors, and the source-ordered list; `measurable_stewartOrthogonalGroupOutput`; exact push-forward `stewartOrthogonalGroupLaw`; unconditional `stewartOrthogonalGroupLaw_univ` | none for measurability or normalization | VERIFIED |
| Theorem 28.1: `Q` is Haar-distributed | exact group-level proposition `StewartTheorem28_1HaarConclusion` | Gaussian null-set handling plus a genuine rotational-invariance/Householder induction proving left invariance of this concrete push-forward; then identify it as normalized Haar | OPEN |
| Randsvd `A = U Σ Vᵀ` using independent factors | paired normalized input measure, `stewartRandsvdMatrix`, and exact right-Gram identity | apply the still-open Haar theorem separately to the two independent Stewart outputs | PARTIAL/OPEN |
| Prescribed singular values and schedule parameter `alpha = kappa_2(A)` | exact right-Gram identity for `U Σ Vᵀ` | prove singular-value-multiset invariance under both orthogonal factors and the extremal-value condition-number theorem with nonnegative, ordered, nonzero hypotheses | PARTIAL/OPEN |
| Single-Householder factors give diagonal plus rank-2 | generic Householder and randsvd definitions | specialize both factors, expand into outer-product corrections, and prove the compatible rectangular rank bound | OPEN |
| Symmetric adaptation `A = Q Lambda Qᵀ` | orthogonal and diagonal matrix infrastructure | define the construction and prove symmetry and prescribed-eigenvalue preservation; its distributional claim still inherits Theorem 28.1 | OPEN |
| Printed randsvd operation-count comparison | construction definitions only | source supplies no exact operation graph, flop-count convention, or selected leading-term proposition | DEFER-MISSING-PRECISE-STATEMENT |

The ambient constructor `stewartLaw_isNormalizedOrthogonalHaarLaw` is not the
missing proof: its premises are precisely mass, orthogonal support, and
left-invariance.  Likewise,
`diracIdentity_isNormalizedOrthogonalHaarLaw_zero` only treats the singleton
dimension-zero ambient matrix space and is not a producer for Stewart's
general-order Gaussian law.

## Toeplitz and companion subgroup

Source: Higham, 2nd ed., printed pp. 521-523 (PDF pages 11-13) of
`References/1.9780898718027.ch28.pdf`.

The earlier surface passed the hard conclusions through hypotheses named as
component identities, characteristic-polynomial coefficients, cyclicity, and
low-rank characteristic polynomials. Those transfers and their order-one
witnesses were removed. The replacement proves the finite constructions that
can currently be justified without assuming a source endpoint.

| Source conclusion / dependency | Genuine Lean progress | Exact remaining foundation | Status |
|---|---|---|---|
| Eigenvalues of `T_n(c,d,e)` | `tridiagonalToeplitz_mulVec_apply`; direct sine recurrence and boundary calculation; nonzero sine eigenvectors; normalized DST orthogonality and exact diagonalization of every symmetric `T_n(c,d,c)` | diagonal-similarity reduction for `c ≠ e`, including the complex/real square-root branch and degenerate cases needed by the printed `d + 2√(ce) cos(kπ/(n+1))` formula | PARTIAL/OPEN |
| Inverse of `T_n(-1,2,-1)` | exact integer Green recurrence and both inverse products | none | VERIFIED |
| `κ₂(T_n(-1,2,-1)) ~ 4n²/π²` | exact inverse, full symmetric sine diagonalization, and `secondDifferenceConditionClosedForm` for the expected extremal quotient | identify both `opNorm2` factors with the extremal sine eigenvalues, prove the closed-form equality, then derive the cosine asymptotic | OPEN |
| LU-diagonal and cyclic-reduction convergence | exact finite Toeplitz definitions and symmetric diagonalization | source lacks a unique fixed-diagonal indexing/topology/rate or precise cyclic-reduction endpoint | DEFER-MISSING-PRECISE-STATEMENT |
| Companion characteristic polynomial | `companionCharacteristicFormula` and its exact coefficient theorem | finite determinant recurrence/Laplace expansion proving `Matrix.charpoly C = companionCharacteristicFormula n a` | OPEN |
| Rank at least `n-1` / nonderogatory | transpose powers of the final basis vector are the reverse standard basis; independently, `companionRankMinor_det` exhibits a unit-determinant minor of every scalar shift and `companionMatrix_sub_scalar_rank_ge` proves the printed bound | none for the printed rank-form characterization | VERIFIED |
| Every matrix similar to a companion matrix is nonderogatory | companion rank-form theorem is verified | prove similarity invariance of the scalar-shift rank/minimal-polynomial characterization | OPEN |
| `compan(poly(A))` has the eigenvalues of `A` | exact target companion polynomial coefficients | prove companion characteristic-polynomial equality and identify it with `charpoly A`, including algebraic multiplicity | OPEN |
| `compan(poly(A))` is normal iff the printed coefficient condition holds | exact entrywise identity for `CᴴC`; audit counterexample `a_0=-1`, all higher coefficients zero | the printed complex `a_0=1` iff is false and `n=1` is exceptional; formulate/prove the repaired `n≥2`, `|a_0|=1`, higher-zero classification | SOURCE DISCREPANCY; REPAIRED THEOREM OPEN |
| Companion singular values | exact entrywise identity `CᴴC = companionGramFormula n a` and the printed exceptional quadratic target | in the source domain `2≤n`, compute the Gram characteristic polynomial/eigenspace multiplicity, show `n-2` unit eigenvalues, and connect the two exceptional roots to singular values | PARTIAL/OPEN |
