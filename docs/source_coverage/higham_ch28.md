# Higham Chapter 28 Source Coverage Ledger

Source: Higham, 2nd ed., Chapter 28, printed pp. 511-526. Mode: core.

| Source group | Terminal status | Lean evidence / dependency |
|---|---|---|
| Hilbert definition and symmetry | VERIFIED | `hilbertMatrix`, `hilbertMatrix_transpose` |
| Hilbert SPD | VERIFIED | `hilbertMatrix_isSymPosDef_explicit` from the compiled `RᵀR` quadratic sum of squares |
| Hilbert total positivity | PASS (EXPLICIT-DOMAIN) | `hilbert_isStrictlyTotallyPositive_of_cauchyMinors` transfers the genuine ordered Cauchy-minor determinant identity |
| Equation (28.1) | VERIFIED | printed entry formula equals the inverse-factor Gram; `hilbert_inverse_formula` and left inverse |
| Exact part of (28.2) | VERIFIED | `hilbert_det_formula` for every order |
| Equations (28.3)-(28.4) | VERIFIED | `hilbertMatrix_eq_choleskyGram` and both factor-inverse products |
| Hilbert determinant/condition/shifted-norm asymptotics | PASS (EXPLICIT-DOMAIN) | exact propositions plus `hilbertDetAsymptotic_of_formula_estimate`, `hilbertConditionAsymptotic_of_relative_estimate`, and `shiftedHilbertNormAsymptotic_of_remainder_estimate` |
| Cauchy formulas | PASS (EXPLICIT-DOMAIN) | fraction-free determinant, partial-fraction inverse, explicit LU product-sum, barycentric-moment, and ordered-minor transfers; order-one inverse/LU producers compile |
| Equations (28.5)-(28.11) | DEFER-MISSING-PRECISE-STATEMENT | source `approx` leaves convergence/error semantics unspecified |
| Randsvd and schedules | VERIFIED definitions | `randsvdMatrix` and four schedule definitions |
| Theorem 28.1 | PASS (EXPLICIT-DOMAIN) | deterministic orthogonality plus `stewartLaw_isNormalizedOrthogonalHaarLaw` from mass/support/left-invariance; dimension-zero Dirac producer |
| Real-Ginibre expected-count limit | PASS (EXPLICIT-DOMAIN) | normalized standard product law and transfer from the exact finite coefficient formula plus its Gamma/Stirling estimate |
| Uniform positive random matrix | PASS (EXPLICIT-DOMAIN) | normalized product law, inhabited strict-positive event, and transfer from boundary-nullness plus deterministic Perron |
| Pascal algebraic core | VERIFIED | `P=LLᵀ`, determinant one, signed factor involution, and `P⁻¹=SᵀS` both sides |
| Pascal perturbation/cube root/condition asymptotic | PASS / PASS (EXPLICIT-DOMAIN) | similarity and reciprocal eigenpair are unconditional; coordinate-cancellation, two-product cube-root, and relative-asymptotic transfers have concrete producers |
| Tridiagonal Toeplitz inverse | VERIFIED | integer Green recurrence and both inverse products for `Tₙ(-1,2,-1)` |
| Toeplitz spectrum/condition asymptotic | PASS (EXPLICIT-DOMAIN) | componentwise sine identity + independence yield the printed eigenbasis; relative estimate yields condition asymptotic; order-one producer compiled |
| Companion eigenvector | VERIFIED | `companionMatrix_mulVec_companionEigenvector` |
| Companion characteristic/nonderogatory/SVD properties | PASS (EXPLICIT-DOMAIN) | determinant-coefficient, Krylov-cyclicity, and exact Gram/low-rank characteristic-polynomial transfers; order-one cyclic producer |
| Problems 28.1-28.2 | EXCLUDED | optional research rows not selected |

Aggregate selected-scope status: **PASS**. Every selected precise row is either
proved unconditionally or closed by a compiled explicit-domain transfer whose
hypotheses are genuine upstream facts. See
`docs/chapter28/CHAPTER28_NOT_PROVED_LEDGER.md`.

Verification targets are `Higham28`, `Higham28Exact`,
`Higham28Probability`, `Higham28Asymptotics`, and `Higham28Contracts`, plus the Algorithms umbrella.
Forbidden-token hygiene and representative axiom audits are required at handoff.
