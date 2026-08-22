# P06-T1 paper context

## Fixed source

The source is Michael P. Connolly and Nicholas J. Higham (2023),
*Probabilistic Rounding Error Analysis of Householder QR Factorization*. The
local PDF SHA-256 is
`c02a20e9ffa8039a5ad3db9261fba19929de84bf0bff7654547541dffe496a79`.

The selected result is the sentence “The columnwise bound (4.17) implies a
normwise one” and equation (4.20), on physical PDF page 10, printed page 1155.
Equation (4.17), on physical page 9, printed page 1154, supplies the premise.
This task does not select the complete Theorem 4.4.

## Selected implication

For a real matrix `A` in `R^(m x n)`, let `DeltaA(u)` be the backward
perturbation at unit roundoff `u`. Equation (4.17) supplies, simultaneously for
every column `j`,

```text
||Deltaa_j(u)||_2 <=
  c6 * lambda * sqrt(n) * gammaTilde_m(lambda,u) * ||a_j||_2 + O(u^2).
```

The selected sentence concludes

```text
||DeltaA(u)||_F <=
  c6 * lambda * sqrt(n) * gammaTilde_m(lambda,u) * ||A||_F + O(u^2).  (4.20)
```

The target keeps the source coefficient exactly through
`p06QRLeadingCoefficient`. Here `c6` is a positive natural constant,
`lambda > 0`, and

```text
gammaTilde_m(lambda,u) =
  exp((lambda*sqrt(m)*u + m*u^2)/(1-u)) - 1.
```

## Higher-order terms

Each column has a scalar remainder function that is genuinely `O(u^2)` as
`u` tends to zero. The simultaneous inequalities and the resulting Frobenius
inequality are eventual statements on the physical domain `0 < u < 1`.
This avoids treating an arbitrary discrepancy at one fixed positive `u` as a
second-order term.

The constructed normwise remainder is the finite sum of the absolute column
remainders. A finite sum of `O(u^2)` functions is again `O(u^2)`. The source
does not state uniformity in the dimensions, `lambda`, or the input matrix, so
none is added.

## Scope

Theorem 4.4 has already established the computed Householder factor, the
orthogonal backward relation, the common probability event, and the
simultaneous bounds (4.17) before the selected sentence. They are not repeated
in this reselected implication. The formal premise is exactly the mathematical
content from (4.17) needed to derive (4.20), rather than an assumed conclusion
of the result now being selected.

The proof identifies the Frobenius norm with the Euclidean norm of the vector
of column Euclidean norms. Pointwise monotonicity and the Euclidean triangle
inequality retain the same leading coefficient; the Euclidean norm of the
column remainder budgets is bounded by their finite `l1` sum.

No floating-point operation is executed by this implication. NaNs, infinities,
overflow, and underflow therefore introduce no additional cases. A one-by-one
zero matrix, zero perturbation family, and zero remainder family establish
that the assumptions are jointly satisfiable.
