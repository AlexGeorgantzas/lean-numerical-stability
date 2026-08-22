# P15-T3 paper context

## Fixed source

The source is Nicholas J. Higham and Theo Mary (2022), *Solving block
low-rank linear systems by LU factorization is numerically stable*. The local
PDF SHA-256 is
`a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7`.

The selected result remains Theorem 4.5, equations (4.23)--(4.25), and its
proof on PDF pages 24--25 (printed pages 974--975). The proof invokes Theorems
4.2 and 4.3 for the factorization and Theorem 4.4 for each triangular solve.

## Quantification and matrix roles

`P15BLRLinearSolveExecution b p r` records one completed computation. It fixes
the dense matrix `A`, its Section 2.1 BLR representation `Atilde`, the computed
factors `L` and `U`, the right-hand side `v`, the intermediate solution `yHat`,
the final solution `xHat`, and one actual precision pair `(u, epsilon)`.

The dimensions are finite real dimensions with matrix order `p*b`. The block
size and block count are positive, `r <= b`, and `r` is the least common
off-diagonal rank bound of the computed factors. `p15BLRRepresents` keeps the
dense and represented matrices distinct and records the paper's oriented,
minimum-rank truncation semantics. The exact backward equation and norm scale
use `A`, following the displayed equations and proof of Theorem 4.5. The
paper's switch between `Atilde` and `A` remains a source notation ambiguity;
the formalization does not silently identify them.

Admissibility is

```text
0 < u < epsilon,     0 < epsilon,     3*c*u < 1,
c = b + 2*r*sqrt(r) + p.
```

The paper says that `u` is safely smaller than `epsilon` but gives no numerical
ratio. The explicit inequality `u < epsilon` is the weakest positive ordering
used here. The real standard model excludes overflow, underflow, NaNs, and
infinities.

## Factorization theorem

`P15CompletedBLRFactorization` contains a raw UFC or UCF trace on `Atilde` and
the four distinct error contributions accumulated in the proofs of Theorems
4.1--4.3:

```text
compression error + rounded-input error
  + factor-arithmetic error + mixed error.
```

The raw trace retains the `j < k` updates, cancellation-safe equation-(4.3)
operand perturbations, Lemma-2.3 diagonal factorizations, equation-(2.9)
matrix-solve residuals, Assumption-2.1 compressions, algorithm-specific
factor/compress ordering, threshold scaling, and optional recompression.

The four analysis terms remain separate. Their bounds respectively use
`xi_p*epsilon*||A||`, `gamma_p*||A||`,
`gamma_c*||L||*||U||`, and an `O(u*epsilon)` remainder. The imported theorem
`p15CompletedBLRFactorization_backwardError` applies Frobenius triangle
inequalities to derive the single Theorem-4.2/4.3 perturbation. That aggregate
perturbation, equation, and bound are not fields of the final execution.

## Triangular-solve theorem

Each `P15CompletedTriangularSolve` contains an operation-level block trace of
equation (4.22). Product errors, right-hand-side summation errors, product
summation errors, and diagonal-solve errors remain distinct, and every diagonal
block is nonsingular. Lower solves use prior blocks; upper solves use later
blocks.

The gathered source analysis retains three matrix contributions with
coefficients `gamma_d`, `gamma_p`, and `gamma_d*gamma_p`, where
`d = b + r*sqrt(r)`. The imported theorem
`p15CompletedTriangularSolve_backwardError` proves their sum is bounded by
`gamma_(d+p)*||T||` and derives the equation-(4.21) perturbation and
right-hand-side bound. Thus the two Theorem-4.4 interfaces used by P15-T3 are
conclusions obtained from the two completed solves, not caller-supplied
certificates.

## Higher-order terms

`p15IsBigOMixedAtRun remainder u epsilon` gives separate positive radii for
`u` and `epsilon`, a uniform `C*u*epsilon` bound in that neighborhood, and
requires the actual execution pair to lie inside it. Consequently the value
used in equation (4.24) is controlled by the same big-O witness; an isolated
spike at the current precision is impossible.

The target constructs the right-hand-side remainder and proves
`p15IsBigOSquareRelativeAtRun` relative to
`||L||*||U||*||xHat||`. Its certified neighborhood also contains the actual
execution pair. The proof derives the explicit supporting coefficient
`16*c^2`, but the controlled target retains the paper's `O(u^2)` form.

## Derived result

The target first derives witnesses for Theorems 4.2--4.4 from the completed
traces. It then constructs exactly the perturbations printed on page 975:

```text
DeltaA = factorError + lowerError*U + L*upperError
           + lowerError*upperError,
Deltav = lowerRhsError + L*upperRhsError
           + lowerError*upperRhsError.
```

It proves

```text
(A + DeltaA) * xHat = v + Deltav,

||DeltaA|| <= (xi_p*epsilon + gamma_p)*||A||
              + gamma_(3c)*||L||*||U|| + O(u*epsilon),

||Deltav|| <= gamma_p*(||v|| + ||L||*||U||*||xHat||)
              + O(u^2).
```

Matrix norms are unsquared, unnormalized Frobenius norms and vector norms are
Euclidean. A private one-block exact UFC construction witnesses satisfiability
of the complete execution and predecessor-analysis interfaces.
