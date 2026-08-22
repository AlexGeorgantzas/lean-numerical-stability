# P15-T3 paper context

## Fixed source

The source is Nicholas J. Higham and Theo Mary (2022), *Solving block
low-rank linear systems by LU factorization is numerically stable*. The local
PDF SHA-256 is
`a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7`.

The selected result is Theorem 4.5, equations (4.23)--(4.25), and its proof on
PDF pages 24--25 (printed pages 974--975). Its inherited inputs are Algorithm 1
and Theorem 4.2 on PDF pages 13 and 19, Algorithm 2 and Theorem 4.3 on PDF page
21, and Theorem 4.4 on PDF pages 23--24.

## Quantification and matrix roles

`P15BLRLinearSolveExecution b p r` records one completed computation, matching
the pointwise quantification of Theorem 4.5. It fixes the dense matrix `A`, its
BLR representation `Atilde`, the right-hand side `v`, the computed `L`, `U`,
`yHat`, and `xHat`, the algorithm, threshold kind, recompression choice, and
the actual precision pair `(u, epsilon)`. Admissibility means

```text
0 < u < epsilon,     0 < epsilon,     3*c*u < 1,
c = b + 2*r*sqrt(r) + p.
```

The paper describes `u` as "safely smaller" than `epsilon` but supplies no
quantitative ratio. The formal execution records the explicit positive
separation `u < epsilon`, without inventing a stronger numerical margin.

The paper has a real notation gap: Theorem 4.5 introduces `Atilde` as the BLR
system matrix but equations (4.23)--(4.24) and the proof use `A`. Section 2.1
calls `Atilde` a BLR representation of dense `A`. The execution retains both
objects and makes that inherited relation explicit with `p15BLRRepresents`.
Diagonal blocks are unchanged. Each off-diagonal block of `Atilde` has its own
minimum threshold-satisfying rank, the equation-(2.3)
lower/upper factor orientation, and an orthonormal `X` factor. Its truncation
error is bounded by `epsilon` times the local or global Section 2.1 scale. The
final backward equation and norm scale use dense `A`, exactly as the displayed
equations do.

The source's `r` is the maximum off-diagonal rank of the computed factors, not
the input BLR rank and not an arbitrary upper estimate. `p15IsFactorBLRRank`
therefore says that `r` is the least common rank bound for `L` and `U`.
`Atilde` has independent per-block ranks.

## Computed execution

`P15CompletedBLRFactorization` is tied to the selected algorithm. At
factorization step `k`, both target blocks `(i,k)` and `(k,i)` sum exactly over
the already computed factors `j < k`, as Algorithms 1 and 2 require. The trace
uses the cancellation-safe equation-(4.3) form: the input block and each
computed product have distinct componentwise perturbations, and each product
has its own normwise error. Diagonal LU factorizations use Lemma 2.3.
Off-diagonal matrix triangular solves use the equation-(2.9) residual form
`X*T = rhs + Delta` or `T*X = rhs + Delta`, with
`||Delta|| <= gamma_b*||T||*||X||`; they do not assume a single coefficient
perturbation. Every stored low-rank block has an explicit minimum-rank
truncated-SVD Assumption-2.1 compression witness. For UFC,
off-diagonal factor blocks are solved before compression; for UCF, updated
off-diagonal blocks are compressed before the factor solves. UFC compression
uses the diagonal-norm-scaled local/global thresholds of equations
(4.13)--(4.14); UCF compression uses the unscaled choices. The recompression
variant controls whether the earlier-product errors in each block update are
zero or satisfy the corresponding threshold bound. Thus the algorithm,
threshold, and recompression fields all constrain actual block equations and
cannot act as labels only.

`P15CompletedTriangularSolve` records the separate low-rank product errors,
right-hand-side and product summation errors, and diagonal-solve errors in
equation (4.22). It does not apply one relative perturbation to the complete
residual, which would be invalid under cancellation. Every diagonal block is
nonsingular. Lower solves use earlier block components and upper solves use
later components. Their aggregate Theorem 4.4 perturbations use
`c_tri = b + r*sqrt(r) + p`; the larger `c = b + 2*r*sqrt(r) + p` is retained
only where Theorems 4.2--4.5 use it. The execution requires the lower solve with
`L` and `v` first, then the upper solve with `U` and the computed `yHat`.

The perturbations supplied by Theorems 4.2--4.4 are retained as the
source-level interface at which the proof of Theorem 4.5 begins. They are tied
to the same traced `L`, `U`, `yHat`, and `xHat`. The execution contains no
final system perturbation and no equation-(4.23) certificate. The target
constructs those aggregate objects from the exact products printed on page
975.

## Higher-order terms

`factorRemainder` is a function of both precision parameters satisfying
`p15IsBigOMixedAtZero`: there are constants `C` and `delta` such that its
absolute value is at most `C*u*epsilon` throughout the positive neighborhood
with `u < epsilon`. The pointwise factor bound evaluates that function only at
the execution's actual `(u, epsilon)`, so the theorem does not require a
completed computation at any other precision.

The target existentially constructs a right-hand-side remainder function and
proves `p15IsBigOSquareRelativeAtZero`. It is `O(u^2)` relative to the displayed
solve scale `||L||*||U||*||xHat||`, and the final bound evaluates it only at the
execution's precision. The private proof may establish an explicit supporting
coefficient, but no such coefficient or extra inequality appears in the
controlled target; equation (4.25) retains its asymptotic form.

## Derived result

For one completed execution, the theorem existentially constructs matrix and
right-hand-side perturbations and proves

```text
(A + DeltaA) * xHat = v + Deltav,

||DeltaA|| <= (xi_p*epsilon + gamma_p)*||A||
              + gamma_(3c)*||L||*||U|| + O(u*epsilon),

||Deltav|| <= gamma_p*(||v|| + ||L||*||U||*||xHat||) + O(u^2).
```

The constructed perturbations are exactly

```text
DeltaA = factorError + lowerError*U + L*upperError
           + lowerError*upperError,
Deltav = lowerRhsError + L*upperRhsError
           + lowerError*upperRhsError.
```

All matrix norms are the unsquared, unnormalized Frobenius norm and all vector
norms are Euclidean. The model is real-valued and follows the paper's standard
relative-error convention; exceptional IEEE values are outside its scope. A
private construction instantiates a complete exact one-block UFC execution,
so the hypotheses are satisfiable.
