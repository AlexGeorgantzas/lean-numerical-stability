# P14-T1 paper context

## Fixed source

The source is Pierre Blanchard, Desmond J. Higham, and Nicholas J. Higham
(2021), *Accurately computing the log-sum-exp and softmax functions*. The
local PDF SHA-256 is
`7247047bc49218e001195edc8a2d66131eea7596d252503f34b0ace6328981cd`.

The selected result is the positive exponential-sum analysis for lines 1--5
of Algorithm 3.1. The algorithm and the no-overflow/no-underflow assumption
are on PDF page 6 / printed page 2316. Equation (3.1), the two unnumbered
recursive-summation bounds, and equation (3.2) are on PDF page 7 / printed
page 2317. Equation (3.3) is on PDF page 8 / printed page 2318.

## Paper contract

For a positive dimension `n` and real input vector `x`, the algorithm first
computes

```text
w_i    = exp(x_i),
wHat_i = w_i * (1 + delta_i),    |delta_i| <= u.
```

It then distinguishes three scalar quantities:

```text
s      = sum_i w_i,
sTilde = sum_i wHat_i                 (an exact real sum),
sHat   = recursive floating-point sum of the wHat_i.
```

The unnumbered bound controls `|sTilde - sHat|` by the recursive-addition
errors. Combining it with the componentwise exponential errors gives the
additive representation in equation (3.3),

```text
sHat = s + DeltaS,
|DeltaS| <= (n + 1) * u * s + O(u^2).
```

The coefficient `n + 1` is the paper's deliberately loose aggregate constant.
In particular, the singleton case still contains exponential-evaluation error
and is not definitionally exact.

## Printed discrepancy

The final line of equation (3.2) omits the factor `u` before its weighted sum.
The line immediately above includes that factor, and equation (3.3) restores
the first-order dependence on `u`. The target follows the internally
consistent derivation and equation (3.3), while recording this typographical
discrepancy rather than treating the literal malformed line as the theorem.

## Lean encoding

`P14BasicSumExecution x u` is a proof-carrying execution of Algorithm 3.1's
first five lines. Its `expError` field supplies equation (3.1), and its
`StandardAddModel` supplies each left-to-right rounded addition. The equation
`fp.u = u` ties both stages to the same unit roundoff.

`p14ExpSum x`, `p14ExactComputedExpSum run`, and
`p14RecursiveComputedExpSum run` are respectively `s`, `sTilde`, and `sHat`.
`p14BasicSumDelta run` is `DeltaS`.

For a family of executions with `u` tending to zero, the target concludes:

1. `s` is positive and every computed exponential has the paper's
   componentwise error bound;
2. the recursive stage satisfies its exact finite `gamma_(n-1)` bound;
3. the total error satisfies the finite envelope
   `(u + gamma_n(u)*(1+u))*s`;
4. that envelope is exactly `(n+1)*u*s` plus
   `p14BasicSumQuadraticRemainder`; and
5. this remainder is genuinely `O(u^2)`, while `sHat = s + DeltaS` holds
   exactly.

The finite envelope is disclosed benchmark-author mathematics that makes the
paper's unquantified remainder checkable without deleting it. It is a
strengthening of the displayed asymptotic upper bound, not a replacement of
the exponential stage by an addition-only lemma.

## Exceptional-value scope

Section 3 explicitly excludes overflow and underflow. The Lean execution is
real-valued and is in scope only when all exponential and addition outputs
satisfy the displayed relative-error equations. An execution involving
overflow, underflow, infinities, or NaNs cannot supply this certificate and is
not claimed to satisfy the theorem.
