# P16-T3 paper context

## Fixed source

The source is Buttari, Higham, Mary, and Vieuble (2026), *A modular framework
for the backward error analysis of GMRES*. The local PDF SHA-256 is
`8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`.

The selected result is Theorem 6.3, equations (6.17)--(6.21), on PDF pages
40--41 (printed pages 1978--1979). Its proof specializes Algorithm 2 and
Theorem 4.1 using the fully stored MGS-GMRES analysis in Theorem 5.2.

## Fixed-precision execution

`P16FixedMixedPrecisionGMRESRun n` represents one execution on a positive-
dimensional nonsingular real system `A*xExact=b`, with `b` nonzero and `Ainv`
constrained by both inverse actions. The same positive unit roundoffs `uHigh`
and `uLow` are used at every restart, with `uHigh <= uLow`. This is a single
fixed-precision run, not a family of runs whose precisions tend to zero.

The target concerns the paper's actual errors

```text
backwardError_i = ||b-A*xHat_i||_2 /
                    (||b||_2 + ||A||_F*||xHat_i||_2)
forwardError_i  = ||xHat_i-xExact||_2 / ||xExact||_2.
```

At each restart, `residualHat_i` and `xHat_(i+1)` obey the high-precision
componentwise residual and update models (6.19)--(6.20). The recorded error
vectors are therefore linked to the computed residual, correction, and
iterate rather than being arbitrary certificates.

## Low-precision MGS correction

`P16FixedLowPrecisionMGSRestart` exposes the low-precision computation used
at each restart. Its key dimension `k_i` is positive and at most `n`, and may
vary with `i`. It records:

- the cast of the high-precision residual to low precision;
- the fully stored MGS basis and the projection, update, and normalization
  operations used to build the Arnoldi relation;
- error bounds for those operations, all tied to the same `uLow`;
- the product model (3.1), the columnwise augmented least-squares model (3.3),
  and rounded correction formation (3.4);
- witness forms of the numerical-rank and key-dimension conditions
  (3.5)--(3.8); and
- the coefficients in equation (3.12), from which the restart's modular
  accuracy is bounded by `dimensionFactor*uLow`.

The paper leaves `c(n,k)` as an unspecified dimension-dependent constant.
`dimensionFactor` is a fixed nonnegative envelope for its value over this
run. No unsupported polynomial degree, evaluation at `(n,n)`, or asymptotic
precision family is imposed.

## Theorem 4.1 boundary

Theorem 6.3 explicitly invokes Theorem 4.1 after checking its MGS-GMRES
premises. `P16Theorem41RestartResult` is the formal boundary for that already
proved source theorem. It supplies restart-specific one-step factors,
high-precision coefficients, and second-order remainders for the same
computed quantities. It does **not** supply the common contraction factor,
either final floor, or a geometric convergence statement.

The run also records the first-order iterate comparisons inherited from
Theorem 4.1. Every second-order remainder has one coefficient that works for
all restart indices. This is the fixed-run meaning used here for the paper's
first-order notation; it avoids changing Theorem 6.3 into a theorem about a
limit of different executions.

The exact-real standard-model equations exclude underflow, overflow, NaNs,
and infinities. The task makes no claim about the scaled variants discussed
elsewhere in the paper.

## Fixed conclusion

Let

```text
Lambda = dimensionFactor * uLow * kappa_F(A),
kappa_F(A) = ||Ainv||_F * ||A||_F.
```

Under the explicit contraction condition `0 <= Lambda < 1`, the target first
derives, for every restart,

```text
backwardError_(i+1) <= Lambda*backwardError_i
                         + dimensionFactor*uHigh + |remainder_i|,
forwardError_(i+1)  <= Lambda*forwardError_i
                         + dimensionFactor*uHigh*kappa_F(A)
                         + |remainder_i|.
```

It then iterates each affine recurrence to obtain a geometric envelope with
the corresponding high-precision floor and a uniform quadratic remainder
budget. Thus the conclusion contains both the per-restart statement and the
convergence consequence asserted in equations (6.17)--(6.18); neither is
stored as a field of the execution.
