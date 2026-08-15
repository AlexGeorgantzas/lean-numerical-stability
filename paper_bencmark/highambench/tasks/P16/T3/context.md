# P16-T3 paper context

## Fixed source

The source is Buttari, Higham, Mary, and Vieuble (2026), *A modular framework
for the backward error analysis of GMRES*. The local PDF SHA-256 is
`8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`.

The selected result is Theorem 6.3, equations (6.17)--(6.21), on PDF pages
40--41 (printed pages 1978--1979). Its proof specializes Algorithm 2 and
Theorem 4.1 using the MGS-GMRES analysis of Section 5.3.

## Algorithm and quantities

`P16MixedPrecisionGMRESRun l` records a positive-dimensional nonsingular real
system `A*xExact=b`, a nonzero right-hand side, the actual inverse `Ainv`, and
the complete restart-indexed computed quantities. The exact errors in the
target are

```text
backwardError_i = ||b-A*xHat_i||_2 /
                    (||b||_2 + ||A||_F*||xHat_i||_2)
forwardError_i  = ||xHat_i-xExact||_2 / ||xExact||_2.
```

Thus neither error is an arbitrary scalar sequence.

At every restart `i`, the run records equations (6.19)--(6.20): the residual
and update are computed in high precision with unit roundoff `uHigh`. The
componentwise residual and update errors remain distinct from the true
residual and exact iterate.

`P16LowPrecisionMGSRestart` records lines 4--7 of Algorithm 2 in low precision:

- the high-precision residual cast and its error;
- a fully stored MGS-Arnoldi basis with restart-dependent key dimension `k_i`;
- the Arnoldi relation and product error;
- the backward-stable least-squares problem and correction formation;
- witness forms of the numerical-rank and key-dimension conditions (3.5)--(3.8);
- the correction-level backward and forward bounds delivered by the Section
  5.3 analysis, before composition with the high-precision operations.

The target proves the final composition; it does not assume a recurrence for
the global backward or forward errors.

## Constants and first-order semantics

`P16PolynomialFactor` makes one occurrence of the paper's unspecified
low-degree `c(n,k)` explicit. Its nonnegative bivariate polynomial at `(n,n)`
uniformly dominates each restart value at `(n,k_i)`. Consequently

```text
Lambda = c(n,n) * uLow * kappa_F(A),
kappa_F(A) = ||Ainv||_F * ||A||_F.
```

`Ainv` is constrained by two-sided inverse actions. `p16MuchLessThanOneAt`
interprets `Lambda << 1` by requiring that `Lambda` tend to zero and eventually
be a nonnegative strict contraction. `p16FirstOrderLeAt` interprets the
paper's `lesssim` by retaining an explicit `O((uHigh+uLow)^2)` remainder.

Theorem 4.1 assumes, in first-order notation,
`||xHat_i|| lesssim ||xHat_(i+1)|| lesssim ||xExact||`. Theorem 6.3 invokes
Theorem 4.1 without discussing this premise. The run records it explicitly so
the inherited source dependency is inspectable rather than silently omitted.

The exact-real standard-model equations exclude underflow, overflow, NaNs,
and infinities. No claim is made about the scaled variants discussed elsewhere
in the paper.

## Fixed conclusion

For every restart, the target derives

```text
backwardError_(i+1) lesssim Lambda*backwardError_i + c(n,n)*uHigh
forwardError_(i+1)  lesssim Lambda*forwardError_i
                              + c(n,n)*uHigh*kappa_F(A).
```

Under `Lambda << 1`, these are the first-order contraction and attainable
floors stated in equations (6.17)--(6.18). The proof combines the low-precision
correction certificates with the exact high-precision residual and update
decompositions; it does not replace the numerical algorithm by an assumed
scalar recurrence.
