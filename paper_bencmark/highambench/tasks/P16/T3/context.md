# P16-T3 paper context

## Fixed source

The source is Buttari, Higham, Mary, and Vieuble (2026), *A modular framework
for the backward error analysis of GMRES*. The local PDF SHA-256 is
`8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`.

The selected result is Theorem 6.3, equations (6.17)--(6.21), on PDF pages
40--41 (printed pages 1978--1979). Its proof specializes Algorithm 2 and
Theorem 4.1 using the fully stored MGS-GMRES analysis in Theorem 5.2.

## Fixed-precision execution

`P16FixedMixedPrecisionGMRESRun n` represents one execution on a
positive-dimensional nonsingular real system `A*xExact=b`, with `b` nonzero
and `Ainv` constrained by both inverse actions. The same positive unit
roundoffs `uHigh` and `uLow` are used at every restart. The source does not
state `uHigh <= uLow` as a separate hypothesis, so the structure does not add
that restriction.

The target concerns the paper's actual errors

```text
backwardError_i = ||b-A*xHat_i||_2 /
                    (||b||_2 + ||A||_F*||xHat_i||_2)
forwardError_i  = ||xHat_i-xExact||_2 / ||xExact||_2.
```

At each restart, `residualHat_i` and `xHat_(i+1)` obey the high-precision
componentwise residual and update models (6.19)--(6.20). The normalized
high-precision contributions are bounded at the two scales printed in (6.18).

## Low-precision MGS correction

`P16FixedLowPrecisionMGSRestart` exposes the low-precision correction at
restart `i`. Its key dimension `k_i` is positive, is at most `n`, and may
vary with `i`. It records:

- the cast of the high-precision residual to low precision;
- the equation identifying that cast residual with its norm times the first
  Arnoldi basis vector;
- the fully stored MGS basis and its projection, update, and normalization
  operations;
- low-precision error bounds tied to the same `uLow`;
- the product model (3.1), columnwise augmented least-squares model (3.3), and
  rounded correction formation (3.4);
- witness forms of conditions (3.5)--(3.8); and
- the coefficients in (3.12) and the correction-level backward and forward
  estimates inherited from the earlier MGS-GMRES analysis.

Those correction-level estimates stop before the high-precision residual and
update are composed. In particular, the run no longer stores a Theorem 4.1
record containing either global one-step recurrence.

## Dimension factors

`dimensionFactor` is a nonnegative bivariate polynomial and is evaluated at
the dimensions `(n,k_i)` of each restart. It therefore cannot depend on the
matrix, basis conditioning, errors, or other run data. This is the explicit
formal counterpart of the paper's generic low-degree `c(n,k)`. Because the
paper supplies no numerical degree cutoff and uses a potentially different
`k_i` at each restart, the target neither invents such a cutoff nor replaces
all `k_i` by `n`.

For restart `i` the displayed quantities are

```text
Lambda_i = c(n,k_i) * uLow * kappa_F(A),
backwardFloor_i = c(n,k_i) * uHigh,
forwardFloor_i  = c(n,k_i) * uHigh * kappa_F(A),
kappa_F(A) = ||Ainv||_F * ||A||_F.
```

The source's qualitative `Lambda << 1` is represented by requiring every
`Lambda_i` to be a nonnegative strict contraction.

## Fixed conclusion

For every restart the target derives

```text
backwardError_(i+1) <= Lambda_i*backwardError_i + backwardFloor_i,
forwardError_(i+1)  <= Lambda_i*forwardError_i  + forwardFloor_i.
```

These exact inequalities are a deliberate strengthening of the paper's
first-order `lesssim` notation. They preserve the two printed attainable
scales without introducing fixed-precision remainder certificates or a
`1/(1-Lambda)` stationary denominator that is absent from equation (6.18).
The proof composes the earlier low-precision MGS correction estimate with the
high-precision residual and update decompositions.

The exact-real standard-model equations exclude underflow, overflow, NaNs, and
infinities. The task makes no claim about the scaled variants discussed
elsewhere in the paper.
