# P04-T3 paper context

## Fixed source

The source is Blanchard, Higham, Lopez, Mary, and Pranesh (2020), *Mixed
Precision Block Fused Multiply-Add: Error Analysis and Application to GPU
Tensor Cores*. The local PDF SHA-256 is
`7ad9ebb7eef9864c58e9a3760ee308be48060647286f8e16cdc740ed4be5b862`.

The selected result is Theorem 4.4 and equation (4.7), PDF page 13, printed
page C136, section 4.1. Algorithm 4.1 and Theorem 4.3 on PDF pages 11--12,
printed pages C134--C135, supply the computed-factor and factorization-error
context used by Theorem 4.4.

## Algorithm and dimensions

`A` is a square `n` by `n` matrix given in working precision `uWork`. It is
partitioned into positive `b` by `b` blocks with positive integer block count
`q` and `n = q*b`. A successful execution of the right-looking block LU
Algorithm 4.1 produces a unit lower-triangular `LHat` and a nonsingular upper-
triangular `UHat`. Forward and backward substitution then produce `yHat` and
the computed solution `xHat`.

The Lean execution certificate records the exact finite-real equations used in
the paper's analysis:

`LHat*UHat = A + factorError`,

`(LHat+deltaL)*yHat = rhs`, and

`(UHat+deltaU)*xHat = yHat`.

It also records the componentwise factorization bound from Theorem 4.3 and the
standard triangular-substitution bounds invoked in Theorem 4.4. The final
matrix `deltaA` from equation (4.7) is not stored in the certificate; it must be
constructed by the proof.

## Precision model and coefficient

The four nonnegative precision parameters remain distinct:

- `uLow` is the precision used to convert off-diagonal factor blocks;
- `uBar` is the internal block-FMA arithmetic precision;
- `uFma` is the block-FMA output precision;
- `uWork` is the working precision used by Algorithm 4.1 and substitution.

The relevant gamma-domain assumptions are explicit. The effective block-FMA
roundoff follows the prioritized definition from equation (3.3). With

`cFact = 2*uLow + uLow^2 +
  max(blockFmaCoeff(effectiveFma,uBar,q-1,n-b+1), gamma(uWork,b))
    *(1+uLow)^2`,

Theorem 4.3 gives

`|factorError| <= cFact * (|A| + |LHat||UHat|)` componentwise.

## Fixed conclusion

The target constructs

`deltaA = factorError + LHat*deltaU + deltaL*UHat + deltaL*deltaU`

and proves both parts of Theorem 4.4:

`(A+deltaA)*xHat = rhs`,

and, componentwise,

`|deltaA| <= (cFact + 2*gamma(uWork,n) + gamma(uWork,n)^2)
  * (|A| + |LHat||UHat|)`.

Absolute values are entrywise and `|LHat||UHat|` is ordinary matrix
multiplication of the entrywise absolute matrices, not a matrix norm. No
first-order term is dropped. The certificate uses finite real values, matching
the paper's standard-model analysis; underflow, overflow, exceptional IEEE
values, and the paper's omitted double-rounding effect are outside its scope.
