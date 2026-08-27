# P04-T1 paper context

## Fixed source

The source is Pierre Blanchard, Nicholas J. Higham, Florent Lopez, Theo Mary,
and Srikara Pranesh, *Mixed Precision Block Fused Multiply-Add: Error Analysis
and Application to GPU Tensor Cores*, SIAM Journal on Scientific Computing
42(3), C124--C141, 2020. The local PDF SHA-256 is
`7ad9ebb7eef9864c58e9a3760ee308be48060647286f8e16cdc740ed4be5b862`.

The selected result is the chained rounding-factor estimate used in equation
(3.4), PDF page 6, printed page C129, section 3.2.

## Local context and statement

The paper writes each scalar product term with two accumulated factors,
`(1+α)(1+β)`. In the same-precision specialization discussed by the paper,
Higham's p04Gamma arithmetic collapses this product to one factor whose error is
bounded by `p04Gamma u (q+n)`. The Lean theorem states the equivalent bound on
`α + β + αβ` under the explicit p04Gamma-validity guard.
