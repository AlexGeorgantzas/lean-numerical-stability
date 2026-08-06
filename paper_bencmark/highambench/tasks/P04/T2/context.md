# P04-T2 paper context

## Fixed source

The source is Blanchard, Higham, Lopez, Mary, and Pranesh (2020), *Mixed
Precision Block Fused Multiply-Add: Error Analysis and Application to GPU
Tensor Cores*. The local PDF SHA-256 is
`7ad9ebb7eef9864c58e9a3760ee308be48060647286f8e16cdc740ed4be5b862`.

The selected result is Theorem 3.2 and equation (3.6), PDF page 7, printed page
C130, section 3.2.

## Local context and statement

Both inputs are first rounded to the low precision, producing perturbations
bounded by `uLow`. The block-FMA multiplication then contributes the
coefficient from equation (3.5). Expanding the two perturbed inputs and
bounding the four error terms gives exactly
`2*uLow + uLow^2 + blockCoeff*(1+uLow)^2`.

The Lean target is the scalar entrywise core of this componentwise matrix
bound. It retains every coefficient and every sign-independent absolute-value
estimate used by the paper.
