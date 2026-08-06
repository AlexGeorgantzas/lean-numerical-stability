# P04-T3 paper context

## Fixed source

The source is Blanchard, Higham, Lopez, Mary, and Pranesh (2020), *Mixed
Precision Block Fused Multiply-Add: Error Analysis and Application to GPU
Tensor Cores*. The local PDF SHA-256 is
`7ad9ebb7eef9864c58e9a3760ee308be48060647286f8e16cdc740ed4be5b862`.

The selected result is Theorem 4.4 and equation (4.7), PDF page 13, printed
page C136, section 4.1.

## Local context and statement

The factorization stage supplies `L*U = A + ΔF`. Forward and backward
substitution supply perturbations `ΔL` and `ΔU`. Their exact composition is

`ΔA = ΔF + L*ΔU + ΔL*U + ΔL*ΔU`,

and its componentwise majorant has coefficient
`cFact + 2*gamma_n + gamma_n^2`, precisely the extra solve contribution in
equation (4.7). The Lean target proves both the assembled equation
`(A+ΔA)x = b` and this bound.
