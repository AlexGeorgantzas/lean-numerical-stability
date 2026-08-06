# P05-T2 paper context

## Fixed source

The source is Rump and Jeannerod (2014), *Improved Backward Error Bounds for LU
and Cholesky Factorizations*. The local PDF SHA-256 is
`dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6`.

The selected result is the square-case sharpening in Theorem 4.2 and equation
(4.2), PDF pages 10--11, printed pages 693--694, section 4.2.

## Local context and statement

Equations (4.3a)--(4.3b) give Doolittle's local residual estimates. In the
square case their row coefficient is bounded by `(i-1)u`, using one-based
paper indices, and therefore by `(n-1)u`. The Lean target starts at those local
estimates, forms `Delta A = LU-A`, and proves both the sharp rowwise and uniform
bounds. Lean's `Fin n` rows are zero-based, so the displayed row coefficient
is `i.val*u`.
