# P16-T1 paper context

## Fixed source

The source is Alfredo Buttari, Nicholas J. Higham, Theo Mary, and Bastien
Vieublé (2026), *A modular framework for the backward error analysis of
GMRES*. The local PDF SHA-256 is
`8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`.

Section 2 on PDF page 4 (printed page 1942) defines the normwise backward
error by perturbations `deltaA`, `deltaB` and gives its normalized-residual
formula.

## Local context and statement

The target records the exact estimate connecting those two views. If
`(A + deltaA)x = b + deltaB`, then `b - Ax = deltaA*x - deltaB`; Euclidean
triangle inequality and the Frobenius matrix-action bound give
`||b-Ax||_2 <= ||deltaA||_F ||x||_2 + ||deltaB||_2`.
