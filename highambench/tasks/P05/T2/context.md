# P05-T2 paper context

## Fixed source

The source is Rump and Jeannerod (2014), *Improved Backward Error Bounds for LU
and Cholesky Factorizations*. The local PDF SHA-256 is
`dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6`.

The selected result is all of Theorem 4.2, including equation (4.2) and the
local estimates (4.3a)--(4.3b), PDF pages 10--11, printed pages 693--694,
section 4.2.

## Paper statement

Let `A` be an `m x n` floating-point matrix with `m >= n`. If Gaussian
elimination runs to completion without underflow or overflow, its computed
factors `LHat` and `UHat` satisfy the exact backward relation

`LHat * UHat = A + DeltaA`

and the componentwise bound

`|DeltaA| <= n*u*|LHat|*|UHat|`.

When `m = n`, row `i` has the sharper one-based coefficient `(i-1)u`, and the
whole matrix is bounded by `(n-1)u*|LHat|*|UHat|`.

The proof analyzes Doolittle's mathematically equivalent formulation. At
one-based stage `k`, each upper-row entry has local coefficient `(k-1)u`, while
each below-diagonal entry has coefficient `k*u`; the diagonal of `LHat` is one.
These are equations (4.3a) and (4.3b), and they hold for any permitted order of
evaluating the subtraction sum.

## Lean encoding

`P05DoolittleRun m n` records one completed floating-point Doolittle execution.
It contains `m >= n`, `n > 0`, one common finite symmetric radix format,
representability of the input and computed factors, the unit-lower-trapezoidal
and upper-triangular structure, and every computed upper and lower entry. Each
entry is linked to a `P05Lemma41Run`, which records the rounded products,
arbitrary permuted binary summation tree, optional pivot division, and range
checks excluding underflow and overflow. Its protected-leaf trace exposes the
actual rounded merges and only the earlier equation (2.4) bounds for sibling
subtrees. It stores neither a Lemma 4.1 residual estimate nor any local or global
conclusion of Theorem 4.2.

Lean uses zero-based `Fin` indices. Thus paper stage `k` becomes Lean stage
`k.val`, making the local coefficients `k.val*u` and `(k.val+1)*u`. In the
square case the paper's row coefficient `(i-1)u` becomes `i.val*u`.

The proof first derives the scalar residual estimates of Lemma 4.1 from each
protected summation trace and the format's round-to-nearest error laws. It then
specializes those estimates to obtain both local Doolittle bounds. The
triangular zero conditions identify each local through-pivot sum with the full
rectangular matrix product. Finally it sets `DeltaA = LHat*UHat-A`, proves the
general `n*u` bound, and derives the two square refinements.

The run type is inhabited: a private construction check instantiates the
`1 x 1` factorization `[1] = [1]*[1]` in an exact two-value finite format.
