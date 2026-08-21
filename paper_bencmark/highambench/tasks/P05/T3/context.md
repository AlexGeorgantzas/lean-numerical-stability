# P05-T3 paper context

## Fixed source

The source is Rump and Jeannerod (2014), *Improved Backward Error Bounds for LU
and Cholesky Factorizations*. The local PDF SHA-256 is
`dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6`.

The selected result is all of Theorem 4.4, including equation (4.4), the
conventional Cholesky update formulas, and local estimates (4.5a)--(4.5b), PDF
pages 11--12, printed pages 694--695, section 4.3.

## Paper statement

Let `A` be a symmetric `n x n` floating-point matrix. If the conventional
Cholesky factorization runs to completion without underflow or overflow, its
computed upper-triangular factor `RHat` satisfies

`transpose(RHat) * RHat = A + DeltaA`

and the componentwise bounds

`|DeltaA| <= diag((i+1)u)*|transpose(RHat)|*|RHat|`

and

`|DeltaA| <= (n+1)u*|transpose(RHat)|*|RHat|`.

The proof computes one column at a time. For one-based `i<j`, the off-diagonal
entry evaluates

`(A_ij - sum_(k<i) RHat_ki*RHat_kj) / RHat_ii`,

and the diagonal entry evaluates the rounded square root of

`A_jj - sum_(k<j) RHat_kj^2`.

Lemma 4.1 gives the off-diagonal local coefficient `i*u` in (4.5a), while
Lemma 4.3 gives the diagonal coefficient `(j+1)u` in (4.5b). Symmetry of both
`A-transpose(RHat)*RHat` and the absolute Gram product supplies the lower
triangle and the full theorem.

## Lean encoding

`P05CholeskyRun n` records a completed conventional floating-point Cholesky
execution. It contains `n>0`, one common finite symmetric radix
round-to-nearest format, representability and symmetry of `A`,
upper-triangular support of `RHat`, and every computed entry. Representability
of `RHat` is not a run premise; it is derived from those entry executions and
is the first conclusion of the target.

The format interface leaves tie-breaking abstract, as the paper does, but it
does not leave the floating set unrelated to its parameters: every
representable value has a bounded radix expansion using the recorded
precision and exponent range. A `safeRange` witness is the operation-level
certificate that the source's no-underflow/no-overflow laws apply. Every paper
format instantiates these laws; allowing additional finite formats satisfying
the same laws only strengthens the quantified theorem.

Each off-diagonal entry is linked to a `P05Lemma41Run`, including its rounded
products, arbitrary permuted binary subtraction tree, pivot division, and
range checks. Each diagonal entry is linked to a `P05Lemma43Run`, which adds a
nonnegative computed radicand and a range-safe rounded square root. Both scalar
runs expose a protected-leaf trace of the actual arbitrary-order subtraction
sum. The format supplies the source's standalone square-root rounding estimate
(3.7). The Lemma 4.1 and Lemma 4.3 residual estimates are then proved from
these ingredients; no local Cholesky or final matrix bound is stored.

Lean indices are zero-based. Therefore (4.5a)'s `i*u` becomes
`(i.val+1)*u`, (4.5b)'s `(j+1)u` becomes `(j.val+2)*u`, and equation (4.4)'s
row coefficient `(i+1)u` becomes `(i.val+2)*u`.

The target first proves that every `RHat` entry is representable: upper and
diagonal entries are rounded outputs, while lower entries are zero. It derives
both local estimates from the entry executions, identifies their through-row
sums with the full Gram product using upper-triangular support, and performs
the paper's symmetry extension. It then sets
`DeltaA=transpose(RHat)*RHat-A` and proves both bounds in (4.4).

The run type is inhabited: a private construction check executes the exact
`1 x 1` factorization `[1]=transpose([1])*[1]`, including a rounded square root.
