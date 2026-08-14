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

`P05CholeskyRun n` is an abstract analytic certificate for a completed
conventional floating-point Cholesky execution. It records `n>0`, one common
finite radix round-to-nearest format, representability of `A` and `RHat`,
symmetry of `A`, upper-triangular support of `RHat`, and every computed entry.

Each off-diagonal entry is linked to a `P05Lemma41Run`, including its rounded
products, arbitrary permuted binary subtraction tree, pivot division, and
range checks. Each diagonal entry is linked to a `P05Lemma43Run`, which adds a
nonnegative computed radicand and a range-safe rounded square root. Their
generic scalar residual fields are the inherited consequences of Theorem 3.1
and Corollary 3.2 used by Lemmas 4.1 and 4.3; they mention no Cholesky matrix
entry or final matrix conclusion.

Lean indices are zero-based. Therefore (4.5a)'s `i*u` becomes
`(i.val+1)*u`, (4.5b)'s `(j+1)u` becomes `(j.val+2)*u`, and equation (4.4)'s
row coefficient `(i+1)u` becomes `(i.val+2)*u`.

The target derives both local estimates from the entry executions, identifies
their through-row sums with the full Gram product using upper-triangular
support, and performs the paper's symmetry extension. It then sets
`DeltaA=transpose(RHat)*RHat-A` and proves both bounds in (4.4).

The run type is inhabited: a private construction check executes the exact
`1 x 1` factorization `[1]=transpose([1])*[1]`, including a rounded square root.
