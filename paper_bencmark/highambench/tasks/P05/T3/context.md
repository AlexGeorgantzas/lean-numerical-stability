# P05-T3 paper context

## Fixed source

The source is Rump and Jeannerod (2014), *Improved Backward Error Bounds for LU
and Cholesky Factorizations*. The local PDF SHA-256 is
`dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6`.

The selected result is Theorem 4.4 and equation (4.4), PDF pages 11--12,
printed pages 694--695, section 4.3.

## Local context and statement

The local Cholesky computations yield bounds on the upper triangle. The paper
then uses symmetry of `A-R^T R` and of `|R^T||R|` to obtain the full
`diag((i+1)u)` componentwise estimate and the uniform `(n+1)u` estimate. The
Lean theorem formalizes exactly this closing step. With zero-based `Fin n`
indices, the paper's row factor `(i+1)u` becomes `(i.val+2)u`.
