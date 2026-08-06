# P15-T3 paper context

## Fixed source

The source is Nicholas J. Higham and Theo Mary (2022), *Solving block
low-rank linear systems by LU factorization is numerically stable*. The local
PDF SHA-256 is
`a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7`.

The selected result is Theorem 4.5 and its proof on PDF pages 24--25 (printed
pages 974--975), with the values of `xi_p` supplied by Table 1 on PDF page 19
(printed page 969).

## Local context and statement

The theorem composes the BLR LU factorization error with the backward errors
of forward and backward substitution. The formal target records the exact
matrix and right-hand-side perturbations from the proof. Its finite radii keep
the products of error coefficients that the paper absorbs into
`O(u*epsilon)` and `O(u^2)`; `factorRemainder` is an explicit nonnegative
upper bound for the factorization's suppressed remainder.
