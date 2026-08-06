# P15-T2 paper context

## Fixed source

The source is Nicholas J. Higham and Theo Mary (2022), *Solving block
low-rank linear systems by LU factorization is numerically stable*. The local
PDF SHA-256 is
`a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7`.

The selected result is Lemma 3.1, especially equation (3.2), on PDF page 6
(printed page 956).

## Local context and statement

The low-rank approximation has truncation error at most `epsilon * beta`, and
the computed factorized matrix-vector product has backward error at most
`gammaC * ||Atilde||_F`. The target constructs their total perturbation and
proves the exact finite bound
`gammaC * ||A||_F + epsilon * (1 + gammaC) * beta`.
