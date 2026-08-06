# P15-T1 paper context

## Fixed source

The source is Nicholas J. Higham and Theo Mary (2022), *Solving block
low-rank linear systems by LU factorization is numerically stable*. The local
PDF SHA-256 is
`a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7`.

The selected property is stated in Section 2.1 on PDF page 3 (printed page
953), where the authors fix the Frobenius norm and list submultiplicativity as
the first property used throughout the analysis.

## Local context and statement

The target states the exact finite square-matrix inequality
`||AB||_F <= ||A||_F ||B||_F`. It is the common norm step used to turn the
paper's exact perturbation expansions into scalar error budgets.
