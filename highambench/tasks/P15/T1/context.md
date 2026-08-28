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

The paper defines its unsubscripted norm explicitly as

```text
||A||_F = sqrt (sum_i sum_j |a_ij|^2)
```

and states, without additional hypotheses, that this norm is
submultiplicative:

```text
||AB||_F <= ||A||_F ||B||_F.
```

The occurrence of `AB` requires compatible dimensions. The surrounding
section uses rectangular factors, so the target quantifies
`A : R^(m x n)` and `B : R^(n x p)` rather than restricting both factors to
one square size. The matrix types themselves enforce compatibility.

`p15RectFrobNorm` is the unsquared, unnormalized square root of the full sum
of squared real entries. `p15RectMatMul` is exact finite matrix
multiplication. Thus all three norm occurrences, the inequality direction,
and the constant one are visible directly in the controlled declarations.

No floating-point execution, low-rank approximation, exceptional-value
condition, or higher-order term belongs to this general norm property. The
zero-sized `Fin` cases are a total formal extension; for positive dimensions
the binders include arbitrary nonzero compatible rectangular matrices.
