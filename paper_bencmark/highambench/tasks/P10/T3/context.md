# P10-T3 paper context

## Fixed source

The source is James Demmel, Ioana Dumitriu, and Olga Holtz (2007), *Fast
linear algebra is stable*. The local PDF SHA-256 is
`0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`.

The selected result is the unnumbered block-matrix inverse displayed in the
proof of Theorem 3.3 on PDF page 12, printed page 70. It is the exact converse
reduction from matrix multiplication to matrix inversion:

```text
[I A 0; 0 I B; 0 0 I]^-1 = [I -A A*B; 0 I -B; 0 0 I].
```

The immediately following sentence states that exact inversion lets one
extract the product `A*B`. The task selects this exact finite part of the
proof, not Theorem 3.3's asymptotic bit-complexity or logarithmic-stability
claims.

## Mathematical setting

Let `A` and `B` be real square matrices of the same positive dimension `n`.
Form the three-by-three upper-triangular block matrices

```text
M = [I A 0; 0 I B; 0 0 I]
N = [I -A A*B; 0 I -B; 0 0 I].
```

Direct block multiplication gives both `M*N = I` and `N*M = I`. Thus `N` is
the two-sided inverse printed in the paper. Its block in row 0 and column 2 is
exactly `A*B`, which is the product-extraction step used by the converse
reduction.

This is exact real matrix algebra. It contains no floating-point rounding,
exceptional values, condition-number estimate, or asymptotic cost claim.

## Lean statement

`P10Matrix n` is the type of `n`-by-`n` real matrices.
`P10ThreeBlockMatrix n` is a three-by-three matrix of such blocks.
`p10MultiplicationReductionInput A B` and
`p10MultiplicationReductionInverse A B` are exactly `M` and `N` above, while
`p10ThreeBlockMul` is ordinary block-matrix multiplication.

`P10MultiplicationViaInverse A B` requires all three source facts:

1. the printed candidate is a right inverse;
2. it is also a left inverse;
3. its upper-right block is the desired product `A*B`.

The target proves this conjunction for arbitrary `A` and `B` at every
positive dimension. Neither inverse equation nor the product-extraction
identity is supplied as a hypothesis or certificate field.

## Tier and non-overlap

P10-T1 and P10-T2 both select first-order product-error content from equation
(8), on PDF page 8, printed page 66. P10-T3 instead selects an exact reduction
from the proof of Theorem 3.3 four printed pages later. It therefore does not
duplicate either earlier task.

The mounted frozen NumStability baseline contains matrix-algebra lemmas, but no
declaration of this three-by-three reduction or theorem proving both inverse
directions and product extraction. The complete reduction must be assembled
for this T3 target.
