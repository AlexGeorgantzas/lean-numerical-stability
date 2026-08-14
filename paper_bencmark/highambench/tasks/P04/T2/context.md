# P04-T2 paper context

## Fixed source

The source is Blanchard, Higham, Lopez, Mary, and Pranesh (2020), *Mixed
Precision Block Fused Multiply-Add: Error Analysis and Application to GPU
Tensor Cores*. The local PDF SHA-256 is
`7ad9ebb7eef9864c58e9a3760ee308be48060647286f8e16cdc740ed4be5b862`.

The selected result is Theorem 3.2 and equation (3.6), PDF page 7, printed page
C130. Its computation and notation are defined by Algorithm 3.1 and equations
(3.1)--(3.5), PDF pages 5--7, printed pages C128--C130.

## Paper result

Let `A` be an `m` by `n` real matrix and `B` an `n` by `t` real matrix. In
Algorithm 3.1 they are partitioned into `b1` by `b` and `b` by `b2` blocks,
with integer block counts

`m = p*b1`, `n = q*b`, and `t = r*b2`.

The inputs need not already be stored in the low precision. Line 1 converts
them componentwise, giving

`convertedA = A + deltaA`, `|deltaA| <= uLow*|A|`,

and the analogous relations for `B`. For every output entry, the chained
block-FMA analysis supplies indexed factors `alpha` and `beta` such that the
computed entry is

`sum_k convertedA[i,k]*convertedB[k,j]*(1+alpha[i,j,k])*(1+beta[i,j,k])`.

The `alpha` radius is `gamma q` at the effective output-rounding parameter from
equation (3.3). That parameter uses the first applicable branch: output
precision if it is coarser than the FMA output precision, zero when the
internal precision is at least the FMA output precision, and otherwise the FMA
output precision. The `beta` radius is `gamma n` at the internal precision.
The paper assumes the relevant gamma denominators are positive.

The theorem concludes, componentwise,

`|computed - A*B| <=`

`(2*uLow + uLow^2 + (gammaEff + gammaInternal +`
` gammaEff*gammaInternal)*(1+uLow)^2) * (|A|*|B|)`.

Here `|A|*|B|` is ordinary matrix multiplication after taking entrywise
absolute values; it is not a matrix norm. Every displayed quadratic and mixed
term is retained.

## Lean model

`P04MixedInputMatMulRun` records the compatible dimensions, both conversions,
the shared precision parameters, and the indexed Algorithm 3.1 factorization
for every matrix entry. It does not assume equation (3.6). The target derives
that bound for all output indices.

As in the paper's analysis, all modeled values are finite reals. Underflow,
overflow, exceptional IEEE values, and the second output rounding explicitly
omitted by the paper are outside the statement's scope.
