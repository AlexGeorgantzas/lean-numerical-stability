# P04-T2 paper context

## Fixed source

The source is Blanchard, Higham, Lopez, Mary, and Pranesh (2020), *Mixed
Precision Block Fused Multiply-Add: Error Analysis and Application to GPU
Tensor Cores*. The local PDF SHA-256 is
`7ad9ebb7eef9864c58e9a3760ee308be48060647286f8e16cdc740ed4be5b862`.

The selected result is Theorem 3.2 and equation (3.6), PDF page 7, printed page
C130. Its computation and notation are defined by the block-FMA framework,
Algorithm 3.1, and equations (3.1)--(3.5), PDF pages 3--7, printed pages
C126--C130.

## Algorithm 3.1 execution

Let `A` be an `m` by `n` real matrix and `B` an `n` by `t` real matrix.
Algorithm 3.1 partitions them into `b1` by `b` and `b` by `b2` blocks, with
positive integer block counts satisfying

```text
m = p*b1,  n = q*b,  t = r*b2.
```

The theorem explicitly repeats `q = n/b` and inherits the row and column
partitions from Algorithm 3.1.

`P04MixedInputMatMulRun` models the algorithm rather than storing its error
bound. It contains the original `A` and `B`, line 1's relative rounding errors,
and one scalar block-FMA trace for every output entry.

The line-1 conversions are

```text
convertedA_(i,k) = A_(i,k)*(1+inputErrorA_(i,k)),
convertedB_(k,j) = B_(k,j)*(1+inputErrorB_(k,j)),
|inputErrorA_(i,k)| <= uLow,
|inputErrorB_(k,j)| <= uLow.
```

This is the paper's standard relative-error representation of
`fl_low(A)` and `fl_low(B)`. It implies the additive conversion bounds printed
immediately before Theorem 3.2, including at zero entries.

The block-FMA framework has low- and high-precision unit roundoffs `uLow` and
`uHigh`, with `uHigh <= uLow`. The FMA output roundoff `uFma` and requested
output roundoff `uOut` must each be one of those two formats. The internal
evaluation roundoff `uBar` satisfies `uBar <= uFma`. All are nonnegative, and
the gamma denominators used in (3.6) are positive.

For each output entry `(i,j)`, `entryRun i j` is a
`P04BlockFmaDotRun n b q`:

- its block operands are exactly the converted row `i` and column `j`, linked
  through the row-major equivalence `Fin q x Fin b ~= Fin n`;
- its precision parameters equal the matrix run's `uBar`, `uFma`, and `uOut`;
- it starts from zero and satisfies the local recurrence (3.2) for all `q`
  chained block FMAs; and
- `run.computed i j` is definitionally the trace's final state.

The run contains no compact `alpha` or `beta`, no final perturbation
factorization, and no instance of equation (3.6). Those are proof obligations.
The traces admit every evaluation order covered by the paper's general bound;
Theorem 3.2 itself retains `gamma_n(uBar)` rather than the optional
right-to-left sharpening.

All modeled quantities are finite reals satisfying the standard relative-error
relations. This is the paper's no-underflow/no-overflow scope. NaNs, infinities,
and the second output rounding deliberately omitted in section 3.2 are outside
the model.

## Fixed conclusion

The exact product is formed from the original inputs, not their converted
values. For every output entry, the theorem proves the componentwise forward
error bound

```text
|computed - A*B| <=
  (2*uLow + uLow^2
    + (gamma_q(effective) + gamma_n(uBar)
       + gamma_q(effective)*gamma_n(uBar))*(1+uLow)^2)
  * (|A|*|B|).
```

The effective roundoff is equation (3.3)'s prioritized value: use `uOut` first
when `uFma < uOut`; otherwise use zero when `uFma <= uBar`; otherwise use
`uFma`.

`|A|*|B|` is ordinary matrix multiplication after componentwise absolute
values. It is not a matrix norm or an entrywise matrix product. The quadratic
input-conversion term, mixed gamma product, full gamma denominators, and
`(1+uLow)^2` factor are all retained exactly; there is no first-order
truncation or big-O remainder.
