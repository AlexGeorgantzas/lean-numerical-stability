# P20-T3 context

Selected result: Theorem 4.1 and equations (4.29)--(4.33), on physical PDF
pages 11--12 (journal pages B795--B796). The supporting derivation is
equations (4.18)--(4.28) on physical pages 10--11 (B794--B795).

The theorem concerns real matrices `A : R^(m x n)` and `B : R^(n x q)`, with
positive dimensions and a positive number `p` of low-precision words. The
exact reference product is `A * B`. Equation (4.32) bounds the induced
row-sum infinity norm of the actual computed result minus this product.

`P20StaticNearestModel1` is the fixed-computation form of Model 1 from
physical pages 2--3 (B786--B787). Its input and accumulation binary formats
determine `u`, `U`, `fmax`, `Fmax`, `gmin`, and `Gmin`; the accumulation
precision and exponent range contain those of the input format. Each rounding
map returns a nearest representable value on its explicit no-overflow domain
and satisfies (2.3) or (2.4), including the mutually exclusive relative and
underflow errors. This task selects the paper's default round-to-nearest case.
The directed-rounding variant requires the paper's separate doubling rule and
is not claimed by the target.

The scaling threshold is exactly

`theta = min(fmax, sqrt(Fmax / n))`.

The row and column factors satisfy the maximal power-of-two intervals
(3.4a)--(3.4b), not just the printed upper bound. A zero row or column uses
factor `1`, the harmless convention left implicit by the paper. Every scaled
entry is bounded by `theta`.

`P20StaticMultiwordRun` records one execution of (4.29)--(4.31). The `p` words
satisfy the complete input-rounded residual recurrences. The triangular sum
retains exactly the pairs `i+j<p` and weights them by `u^(i+j)`. Every retained
inner product rounds each multiplication and then each addition in the
accumulation format. The retained word products are also added in that format,
and the run supplies no-overflow evidence for all these operations. The
power-of-two weights and inverse scaling are exact, as in the source's
high-precision external-storage setup. Thus `run.computed` is linked to the
paper's algorithm rather than being an arbitrary matrix.

`P20StaticSection4Derivation` exposes only the source-local results preceding
Theorem 4.1:

- the two decompositions and `zeta` bounds in (4.18)--(4.20);
- the retained/omitted partition from which (4.21)--(4.25) is derived;
- the omitted-product estimate (4.26);
- the raw accumulation estimate (4.27), its underflow count `r`, and
  `r <= np(p+1)/2`; and
- the quadratic `zeta^2` term shown in (4.28).

It does not contain equation (4.32), its collected four-term coefficient, or
a final forward-error certificate. The target must use matrix infinity-norm
submultiplicativity and the triangle inequality, bound `zeta` by the sum of
its two branches, substitute the bound on `r`, combine the omitted and
accumulation estimates, and place the quadratic and local omitted terms into
the explicit second-order remainder.

`p20FirstOrderLe` gives the paper's informal `lesssim` a fixed, pointwise
meaning: an exact inequality after adding the absolute value of a term
classified as second order. It has no arbitrary filter, eventual quantifier,
or unrelated asymptotic scale.

The derived coefficient in (4.32) has all four source terms:

- input rounding: `(p+1)u^p`;
- input underflow: `4 n u^(p-1) theta^(-1) gmin`;
- accumulation rounding: `(n+p^2)U`; and
- accumulation underflow: `2 p(p+1)n^2 theta^(-2) Gmin`.

The second target conclusion is itself a forward-error statement: it rewrites
the (4.32) right-hand side as the range-free (4.33) envelope plus the two
underflow envelopes. The third makes the discussion on B796 precise: relative
to the single-word input terms `2u` and `4n^2 theta^(-1)gmin`, the two
multiword input terms both contain the factor `u^(p-1)` (up to the displayed
dimension and word-count constants).

There is a source typo in that prose: B796 calls the second single-word term
`4n theta^(-1)gmin`, while equation (3.26) on B791 displays
`4n^2 theta^(-1)gmin`. The formal comparison follows the displayed equation,
so it states `n * multiwordInputUnderflow = u^(p-1) *
singlewordInputUnderflow`. This preserves the paper's qualitative
order-`u^(p-1)` conclusion without silently choosing the prose's missing
factor of `n`.

All arithmetic values are finite reals. NaNs and infinities are outside the
model. Underflow is included through `gmin` and `Gmin`; overflow is excluded
for every represented rounding operation. A concrete one-by-one, one-word
zero-matrix model, run, and Section 4 derivation establish that the hypotheses
are jointly satisfiable.
