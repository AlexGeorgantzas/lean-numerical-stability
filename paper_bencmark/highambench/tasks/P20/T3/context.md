# P20-T3 context

Selected result: Theorem 4.1, especially equations (4.29)--(4.32), on
physical PDF page 11 (journal page B795). Equation (4.33) on the same page is
the range-unrestricted comparator.

The theorem concerns real matrices `A : R^(m x n)` and `B : R^(n x q)`, with
positive dimensions and a positive number `p` of low-precision words. The
exact reference product is `A * B`; the quantity bounded in (4.32) is the
matrix infinity norm of the actual computed result minus that exact product.

`P20Model1` records the mixed-precision MMA model from physical pages 2--3
(B786--B787). Its binary input and accumulation formats determine `u`, `U`,
`fmax`, `Fmax`, `gmin`, and `Gmin`. The accumulation precision and exponent
range contain those of the input format. The input- and accumulation-rounding
maps satisfy (2.3) and (2.4): each error is either a bounded relative error or
a bounded underflow error, but not both. The maps represent operations for
which overflow does not occur. The formal model uses the paper's default
round-to-nearest case. The directed-mode doubling remark after (2.4) is not
separately parameterized in this task.

The scaling threshold is not arbitrary:

`theta = min(fmax, sqrt(Fmax / n))`.

The diagonal entries of `Lambda` and `M` are positive powers of two.
`p20MaximalPowerTwoScale` records both endpoints of (3.4a)--(3.4b), because
the derivation of Theorem 4.1 uses the lower endpoint even though the printed
theorem repeats only the upper elementwise bound. A zero row or column uses
the explicit harmless factor `1`; the paper leaves that convention unstated.
Every element of `Lambda A` and `B M` is bounded by `theta`.

`P20MultiwordRun` then records the computation itself. `Aword` and `Bword`
satisfy the rounded residual recurrences (4.29)--(4.30), with indices
`0,...,p-1` and rounding to the input format. `p20RetainedWordProduct` retains
exactly the pairs `i+j<p`, weights each accumulation-format inner product by
`u^(i+j)`, and `p20UnscaleProduct` applies `Lambda^(-1)` and `M^(-1)` as in
(4.31). Thus `run.computed` is linked to the source algorithm rather than
being an arbitrary matrix.

The paper's derivation (4.18)--(4.28) separates four first-order error sources:

- input rounding or truncation: `(p+1)u^p`;
- input underflow: `4 n u^(p-1) theta^(-1) gmin`;
- accumulation rounding: `(n+p^2)U`;
- accumulation underflow: `2 p(p+1)n^2 theta^(-2) Gmin`.

`P20MultiwordErrorData` and `P20MultiwordForwardAnalysis` are the
proof-carrying form of that derivation. They expose the reconstructed word
sums, the exact retained product, the omitted tail, and the input and
accumulation errors. The split error parts must vanish whenever the matching
Model-1 relative- or underflow-error function vanishes. The four contribution
matrices are fixed formulas from those objects, and the remainder is defined
as the exact residual after subtracting them from the actual forward-error
matrix. Each contribution has the corresponding source bound, and the fixed
remainder norm must be second order. The structures do not assume (4.32).

Equations (4.26)--(4.33) use an undefined `lesssim`, and (4.28) contains the
quadratic term omitted from (4.32). `p20FirstOrderLeAt` therefore gives this a
precise first-order meaning: the displayed inequality holds along a nontrivial
precision filter with an additive remainder whose norm is `O(scale^2)`. The
target derives (4.32) by the matrix infinity-norm triangle inequality and the
four component bounds.

The target also states the literal coefficient comparison with (4.33): the
narrow-range coefficient is the range-free coefficient plus the two
underflow coefficients. This secondary identity compares the displayed
right-hand sides only; it is not asserted to be an exact relation between the
two `lesssim` error bounds, and the old equality/iff/strictness claims have
been removed.

All matrices and rounding witnesses are finite real objects. NaNs and
infinities are outside the model. Underflow is included through `gmin` and
`Gmin`; overflow is excluded on the operations represented by Model 1 and by
the source scaling assumptions. A concrete one-by-one, one-word zero-matrix
execution with identity rounding validates that the formal assumptions are
jointly satisfiable.
