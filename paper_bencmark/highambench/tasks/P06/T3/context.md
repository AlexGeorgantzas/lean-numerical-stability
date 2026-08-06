# P06-T3 paper context

## Fixed source

The source is Michael P. Connolly and Nicholas J. Higham (2023),
*Probabilistic Rounding Error Analysis of Householder QR Factorization*. The
local PDF SHA-256 is
`c02a20e9ffa8039a5ad3db9261fba19929de84bf0bff7654547541dffe496a79`.

The selected result is the product expansion in equations (4.8)--(4.9), PDF
page 7, printed page 1152, section 4, inside the proof of Lemma 4.2.

## Local context and statement

The paper expands a product of locally perturbed Householder transformations
into the exact product, the sum of terms containing one `ΔP_j`, and terms of
order at least two. Its matrices `F_j` are precisely the single-perturbation
insertions after conjugating through the surrounding exact factors. The target
makes the `O(u²)` bookkeeping exact: a scalar `t` marks each local perturbation,
`p06FirstOrderState` collects the terms with one marker, and
`p06HigherOrderState` explicitly collects all remaining terms after a factor
of `t²` is removed.
