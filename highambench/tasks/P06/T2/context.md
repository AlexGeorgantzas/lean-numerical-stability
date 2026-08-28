# P06-T2 paper context

## Fixed source

The source is Michael P. Connolly and Nicholas J. Higham (2023),
*Probabilistic Rounding Error Analysis of Householder QR Factorization*. The
local PDF SHA-256 is
`c02a20e9ffa8039a5ad3db9261fba19929de84bf0bff7654547541dffe496a79`.

The selected result is equation (3.4), PDF page 5, printed page 1150,
section 3.

## Local context and statement

The paper embeds a rectangular matrix `M` in the symmetric block matrix
`[[0,M],[Mᵀ,0]]` and states that the largest eigenvalue of this dilation is
the operator 2-norm of `M`. The target records the equivalent threshold form:
for every nonnegative `L`, the rectangular operator bound by `L` holds exactly
when the dilation is bounded above by `L I` in quadratic-form order. This form
is sufficient for the rectangular concentration reduction and avoids adding a
separate eigenvalue definition to the controlled task.
