# P20-T2 context

Source: equation (3.13) and its derivation in equations (3.3)-(3.12) on
physical PDF page 5 (journal page B789).

For a nonzero row `x` and column `y` of positive length `n`, Model 1 fixes
the input-format unit roundoff `u`, input underflow envelope `gmin`, and
scaling threshold
`theta = min(fmax, sqrt(Fmax / n))`. The positive powers of two `lambda` and
`mu` satisfy the maximal scaling intervals (3.4a)-(3.4b).

The quantity `p20ScaledInputInnerProduct` is the exact inverse scaling of the
componentwise input-rounded vectors in (3.3). No accumulation-format rounding
is included at this stage. `p20InputStageError` is its difference from the
exact inner product, namely `epsilon_1` in (3.8).

The target proves the exact bound (3.13): the input-stage error is at most
`(2*u + u^2) * |x|^T|y|` plus
`4*n*theta^-1*gmin*(1 + u + theta^-1*gmin) * ||x||_infinity * ||y||_infinity`.
The real-valued rounding maps cover operations for which overflow does not
occur; NaNs and infinities are outside this model.
