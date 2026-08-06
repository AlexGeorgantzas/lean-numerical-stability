# P08-T2 paper context

## Fixed source

The source is Robert D. Skeel (1980), *Iterative Refinement Implies Numerical
Stability for Gaussian Elimination*. The local PDF SHA-256 is
`f520066b46331dcbf25e51345c5ff5ffffe8fcad573d7f46e68834f83b3a2c54`.

The selected result is the first inequality of Lemma 4.2 on PDF page 11, printed page 826, section 4.

## Local context and statement

The paper rewrites the new iterate as `xNext = Ainv*q + x + h` and assumes
the componentwise update-rounding estimate
`abs(h) <= u*abs(Ainv*q) + u*abs(x)`. The selected conclusion bounds the residual image. The target expands the printed matrix products
`(I + u*abs(A)*abs(Ainv))*abs(q)` into finite sums, while requiring only the exact inverse action needed for this particular `q`.
