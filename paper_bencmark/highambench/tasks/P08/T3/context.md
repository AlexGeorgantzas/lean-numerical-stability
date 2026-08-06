# P08-T3 paper context

## Fixed source

The source is Robert D. Skeel (1980), *Iterative Refinement Implies Numerical
Stability for Gaussian Elimination*. The local PDF SHA-256 is
`f520066b46331dcbf25e51345c5ff5ffffe8fcad573d7f46e68834f83b3a2c54`.

The selected result is the induction step and finite geometric bound in Lemma
4.3 on PDF page 12, printed page 827, section 4.

## Local context and statement

The proof first obtains a componentwise affine recurrence for the exact
residuals and then says the lemma follows by induction. The target isolates
that deterministic core: `q_(m+1) = B*q_m + d_m`, the propagation matrix `B`
is nonnegative, and `abs(d_m) <= s`. It concludes the exact, finite
matrix-geometric budget. This retains every iteration term and introduces no
convergence limit, inverse, or big-O notation.
