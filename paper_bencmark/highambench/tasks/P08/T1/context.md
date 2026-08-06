# P08-T1 paper context

## Fixed source

The source is Robert D. Skeel (1980), *Iterative Refinement Implies Numerical
Stability for Gaussian Elimination*. The local PDF SHA-256 is
`f520066b46331dcbf25e51345c5ff5ffffe8fcad573d7f46e68834f83b3a2c54`.

The selected result is the second inequality of Lemma 4.2 on PDF page 11,
printed page 826, section 4.

## Local context and statement

The paper rewrites the new iterate as `xNext = Ainv*q + x + h` and assumes
`abs(h) <= u*abs(Ainv*q) + u*abs(x)`. The target is exactly its resulting
forward-error bound, with `abs(Ainv)*abs(q)` expanded as a finite sum. No full
matrix inverse object is required beyond the inverse action already present in
the displayed update.
