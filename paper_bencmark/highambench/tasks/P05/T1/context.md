# P05-T1 paper context

## Fixed source

The source is Siegfried M. Rump and Claude-Pierre Jeannerod (2014),
*Improved Backward Error Bounds for LU and Cholesky Factorizations*. The local
PDF SHA-256 is
`dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6`.

The selected result is Lemma 4.1, PDF page 10, printed page 693, section 4.1.

## Local context and statement

The paper first bounds the scalar residual by `k*u` times the sum of the
magnitudes of the computed result, `c`, and all product terms. It then assigns
sign-aligned perturbation coefficients to those same sources. Every
coefficient has magnitude at most `k*u`, and the resulting perturbed equation
is exact. The Lean target isolates precisely this coefficient-distribution
step. Its `Fin k` indexes the paper's product terms after renaming the paper's
`k-1` to Lean's `k`; accordingly the coefficient is `(k+1)u`. The nested
`Option` index is only a disjoint union of the three source families.
