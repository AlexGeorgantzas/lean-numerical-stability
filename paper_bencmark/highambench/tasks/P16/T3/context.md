# P16-T3 paper context

## Fixed source

The source is Buttari, Higham, Mary, and Vieublé (2026), *A modular framework
for the backward error analysis of GMRES*. The local PDF SHA-256 is
`8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`.

The selected result is Theorem 6.3, equations (6.17)--(6.18), on PDF page 40
(printed page 1978).

## Local context and statement

Theorem 6.3 says that mixed-precision restarted GMRES contracts its forward
and backward errors by at least `Lambda = c(n,k) u_low kappa_F(A)` until the
high-precision attainable floors are reached. The target turns this into an
exact finite certificate: after `i` consecutive above-floor restarts, each
error is at most `Lambda^i` times its initial value. Supplying the actual
inverse for `Ainv` makes `p16ConditionNumberF A Ainv` the paper's Frobenius
condition number.
