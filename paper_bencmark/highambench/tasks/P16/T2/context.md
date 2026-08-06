# P16-T2 paper context

## Fixed source

The source is Buttari, Higham, Mary, and Vieublé (2026), *A modular framework
for the backward error analysis of GMRES*. The local PDF SHA-256 is
`8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`.

The selected result is the backward-error half of Lemma 4.2, equations
(4.14)--(4.15), on PDF page 19 (printed page 1957), together with the exact
residual identity (4.18) on PDF page 20 (printed page 1958).

## Local context and statement

The paper combines the correction residual with the computed-residual and
update errors, then drops second-order terms. The target keeps the exact
finite composition. Under the displayed operation bounds and
`||x_i||_2 <= ||x_{i+1}||_2`, it proves the next-residual recurrence with
coefficient `epsilonR + epsilonU + omega` and no hidden remainder.
