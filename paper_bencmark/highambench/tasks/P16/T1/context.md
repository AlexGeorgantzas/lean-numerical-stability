# P16-T1 paper context

## Fixed source

The source is Alfredo Buttari, Nicholas J. Higham, Theo Mary, and Bastien
Vieublé (2026), *A modular framework for the backward error analysis of
GMRES*. The local PDF SHA-256 is
`8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`.

Equation (1.1) on PDF page 1 (printed page 1939) fixes a nonsingular square
real matrix `A` and a nonzero right-hand side `b`. Section 2 on PDF page 4
(printed page 1942) defines the normwise backward error of a computed candidate
`xHat` as the minimum shared `epsilon` over perturbations `deltaA`, `deltaB`
satisfying

`(A + deltaA)xHat = b + deltaB`,
`||deltaA||_F <= epsilon ||A||_F`, and
`||deltaB||_2 <= epsilon ||b||_2`.

It states that this minimum equals
`||b - A xHat||_2 / (||A||_F ||xHat||_2 + ||b||_2)`.

## Local context and statement

The target encodes the displayed minimum with `IsLeast`. Membership supplies
perturbations attaining the normalized residual with one shared relative
level. The lower-bound field says every perturbation pair satisfying both
relative bounds has `epsilon` at least the normalized residual. The nonzero
right-hand side makes the denominator positive; nonsingularity records the
paper's standing linear-system setting. This is an exact real statement and
does not require a floating-point model, exceptional-value assumptions, or
higher-order terms.
