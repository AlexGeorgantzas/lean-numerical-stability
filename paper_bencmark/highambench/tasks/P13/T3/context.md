# P13-T3 paper context

## Fixed source

The source is Nicholas J. Higham (2004), *The numerical stability of
barycentric Lagrange interpolation*. The local PDF SHA-256 is
`9ebf8adb699f96c82ccbb153dd6ca592c64475a8bc3e0703a50cb659b012c520`.

The selected source is the exact perturbed quotient preceding Theorem 4.1 on
PDF page 5 (printed page 551) and the two-condition-number forward bound in
Theorem 4.1, equations (4.2)--(4.3), on PDF page 6 (printed page 552).

## Local context and statement

The second barycentric formula is a quotient of a weighted-data sum and a
weight sum. Numerator and denominator perturbations are bounded separately.
The target gives an exact finite bound with denominator correction
`1/(1-epsilonDen*condDen)`; its first-order expansion is precisely the two
terms displayed by Higham, while the correction records the finite remainder
hidden by `O(u^2)`.
