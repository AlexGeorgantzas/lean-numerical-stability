# P14-T2 paper context

## Fixed source

The source is Pierre Blanchard, Desmond J. Higham, and Nicholas J. Higham
(2021), *Accurately computing the log-sum-exp and softmax functions*.  The
local PDF SHA-256 is
`7247047bc49218e001195edc8a2d66131eea7596d252503f34b0ace6328981cd`.

The selected source is the componentwise derivation on PDF page 8 (printed
page 2318) and Theorem 3.3, equation (3.6), on PDF page 9 (printed page 2319).

## Local context and statement

The target records separate finite radii for exponential evaluation and the
final division.  Recursive summation contributes the denominator radius
`epsilonExp + gamma(u,n)*(1+epsilonExp)`.  Quotient composition supplies the
denominator-safety factor.  If both operation radii are `u`, the first-order
sum of radii is `(n+3)u`, exactly the constant displayed in Theorem 3.3.
