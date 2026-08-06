# P03-T3 paper context

## Fixed source

The source is Erin Carson and Nicholas J. Higham, *Accelerating the Solution of
Linear Systems by Iterative Refinement in Three Precisions*, SIAM Journal on
Scientific Computing 40(2), A817--A847, 2018. The local PDF SHA-256 is
`952c6827db21fb2a9362b5aa4d38a1b2c75361f2cc7a3badbb7cd4a232d7b7bc`.

The selected result is Theorem 5.1, beginning on PDF page 10 / printed page
A826 and continuing on PDF page 11 / printed page A827, in section 5,
“Componentwise backward error analysis.” The proof uses equations (5.2)--(5.6).

## Local context and statement

Equation (5.2) separates the next residual into the old-residual term, the
residual-computation floor, the correction term, and update rounding. The
correction satisfies a Neumann-type inequality. Under (5.6), the inverse
`M₁ = (I-P)⁻¹` is entrywise nonnegative; applying it bounds the correction by
`M₁` applied to the old residual and data floor.

The neutral Lean target packages exactly the nonnegative inverse-action
contract, derives the correction bound by order-preserving matrix-vector
multiplication, and substitutes it into (5.2). Expanding the result gives the
`W_i` and `y_i` recurrence stated in Theorem 5.1.
