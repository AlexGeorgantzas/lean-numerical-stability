# P03-T2 paper context

## Fixed source

The source is Erin Carson and Nicholas J. Higham, *Accelerating the Solution of
Linear Systems by Iterative Refinement in Three Precisions*, SIAM Journal on
Scientific Computing 40(2), A817--A847, 2018. The local PDF SHA-256 is
`952c6827db21fb2a9362b5aa4d38a1b2c75361f2cc7a3badbb7cd4a232d7b7bc`.

The selected result is Theorem 4.1 on PDF page 9, printed page A825, in
section 4, “Normwise backward error analysis.” Its derivation starts from
equation (4.1) on PDF page 8.

## Local context and statement

Write `R` for the old normwise residual, `D` for
`‖b‖ + ‖A‖‖x_i‖`, and `Y` for `‖A‖‖x_{i+1}‖`. The three local hypotheses
in the Lean target are precisely the bounds for residual-computation error,
correction-solve error, and update-rounding error used immediately before
Theorem 4.1. The denominator `1-c₁ κ(A) u_s` is positive under the paper's
stated condition.

Combining those three bounds and collecting the coefficient of `R` gives the
paper's `α_i`; collecting the data and update terms gives `β_i`. The target
keeps the exact rational coefficients and contains no asymptotic notation.
