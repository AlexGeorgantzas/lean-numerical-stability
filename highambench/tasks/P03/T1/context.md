# P03-T1 paper context

## Fixed source

The source is Erin Carson and Nicholas J. Higham, *Accelerating the Solution of
Linear Systems by Iterative Refinement in Three Precisions*, SIAM Journal on
Scientific Computing 40(2), A817--A847, 2018. The local PDF SHA-256 is
`952c6827db21fb2a9362b5aa4d38a1b2c75361f2cc7a3badbb7cd4a232d7b7bc`.

The selected result is equation (4.1), PDF page 8, printed page A824, in
section 4, “Normwise backward error analysis.”

## Local context and statement

At refinement step `i`, the computed residual is the exact residual plus the
residual-computation error `Δr`. The next stored iterate is the old iterate
plus the computed correction and the update-rounding error `Δx`. Expanding the
matrix-vector product gives equation (4.1): the new residual is exactly the
sum of the residual-computation, correction-solve, and update-rounding terms.

The Lean theorem records this equality component by component. It assumes only
the two defining identities needed for the algebra and uses the same statement
and P03 definitions in conditions N and L.
