# P20-T1 context

Sources: equation (3.1) and its scaling assumptions on physical PDF page 4
(journal page B788), followed by equation (3.2), equation (3.4a), and the
maximum-coefficient statement on physical page 5 (journal page B789).

The paper computes `A * B` after left scaling `A` by a nonsingular diagonal
matrix `Lambda`. Each diagonal entry `lambda_i` is a power of two, so the
scaling itself introduces no rounding error in the paper's model. The allowed
scaled-input magnitude is fixed by the two format ceilings:

`theta = min fmax (sqrt (Fmax / n))`.

Here `fmax` is the largest finite input-format value, `Fmax` is the largest
finite accumulation-format value, and `n` is the inner-product dimension.
They are positive, and `n` is nonzero.

`p20InfNormVec` is defined explicitly as the finite maximum of the absolute
row coefficients. The theorem requires every row of `A` to have positive
infinity norm. This makes the quotients in (3.4a) defined; the paper does not
state a convention for a zero row.

For a row `x`, `p20RowScaleExponent` selects the integer exponent whose power
of two lies immediately below `theta / ||x||_infinity`, and
`p20RowScaleFactor` is that power of two. `p20RowScalingMatrix` collects these
factors as the diagonal matrix `Lambda`, while `p20LeftScaledMatrix` is the
literal matrix product `Lambda A`.

The target proves for every row that its selected factor is positive, is an
integer power of two, and satisfies the strict-lower/closed-upper interval
(3.4a). It then proves directly that every coefficient of the scaled row is at
most `theta` in absolute value and that one coefficient is strictly larger
than `theta / 2`.

All quantities are real. The paper assumes that `A`, `B`, and `C` are stored
exactly in a sufficiently high precision and that no underflow or overflow
occurs before the forward scaling or after the inverse scaling. This task
formalizes the exact scaling selection before input-format rounding; NaNs,
infinities, and range exceptions are outside its model.
