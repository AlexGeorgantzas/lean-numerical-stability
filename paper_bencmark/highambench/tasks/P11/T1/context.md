# P11-T1 paper context

## Fixed source

The source is Alicja Smoktunowicz, Jesse L. Barlow, and Julien Langou (2006),
*A note on the error analysis of classical Gram-Schmidt*. The local PDF
SHA-256 is
`72b7521848be07971a6721ea0356bb898c63e21b8ad3aa109fee8f41517284a5`.

The selected result is the exact first-column residual identity immediately
preceding equation (16) and the complete norm chain in equation (16), PDF page
10, printed page 308, in the appendix proof of Theorem 1.

## Mathematical setting

The standing input is a full-column-rank matrix `A` in `R^(m x n)`, where `m`
and `n` are positive and `n <= m`. Algorithm 2, CGS-P, computes rectangular
`Q` and upper-triangular `R`. Theorem 1 assumes for every leading block `R_k`
that

`c4(m,k) * epsilonM * kappa2(R_k)^2 < 1`.

This makes `R` nonsingular and in particular gives `r11 > 0`. The arithmetic
model is the paper's IEEE normalized-range relative-error model with machine
unit `epsilonM`; overflow, subnormal underflow, infinities, and NaNs are not
covered.

For the computed first normalization, standard division error supplies an
operator `G1` such that

`q1 = (I + G1) * a1 / r11` and `||G1||_2 <= epsilonM`.

The paper does not specify the entries or structure of `G1`, so the Lean model
keeps it opaque. Its norm is the exact induced spectral 2-norm, not the
Frobenius norm.

## Lean statement

`P11CGSPFirstColumnRun m n` is a proof-carrying contract for the computed
first column of an admissible CGS-P execution. It records the dimensions,
input and computed factors, full column rank, triangular structure, certified
inverses of all leading blocks, condition (3), nonnegative machine unit, and
the normalized first-column perturbation relation.

`P11Equation16 run` states all parts of the selected source passage:

- the computed normalization relation;
- the exact post-analysis identity `A1 - Q1*R1 = a1 - q1*r11`;
- the exact action identity `a1 - q1*r11 = -G1*a1`;
- identification of the one-column matrix 2-norm with its Euclidean column
  norm;
- invariance of that norm under the residual's minus sign;
- `||G1*a1||_2 <= ||G1||_2 * ||a1||_2`;
- `||G1||_2 * ||a1||_2 <= epsilonM * ||a1||_2`.

Together these fields are exactly the residual identity and complete norm
chain displayed in equation (16), with coefficient one. The matrix product
and subtraction are exact post-analysis operations on computed factors. No
additional rounding operation is introduced for evaluating the residual.

The paper uses higher-order suppression in the surrounding Theorem 1 analysis,
but equation (16) itself has no displayed `O(epsilonM^2)` remainder, so none is
added here. The source does not identify a rounding mode more precisely than
the stated IEEE normalized-range model.
