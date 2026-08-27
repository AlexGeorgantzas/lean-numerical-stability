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

Here `c4(m,k) = c2(m,k) + 2*c1(m,k)`, with `c1(m,1) = 1` and
`c1(m,k) = 2*sqrt(2*m*k) + 2*sqrt(k)` for `k >= 2`, exactly as in
equation (2) on printed page 302.

This makes `R` nonsingular and in particular gives `r11 > 0`. The arithmetic
model is the paper's IEEE normalized-range relative-error model with machine
unit `epsilonM`; overflow, subnormal underflow, infinities, and NaNs are not
covered.

For the computed first normalization, standard division error produces an
operator `G1` such that

`q1 = (I + G1) * a1 / r11` and `||G1||_2 <= epsilonM`.

The theorem concludes only that such a dimension-compatible `G1` exists; it
does not assert unprinted structure or uniqueness. Its norm is the exact
induced spectral 2-norm, not the Frobenius norm.

## Lean statement

`P11CGSPFirstColumnRun m n` is a proof-carrying contract for the computed
first column of an admissible CGS-P execution. It records the dimensions,
input and computed factors, full column rank, triangular structure, certified
inverses of all leading blocks, condition (3), positive machine unit, and the
actual first-column Algorithm 2 operations. In particular, `r11` is linked to
a computed norm and each `q1` entry is linked to a normalized IEEE division.
The arithmetic interface supplies primitive relative division errors bounded
by `epsilonM`; it does not contain `G1` or equation (16).

The computed norm relation retains the source's
`(0.5*m+1)*epsilonM + O(epsilonM^2)` error. The unspecified higher-order term
is represented by one nonnegative arithmetic-level coefficient, without
assigning it a value.

`P11Equation16 run` existentially produces `G1` and states all parts of the
selected source passage:

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

The proof may construct a diagonal witness from the componentwise division
errors, but diagonality is not part of the public conclusion. The paper uses
higher-order suppression in the surrounding Theorem 1 analysis, but equation
(16) itself has no displayed `O(epsilonM^2)` remainder, so none is added to the
residual bound. The source does not identify a rounding mode more precisely
than the stated IEEE normalized-range model.
