# P03-T3 paper context

## Fixed source

The source is Erin Carson and Nicholas J. Higham, *Accelerating the Solution of
Linear Systems by Iterative Refinement in Three Precisions*, SIAM Journal on
Scientific Computing 40(2), A817--A847, 2018. The local PDF SHA-256 is
`952c6827db21fb2a9362b5aa4d38a1b2c75361f2cc7a3badbb7cd4a232d7b7bc`.

The selected result is Theorem 5.1. It begins on PDF page 10 / printed page
A826 and continues on PDF page 11 / printed page A827 in section 5,
"Componentwise backward error analysis." The target is the theorem's exact
componentwise residual recurrence, not the later asymptotic interpretation in
equation (5.7) and not the later bound on componentwise backward error.

## Algorithm and numerical model

`P03ComponentwiseIRRun n` is a proof-carrying execution of the unscaled
Algorithm 1.1 for a positive dimension `n` and a nonsingular real system
`A x = b`:

- `Ainv` is the inverse of `A`, recorded by left and right inverse actions.
- `x i`, `rHat i`, and `dHat i` are the stored iterate, computed residual, and
  computed correction at iteration `i`.
- `uR <= u <= uS <= uF`; `uR` is nonnegative. Residuals are computed at `uR`
  and rounded to `uS`, updates are rounded at `u`, and the correction solver
  has effective precision `uS`.
- `p03MaxAugmentedRowNnz A b` is the paper's `p`, the maximum number of
  nonzeros in a row of `[A b]`. `GammaValid` makes
  `gamma uR p = p*uR/(1-p*uR)` finite and nonnegative.
- `residual_equation` and `residual_error_bound` are exactly the residual model
  (3.3), with `rHat i` kept distinct from the exact residual `b - A*x i`.
- `correction_solver_bound` is the componentwise solver model (2.5), with an
  iteration-dependent entrywise nonnegative matrix `G i`.
- `update_equation` and `update_error_bound` are exactly the rounded update
  model (3.6).

Theorem 5.1 states no accuracy model for the initial solve in step 1 and its
proof uses only the stored starting iterate and the refinement loop. Accordingly,
`x 0` is arbitrary; every residual, correction, and update from that point is
constrained by the paper's displayed models.

As in the paper's standard-model analysis, these real-valued equations exclude
underflow and overflow. Section 6's scaled variant is not part of this task.

## Theorem 5.1 quantities

All vector and matrix absolute values are entrywise, all inequalities in the
target are componentwise, and `p03MatInfNorm` is the induced infinity norm.
For every iteration `i`, the controlled definitions state

```text
exactResidual_i = b - A*x_i
data_{i+1}       = |b| + |A|*|x_{i+1}|
Z_i              = uS*G_i + (1+uS)*gamma_p^r*|A|
P_i              = Z_i*|Ainv|
M_i              = (I-P_i)^(-1)
W_i              = uS*I + (1+uS)*M_i*P_i
y_i              = (1+uS)*(1+u)*gamma_p^r
                     *(I+M_i*P_i)*data_{i+1}
                   + u*|A|*|x_{i+1}|.
```

The products have the displayed noncommutative order. Although the paper calls
the first two iteration-dependent matrices `Z_1` and `M_1`, `Z_1` contains
`G_i`; the Lean definitions expose that dependence through the argument `i`.

Condition (5.6) is recorded uniformly for every iteration:

```text
uS * ||G_i*|Ainv|||_inf
  + (1+uS)*gamma_p^r * |||A|*|Ainv|||_inf <= 1/2.
```

The paper proves immediately before Theorem 5.1 that this condition makes
`I-P_i` an M-matrix, so `M_i` exists, is entrywise nonnegative, and has
`||M_i||_inf <= 2`. The run carries those three derived facts as a Lean
certificate together with condition (5.6); they are not a replacement for the
condition or an additional numerical assumption.

## Fixed conclusion

For arbitrary `i : Nat` and every component `j`, the target is exactly

```text
|exactResidual_{i+1}|_j <= (W_i*|exactResidual_i|)_j + (y_i)_j.
```

The proof derives equation (5.1) from the rounded update, combines (3.3),
(3.6), and (2.5) to obtain equation (5.2), and derives

```text
c_i <= P_i*c_i + P_i*q_i,
```

where `c_i = Z_i*|dHat_i|` and `q_i` is the bracketed source vector in (5.4).
Applying the nonnegative inverse gives `c_i <= M_i*P_i*q_i`; substitution into
(5.2) and exact distribution produces the printed `W_i` and `y_i` recurrence.
No big-O term or suppressed higher-order term is introduced.
