# P17-T3 paper context

## Fixed source

The source is El-Mehdi El Arar, Massimiliano Fasi, Silviu-Ioan Filip, and
Mantas Mikaitis, *Probabilistic Error Analysis of Limited-Precision Stochastic
Rounding*, SIAM Journal on Scientific Computing 47(5), B1227--B1249, 2025.
The local PDF SHA-256 is
`df1ce5dd33285adfcffc6a4c7ab94f9604b46739cb848c6cbb5f997e8fac597d`.

The selected result is Theorem 4.3, equation (4.11), on PDF page 15 / journal
page B1241. Its definitions and proof use equations (4.1)--(4.4) on PDF page
13 / B1239, the error decomposition (4.8) on PDF page 14 / B1240, and the
remainder and centered bounds (4.10) and (4.12) on PDF page 15 / B1241.
Lemma 3.10 and equations (3.8)--(3.9) on PDF pages 11--12 / B1237--B1238
provide the mean-independent errors and pathwise remainder bound.

## Recursive-summation execution

`P17VarianceRecursiveSumRun m Omega` extends the same proof-carrying
`SR_{p,r}` execution used by P17-T2. Lean's `m` is the paper's `n-1`, so the
run has `m+1` exact inputs and `m` rounded left-to-right additions.

- `run.a` is the exact input vector, `p17ExactSum run.a` is `y`, and
  `p17RecursiveSum run.a (run.delta ... omega)` is the computed `yHat` in
  equation (4.4).
- `run.p` and `run.r` are positive. `p17UnitRoundoff run.p` is `u_p`, and
  `p17UnitRoundoff (run.p + run.r)` is `u_(p+r)`.
- `delta_k` is the relative error of the actual limited-precision stochastic
  rounding step. `beta_k` is the corresponding deterministic `p+r`-bit
  truncation error, linked to that step's exact pre-rounding value.
- The base run records the local error bounds, nonnegative rounding factors,
  zero-result convention, history dependence of `beta`, and the conditional
  identity `E(delta_k | prior errors) = beta_k`.
- `p17Alpha run k omega = delta_k - beta_k`. The extended run records the
  conclusions of Lemma 3.10 that `alpha_k` is mean independent and
  `|alpha_k| <= u_p`.

The finite sample space represents the finite support of the random choices in
one finite computation. As in the paper's standard relative-error model, the
real-valued trace describes nonexceptional operations and does not model
overflow, underflow, NaNs, or infinities.

## Error decomposition and inherited lemmas

`p17RecursiveCoefficient error i` is the suffix product multiplying input
`a_i` in equation (4.4). It gives the paper's path-dependent quantities

```text
B_i = coefficient(delta)_i - coefficient(alpha)_i
M   = sum_i a_i * (coefficient(alpha)_i - 1)
A   = sum_i a_i * B_i.
```

Thus the computed error is exactly `yHat-y = M+A`; `A` is a random function of
the outcome, not a fixed scalar bias.

The extended run carries two source-derived certificates rather than assuming
the final theorem:

- `coefficient_remainder_bound` is Lemma 3.10's bound enlarged to the uniform
  `gamma_m(u_p+u_(p+r))-gamma_m(u_p)` radius used in equation (4.10).
- `alpha_product_covariance_bound` is the suffix-product specialization of
  reference [11, Lemma 3.1], which Theorem 4.3 explicitly invokes. It bounds
  each centered suffix-product covariance by `gamma_m(u_p^2)`.

The target proof must derive the second-moment bound for `M` by summing those
covariances, apply finite Chebyshev, derive the pathwise bound for `A`, and
assemble the final event. Neither equation (4.12) nor the final probability
event is a run field.

## Fixed conclusion

The exact sum is required to be nonzero, as needed by the relative error and
the condition number in equation (4.2). For every `0 < lambda < 1`, the target
states that, with probability at least `1-lambda`,

```text
|yHat-y| / |y| <= kappa(a) *
  (sqrt(gamma_m(u_p^2) / lambda)
    + gamma_m(u_p+u_(p+r)) - gamma_m(u_p)).
```

Here `p17SummationCondition run.a` is exactly
`kappa(a) = (sum_i |a_i|)/|y|`, and
`p17Gamma m u = (1+u)^m-1`. All indices, constants, and higher-order gamma
terms are retained exactly; this is not the first-order asymptotic expression.
