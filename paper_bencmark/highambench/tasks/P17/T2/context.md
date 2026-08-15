# P17-T2 context

Source: equations (4.1)--(4.6) and Theorem 4.1 on PDF page 13
(journal page B1239), with its proof on PDF page 14 (journal page B1240).

The paper recursively sums `n` real inputs using precision-`p`
limited-precision stochastic rounding `SR_{p,r}`. It sets the first partial sum
equal to the first input and performs `n-1` rounded additions. This target uses
`m + 1` inputs, so Lean's `m` is the paper's `n - 1`.

`P17LimitedPrecisionRecursiveSumRun m Omega` records one finite stochastic
execution model:

- `a` is the exact input vector and `p17RecursiveSum` is the left-to-right
  rounded recurrence from the table before equation (4.4).
- `p` is the output precision and `r` is the positive random-bit count.
  `p17UnitRoundoff q` is `u_q = 2^(1-q)` on the required positive-precision
  domain.
- `delta k` is the relative error of rounded addition `k`; its factor is
  nonnegative and its magnitude is at most `u_p`.
- `beta k` is the deterministic relative error obtained by truncating that
  addition's exact pre-rounding value to `p+r` bits. The field
  `truncation_equation` links it to that value, and `|beta k| <= u_(p+r)`.
- `p17HistoryMeasurable` means that a random variable depends only on errors
  preceding a given addition. `conditional_mean` is the finite test-function
  form of Lemma 3.2's
  `E(delta_k | delta_0,...,delta_(k-1)) = beta_k`; it is not an assumed bound on
  the final suffix products.
- `p17ExpectedRecursiveSum` is the expectation of the generated final partial
  sum under the finite probability law.

The finite sample space represents the finite support of a computation using a
finite number of random bits. The trace is an axiomatic real-valued model of
nonexceptional `SR_{p,r}` executions: it does not formalize bit encodings,
overflow, underflow, NaNs, or infinities, which are outside the paper's standard
relative-error model.

The exact sum is `p17ExactSum run.a`, and the explicit nonzero hypothesis gives
the domain of the relative condition number in equation (4.2). The conclusion
is exactly equation (4.6):

`|E(yHat)-y| / |y| <= kappa(a) * gamma_m(u_(p+r))`,

where `p17Gamma m u = (1+u)^m-1`. The suffix-product expectation envelope used
in the paper's proof must be derived from the run's local conditional-mean and
truncation-error fields; it is not a premise of the target.
