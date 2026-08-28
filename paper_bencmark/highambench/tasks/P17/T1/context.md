# P17-T1 context

Source: Theorem 3.6 on PDF page 9 (journal page B1235), with its induction
continuing on PDF page 10 (journal page B1236). Lemma 3.2 on PDF page 8
(journal page B1234) supplies the conditional-bias pattern used by the theorem.

Theorem 3.6 studies random relative errors `delta_k` and bias variables
`beta_k`. It equates the expectations of the first pair and identifies each
later conditional mean of `delta_k` with the history-measurable `beta_k`. If
every `|beta_k|` is bounded by `B`, it claims that the expectation of the
accumulated product lies between `(1-B)^n` and `(1+B)^n`.

The published statement omits sign conditions used by its induction. The step
that multiplies the bounds for `1 + beta_k` by the preceding product requires
that product to be nonnegative, and the lower induction also requires
`1-B >= 0`. As written, the theorem admits a two-outcome counterexample.

This target is the project-authorized corrected version of Theorem 3.6. The
finite run therefore records:

- a positive number `n` of operations;
- a finite probability law;
- `0 < B <= 1`;
- random families `delta_k` and `beta_k`;
- nonnegative factors `1 + delta_k`;
- the pointwise bias bound `|beta_k| <= B`;
- history measurability of each `beta_k` after the first operation; and
- the finite test-function identity expressing
  `E(delta_k | delta_0, ..., delta_(k-1)) = beta_k`.

The goal is the expected full-product envelope. No bound on `delta_k` itself is
assumed, and the desired product bound is not a field of the run structure.

This is the corrected abstract theorem, not Remark 3.7's specialization to a
particular `SR_(p,r)` execution. Consequently, the target does not identify
`B` with a unit roundoff or claim algorithm linkage that Theorem 3.6 itself
does not contain. Actual stochastic rounding supplies the added sign conditions
through its separate rounding-error bound.

The frozen NumStability library provides finite-expectation linearity and
monotonicity, plus a deterministic product bound, but no theorem for this
conditional-expectation product induction.
